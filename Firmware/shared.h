#include <stdbool.h>
#include <stddef.h>
#include <stdint.h>
#include <stdio.h>
#include <stdlib.h>
#include <string.h>
#include <stdatomic.h>

#include "nvs.h"
#include "shared.h"
#include "c_shims.h"
#include "img_converters.h"

/* Compile-time RGB565 helper for static const C initializers */
#define COLOR565(r, g, b) \
  ((uint16_t)(((((uint16_t)(r)) & 0xF8U) << 8) | \
              ((((uint16_t)(g)) & 0xFCU) << 3) | \
              (((uint16_t)(b)) >> 3)))

/* ================= NVS NAMESPACES ================= */
/* "cnt" — file counters (pictureNumber, videoNumber) */
/* "cam" — camera sensor settings (CameraSettings struct) */

/* ================= NVS HELPERS (C / ESP-IDF) ================= */
static int32_t nvs_read_i32(const char *ns, const char *key, int32_t default_val) {
  nvs_handle_t handle;
  int32_t val = default_val;
  if (nvs_open(ns, NVS_READONLY, &handle) == ESP_OK) {
    nvs_get_i32(handle, key, &val);
    nvs_close(handle);
  }
  return val;
}

static void nvs_write_i32(const char *ns, const char *key, int32_t val) {
  nvs_handle_t handle;
  if (nvs_open(ns, NVS_READWRITE, &handle) == ESP_OK) {
    nvs_set_i32(handle, key, val);
    nvs_commit(handle);
    nvs_close(handle);
  }
}

/* ================= ENCODER STATE TABLE ================= */
/* Quadrature state table — DRAM_ATTR ensures ISR-safe access during flash operations. */
/* Index = (prevState << 2) | currState, where state = (CLK << 1) | DT. */
/* +1 = CW step, -1 = CCW step, 0 = invalid/bounce (ignored). */
static const DRAM_ATTR int8_t ENC_TABLE[16] = {
   0, -1,  1,  0,
   1,  0,  0, -1,
  -1,  0,  0,  1,
   0,  1, -1,  0
};

/* ================= GLOBAL VARIABLE DEFINITIONS ================= */
/* All globals declared as extern in shared.h are defined here (except */
/* AVI writer globals in avi_writer.c/cpp and webServer in wifi_server.c/cpp). */

SemaphoreHandle_t spiMutex = NULL;
volatile AppState appState = STATE_IDLE;
EventGroupHandle_t appEvents = NULL;
QueueHandle_t inputEventQueue = NULL;
SDStatus globalSDState = {false, false, "NO CARD"};
CameraSettings camSettings = { 1, 0, 2, 0, 0, 0, 1, 0, 12, 10, 0, 0, 0, 5 };
camera_config_t config;
int pictureNumber = 0;
/* Video removed — kept as zero/NULL placeholders only if declared extern in shared.h */
int videoNumber = 0;
unsigned long recordingStartTime = 0;
sd_file_t *videoFile = NULL;
TaskHandle_t taskDisplayHandle = NULL;

/* Display buffer (single DRAM buffer on ESP32-WROOM-32 without PSRAM) */
uint8_t *dispBuf[2] = {NULL, NULL};
volatile size_t dispLen[2] = {0, 0};
static size_t dispBufCap = 0;
atomic_int dispWriteSlot = 0;
atomic_int dispReadSlot = -1;
atomic_int dispRendering = -1;

/* Unused video/audio placeholders for shared.h extern compatibility (zero RAM allocated) */
uint8_t *recPool[REC_POOL_SIZE] = {NULL, NULL, NULL};
QueueHandle_t recFrameQueue = NULL;
SemaphoreHandle_t recPoolFree = NULL;
int recPoolWriteIdx = 0;
int16_t *audioRecBuf = NULL;
i2s_chan_handle_t i2s_rx_handle = NULL;

/* Gallery state */
char **galleryFiles = NULL;
int galleryFileCount = 0;
int galleryIndex = 0;
int galleryTypeSelection = 0;
int deleteSelection = 0;
volatile bool galleryNeedsRedraw = false;

/* Menu state */
int menuMainSelection = 0;
int settingsIndex = 0;
bool settingsEditing = false;
int resetCounterConfirm = 0;

/* Encoder ISR state — DRAM_ATTR keeps these in internal SRAM so ISRs */
/* can access them safely even during flash cache misses (e.g. SD writes). */
DRAM_ATTR volatile uint8_t  encPrevState = 3;   /* both HIGH at boot (INPUT_PULLUP default) */
DRAM_ATTR volatile int8_t   encAccum     = 0;   /* direction accumulator between detents */
DRAM_ATTR volatile uint32_t encSwPressMs = 0;   /* timestamp of SW button press edge */

/* Debug counters: ISR increments, taskInput reads and prints the delta. */
/* Safe because uint32 reads/writes are atomic on Xtensa; no mutex needed. */
#if DEBUG_INPUT
volatile uint32_t dbgEncCw    = 0;
volatile uint32_t dbgEncCcw   = 0;
volatile uint32_t dbgEncClick = 0;
volatile uint32_t dbgEncLong  = 0;
#endif

/* ================= TASK & HELPER PROTOTYPES (file-local) ================= */
static void taskSDMonitor(void *pvParameters);
static void taskCapture(void *pvParameters);
static void taskDisplay(void *pvParameters);
static void taskInput(void *pvParameters);
static void sendInputEvent(InputEventType t);
static void savePhotoHighRes(void);
static void drawStatusBar(float fps);
static void encoderISR(void);
static void encSwISR(void);
static void runTimelapse(void);
static void runSelfTimerCountdown(void);
static void runBootAnimation(void);
static uint8_t ov7670_jpeg_quality(int cam_quality);

/* ================= SETUP ================= */
void setup(void) {
  serial_begin(115200);
#if DEBUG_BOOT_DELAY
  delay(8000);  /* Long delay for Serial Monitor attachment during debugging */
#else
  delay(1000);
#endif

  wifi_set_off();
  esp_bt_controller_disable();

  /* Boot button (GPIO 0) no longer used — mirror and WiFi are in encoder menu. */
  pinMode(SHUTTER_BTN_PIN_2, INPUT_PULLUP);

  /* LED flashlight output (GPIO4). Always starts OFF — the LED only activates */
  /* during photo capture, never in idle or menus. */
  pinMode(LED_FLASHLIGHT_PIN, OUTPUT);
  digitalWrite(LED_FLASHLIGHT_PIN, LOW);

  pinMode(ENC_CLK, INPUT_PULLUP);
  pinMode(ENC_DT,  INPUT_PULLUP);
  pinMode(ENC_SW,  INPUT_PULLUP);

  spiMutex = xSemaphoreCreateMutex();
  appEvents = xEventGroupCreate();
  inputEventQueue = xQueueCreate(16, sizeof(InputEvent));

  spi_begin(TFT_SCK, TFT_MISO, TFT_MOSI, SD_CS_PIN);
  delay(100);

  tft_init();
  tft_setRotation(1);
  tft_fillScreen(TFT_BLACK);

  /* Boot animation — retro first impression before hardware init */
  runBootAnimation();

  /* Load photo counter from NVS */
  pictureNumber = (int)nvs_read_i32("cnt", "pic", 0);

  /* Load camera settings from NVS */
  loadCameraSettings();

  /* Build EXIF metadata block */
  buildExifBlock();

  serial_printf("Initial image no: %d\n", pictureNumber);

  /* CAMERA CONFIG (ESP32-WROOM-32 + OV7670 V2) */
  config.ledc_channel = LEDC_CHANNEL_0;
  config.ledc_timer   = LEDC_TIMER_0;
  config.pin_d0       = Y2_GPIO_NUM;
  config.pin_d1       = Y3_GPIO_NUM;
  config.pin_d2       = Y4_GPIO_NUM;
  config.pin_d3       = Y5_GPIO_NUM;
  config.pin_d4       = Y6_GPIO_NUM;
  config.pin_d5       = Y7_GPIO_NUM;
  config.pin_d6       = Y8_GPIO_NUM;
  config.pin_d7       = Y9_GPIO_NUM;
  config.pin_xclk     = XCLK_GPIO_NUM;
  config.pin_pclk     = PCLK_GPIO_NUM;
  config.pin_vsync    = VSYNC_GPIO_NUM;
  config.pin_href     = HREF_GPIO_NUM;
  config.pin_sccb_sda = SIOD_GPIO_NUM;
  config.pin_sccb_scl = SIOC_GPIO_NUM;
  config.pin_pwdn     = PWDN_GPIO_NUM;
  config.pin_reset    = RESET_GPIO_NUM;
  /* OV7670 V2 runs reliably at 10 MHz XCLK on ESP32 (20 MHz can cause PCLK/sync artifacts) */
  config.xclk_freq_hz = 10000000;

  initCamera(IDLE_MODE, IDLE_RESOLUTION, IDLE_JPEG_QUALITY);

  allocateBuffers();

  delay(2000);

  /* Task: SD Card Monitor (Core 0, Priority 1) */
  xTaskCreatePinnedToCore(taskSDMonitor, "SD_Mon", 4096, NULL, 1, NULL, 0);

  /* Task: Button/Input Handler (Core 0, Priority 2) */
  xTaskCreatePinnedToCore(taskInput, "Input", 4096, NULL, 2, NULL, 0);

  /* Task: TFT Display (Core 1, Priority 3) — sized for ESP32-WROOM-32 DRAM */
  xTaskCreatePinnedToCore(taskDisplay, "Display", 10240, NULL, 3, &taskDisplayHandle, 1);

  /* Task: Camera Capture (Core 1, Priority 6 - highest) */
  xTaskCreatePinnedToCore(taskCapture, "Capture", 6144, NULL, 6, NULL, 1);

  /* Attach encoder interrupts AFTER tasks are created so the queue exists. */
  attachInterrupt(digitalPinToInterrupt(ENC_CLK), encoderISR, CHANGE);
  attachInterrupt(digitalPinToInterrupt(ENC_DT),  encoderISR, CHANGE);
  attachInterrupt(digitalPinToInterrupt(ENC_SW),  encSwISR,  CHANGE);
  serial_println("Encoder ISRs attached (CLK+DT+SW).");

  serial_println("Cam is ready (ESP32-WROOM-32 + OV7670 V2, photo-only). Tasks launched.");
}

/* ================= LOOP ================= */
void loop(void) {
  vTaskDelete(NULL);
}

/* ================= BUFFER ALLOCATION (ESP32-WROOM-32 INTERNAL DRAM) ================= */
void allocateBuffers(void) {
  /* ESP32-WROOM-32 has no PSRAM: allocate a single display buffer in internal DRAM. */
  dispBuf[0] = (uint8_t *)malloc(DISP_BUF_SIZE);
  if (dispBuf[0]) {
    dispBufCap = DISP_BUF_SIZE;
  } else {
    /* Fallback to QQVGA RGB565 buffer (38.4 KB) if DRAM cannot fit full QVGA */
    size_t qqvgaBytes = 160U * 120U * 2U;
    dispBuf[0] = (uint8_t *)malloc(qqvgaBytes);
    dispBufCap = dispBuf[0] ? qqvgaBytes : 0;
    if (!dispBuf[0]) serial_println("[ERR] dispBuf[0] alloc failed!");
  }
  dispBuf[1] = NULL;

  serial_printf("[MEM] Free internal DRAM after boot alloc: %u bytes\n",
                (unsigned int)heap_caps_get_free_size(MALLOC_CAP_INTERNAL | MALLOC_CAP_8BIT));
}

/* Centred transient message. Pausing taskDisplay during the hold is essential */
/* in IDLE — otherwise the next camera frame pushes over the text within ~40 ms */
/* and the user only sees a one-frame flash of e.g. "NO SD CARD!". */
void showTFTMessage(const char *msg, uint16_t color, int durationMs) {
  AppState saved = appState;
  bool pauseDisplay = (durationMs > 0 && saved == STATE_IDLE);
  if (pauseDisplay) appState = STATE_PHOTO;

  if (xSemaphoreTake(spiMutex, portMAX_DELAY)) {
    tft_fillRect(0, 80, 320, 60, TFT_BLACK);
    tft_setTextDatum(middle_center);
    tft_setTextSize(2);
    tft_setTextColor(color);
    tft_drawString(msg, tft_width() / 2, 110);
    tft_setTextDatum(top_left);
    xSemaphoreGive(spiMutex);
  }
  if (durationMs > 0) vTaskDelay(pdMS_TO_TICKS(durationMs));

  if (pauseDisplay) appState = saved;
}

/* ================= HELPER: EMERGENCY EXIT ================= */
/* Exits any menu/gallery state back to IDLE. Reverts uncommitted settings edits, */
/* frees gallery memory, reinits camera and clears the screen. */
void emergencyExitToIdle(void) {
  serial_println("[MENU] Emergency exit -> IDLE");
  if (settingsEditing) {
    loadCameraSettings();
    settingsEditing = false;
  }
  freeGalleryFiles();
  initCamera(IDLE_MODE, IDLE_RESOLUTION, IDLE_JPEG_QUALITY);
  if (xSemaphoreTake(spiMutex, portMAX_DELAY)) {
    tft_fillScreen(TFT_BLACK);
    xSemaphoreGive(spiMutex);
  }
  appState = STATE_IDLE;
}

/* ================= TASK: SD MONITOR (Core 0, Priority 1) ================= */
static void taskSDMonitor(void *pvParameters) {
  (void)pvParameters;

  while (true) {
    /* WiFi mode: lightweight SD presence check only. */
    /* Skip remount attempts (sd_end/sd_begin) to avoid colliding with active downloads. */
    /* Update globalSDState so web routes return correct errors if SD removed. */
    /* Update TFT status so user can see SD state without browser. */
    if (appState == STATE_WIFI_MODE) {
      if (xSemaphoreTake(spiMutex, pdMS_TO_TICKS(500)) == pdTRUE) {
        bool wasMounted = globalSDState.isMounted;
        if (sd_card_type() == CARD_NONE || sd_total_bytes() == 0) {
          globalSDState.isMounted = false;
          globalSDState.isFull = false;
          globalSDState.errorMsg = "SD REMOVED";
        } else {
          globalSDState.isMounted = true;
          uint64_t freeBytes = sd_total_bytes() - sd_used_bytes();
          globalSDState.isFull = (freeBytes < 10ULL * 1024ULL * 1024ULL);
          globalSDState.errorMsg = globalSDState.isFull ? "SD FULL" : "READY";
        }
        xSemaphoreGive(spiMutex);

        /* SD state changed — update TFT bottom bar */
        if (wasMounted != globalSDState.isMounted) {
          if (xSemaphoreTake(spiMutex, pdMS_TO_TICKS(200))) {
            tft_fillRect(0, 210, 320, 30, TFT_BLACK);
            tft_setTextDatum(middle_center);
            tft_setTextSize(1);
            if (!globalSDState.isMounted) {
              tft_setTextColor(TFT_RED);
              tft_drawString("! SD CARD REMOVED !", tft_width() / 2, 220);
              serial_println("[WIFI] SD card removed during WiFi mode.");
            } else {
              tft_setTextColor(0x7BEF);
              tft_drawString("Press to exit", tft_width() / 2, 220);
              serial_println("[WIFI] SD card re-inserted during WiFi mode.");
            }
            tft_setTextDatum(top_left);
            xSemaphoreGive(spiMutex);
          }
        }
      }
      vTaskDelay(pdMS_TO_TICKS(3000));
      continue;
    }

    if (xSemaphoreTake(spiMutex, pdMS_TO_TICKS(1000)) == pdTRUE) {
      bool currentMount = false;
      bool currentFull = false;
      const char *msg = "";

      if (sd_card_type() == CARD_NONE || sd_total_bytes() == 0) {
        sd_end();
        if (!sd_begin(SD_CS_PIN, 20000000)) {
          currentMount = false;
          msg = "NO SD CARD";
        } else {
          currentMount = true;
        }
      } else {
        currentMount = true;
      }

      if (currentMount) {
        uint64_t total = sd_total_bytes();
        uint64_t used = sd_used_bytes();
        uint64_t freeSpace = total - used;

        if (freeSpace < 10ULL * 1024ULL * 1024ULL) {
          currentFull = true;
          msg = "SD FULL";
        } else {
          currentFull = false;
          msg = "READY";
        }
      }

      globalSDState.isMounted = currentMount;
      globalSDState.isFull = currentFull;
      globalSDState.errorMsg = msg;

      xSemaphoreGive(spiMutex);
    }

    vTaskDelay(pdMS_TO_TICKS(2000));
  }
}

/* ================= INPUT EVENT HELPER ================= */
static void sendInputEvent(InputEventType t) {
  InputEvent e = { t };
  xQueueSend(inputEventQueue, &e, 0);
#if DEBUG_INPUT
  static const char *const names[] = {
    "BTN_SHORT", "BTN_LONG",
    "ENC_CW",    "ENC_CCW",  "ENC_CLICK",  "ENC_LONG"
  };
  serial_printf("[INPUT] %s\n", (t < 6) ? names[t] : "?");
#endif
}

/* ================= TASK: INPUT HANDLER (Core 0, Priority 2) ================= */
/*
 * Queue-based input pipeline.
 * All physical inputs are translated into InputEvent and pushed to inputEventQueue.
 * Encoder ISRs push CW/CCW/CLICK/LONG directly; shutter button is polled here.
 *
 * State machine (Photo-only build for ESP32-WROOM-32 + OV7670 V2):
 *   IDLE -> ENC_CLICK -> MENU_MAIN -> (Gallery | WiFi | Settings | Timelapse | Slideshow | Exit)
 *   ENC_LONG = universal "go back one level"
 *   SHUTTER = take photo (IDLE), cancel self-timer, or emergency exit from any menu
 */
static void taskInput(void *pvParameters) {
  (void)pvParameters;
  bool lastShutter = HIGH;
  unsigned long shutterPressTime = 0;

  while (true) {
    bool shutterNow = (digitalRead(SHUTTER_BTN_PIN_2) != 0);

    /* ── SHUTTER press edge ── */
    if (lastShutter == HIGH && shutterNow == LOW) {
      shutterPressTime = millis();
    }

    /* ── SHUTTER release edge ── */
    if (lastShutter == LOW && shutterNow == HIGH) {
      (void)shutterPressTime;
      if (appState == STATE_IDLE) {
        /* Take photo — respect self-timer if configured */
        bool canSave = false;
        const char *errMsg = "";
        if (xSemaphoreTake(spiMutex, pdMS_TO_TICKS(100))) {
          if (!globalSDState.isMounted) errMsg = "NO SD CARD!";
          else if (globalSDState.isFull)  errMsg = "SD FULL!";
          else canSave = true;
          xSemaphoreGive(spiMutex);
        }
        if (canSave) {
          if (camSettings.selftimer_seconds > 0) {
            /* Intercept: show countdown, then fire the photo at 0. */
            /* taskDisplay will call runSelfTimerCountdown() which sends EVT_TAKE_PHOTO. */
            appState = STATE_SELFTIMER_COUNTDOWN;
            if (taskDisplayHandle) xTaskNotifyGive(taskDisplayHandle);
          } else {
            xEventGroupSetBits(appEvents, EVT_TAKE_PHOTO);
            sendInputEvent(INPUT_BTN_SHORT);
          }
        } else {
          showTFTMessage(errMsg, TFT_RED, 2000);
        }
      } else if (appState == STATE_SELFTIMER_COUNTDOWN) {
        /* Shutter press during countdown cancels it */
        appState = STATE_IDLE;
      } else if (appState == STATE_TIMELAPSE) {
        /* Safe exit: use intermediate state so runTimelapse() handles camera cleanup. */
        appState = STATE_MENU_MAIN;
      } else if (appState == STATE_SLIDESHOW) {
        emergencyExitToIdle();
      } else if (appState == STATE_MENU_MAIN || appState == STATE_SETTINGS ||
                 appState == STATE_GALLERY_PHOTOS || appState == STATE_DELETE_CONFIRM ||
                 appState == STATE_GALLERY_PHOTO_VIEW) {
        /* Emergency exit from any gallery/menu state -> IDLE */
        emergencyExitToIdle();
      }
    }

    /* ── Process encoder events from ISR queue ── */
    /* Unified consumer: all encoder-based state transitions handled here. */
    /* Skipped during timelapse, slideshow, and self-timer — those modes consume events directly. */
    if (appState != STATE_TIMELAPSE && appState != STATE_SLIDESHOW &&
        appState != STATE_SELFTIMER_COUNTDOWN) {
      InputEvent ev;
      while (xQueueReceive(inputEventQueue, &ev, 0) == pdTRUE) {
        if (ev.type != INPUT_ENC_CW && ev.type != INPUT_ENC_CCW &&
            ev.type != INPUT_ENC_CLICK && ev.type != INPUT_ENC_LONG) continue;

        switch (appState) {
          case STATE_IDLE:
            if (ev.type == INPUT_ENC_CLICK) {
              /* Menu is always accessible regardless of SD state. */
              menuMainSelection = 0;
              enterMenuMain();
            }
            break;

          case STATE_MENU_MAIN:
            if (ev.type == INPUT_ENC_CW) {
              menuMainSelection = (menuMainSelection + 1) % MENU_MAIN_ITEMS;
              galleryNeedsRedraw = true;
              if (taskDisplayHandle) xTaskNotifyGive(taskDisplayHandle);
            } else if (ev.type == INPUT_ENC_CCW) {
              menuMainSelection = (menuMainSelection + MENU_MAIN_ITEMS - 1) % MENU_MAIN_ITEMS;
              galleryNeedsRedraw = true;
              if (taskDisplayHandle) xTaskNotifyGive(taskDisplayHandle);
            } else if (ev.type == INPUT_ENC_CLICK) {
              switch (menuMainSelection) {
                case 0: /* Photo Gallery (video removed) — requires SD */
                  if (!globalSDState.isMounted) {
                    showTFTMessage("SD REQUIRED!", TFT_RED, 2000);
                    galleryNeedsRedraw = true;
                    if (taskDisplayHandle) xTaskNotifyGive(taskDisplayHandle);
                    break;
                  }
                  galleryTypeSelection = 0;
                  if (xSemaphoreTake(spiMutex, portMAX_DELAY)) {
                    tft_fillRect(0, 200, 320, 20, TFT_BLACK);
                    tft_setTextDatum(middle_center);
                    tft_setTextSize(1);
                    tft_setTextColor(TFT_YELLOW);
                    tft_drawString("Scanning SD card...", tft_width() / 2, 210);
                    tft_setTextDatum(top_left);
                    xSemaphoreGive(spiMutex);
                  }
                  scanGalleryFiles(false);
                  if (galleryFileCount > 0) {
                    galleryIndex = 0;
                    gridPage = 0;
                    galleryNeedsRedraw = true;
                    appState = STATE_GALLERY_PHOTOS;
                  } else {
                    showTFTMessage("NO PHOTOS FOUND", TFT_RED, 1500);
                    galleryNeedsRedraw = true;
                  }
                  if (taskDisplayHandle) xTaskNotifyGive(taskDisplayHandle);
                  break;
                case 1: /* WiFi — requires SD */
                  if (!globalSDState.isMounted) {
                    showTFTMessage("SD REQUIRED!", TFT_RED, 2000);
                    galleryNeedsRedraw = true;
                    if (taskDisplayHandle) xTaskNotifyGive(taskDisplayHandle);
                    break;
                  }
                  startWiFiMode();
                  break;
                case 2: /* Settings — no SD needed */
                  settingsIndex = 0;
                  settingsEditing = false;
                  galleryNeedsRedraw = true;
                  appState = STATE_SETTINGS;
                  if (taskDisplayHandle) xTaskNotifyGive(taskDisplayHandle);
                  break;
                case 3: /* Timelapse — requires SD */
                  if (!globalSDState.isMounted) {
                    showTFTMessage("SD REQUIRED!", TFT_RED, 2000);
                    galleryNeedsRedraw = true;
                    if (taskDisplayHandle) xTaskNotifyGive(taskDisplayHandle);
                    break;
                  }
                  appState = STATE_TIMELAPSE;
                  galleryNeedsRedraw = true;
                  if (taskDisplayHandle) xTaskNotifyGive(taskDisplayHandle);
                  break;
                case 4: /* Slideshow — requires SD */
                  if (!globalSDState.isMounted) {
                    showTFTMessage("SD REQUIRED!", TFT_RED, 2000);
                    galleryNeedsRedraw = true;
                    if (taskDisplayHandle) xTaskNotifyGive(taskDisplayHandle);
                    break;
                  }
                  appState = STATE_SLIDESHOW;
                  galleryNeedsRedraw = true;
                  if (taskDisplayHandle) xTaskNotifyGive(taskDisplayHandle);
                  break;
                case 5: /* Exit */
                  exitMenuToIdle();
                  break;
              }
            } else if (ev.type == INPUT_ENC_LONG) {
              exitMenuToIdle();
            }
            break;

          case STATE_WIFI_MODE:
            if (ev.type == INPUT_ENC_CLICK || ev.type == INPUT_ENC_LONG) {
              stopWiFiMode();
            }
            break;

          case STATE_GALLERY_PHOTOS: {
            /* Grid view: cursor moves between cells, page changes trigger full redraw */
            if (ev.type == INPUT_ENC_CW || ev.type == INPUT_ENC_CCW) {
              int oldIdx = galleryIndex;
              int oldPage = gridPage;
              if (ev.type == INPUT_ENC_CW && galleryIndex < galleryFileCount - 1) {
                galleryIndex++;
              } else if (ev.type == INPUT_ENC_CCW && galleryIndex > 0) {
                galleryIndex--;
              }
              gridPage = galleryIndex / GRID_ITEMS_PER_PAGE;
              if (gridPage != oldPage) {
                /* Page changed — full grid redraw */
                galleryNeedsRedraw = true;
                if (taskDisplayHandle) xTaskNotifyGive(taskDisplayHandle);
              } else if (galleryIndex != oldIdx) {
                /* Same page — just move the cursor border */
                int pageStart = gridPage * GRID_ITEMS_PER_PAGE;
                int oldLocal = oldIdx - pageStart;
                int newLocal = galleryIndex - pageStart;
                clearGridCursor(oldLocal % GRID_COLS, oldLocal / GRID_COLS);
                drawGridCursor(newLocal % GRID_COLS, newLocal / GRID_COLS, TFT_CYAN);
              }
            } else if (ev.type == INPUT_ENC_CLICK) {
              /* Drill down to detail view */
              galleryNeedsRedraw = true;
              appState = STATE_GALLERY_PHOTO_VIEW;
              if (taskDisplayHandle) xTaskNotifyGive(taskDisplayHandle);
            } else if (ev.type == INPUT_ENC_LONG) {
              freeGalleryFiles();
              galleryNeedsRedraw = true;
              menuMainSelection = 0;
              appState = STATE_MENU_MAIN;
              if (taskDisplayHandle) xTaskNotifyGive(taskDisplayHandle);
            }
            break;
          }

          case STATE_GALLERY_PHOTO_VIEW:
            /* Detail view: CW/CCW = prev/next, CLICK = delete, LONG = back to grid */
            if (ev.type == INPUT_ENC_CW) {
              if (galleryIndex < galleryFileCount - 1) {
                galleryIndex++;
                galleryNeedsRedraw = true;
                if (taskDisplayHandle) xTaskNotifyGive(taskDisplayHandle);
              }
            } else if (ev.type == INPUT_ENC_CCW) {
              if (galleryIndex > 0) {
                galleryIndex--;
                galleryNeedsRedraw = true;
                if (taskDisplayHandle) xTaskNotifyGive(taskDisplayHandle);
              }
            } else if (ev.type == INPUT_ENC_CLICK) {
              deleteSelection = 0;
              galleryNeedsRedraw = true;
              appState = STATE_DELETE_CONFIRM;
              if (taskDisplayHandle) xTaskNotifyGive(taskDisplayHandle);
            } else if (ev.type == INPUT_ENC_LONG) {
              /* Return to grid, update gridPage to match current index */
              gridPage = galleryIndex / GRID_ITEMS_PER_PAGE;
              galleryNeedsRedraw = true;
              appState = STATE_GALLERY_PHOTOS;
              if (taskDisplayHandle) xTaskNotifyGive(taskDisplayHandle);
            }
            break;

          case STATE_DELETE_CONFIRM:
            if (ev.type == INPUT_ENC_CW || ev.type == INPUT_ENC_CCW) {
              deleteSelection = 1 - deleteSelection;
              galleryNeedsRedraw = true;
              if (taskDisplayHandle) xTaskNotifyGive(taskDisplayHandle);
            } else if (ev.type == INPUT_ENC_CLICK) {
              if (deleteSelection == 1 && galleryFileCount > 0) {
                /* Delete the photo */
                bool ok = false;
                if (xSemaphoreTake(spiMutex, portMAX_DELAY)) {
                  ok = sd_remove(galleryFiles[galleryIndex]);
                  xSemaphoreGive(spiMutex);
                }
                serial_printf("[GAL] Delete %s: %s\n", galleryFiles[galleryIndex], ok ? "OK" : "FAIL");
                if (ok) {
                  free(galleryFiles[galleryIndex]);
                  for (int i = galleryIndex; i < galleryFileCount - 1; i++) {
                    galleryFiles[i] = galleryFiles[i + 1];
                  }
                  galleryFileCount--;
                  if (galleryIndex >= galleryFileCount && galleryIndex > 0) galleryIndex--;
                }
                /* Return to grid view (or main menu if empty) */
                if (galleryFileCount > 0) {
                  gridPage = galleryIndex / GRID_ITEMS_PER_PAGE;
                  appState = STATE_GALLERY_PHOTOS;
                } else {
                  freeGalleryFiles();
                  menuMainSelection = 0;
                  appState = STATE_MENU_MAIN;
                }
                galleryNeedsRedraw = true;
                if (taskDisplayHandle) xTaskNotifyGive(taskDisplayHandle);
              } else {
                /* "Cancel" selected (deleteSelection == 0) */
                appState = STATE_GALLERY_PHOTO_VIEW;
                galleryNeedsRedraw = true;
                if (taskDisplayHandle) xTaskNotifyGive(taskDisplayHandle);
              }
            } else if (ev.type == INPUT_ENC_LONG) {
              /* Cancel — go back to detail view */
              appState = STATE_GALLERY_PHOTO_VIEW;
              galleryNeedsRedraw = true;
              if (taskDisplayHandle) xTaskNotifyGive(taskDisplayHandle);
            }
            break;

          case STATE_SETTINGS: {
            /* Settings menu: browse or edit camera parameters (video setting index 10 removed) */
            if (!settingsEditing) {
              /* Browsing mode: CW/CCW move highlight, CLICK enters edit */
              if (ev.type == INPUT_ENC_CW) {
                settingsIndex = (settingsIndex + 1) % SETTINGS_COUNT;
                if (settingsIndex == 10) settingsIndex = (settingsIndex + 1) % SETTINGS_COUNT;
                galleryNeedsRedraw = true;
                if (taskDisplayHandle) xTaskNotifyGive(taskDisplayHandle);
              } else if (ev.type == INPUT_ENC_CCW) {
                settingsIndex = (settingsIndex + SETTINGS_COUNT - 1) % SETTINGS_COUNT;
                if (settingsIndex == 10) settingsIndex = (settingsIndex + SETTINGS_COUNT - 1) % SETTINGS_COUNT;
                galleryNeedsRedraw = true;
                if (taskDisplayHandle) xTaskNotifyGive(taskDisplayHandle);
              } else if (ev.type == INPUT_ENC_CLICK) {
                if (settingsIndex == 10) break;
                resetCounterConfirm = 0;  /* safety: always start at "No" */
                settingsEditing = true;
                galleryNeedsRedraw = true;
                if (taskDisplayHandle) xTaskNotifyGive(taskDisplayHandle);
              } else if (ev.type == INPUT_ENC_LONG) {
                /* Save and return to main menu */
                saveCameraSettings();
                galleryNeedsRedraw = true;
                menuMainSelection = 0;
                appState = STATE_MENU_MAIN;
                if (taskDisplayHandle) xTaskNotifyGive(taskDisplayHandle);
              }
            } else {
              /* Editing mode: CW/CCW adjust value, CLICK confirms */

              /* Special case: counter reset (index 12) — action-type setting */
              if (settingsIndex == 12) {
                if (ev.type == INPUT_ENC_CW || ev.type == INPUT_ENC_CCW) {
                  resetCounterConfirm = 1 - resetCounterConfirm;
                  galleryNeedsRedraw = true;
                  if (taskDisplayHandle) xTaskNotifyGive(taskDisplayHandle);
                } else if (ev.type == INPUT_ENC_CLICK) {
                  if (resetCounterConfirm == 1) {
                    /* Execute counter reset */
                    pictureNumber = 0;
                    nvs_write_i32("cnt", "pic", 0);
                    serial_println("[NVS] Photo counter reset to 0.");

                    /* Show warning on TFT */
                    settingsEditing = false;
                    resetCounterConfirm = 0;
                    if (xSemaphoreTake(spiMutex, portMAX_DELAY)) {
                      tft_fillScreen(TFT_BLACK);
                      tft_setTextDatum(middle_center);
                      tft_setTextSize(2);
                      tft_setTextColor(TFT_GREEN);
                      tft_drawString("Counter Reset!", tft_width() / 2, 40);
                      tft_setTextSize(1);
                      tft_setTextColor(TFT_YELLOW);
                      tft_drawString("P:0", tft_width() / 2, 70);
                      tft_setTextSize(2);
                      tft_setTextColor(TFT_RED);
                      tft_drawString("!! WARNING !!", tft_width() / 2, 110);
                      tft_setTextSize(1);
                      tft_setTextColor(TFT_WHITE);
                      tft_drawString("Gallery will show wrong", tft_width() / 2, 140);
                      tft_drawString("files after counter reset.", tft_width() / 2, 155);
                      tft_setTextColor(TFT_CYAN);
                      tft_drawString("Backup your photos", tft_width() / 2, 180);
                      tft_drawString("via WiFi, then delete them", tft_width() / 2, 195);
                      tft_drawString("from SD card.", tft_width() / 2, 210);
                      tft_setTextDatum(top_left);
                      xSemaphoreGive(spiMutex);
                    }
                    vTaskDelay(pdMS_TO_TICKS(4000));
                    galleryNeedsRedraw = true;
                    if (taskDisplayHandle) xTaskNotifyGive(taskDisplayHandle);
                  } else {
                    /* "No" selected — cancel */
                    settingsEditing = false;
                    resetCounterConfirm = 0;
                    galleryNeedsRedraw = true;
                    if (taskDisplayHandle) xTaskNotifyGive(taskDisplayHandle);
                  }
                } else if (ev.type == INPUT_ENC_LONG) {
                  /* Cancel */
                  settingsEditing = false;
                  resetCounterConfirm = 0;
                  galleryNeedsRedraw = true;
                  if (taskDisplayHandle) xTaskNotifyGive(taskDisplayHandle);
                }
                break;  /* handled — skip normal val logic */
              }

              int *val = NULL;
              int lo = 0, hi = 0;
              switch (settingsIndex) {
                case 0:  val = &camSettings.brightness;         lo = -2; hi = 2;  break;
                case 1:  val = &camSettings.contrast;           lo = -2; hi = 2;  break;
                case 2:  val = &camSettings.saturation;         lo = -2; hi = 2;  break;
                case 3:  val = &camSettings.ae_level;           lo = -2; hi = 2;  break;
                case 4:  val = &camSettings.wb_mode;            lo = 0;  hi = 4;  break;
                case 5:  val = &camSettings.special_effect;     lo = 0;  hi = 6;  break;
                case 6:  val = &camSettings.hmirror;            lo = 0;  hi = 1;  break;
                case 7:  val = &camSettings.vflip;              lo = 0;  hi = 1;  break;
                case 8:  val = &camSettings.jpeg_quality;       lo = 4;  hi = 63; break;
                case 9:  val = &camSettings.timelapse_interval; break;
                case 11: val = &camSettings.flashlight_on;      lo = 0;  hi = 1;  break;
                case 13: val = &camSettings.selftimer_seconds;  break;
                case 14: val = &camSettings.slideshow_interval; break;
                default: break;
              }
              if (val) {
                if (ev.type == INPUT_ENC_CW || ev.type == INPUT_ENC_CCW) {
                  bool cw = (ev.type == INPUT_ENC_CW);
                  if (settingsIndex == 9) {
                    /* Timelapse interval: step through presets */
                    static const int p[] = {5, 10, 15, 30, 60, 120, 300, 600};
                    int n = 8, ci = 0;
                    for (int i = 0; i < n; i++) {
                      if (p[i] >= *val) { ci = i; break; }
                      if (i == n - 1) ci = n - 1;
                    }
                    if (cw && ci < n - 1) *val = p[ci + 1];
                    else if (!cw && ci > 0) *val = p[ci - 1];
                  } else if (settingsIndex == 13) {
                    /* Self-timer: 0 (off), 3, 5, 10 seconds */
                    static const int sp[] = {0, 3, 5, 10};
                    int sn = 4, sci = 0;
                    for (int i = 0; i < sn; i++) {
                      if (sp[i] >= *val) { sci = i; break; }
                      if (i == sn - 1) sci = sn - 1;
                    }
                    if (cw && sci < sn - 1) *val = sp[sci + 1];
                    else if (!cw && sci > 0) *val = sp[sci - 1];
                  } else if (settingsIndex == 14) {
                    /* Slideshow interval: 3, 5, 10 seconds */
                    static const int slp[] = {3, 5, 10};
                    int sln = 3, slci = 0;
                    for (int i = 0; i < sln; i++) {
                      if (slp[i] >= *val) { slci = i; break; }
                      if (i == sln - 1) slci = sln - 1;
                    }
                    if (cw && slci < sln - 1) *val = slp[slci + 1];
                    else if (!cw && slci > 0) *val = slp[slci - 1];
                  } else {
                    /* Linear range settings */
                    if (cw) { if (*val < hi) (*val)++; }
                    else { if (*val > lo) (*val)--; }
                  }
                  galleryNeedsRedraw = true;
                  if (taskDisplayHandle) xTaskNotifyGive(taskDisplayHandle);
                } else if (ev.type == INPUT_ENC_CLICK) {
                  /* Confirm edit — save to NVS immediately */
                  settingsEditing = false;
                  saveCameraSettings();
                  galleryNeedsRedraw = true;
                  if (taskDisplayHandle) xTaskNotifyGive(taskDisplayHandle);
                } else if (ev.type == INPUT_ENC_LONG) {
                  /* Cancel edit — revert to saved */
                  loadCameraSettings();
                  settingsEditing = false;
                  galleryNeedsRedraw = true;
                  if (taskDisplayHandle) xTaskNotifyGive(taskDisplayHandle);
                }
              }
            }
            break;
          }

          default:
            break;
        }
      }
    }

    lastShutter = shutterNow;

#if DEBUG_INPUT
    /* Print ISR-generated encoder events (not routed through sendInputEvent). */
    /* Uses snapshot deltas so we don't miss rapid pulses. */
    static uint32_t lastCw = 0, lastCcw = 0, lastClick = 0, lastLong = 0;
    uint32_t cw = dbgEncCw, ccw = dbgEncCcw, clk = dbgEncClick, lng = dbgEncLong;
    if (cw  != lastCw)    { serial_printf("[ENC] CW  x%lu\n", (unsigned long)(cw - lastCw));   lastCw    = cw;  }
    if (ccw != lastCcw)   { serial_printf("[ENC] CCW x%lu\n", (unsigned long)(ccw - lastCcw)); lastCcw   = ccw; }
    if (clk != lastClick) { serial_printf("[ENC] CLICK\n");                                    lastClick = clk; }
    if (lng != lastLong)  { serial_printf("[ENC] LONG PRESS\n");                               lastLong  = lng; }
#endif

    vTaskDelay(pdMS_TO_TICKS(20));  /* 50 Hz polling */
  }
}

/* ================= ENCODER ISRs ================= */
/* Placed in IRAM so they execute even during Flash cache misses (e.g. SD writes). */
/* Both ISRs push directly to inputEventQueue — the same queue taskInput uses — */
/* so all menu logic consumes from a single source. */
static void IRAM_ATTR encoderISR(void) {
  /* Read current 2-bit state: (CLK << 1) | DT */
  uint8_t s = ((uint8_t)digitalRead(ENC_CLK) << 1) | (uint8_t)digitalRead(ENC_DT);

  /* Lookup direction from state transition table */
  int8_t dir = ENC_TABLE[(encPrevState << 2) | s];
  encPrevState = s;
  if (dir == 0) return;  /* invalid transition (bounce) — discard silently */

  encAccum += dir;

  /* Emit event only at detent rest position (both pins HIGH = 0x03). */
  /* This absorbs all intermediate bounce and partial-rotation noise; */
  /* the accumulated direction tells us which way the knob actually moved. */
  if (s == 0x03) {
    if (encAccum > 0) {
      InputEvent e = { INPUT_ENC_CW };
#if DEBUG_INPUT
      dbgEncCw = dbgEncCw + 1;
#endif
      BaseType_t woken = pdFALSE;
      xQueueSendFromISR(inputEventQueue, &e, &woken);
      if (woken) portYIELD_FROM_ISR();
    } else if (encAccum < 0) {
      InputEvent e = { INPUT_ENC_CCW };
#if DEBUG_INPUT
      dbgEncCcw = dbgEncCcw + 1;
#endif
      BaseType_t woken = pdFALSE;
      xQueueSendFromISR(inputEventQueue, &e, &woken);
      if (woken) portYIELD_FROM_ISR();
    }
    encAccum = 0;
  }
}

static void IRAM_ATTR encSwISR(void) {
  uint32_t now = millis();
  if (digitalRead(ENC_SW) == LOW) {
    /* Falling edge — record press start time. */
    encSwPressMs = now;
  } else {
    /* Rising edge — reject contact bounce (< 30 ms press is physically impossible). */
    uint32_t dur = now - encSwPressMs;
    if (dur < 30) return;
    InputEvent e;
    e.type = (dur > 500) ? INPUT_ENC_LONG : INPUT_ENC_CLICK;
#if DEBUG_INPUT
    if (e.type == INPUT_ENC_LONG) dbgEncLong  = dbgEncLong  + 1;
    else                          dbgEncClick = dbgEncClick + 1;
#endif
    BaseType_t woken = pdFALSE;
    xQueueSendFromISR(inputEventQueue, &e, &woken);
    if (woken) portYIELD_FROM_ISR();
  }
}

/* ================= TASK: CAMERA CAPTURE (Core 1, Priority 6) ================= */
static void taskCapture(void *pvParameters) {
  (void)pvParameters;
  int fail_count = 0;

  /* Camera watchdog timer — persists across iterations (local static) */
  /* Tracks time since last reinit; reset to 0 whenever we leave IDLE. */
  static unsigned long camWdgLastReset = 0;

  while (true) {
    /* Skip capture when camera is deinited (WiFi mode, gallery/menu/slideshow states). */
    /* STATE_SELFTIMER_COUNTDOWN is NOT in this list — camera stays alive so taskCapture */
    /* can process EVT_TAKE_PHOTO at countdown end. */
    {
      AppState cs = appState;
      if (cs == STATE_WIFI_MODE || cs == STATE_MENU_MAIN || cs == STATE_SETTINGS ||
          cs == STATE_GALLERY_PHOTOS || cs == STATE_DELETE_CONFIRM ||
          cs == STATE_TIMELAPSE || cs == STATE_GALLERY_PHOTO_VIEW ||
          cs == STATE_SLIDESHOW) {
        camWdgLastReset = 0;  /* not in IDLE — reset timer when we return */
        vTaskDelay(pdMS_TO_TICKS(100));
        continue;
      }
    }

    /* ── Camera watchdog: periodic soft-reset to prevent AEC/AGC drift ── */
    if (appState == STATE_IDLE) {
      unsigned long now = millis();
      if (camWdgLastReset == 0) {
        camWdgLastReset = now;                            /* arm timer on first IDLE frame */
      } else if (now - camWdgLastReset >= 30000UL) {
        serial_println("[CAM] Watchdog: soft-reset to prevent AEC/AGC drift");
        camWdgLastReset = now;
        initCamera(IDLE_MODE, IDLE_RESOLUTION, IDLE_JPEG_QUALITY);
        vTaskDelay(pdMS_TO_TICKS(100));
        continue;                                         /* skip this frame's fb_get */
      }
    } else {
      camWdgLastReset = 0;  /* photo/menu — re-arm after returning to IDLE */
    }

    /* ---- Handle state transition events ---- */
    EventBits_t bits = xEventGroupGetBits(appEvents);

    /* TAKE PHOTO */
    if (bits & EVT_TAKE_PHOTO) {
      xEventGroupClearBits(appEvents, EVT_TAKE_PHOTO);
      savePhotoHighRes();
      continue;
    }

    /* ---- Normal frame capture ---- */
    camera_fb_t *fb = esp_camera_fb_get();

    if (!fb) {
      fail_count++;
      serial_printf("Cam Fail: %d\n", fail_count);
      if (fail_count > 10) {
        if (xSemaphoreTake(spiMutex, portMAX_DELAY)) {
          tft_fillScreen(TFT_RED);
          tft_setTextSize(2);
          tft_drawString("CAM RESET...", 20, 110);
          xSemaphoreGive(spiMutex);
        }
        delay(100);
        initCamera(IDLE_MODE, IDLE_RESOLUTION, IDLE_JPEG_QUALITY);
        fail_count = 0;
      }
      vTaskDelay(10);
      continue;
    }
    fail_count = 0;

    /* Copy frame for display (single buffer on ESP32-WROOM-32, or ping-pong if 2 slots exist) */
    if (appState == STATE_IDLE) {
      int ws = atomic_load(&dispWriteSlot);
      if (ws != atomic_load(&dispRendering) && fb->len <= dispBufCap && dispBuf[ws]) {
        memcpy(dispBuf[ws], fb->buf, fb->len);
        dispLen[ws] = fb->len;
        atomic_store(&dispReadSlot, ws);
        if (dispBuf[1 - ws]) {
          atomic_store(&dispWriteSlot, 1 - ws);
        }
        if (taskDisplayHandle) xTaskNotifyGive(taskDisplayHandle);
      }
    }

    /* Return camera buffer immediately — prevents frame drop with fb_count=1 in DRAM */
    esp_camera_fb_return(fb);

    vTaskDelay(1);
  }
}

/* ================= TASK: TFT DISPLAY (Core 1, Priority 3) ================= */
static void taskDisplay(void *pvParameters) {
  (void)pvParameters;
  uint32_t last_fps_time = 0;
  uint32_t frame_count = 0;
  float fps = 0.0f;

  while (true) {
    /* wait for a new frame notification (200ms timeout for FPS update even if no frames) */
    ulTaskNotifyTake(pdTRUE, pdMS_TO_TICKS(200));

    /* Don't render during photo/wifi — let notifications stay on screen */
    if (appState == STATE_PHOTO || appState == STATE_WIFI_MODE) {
      vTaskDelay(pdMS_TO_TICKS(50));
      continue;
    }

    /* Menu and photo gallery states — render on demand, skip camera preview */
    if (appState == STATE_MENU_MAIN || appState == STATE_SETTINGS ||
        appState == STATE_GALLERY_PHOTOS || appState == STATE_DELETE_CONFIRM ||
        appState == STATE_GALLERY_PHOTO_VIEW) {
      if (galleryNeedsRedraw) {
        galleryNeedsRedraw = false;
        switch (appState) {
          case STATE_MENU_MAIN:          drawMenuMain(); break;
          case STATE_SETTINGS:           drawSettingsMenu(); break;
          case STATE_GALLERY_PHOTOS:     drawPhotoGrid(); break;
          case STATE_GALLERY_PHOTO_VIEW: drawGalleryPhotoView(); break;
          case STATE_DELETE_CONFIRM:     drawDeleteConfirm(); break;
          default: break;
        }
      }
      vTaskDelay(pdMS_TO_TICKS(50));
      continue;
    }

    /* Timelapse — blocking capture loop until stopped */
    if (appState == STATE_TIMELAPSE) {
      runTimelapse();
      continue;
    }

    /* Self-timer countdown — blocking digit display until 0 or cancelled */
    if (appState == STATE_SELFTIMER_COUNTDOWN) {
      runSelfTimerCountdown();
      continue;
    }

    /* Slideshow — blocking photo cycling until stopped */
    if (appState == STATE_SLIDESHOW) {
      runSlideshow();
      continue;
    }

    int rs = atomic_load(&dispReadSlot);
    if (rs < 0 || !dispBuf[rs]) {
      vTaskDelay(10);
      continue;
    }

    atomic_store(&dispRendering, rs);  /* mark slot as being rendered */

    if (xSemaphoreTake(spiMutex, portMAX_DELAY)) {
      tft_startWrite();

      /* idle: RGB565 preview (160x120 QQVGA upscaled 2x for WROOM-32 DRAM, or 320x240 QVGA 1:1) */
      if (dispLen[rs] == (size_t)(160 * 120 * 2)) {
        uint16_t lineBuf[320];
        const uint16_t *src = (const uint16_t *)dispBuf[rs];
        for (int sy = 0; sy < 108; sy++) {
          const uint16_t *row = src + sy * 160;
          for (int sx = 0; sx < 160; sx++) {
            uint16_t px = row[sx];
            lineBuf[sx * 2]     = px;
            lineBuf[sx * 2 + 1] = px;
          }
          tft_pushImage(0, sy * 2,     320, 1, lineBuf);
          tft_pushImage(0, sy * 2 + 1, 320, 1, lineBuf);
        }
      } else {
        for (int y = 0; y < 216; y++) {
          tft_pushImage(0, y, 320, 1, (const uint16_t *)(dispBuf[rs] + y * 320 * 2));
        }
      }

      tft_endWrite();
      xSemaphoreGive(spiMutex);
    }

    atomic_store(&dispRendering, -1);  /* slot is free now */

    /* FPS calculation */
    frame_count++;
    uint32_t now = millis();
    if (now - last_fps_time >= 1000) {
      fps = (float)frame_count * 1000.0f / (float)(now - last_fps_time);
      drawStatusBar(fps);
      frame_count = 0;
      last_fps_time = now;
    }
  }
}

/* Draws the persistent bottom status bar (FPS + version + SD indicator). */
/* Called from taskDisplay whenever the 1-second FPS window elapses. */
static void drawStatusBar(float fps) {
  if (!xSemaphoreTake(spiMutex, pdMS_TO_TICKS(10))) return;

  tft_fillRect(0, 216, 320, 24, TFT_BLACK);

  /* FPS — left side */
  tft_setTextSize(2);
  tft_setCursor(8, 220);
  tft_setTextColor(TFT_GREEN);
  tft_printf("FPS: %.1f", fps);

  /* Firmware version — right-center */
  tft_setTextSize(1);
  tft_setTextColor(0x4208);  /* dim grey (RGB565) */
  tft_setCursor(218, 224);
  tft_print(FIRMWARE_VERSION);

  /* SD status dot — far right */
  if (globalSDState.isMounted && !globalSDState.isFull)
    tft_fillCircle(308, 228, 5, TFT_GREEN);
  else
    tft_fillCircle(308, 228, 5, TFT_RED);

  xSemaphoreGive(spiMutex);
}

/* ================= PHOTO CAPTURE ================= */
static void savePhotoHighRes(void) {
  appState = STATE_PHOTO;

  /* Turn on flashlight as fill light during photo capture */
  if (camSettings.flashlight_on) {
    digitalWrite(LED_FLASHLIGHT_PIN, HIGH);
  }

  /* Show "HOLD ON..." — taskDisplay skips rendering during STATE_PHOTO */
  if (xSemaphoreTake(spiMutex, portMAX_DELAY)) {
    tft_fillRoundRect(60, 85, 200, 50, 8, TFT_BLUE);
    tft_drawRoundRect(60, 85, 200, 50, 8, TFT_WHITE);
    tft_setTextSize(2);
    tft_setTextColor(TFT_WHITE);
    tft_setCursor(95, 102);
    tft_print("HOLD ON...");
    xSemaphoreGive(spiMutex);
  }

  serial_println("--- HD Mode Start ---");

  initCamera(PHOTO_MODE, PHOTO_RESOLUTION, REC_JPEG_QUALITY);

  /* warm up */
  camera_fb_t *fb = NULL;
  for (int i = 0; i < 15; i++) {
    fb = esp_camera_fb_get();
    if (fb) esp_camera_fb_return(fb);
    vTaskDelay(20);
  }

  fb = esp_camera_fb_get();
  if (!fb) {
    serial_println("Cam error!");
    if (xSemaphoreTake(spiMutex, portMAX_DELAY)) {
      tft_setTextSize(2);
      tft_setCursor(95, 102);
      tft_print("CAM ERROR");
      xSemaphoreGive(spiMutex);
    }
  } else {
    bool saved = false;
    bool writeErr = false;
    bool sdLost = false;
    uint8_t *jpgBuf = NULL;
    size_t jpgLen = 0;
    const uint8_t *jpegData = fb->buf;
    size_t jpegSize = fb->len;

    if (fb->format != PIXFORMAT_JPEG) {
      if (!frame2jpg(fb, ov7670_jpeg_quality(camSettings.jpeg_quality), &jpgBuf, &jpgLen)) {
        serial_println("Software JPEG encode failed!");
        writeErr = true;
      } else {
        jpegData = jpgBuf;
        jpegSize = jpgLen;
      }
    }

    /* SD write — separate mutex take to avoid nesting */
    if (!writeErr && xSemaphoreTake(spiMutex, portMAX_DELAY)) {
      if (sd_total_bytes() > 0) {
        char path[64];
        snprintf(path, sizeof(path), "/hd_pic_%d.jpg", pictureNumber);
        /* Skip past any existing files (prevents overwrite on NVS counter reset) */
        while (sd_exists(path)) {
          pictureNumber++;
          snprintf(path, sizeof(path), "/hd_pic_%d.jpg", pictureNumber);
        }
        serial_printf("Saving (%u bytes): %s\n", (unsigned int)jpegSize, path);

        sd_file_t *file = sd_open_write(path);
        if (file) {
          /* Write SOI (first 2 bytes) + EXIF block + rest of JPEG */
          const uint8_t *exifData = NULL;
          size_t exifLen = getExifBlock(&exifData);
          bool writeOk = true;
          /* SOI marker (0xFFD8) */
          if (sd_file_write(file, jpegData, 2) != 2) writeOk = false;
          /* EXIF APP1 segment */
          if (writeOk && exifLen > 0 && exifData) {
            if (sd_file_write(file, exifData, exifLen) != exifLen) writeOk = false;
          }
          /* Rest of JPEG (skip SOI) */
          size_t remaining = (jpegSize > 2) ? (jpegSize - 2) : 0;
          if (writeOk && remaining > 0 && sd_file_write(file, jpegData + 2, remaining) != remaining) writeOk = false;
          sd_file_close(file);
          if (writeOk) {
            serial_println("SUCCESS!");
            pictureNumber++;
            nvs_write_i32("cnt", "pic", (int32_t)pictureNumber);
            saved = true;
          } else {
            serial_printf("[ERR] Photo write incomplete (EXIF inject)\n");
            writeErr = true;
          }
        } else {
          serial_println("File Open Error");
          writeErr = true;
        }
      } else {
        serial_println("SD Lost during capture");
        sdLost = true;
      }
      xSemaphoreGive(spiMutex);
    }

    if (jpgBuf) free(jpgBuf);
    esp_camera_fb_return(fb);

    /* Show result on TFT — separate mutex take */
    if (xSemaphoreTake(spiMutex, portMAX_DELAY)) {
      if (saved) {
        char msg[32];
        snprintf(msg, sizeof(msg), "PIC SAVED #%d", pictureNumber - 1);
        tft_fillRoundRect(60, 85, 200, 50, 8, TFT_WHITE);
        tft_drawRoundRect(60, 85, 200, 50, 8, TFT_BLACK);
        tft_setTextSize(2);
        tft_setTextColor(TFT_BLACK);
        tft_setCursor(75, 102);
        tft_print(msg);
      } else if (writeErr) {
        tft_setTextSize(2);
        tft_setCursor(10, 10);
        tft_setTextColorBg(TFT_RED, TFT_BLACK);
        tft_print("WRITE ERROR");
      } else if (sdLost) {
        tft_setTextSize(2);
        tft_setCursor(10, 10);
        tft_setTextColorBg(TFT_RED, TFT_BLACK);
        tft_print("SD CONNECTION LOST");
      }
      xSemaphoreGive(spiMutex);
    }
  }

  serial_println("--- Returning to Idle Mode ---");

  /* Keep notification visible for 1 second (STATE_PHOTO blocks taskDisplay) */
  vTaskDelay(pdMS_TO_TICKS(1000));

  /* LED off — flashlight is only active during capture/recording */
  digitalWrite(LED_FLASHLIGHT_PIN, LOW);

  initCamera(IDLE_MODE, IDLE_RESOLUTION, IDLE_JPEG_QUALITY);
  appState = STATE_IDLE;
}

/* Map sensor-style JPEG quality (4=best .. 63=worst) to frame2jpg quality (1..100, higher=best). */
static uint8_t ov7670_jpeg_quality(int cam_quality) {
  if (cam_quality <= 4)  return 95;
  if (cam_quality >= 63) return 15;
  return (uint8_t)(95 - ((cam_quality - 4) * 80) / 59);
}

/* ================= CAMERA INIT (ESP32-WROOM-32 + OV7670 V2) ================= */
void initCamera(pixformat_t format, framesize_t size, int jpeg_quality) {
  (void)format;
  esp_camera_deinit();

  /* ESP32-WROOM-32 has NO PSRAM: framebuffers must reside in internal DRAM. */
  /* Live preview (IDLE_RESOLUTION) uses QQVGA (160x120 = 38.4 KB) so DRAM */
  /* fits both the camera DMA buffer and dispBuf[0]. Photo capture tries QVGA */
  /* (320x240 = 153.6 KB) and falls back to HQVGA/QQVGA if DMA heap is tight. */
  if (size == IDLE_RESOLUTION) {
    if (size > FRAMESIZE_QQVGA) size = FRAMESIZE_QQVGA;
  } else if (size > FRAMESIZE_QVGA) {
    size = FRAMESIZE_QVGA;
  }

  config.pixel_format = PIXFORMAT_RGB565;
  config.frame_size = size;
  config.jpeg_quality = jpeg_quality;
  config.fb_count = 1;
  config.fb_location = CAMERA_FB_IN_DRAM;
  config.grab_mode = CAMERA_GRAB_WHEN_EMPTY;

  if (esp_camera_init(&config) != ESP_OK) {
    if (size > FRAMESIZE_HQVGA) {
      serial_println("QVGA DRAM init failed, retrying HQVGA...");
      config.frame_size = FRAMESIZE_HQVGA;
      if (esp_camera_init(&config) == ESP_OK) goto cam_ready;
    }
    if (size > FRAMESIZE_QQVGA) {
      serial_println("HQVGA DRAM init failed, retrying QQVGA...");
      config.frame_size = FRAMESIZE_QQVGA;
      if (esp_camera_init(&config) == ESP_OK) goto cam_ready;
    }
    serial_println("OV7670 Cam init error");
    return;
  }

cam_ready:;
  sensor_t *s = esp_camera_sensor_get();
  if (s) {
    applySettings(s);

    /* Guard every callback — OV7670 leaves several OV2640 hooks (e.g. aec2/awb_gain) NULL. */
    if (s->set_whitebal)      s->set_whitebal(s, 1);
    if (s->set_awb_gain)      s->set_awb_gain(s, 1);
    if (s->set_exposure_ctrl) s->set_exposure_ctrl(s, 1);
    if (s->set_aec2)          s->set_aec2(s, 1);
    if (s->set_gain_ctrl)     s->set_gain_ctrl(s, 1);
    if (s->set_gainceiling)   s->set_gainceiling(s, (config.frame_size > FRAMESIZE_QQVGA) ? GAINCEILING_8X : GAINCEILING_2X);
  }
  delay(100);
}

/* ================= MICROPHONE STUBS (Video/Audio removed) ================= */
void initMicrophone(void) { }
void deinitMicrophone(void) { }

/* ================= TIMELAPSE MODE ================= */
/* Runs in taskDisplay context (Core 1). Camera is reinited for HD JPEG. */
/* taskCapture is idle (STATE_TIMELAPSE is in its skip list). */
/* Encoder events consumed directly from inputEventQueue (like video playback). */
/* Exit via: ENC_LONG, shutter button (appState changed externally by taskInput), */
/* or SD card removal. */
static void runTimelapse(void) {
  int interval = camSettings.timelapse_interval;
  if (interval < 1) interval = 10;

  serial_printf("[TL] Starting timelapse, interval=%ds\n", interval);

  /* Camera was deinited during menu navigation — reinit for HD photo capture */
  initCamera(PHOTO_MODE, PHOTO_RESOLUTION, camSettings.jpeg_quality);

  /* Warm up sensor (auto-exposure settle) */
  for (int i = 0; i < 10; i++) {
    camera_fb_t *fb = esp_camera_fb_get();
    if (fb) esp_camera_fb_return(fb);
    vTaskDelay(pdMS_TO_TICKS(50));
  }

  int captureCount = 0;
  bool paused = false;
  bool tlStopped = false;
  unsigned long startTime = millis();
  unsigned long lastCaptureTime = 0;  /* 0 = capture immediately on first iteration */
  unsigned long lastDisplayUpdate = 0;

  /* Draw initial UI chrome (title + footer — redrawn only once) */
  if (xSemaphoreTake(spiMutex, portMAX_DELAY)) {
    tft_fillScreen(TFT_BLACK);
    tft_setTextDatum(middle_center);
    tft_setTextSize(2);
    tft_setTextColor(TFT_CYAN);
    tft_drawString("TIMELAPSE", tft_width() / 2, 16);
    tft_setTextDatum(top_left);
    xSemaphoreGive(spiMutex);
  }

  while (appState == STATE_TIMELAPSE && !tlStopped) {
    /* ── Consume encoder events ── */
    InputEvent ev;
    while (xQueueReceive(inputEventQueue, &ev, 0) == pdTRUE) {
      if (ev.type == INPUT_ENC_CLICK) {
        paused = !paused;
        /* Immediate visual feedback for pause toggle */
        if (xSemaphoreTake(spiMutex, pdMS_TO_TICKS(50))) {
          tft_fillRect(0, 50, 320, 40, TFT_BLACK);
          tft_setTextDatum(middle_center);
          tft_setTextSize(3);
          if (paused) {
            tft_setTextColor(TFT_YELLOW);
            tft_drawString("PAUSED", tft_width() / 2, 70);
          }
          tft_setTextDatum(top_left);
          xSemaphoreGive(spiMutex);
        }
        lastDisplayUpdate = 0; /* force redraw on resume */
      } else if (ev.type == INPUT_ENC_LONG) {
        tlStopped = true;
      }
    }
    if (tlStopped) break;

    /* ── Paused: just wait ── */
    if (paused) {
      vTaskDelay(pdMS_TO_TICKS(200));
      continue;
    }

    unsigned long now = millis();
    unsigned long sinceCapture = (lastCaptureTime == 0) ? (unsigned long)interval * 1000UL : (now - lastCaptureTime);
    int remaining = interval - (int)(sinceCapture / 1000UL);
    if (remaining < 0) remaining = 0;

    /* ── Time to capture? ── */
    if (sinceCapture >= (unsigned long)interval * 1000UL) {
      /* Show capturing indicator */
      if (xSemaphoreTake(spiMutex, pdMS_TO_TICKS(50))) {
        tft_fillRect(0, 50, 320, 40, TFT_BLACK);
        tft_setTextDatum(middle_center);
        tft_setTextSize(2);
        tft_setTextColor(TFT_GREEN);
        tft_drawString("CAPTURING...", tft_width() / 2, 70);
        tft_setTextDatum(top_left);
        xSemaphoreGive(spiMutex);
      }

      camera_fb_t *fb = esp_camera_fb_get();
      if (fb) {
        bool saved = false;
        uint8_t *jpgBuf = NULL;
        size_t jpgLen = 0;
        const uint8_t *jpegData = fb->buf;
        size_t jpegSize = fb->len;
        bool jpegReady = true;

        if (fb->format != PIXFORMAT_JPEG) {
          jpegReady = frame2jpg(fb, ov7670_jpeg_quality(camSettings.jpeg_quality), &jpgBuf, &jpgLen);
          jpegData = jpgBuf;
          jpegSize = jpgLen;
        }

        if (jpegReady && xSemaphoreTake(spiMutex, portMAX_DELAY)) {
          if (globalSDState.isMounted) {
            char path[64];
            snprintf(path, sizeof(path), "/hd_pic_%d.jpg", pictureNumber);
            while (sd_exists(path)) {
              pictureNumber++;
              snprintf(path, sizeof(path), "/hd_pic_%d.jpg", pictureNumber);
            }
            sd_file_t *file = sd_open_write(path);
            if (file) {
              /* Write SOI + EXIF + rest of JPEG (same pattern as savePhotoHighRes) */
              const uint8_t *exifData = NULL;
              size_t exifLen = getExifBlock(&exifData);
              bool writeOk = true;
              if (sd_file_write(file, jpegData, 2) != 2) writeOk = false;
              if (writeOk && exifLen > 0 && exifData) {
                if (sd_file_write(file, exifData, exifLen) != exifLen) writeOk = false;
              }
              size_t rem_bytes = (jpegSize > 2) ? (jpegSize - 2) : 0;
              if (writeOk && rem_bytes > 0 && sd_file_write(file, jpegData + 2, rem_bytes) != rem_bytes) writeOk = false;
              sd_file_close(file);
              if (writeOk) {
                pictureNumber++;
                nvs_write_i32("cnt", "pic", (int32_t)pictureNumber);
                captureCount++;
                saved = true;
                serial_printf("[TL] Saved: %s (%u bytes)\n", path, (unsigned int)jpegSize);
              } else {
                serial_printf("[TL] Write incomplete (EXIF inject)\n");
              }
            }
          }
          xSemaphoreGive(spiMutex);
        }
        if (jpgBuf) free(jpgBuf);
        esp_camera_fb_return(fb);

        /* Show save result */
        if (xSemaphoreTake(spiMutex, pdMS_TO_TICKS(50))) {
          tft_fillRect(0, 140, 320, 20, TFT_BLACK);
          tft_setTextDatum(middle_center);
          tft_setTextSize(1);
          if (saved) {
            tft_setTextColor(TFT_GREEN);
            char msg[32];
            snprintf(msg, sizeof(msg), "PIC #%d saved", pictureNumber - 1);
            tft_drawString(msg, tft_width() / 2, 150);
          } else {
            tft_setTextColor(TFT_RED);
            tft_drawString("Save failed!", tft_width() / 2, 150);
          }
          tft_setTextDatum(top_left);
          xSemaphoreGive(spiMutex);
        }

        /* SD removed during timelapse — stop */
        if (!saved && !globalSDState.isMounted) {
          serial_println("[TL] SD removed, stopping.");
          break;
        }
      }
      lastCaptureTime = millis();
    }

    /* ── Update display (~500ms rate) ── */
    now = millis();
    if (now - lastDisplayUpdate >= 500) {
      lastDisplayUpdate = now;
      unsigned long elapsedSec = (now - startTime) / 1000UL;
      /* Recalculate remaining after potential capture */
      if (lastCaptureTime > 0) {
        remaining = interval - (int)((now - lastCaptureTime) / 1000UL);
        if (remaining < 0) remaining = 0;
      }

      if (xSemaphoreTake(spiMutex, pdMS_TO_TICKS(50))) {
        /* Countdown */
        tft_fillRect(0, 50, 320, 40, TFT_BLACK);
        tft_setTextDatum(middle_center);
        tft_setTextSize(3);
        tft_setTextColor(TFT_GREEN);
        char countBuf[8];
        snprintf(countBuf, sizeof(countBuf), "%d", remaining);
        tft_drawString(countBuf, tft_width() / 2, 70);

        /* Info line 1: photo count + interval */
        tft_fillRect(0, 100, 320, 35, TFT_BLACK);
        tft_setTextSize(1);
        tft_setTextColor(TFT_WHITE);
        char infoBuf[40];
        snprintf(infoBuf, sizeof(infoBuf), "Photos: %d   Interval: %ds", captureCount, interval);
        tft_drawString(infoBuf, tft_width() / 2, 110);

        /* Info line 2: elapsed time */
        snprintf(infoBuf, sizeof(infoBuf), "Elapsed: %02lu:%02lu",
                 elapsedSec / 60UL, elapsedSec % 60UL);
        tft_drawString(infoBuf, tft_width() / 2, 125);

        /* Footer */
        tft_fillRect(0, 218, 320, 22, TFT_BLACK);
        tft_setTextColor(0x4208);
        tft_drawString("Click: Pause  Long: Stop", tft_width() / 2, 228);

        tft_setTextDatum(top_left);
        xSemaphoreGive(spiMutex);
      }
    }

    vTaskDelay(pdMS_TO_TICKS(100));
  }

  serial_printf("[TL] Timelapse ended. %d photos in %lus.\n",
                captureCount, (millis() - startTime) / 1000UL);

  /* Reinit camera to IDLE preview mode and return */
  initCamera(IDLE_MODE, IDLE_RESOLUTION, IDLE_JPEG_QUALITY);
  if (xSemaphoreTake(spiMutex, portMAX_DELAY)) {
    tft_fillScreen(TFT_BLACK);
    xSemaphoreGive(spiMutex);
  }
  appState = STATE_IDLE;
}

/* ================= SELF-TIMER COUNTDOWN ================= */
/* Runs in taskDisplay context (Core 1). */
/* Camera stays ALIVE in IDLE mode — taskCapture continues to fill dispBuf, */
/* but this function blocks taskDisplay from rendering those frames. */
/* At countdown end, EVT_TAKE_PHOTO is fired and STATE_SELFTIMER_COUNTDOWN */
/* transitions to STATE_PHOTO via the normal savePhotoHighRes() path in taskCapture. */
/* */
/* Cancellation: taskInput sets appState = STATE_IDLE on shutter/ENC_CLICK. */
/* The while loop checks appState every 100ms and exits cleanly. */
static void runSelfTimerCountdown(void) {
  int seconds = camSettings.selftimer_seconds;
  if (seconds <= 0) {
    /* Timer unexpectedly 0 — fire immediately */
    xEventGroupSetBits(appEvents, EVT_TAKE_PHOTO);
    appState = STATE_IDLE;
    return;
  }

  serial_printf("[TIMER] Self-timer started: %d seconds\n", seconds);

  /* Draw static chrome: title */
  if (xSemaphoreTake(spiMutex, portMAX_DELAY)) {
    tft_fillScreen(TFT_BLACK);
    tft_setTextDatum(middle_center);
    tft_setTextSize(2);
    tft_setTextColor(TFT_WHITE);
    tft_drawString("SELF TIMER", tft_width() / 2, 30);
    tft_setTextSize(1);
    tft_setTextColor(0x4208);
    tft_drawString("Press shutter to cancel", tft_width() / 2, 225);
    tft_setTextDatum(top_left);
    xSemaphoreGive(spiMutex);
  }

  /* Drain any pending encoder events (don't process them during countdown) */
  {
    InputEvent ev;
    while (xQueueReceive(inputEventQueue, &ev, 0) == pdTRUE) { (void)ev; }
  }

  /* Digit loop: one iteration per second */
  for (int remaining = seconds; remaining > 0; remaining--) {
    if (appState != STATE_SELFTIMER_COUNTDOWN) {
      /* Cancelled externally (shutter button in taskInput) */
      serial_println("[TIMER] Countdown cancelled.");
      digitalWrite(LED_FLASHLIGHT_PIN, LOW);
      /* Drain encoder events that queued up during the blocked countdown */
      { InputEvent _ev; while (xQueueReceive(inputEventQueue, &_ev, 0) == pdTRUE) { (void)_ev; } }
      if (xSemaphoreTake(spiMutex, portMAX_DELAY)) {
        tft_fillScreen(TFT_BLACK);
        xSemaphoreGive(spiMutex);
      }
      return;
    }

    /* Draw large digit */
    if (xSemaphoreTake(spiMutex, portMAX_DELAY)) {
      tft_fillRect(0, 60, 320, 150, TFT_BLACK);
      tft_setTextDatum(middle_center);
      tft_setTextSize(8);
      /* Last second: red countdown; otherwise white */
      tft_setTextColor(remaining == 1 ? TFT_RED : TFT_WHITE);
      char buf[4];
      snprintf(buf, sizeof(buf), "%d", remaining);
      tft_drawString(buf, tft_width() / 2, 130);
      tft_setTextDatum(top_left);
      xSemaphoreGive(spiMutex);
    }

    /* LED blink pattern for one second: */
    /* Last second = fast blink (100ms on/off x5), earlier = slow (500ms on/off x1) */
    if (remaining == 1) {
      /* Fast blink: 5 x (100ms ON + 100ms OFF) = 1000ms */
      for (int b = 0; b < 5 && appState == STATE_SELFTIMER_COUNTDOWN; b++) {
        digitalWrite(LED_FLASHLIGHT_PIN, camSettings.flashlight_on ? LOW : HIGH);
        vTaskDelay(pdMS_TO_TICKS(100));
        digitalWrite(LED_FLASHLIGHT_PIN, camSettings.flashlight_on ? HIGH : LOW);
        vTaskDelay(pdMS_TO_TICKS(100));
      }
    } else {
      /* Slow blink: 500ms ON, 500ms OFF (invert if flashlight is on) */
      digitalWrite(LED_FLASHLIGHT_PIN, camSettings.flashlight_on ? LOW : HIGH);
      vTaskDelay(pdMS_TO_TICKS(500));
      if (appState == STATE_SELFTIMER_COUNTDOWN) {
        digitalWrite(LED_FLASHLIGHT_PIN, camSettings.flashlight_on ? HIGH : LOW);
        vTaskDelay(pdMS_TO_TICKS(500));
      }
    }
  }

  /* Final check: still running? (cancelled during last blink delay) */
  if (appState != STATE_SELFTIMER_COUNTDOWN) {
    digitalWrite(LED_FLASHLIGHT_PIN, LOW);
    { InputEvent _ev; while (xQueueReceive(inputEventQueue, &_ev, 0) == pdTRUE) { (void)_ev; } }
    if (xSemaphoreTake(spiMutex, portMAX_DELAY)) {
      tft_fillScreen(TFT_BLACK);
      xSemaphoreGive(spiMutex);
    }
    return;
  }

  /* Show camera flash indicator */
  if (xSemaphoreTake(spiMutex, portMAX_DELAY)) {
    tft_fillRect(0, 60, 320, 150, TFT_BLACK);
    tft_setTextDatum(middle_center);
    tft_setTextSize(3);
    tft_setTextColor(TFT_WHITE);
    tft_drawString("CLICK!", tft_width() / 2, 130);
    tft_setTextDatum(top_left);
    xSemaphoreGive(spiMutex);
  }

  /* Drain any encoder events that queued up during the countdown before firing. */
  { InputEvent _ev; while (xQueueReceive(inputEventQueue, &_ev, 0) == pdTRUE) { (void)_ev; } }

  /* Return to IDLE then fire photo event. */
  /* savePhotoHighRes() sets STATE_PHOTO itself; IDLE here lets taskCapture proceed. */
  appState = STATE_IDLE;
  xEventGroupSetBits(appEvents, EVT_TAKE_PHOTO);
  serial_println("[TIMER] Countdown complete, firing photo.");
}

/* ================= MENU HELPERS ================= */

/* Enter main menu from IDLE: deinit camera, set state, trigger redraw. */
/* Camera is powered down during menu navigation to free PSRAM and reduce power. */
void enterMenuMain(void) {
  /* Suppress any pending redraw — taskDisplay would otherwise race us during */
  /* the deinit delay, paint the menu, then get wiped by our fillScreen below. */
  galleryNeedsRedraw = false;
  appState = STATE_MENU_MAIN;
  vTaskDelay(pdMS_TO_TICKS(150));
  esp_camera_deinit();
  serial_println("[MENU] Camera deinited for menu");
  if (xSemaphoreTake(spiMutex, portMAX_DELAY)) {
    tft_fillScreen(TFT_BLACK);
    xSemaphoreGive(spiMutex);
  }
  galleryNeedsRedraw = true;
  if (taskDisplayHandle) xTaskNotifyGive(taskDisplayHandle);
}

/* Exit menu back to IDLE: reinit camera, clear screen. */
void exitMenuToIdle(void) {
  freeGalleryFiles();
  initCamera(IDLE_MODE, IDLE_RESOLUTION, IDLE_JPEG_QUALITY);
  if (xSemaphoreTake(spiMutex, portMAX_DELAY)) {
    tft_fillScreen(TFT_BLACK);
    xSemaphoreGive(spiMutex);
  }
  appState = STATE_IDLE;
}

/* ================= BOOT ANIMATION ================= */
/* Retro startup sequence: colour-stepping fade-in of the title text, */
/* LED flash accent, and subtitle. Runs once during setup(), ~2 seconds. */
/* Uses direct TFT calls (no spiMutex needed — tasks haven't started yet). */
static void runBootAnimation(void) {
  tft_fillScreen(TFT_BLACK);
  delay(200);

  /* Fade-in "RETRO CAM" — 6 steps from dark grey to white */
  static const uint16_t fadeSteps[] = {
    COLOR565(30, 30, 30),
    COLOR565(70, 70, 70),
    COLOR565(120, 120, 120),
    COLOR565(180, 180, 180),
    COLOR565(230, 230, 230),
    TFT_WHITE
  };

  tft_setTextDatum(middle_center);
  for (int i = 0; i < 6; i++) {
    tft_setTextSize(4);
    tft_setTextColorBg(fadeSteps[i], TFT_BLACK);
    tft_drawString("RETRO CAM", tft_width() / 2, 100);
    delay(80);
  }

  /* LED flash — brief camera-flash effect */
  digitalWrite(LED_FLASHLIGHT_PIN, HIGH);
  delay(120);
  digitalWrite(LED_FLASHLIGHT_PIN, LOW);

  /* Subtitle fade-in */
  delay(150);
  tft_setTextSize(2);
  tft_setTextColorBg(tft_color565(80, 80, 80), TFT_BLACK);
  tft_drawString("github/barkinsarikartal", tft_width() / 2, 145);
  delay(100);
  tft_setTextColorBg(0x7BEF, TFT_BLACK);  /* light grey */
  tft_drawString("github/barkinsarikartal", tft_width() / 2, 145);

  /* Firmware version tag */
  delay(100);
  tft_setTextSize(2);
  tft_setTextColor(tft_color565(60, 60, 60));
  tft_drawString(FIRMWARE_VERSION, tft_width() / 2, 170);

  /* Hold for readability */
  delay(800);

  /* Clear for next screen */
  /* tft_fillScreen(TFT_BLACK); */
  tft_setTextDatum(top_left);
}
