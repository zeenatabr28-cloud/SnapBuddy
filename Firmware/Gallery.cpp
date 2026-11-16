#include "shared.h"

// ================= GALLERY FUNCTIONS (ESP32-WROOM-32 + OV7670 V2, PHOTO-ONLY) =================

// Parse width and height from a JPEG buffer's SOF0/SOF2 marker.
// Returns true on success; falls back to false if marker is not found.
static bool getJpegDimensions(const uint8_t *buf, size_t len, uint16_t *outW, uint16_t *outH) {
  if (!buf || len < 4 || buf[0] != 0xFF || buf[1] != 0xD8) return false;

  size_t i = 2;
  while (i + 4 < len) {
    if (buf[i] != 0xFF) {
      i++;
      continue;
    }
    while (i < len && buf[i] == 0xFF) i++;
    if (i >= len) break;

    uint8_t marker = buf[i++];
    if (marker == 0xD8 || marker == 0xD9 || marker == 0x00 ||
        (marker >= 0xD0 && marker <= 0xD7)) {
      continue;
    }
    if (marker == 0xDA) break;  // SOS — image data follows

    if (i + 2 > len) break;
    uint16_t segLen = ((uint16_t)buf[i] << 8) | buf[i + 1];
    if (segLen < 2 || i + segLen > len) break;

    if ((marker == 0xC0 || marker == 0xC1 || marker == 0xC2) && segLen >= 7) {
      uint16_t h = ((uint16_t)buf[i + 3] << 8) | buf[i + 4];
      uint16_t w = ((uint16_t)buf[i + 5] << 8) | buf[i + 6];
      if (w > 0 && h > 0) {
        *outW = w;
        *outH = h;
        return true;
      }
      return false;
    }
    i += segLen;
  }
  return false;
}

// Scan SD root for .jpg files into DRAM-backed array (ESP32-WROOM-32 has no PSRAM).
// Call freeGalleryFiles() before re-scanning or exiting gallery.
void scanGalleryFiles(bool videosOnly) {
  (void)videosOnly;
  freeGalleryFiles();
  if (!globalSDState.isMounted) return;

  const char *ext = ".jpg";

  // Allocate pointer array in internal DRAM
  galleryFiles = (char**)malloc(GALLERY_MAX_FILES * sizeof(char*));
  if (!galleryFiles) {
    Serial.println("[GAL] DRAM alloc failed for file index");
    return;
  }

  int count = 0;
  if (xSemaphoreTake(spiMutex, portMAX_DELAY)) {
    File root = SD.open("/");
    if (root) {
      File f = root.openNextFile();
      while (f && count < GALLERY_MAX_FILES) {
        if (!f.isDirectory()) {
          String name = f.name();
          if (name.endsWith(ext) || name.endsWith(".JPG")) {
            galleryFiles[count] = (char*)malloc(GALLERY_NAME_LEN);
            if (!galleryFiles[count]) {
              Serial.println("[GAL] DRAM alloc limit reached for file list");
              f.close();
              break;
            }
            // f.name() may or may not include leading '/' depending on
            // ESP32 Arduino core version. Normalize to always have '/'.
            if (name.startsWith("/")) {
              strncpy(galleryFiles[count], name.c_str(), GALLERY_NAME_LEN - 1);
            } else {
              snprintf(galleryFiles[count], GALLERY_NAME_LEN, "/%s", name.c_str());
            }
            galleryFiles[count][GALLERY_NAME_LEN - 1] = '\0';
            count++;
          }
        }
        f.close();
        f = root.openNextFile();
      }
      root.close();
    }
    xSemaphoreGive(spiMutex);
  }

  galleryFileCount = count;

  // Sort descending by embedded number (newest/highest first).
  // Filenames follow patterns like /hd_pic_42.jpg.
  // Extract trailing number for numeric comparison so pic_10 > pic_9.
  if (galleryFileCount > 1) {
    for (int i = 1; i < galleryFileCount; i++) {
      char *key = galleryFiles[i];
      const char *p = key + strlen(key) - 1;
      while (p > key && *p != '_') p--;
      int keyNum = (p > key) ? atoi(p + 1) : 0;

      int j = i - 1;
      while (j >= 0) {
        const char *q = galleryFiles[j] + strlen(galleryFiles[j]) - 1;
        while (q > galleryFiles[j] && *q != '_') q--;
        int jNum = (q > galleryFiles[j]) ? atoi(q + 1) : 0;
        if (jNum < keyNum) {
          galleryFiles[j + 1] = galleryFiles[j];
          j--;
        } else {
          break;
        }
      }
      galleryFiles[j + 1] = key;
    }
  }

  galleryIndex = 0;
  Serial.printf("[GAL] Found %d photo files\n", galleryFileCount);
}

// Release gallery file index memory.
void freeGalleryFiles() {
  if (galleryFiles) {
    for (int i = 0; i < galleryFileCount; i++) {
      if (galleryFiles[i]) free(galleryFiles[i]);
    }
    free(galleryFiles);
    galleryFiles = nullptr;
  }
  galleryFileCount = 0;
  galleryIndex = 0;
}

// Grid page index (0-indexed). Reset on gallery entry.
int gridPage = 0;

// Helper: render one photo thumbnail cell at grid position (col, row).
// Reads JPEG from SD into dispBuf[0] and decodes to TFT scaled to fit THUMB_W x THUMB_H.
// Caller must NOT hold spiMutex — this function acquires it internally.
static void renderThumbCell(int col, int row, int fileIdx) {
  // Cell geometry: 4px outer padding, 4px gap between cells
  // Total grid width = 4 + 4*70 + 3*4 + 4 = 300, centered in 320 -> x_offset=10
  // Total grid height = 22 + 4 + 3*52 + 2*4 + 4 = 194 (header 22px)
  int x = 10 + col * (THUMB_W + 4);
  int y = 22 + row * (THUMB_H + 4);

  uint8_t *buf = dispBuf[0];
  size_t jpgLen = 0;

  if (fileIdx < galleryFileCount && buf) {
    if (xSemaphoreTake(spiMutex, portMAX_DELAY)) {
      File f = SD.open(galleryFiles[fileIdx], FILE_READ);
      if (f) {
        size_t sz = f.size();
        if (sz > 0 && sz <= DISP_BUF_SIZE) jpgLen = f.read(buf, sz);
        f.close();
      }
      xSemaphoreGive(spiMutex);
    }
  }

  if (xSemaphoreTake(spiMutex, portMAX_DELAY)) {
    if (jpgLen > 0) {
      // Scale dynamically to fill THUMB_W x THUMB_H (supports OV7670 QVGA/HQVGA/QQVGA)
      uint16_t jw = 320, jh = 240;
      getJpegDimensions(buf, jpgLen, &jw, &jh);
      float sx = (float)THUMB_W / (float)jw;
      float sy = (float)THUMB_H / (float)jh;
      float scale = (sx > sy) ? sx : sy;
      tft.drawJpg(buf, jpgLen, x, y, THUMB_W, THUMB_H, 0, 0, scale);
    } else {
      // Placeholder: dark grey cell
      tft.fillRect(x, y, THUMB_W, THUMB_H, tft.color565(30, 30, 30));
      tft.setTextDatum(middle_center);
      tft.setTextSize(1);
      tft.setTextColor(0x4208);
      tft.drawString("IMG", x + THUMB_W / 2, y + THUMB_H / 2);
      tft.setTextDatum(top_left);
    }
    xSemaphoreGive(spiMutex);
  }
}

// Helper: draw selection border around cursor cell.
void drawGridCursor(int col, int row, uint16_t color) {
  int x = 10 + col * (THUMB_W + 4);
  int y = 22 + row * (THUMB_H + 4);
  if (xSemaphoreTake(spiMutex, portMAX_DELAY)) {
    tft.drawRect(x - 1, y - 1, THUMB_W + 2, THUMB_H + 2, color);
    tft.drawRect(x - 2, y - 2, THUMB_W + 4, THUMB_H + 4, color);
    xSemaphoreGive(spiMutex);
  }
}

// Helper: clear selection border by drawing black over it.
void clearGridCursor(int col, int row) {
  drawGridCursor(col, row, TFT_BLACK);
}

// Render the full photo grid page. Shows "Loading..." then decodes all thumbnails.
void drawPhotoGrid() {
  if (galleryFileCount == 0) return;

  int totalPages = (galleryFileCount + GRID_ITEMS_PER_PAGE - 1) / GRID_ITEMS_PER_PAGE;
  if (gridPage >= totalPages) gridPage = totalPages - 1;
  if (gridPage < 0) gridPage = 0;
  int pageStart = gridPage * GRID_ITEMS_PER_PAGE;

  // Loading screen
  if (xSemaphoreTake(spiMutex, portMAX_DELAY)) {
    tft.fillScreen(TFT_BLACK);
    tft.setTextDatum(middle_center);
    tft.setTextSize(1);
    tft.setTextColor(TFT_YELLOW);
    tft.drawString("Loading thumbnails...", tft.width() / 2, 120);
    tft.setTextDatum(top_left);
    xSemaphoreGive(spiMutex);
  }

  // Clear screen for grid
  if (xSemaphoreTake(spiMutex, portMAX_DELAY)) {
    tft.fillScreen(TFT_BLACK);
    xSemaphoreGive(spiMutex);
  }

  // Render each thumbnail cell
  for (int i = 0; i < GRID_ITEMS_PER_PAGE; i++) {
    int fileIdx = pageStart + i;
    if (fileIdx >= galleryFileCount) break;
    int col = i % GRID_COLS;
    int row = i / GRID_COLS;
    renderThumbCell(col, row, fileIdx);
  }

  // Header: page indicator
  if (xSemaphoreTake(spiMutex, portMAX_DELAY)) {
    tft.setTextDatum(middle_center);
    tft.setTextSize(1);
    tft.setTextColor(TFT_CYAN);
    char hdr[32];
    snprintf(hdr, sizeof(hdr), "Photos  %d/%d", gridPage + 1, totalPages);
    tft.drawString(hdr, tft.width() / 2, 10);

    // Footer
    tft.setTextColor(0x4208);
    tft.drawString("Turn:Move  Click:View  Long:Back", tft.width() / 2, 232);
    tft.setTextDatum(top_left);
    xSemaphoreGive(spiMutex);
  }

  // Draw cursor on current selection
  int localIdx = galleryIndex - pageStart;
  if (localIdx >= 0 && localIdx < GRID_ITEMS_PER_PAGE) {
    drawGridCursor(localIdx % GRID_COLS, localIdx / GRID_COLS, TFT_CYAN);
  }
}

// Display a single photo detail view.
// Reads JPEG file into dispBuf[0] (safe because taskCapture skips copy during gallery),
// then decodes with LovyanGFX drawJpg fitted inside the 320x180 viewport.
void drawGalleryPhotoView() {
  if (galleryFileCount == 0 || galleryIndex >= galleryFileCount) return;
  if (!globalSDState.isMounted) return;

  const char *filePath = galleryFiles[galleryIndex];

  // Camera copy is paused in gallery states, so dispBuf[0] is free for JPEG I/O.
  uint8_t *jpgBuf = dispBuf[0];
  size_t jpgLen = 0;
  size_t fileBytes = 0;

  if (xSemaphoreTake(spiMutex, portMAX_DELAY)) {
    File f = SD.open(filePath, FILE_READ);
    if (f) {
      fileBytes = f.size();
      if (fileBytes > 0 && fileBytes <= DISP_BUF_SIZE && jpgBuf) {
        jpgLen = f.read(jpgBuf, fileBytes);
      }
      f.close();
    }
    xSemaphoreGive(spiMutex);
  }

  if (xSemaphoreTake(spiMutex, portMAX_DELAY)) {
    tft.fillScreen(TFT_BLACK);
    tft.setTextDatum(middle_center);

    // Header: index / total
    tft.setTextSize(1);
    tft.setTextColor(TFT_WHITE);
    char header[32];
    snprintf(header, sizeof(header), "%d / %d", galleryIndex + 1, galleryFileCount);
    tft.drawString(header, tft.width() / 2, 8);

    // Filename (strip leading /)
    tft.setTextColor(TFT_CYAN);
    const char *dispName = filePath;
    if (dispName[0] == '/') dispName++;
    tft.drawString(dispName, tft.width() / 2, 20);

    if (jpgLen > 0) {
      // Fit image inside 320x180 viewport (y=30..210) centered horizontally & vertically
      uint16_t jw = 320, jh = 240;
      getJpegDimensions(jpgBuf, jpgLen, &jw, &jh);
      float sx = 320.0f / (float)jw;
      float sy = 180.0f / (float)jh;
      float scale = (sx < sy) ? sx : sy;
      int drawW = (int)(jw * scale);
      int drawH = (int)(jh * scale);
      int drawX = (320 - drawW) / 2;
      int drawY = 30 + (180 - drawH) / 2;
      tft.drawJpg(jpgBuf, jpgLen, drawX, drawY, drawW, drawH, 0, 0, scale);
    } else {
      tft.setTextSize(2);
      tft.setTextColor(TFT_RED);
      tft.drawString("Cannot display", tft.width() / 2, 120);
    }

    // File size
    if (fileBytes > 0) {
      char sizeStr[16];
      if (fileBytes < 1024 * 1024) {
        snprintf(sizeStr, sizeof(sizeStr), "%.1f KB", fileBytes / 1024.0f);
      } else {
        snprintf(sizeStr, sizeof(sizeStr), "%.1f MB", fileBytes / 1048576.0f);
      }
      tft.setTextSize(1);
      tft.setTextColor(0x7BEF);
      tft.drawString(sizeStr, tft.width() / 2, 215);
    }

    tft.setTextSize(1);
    tft.setTextColor(0x4208);
    tft.drawString("Click:Delete  Long:Back", tft.width() / 2, 225);

    tft.setTextDatum(top_left);
    xSemaphoreGive(spiMutex);
  }
}

// Draw the delete confirmation dialog.
void drawDeleteConfirm() {
  if (galleryFileCount == 0 || galleryIndex >= galleryFileCount) return;

  if (xSemaphoreTake(spiMutex, portMAX_DELAY)) {
    tft.fillScreen(TFT_BLACK);
    tft.setTextDatum(middle_center);

    // Title
    tft.setTextSize(2);
    tft.setTextColor(TFT_RED);
    tft.drawString("DELETE FILE?", tft.width() / 2, 30);

    // Filename
    tft.setTextSize(1);
    tft.setTextColor(TFT_WHITE);
    const char *dispName = galleryFiles[galleryIndex];
    if (dispName[0] == '/') dispName++;
    tft.drawString(dispName, tft.width() / 2, 60);

    // Cancel option
    tft.setTextSize(2);
    if (deleteSelection == 0) {
      tft.fillRoundRect(60, 90, 200, 40, 8, TFT_GREEN);
      tft.setTextColor(TFT_BLACK);
    } else {
      tft.drawRoundRect(60, 90, 200, 40, 8, 0x4208);
      tft.setTextColor(0x7BEF);
    }
    tft.drawString("Cancel", tft.width() / 2, 110);

    // Delete option
    tft.setTextSize(2);
    if (deleteSelection == 1) {
      tft.fillRoundRect(60, 150, 200, 40, 8, TFT_RED);
      tft.setTextColor(TFT_WHITE);
    } else {
      tft.drawRoundRect(60, 150, 200, 40, 8, 0x4208);
      tft.setTextColor(0x7BEF);
    }
    tft.drawString("Delete", tft.width() / 2, 170);

    // Footer
    tft.setTextSize(1);
    tft.setTextColor(0x4208);
    tft.drawString("Long press: Back", tft.width() / 2, 225);

    tft.setTextDatum(top_left);
    xSemaphoreGive(spiMutex);
  }
}

// ================= SLIDESHOW MODE =================
// Runs in taskDisplay context (Core 1).
// Camera is deinited (STATE_SLIDESHOW is in taskCapture skip list).
// Scans SD for .jpg files on entry, then cycles through them full-screen.
// ENC_CLICK = pause/resume | ENC_LONG = exit to MENU_MAIN
// Shutter = handled externally by taskInput (emergencyExitToIdle -> STATE_IDLE)
void runSlideshow() {
  scanGalleryFiles(false);

  if (galleryFileCount == 0) {
    if (xSemaphoreTake(spiMutex, portMAX_DELAY)) {
      tft.fillScreen(TFT_BLACK);
      tft.setTextDatum(middle_center);
      tft.setTextSize(2);
      tft.setTextColor(TFT_RED);
      tft.drawString("No photos found", tft.width() / 2, 100);
      tft.setTextSize(1);
      tft.setTextColor(0x4208);
      tft.drawString("Add photos to SD card", tft.width() / 2, 130);
      tft.setTextDatum(top_left);
      xSemaphoreGive(spiMutex);
    }
    vTaskDelay(pdMS_TO_TICKS(2000));
    freeGalleryFiles();
    appState = STATE_MENU_MAIN;
    galleryNeedsRedraw = true;
    if (taskDisplayHandle) xTaskNotifyGive(taskDisplayHandle);
    return;
  }

  int intervalMs = camSettings.slideshow_interval * 1000;
  if (intervalMs < 1000) intervalMs = 3000;

  Serial.printf("[SLIDE] Starting slideshow: %d photos, %ds interval\n",
                galleryFileCount, camSettings.slideshow_interval);

  galleryIndex = 0;
  bool paused = false;
  unsigned long lastAdvance = 0;

  if (xSemaphoreTake(spiMutex, portMAX_DELAY)) {
    tft.fillScreen(TFT_BLACK);
    tft.setTextDatum(middle_center);
    tft.setTextSize(2);
    tft.setTextColor(TFT_MAGENTA);
    tft.drawString("SLIDESHOW", tft.width() / 2, 120);
    tft.setTextDatum(top_left);
    xSemaphoreGive(spiMutex);
  }
  vTaskDelay(pdMS_TO_TICKS(800));

  while (appState == STATE_SLIDESHOW) {
    InputEvent ev;
    while (xQueueReceive(inputEventQueue, &ev, 0) == pdTRUE) {
      if (ev.type == INPUT_ENC_CLICK) {
        paused = !paused;
        if (xSemaphoreTake(spiMutex, pdMS_TO_TICKS(50))) {
          if (paused) {
            tft.fillRect(4, 4, 26, 20, TFT_BLACK);
            tft.fillRect(5, 5, 8, 18, TFT_WHITE);
            tft.fillRect(16, 5, 8, 18, TFT_WHITE);
          } else {
            tft.fillRect(4, 4, 26, 20, TFT_BLACK);
          }
          xSemaphoreGive(spiMutex);
        }
      } else if (ev.type == INPUT_ENC_LONG) {
        Serial.println("[SLIDE] ENC_LONG: exiting slideshow.");
        freeGalleryFiles();
        appState = STATE_MENU_MAIN;
        galleryNeedsRedraw = true;
        if (taskDisplayHandle) xTaskNotifyGive(taskDisplayHandle);
        return;
      }
    }

    if (paused) {
      vTaskDelay(pdMS_TO_TICKS(100));
      continue;
    }

    unsigned long now = millis();
    bool timeToAdvance = (lastAdvance == 0) ||
                         ((now - lastAdvance) >= (unsigned long)intervalMs);

    if (timeToAdvance) {
      const char *filePath = galleryFiles[galleryIndex];
      uint8_t *jpgBuf = dispBuf[0];
      size_t jpgLen = 0;

      if (xSemaphoreTake(spiMutex, portMAX_DELAY)) {
        File f = SD.open(filePath, FILE_READ);
        if (f) {
          size_t sz = f.size();
          if (sz > 0 && sz <= DISP_BUF_SIZE && jpgBuf) {
            jpgLen = f.read(jpgBuf, sz);
          }
          f.close();
        }
        xSemaphoreGive(spiMutex);
      }

      if (xSemaphoreTake(spiMutex, portMAX_DELAY)) {
        tft.fillScreen(TFT_BLACK);
        if (jpgLen > 0) {
          uint16_t jw = 320, jh = 240;
          getJpegDimensions(jpgBuf, jpgLen, &jw, &jh);
          float sx = 320.0f / (float)jw;
          float sy = 180.0f / (float)jh;
          float scale = (sx < sy) ? sx : sy;
          int drawW = (int)(jw * scale);
          int drawH = (int)(jh * scale);
          int drawX = (320 - drawW) / 2;
          int drawY = 30 + (180 - drawH) / 2;
          tft.drawJpg(jpgBuf, jpgLen, drawX, drawY, drawW, drawH, 0, 0, scale);
        } else {
          tft.setTextDatum(middle_center);
          tft.setTextSize(1);
          tft.setTextColor(TFT_RED);
          tft.drawString("Cannot load photo", tft.width() / 2, 120);
          tft.setTextDatum(top_left);
        }
        tft.fillRect(0, 0, 320, 28, TFT_BLACK);
        tft.setTextDatum(middle_center);
        tft.setTextSize(1);
        tft.setTextColor(TFT_MAGENTA);
        char hdr[32];
        snprintf(hdr, sizeof(hdr), "Slideshow  %d / %d", galleryIndex + 1, galleryFileCount);
        tft.drawString(hdr, tft.width() / 2, 10);
        const char *dispName = filePath;
        if (dispName[0] == '/') dispName++;
        tft.setTextColor(0x7BEF);
        tft.drawString(dispName, tft.width() / 2, 22);
        tft.fillRect(0, 215, 320, 25, TFT_BLACK);
        tft.setTextSize(1);
        tft.setTextColor(0x4208);
        tft.drawString("Click:Pause  Long:Exit", tft.width() / 2, 228);
        tft.setTextDatum(top_left);
        xSemaphoreGive(spiMutex);
      }

      galleryIndex = (galleryIndex + 1) % galleryFileCount;
      lastAdvance = millis();
    }

    vTaskDelay(pdMS_TO_TICKS(100));
  }

  Serial.println("[SLIDE] Slideshow ended.");
  freeGalleryFiles();

  // Only redirect to MENU_MAIN if we weren't already sent to IDLE.
  AppState exitState = appState;
  if (exitState == STATE_SLIDESHOW || exitState == STATE_MENU_MAIN) {
    appState = STATE_MENU_MAIN;
    galleryNeedsRedraw = true;
    if (taskDisplayHandle) xTaskNotifyGive(taskDisplayHandle);
  }
}