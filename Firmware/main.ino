#include <Arduino.h>
#include <OV7670.h>
#include "main.h"
#include "sd_card.h"
#include "menu.h"


int main() {
    // Arduino Framework init
    init();

    // Camera init
    OV7670 camera;
    camera.begin();

    // Main loop
    while (true) {
        // Image capture
        camera.captureImage();

        // Processing and saving
        // ...
        println("Picture Taken!");
        saveImage(camera.getImageBuffer(), camera.getImageSize());
        // save to SD card

        // delay to control frmrt
        delay(100);
    }

    return 0;
}
