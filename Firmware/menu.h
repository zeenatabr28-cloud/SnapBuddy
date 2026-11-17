#pragma once
#include <Arduino.h>

namespace SnapBuddyMenu {

// Select pins that do not conflict with the camera or other peripherals.
constexpr uint8_t ENCODER_CLK_PIN = 32;
constexpr uint8_t ENCODER_DT_PIN = void;
constexpr uint8_t ENCODER_SW_PIN = 25;

enum class Setting : uint8_t {
	Resolution,
	Brightness,
	Contrast,
	Exposure,
	Saturation,
	HorizontalMirror,
	VerticalFlip,
	Count
};

using ApplyCallback = void (*)(Setting setting, int value);
using RenderCallback = void (*)(const char *title, const char *item,
																int value, bool editing);

class CameraMenu {
 public:
	CameraMenu(uint8_t clkPin = ENCODER_CLK_PIN,
						 uint8_t dtPin = ENCODER_DT_PIN,
						 uint8_t switchPin = ENCODER_SW_PIN)
			: clkPin_(clkPin), dtPin_(dtPin), switchPin_(switchPin) {}

	void begin(ApplyCallback apply, RenderCallback render) {
		apply_ = apply;
		render_ = render;
		pinMode(clkPin_, INPUT_PULLUP);
		pinMode(dtPin_, INPUT_PULLUP);
		pinMode(switchPin_, INPUT_PULLUP);
		lastClk_ = digitalRead(clkPin_);
		lastButton_ = digitalRead(switchPin_);
		renderCurrent();
	}

	// Call repeatedly from loop(). Rotation selects items or adjusts a value;
	// pressing the encoder switches between those modes.
	void update() {
		const int clk = digitalRead(clkPin_);
		if (clk != lastClk_) {
			if (lastClk_ == HIGH && clk == LOW) {
				rotate(digitalRead(dtPin_) != clk ? 1 : -1);
			}
			lastClk_ = clk;
		}

		const int button = digitalRead(switchPin_);
		const uint32_t now = millis();
		if (button != lastButton_ && now - lastButtonChange_ >= debounceMs_) {
			lastButtonChange_ = now;
			lastButton_ = button;
			if (button == LOW) {
				editing_ = !editing_;
				renderCurrent();
			}
		}
	}

	int value(Setting setting) const {
		const int index = static_cast<int>(setting);
		return index >= 0 && index < static_cast<int>(Setting::Count)
							 ? items_[index].value
							 : 0;
	}

 private:
	struct MenuItem {
		Setting setting;
		const char *label;
		int minimum;
		int maximum;
		int value;
	};

	MenuItem items_[static_cast<uint8_t>(Setting::Count)] = {
			{Setting::Resolution, "Resolution", 0, 2, 0},
			{Setting::Brightness, "Brightness", -2, 2, 0},
			{Setting::Contrast, "Contrast", -2, 2, 0},
			{Setting::Exposure, "Exposure", 0, 5, 3},
			{Setting::Saturation, "Saturation", -2, 2, 0},
			{Setting::HorizontalMirror, "H-Mirror", 0, 1, 0},
			{Setting::VerticalFlip, "V-Flip", 0, 1, 0},
	};

	uint8_t clkPin_;
	uint8_t dtPin_;
	uint8_t switchPin_;
	uint8_t selected_ = 0;
	int lastClk_ = HIGH;
	int lastButton_ = HIGH;
	uint32_t lastButtonChange_ = 0;
	bool editing_ = false;
	ApplyCallback apply_ = nullptr;
	RenderCallback render_ = nullptr;
	static constexpr uint32_t debounceMs_ = 35;

	void rotate(int direction) {
		if (editing_) {
			MenuItem &item = items_[selected_];
			item.value += direction;
			if (item.value < item.minimum) item.value = item.minimum;
			if (item.value > item.maximum) item.value = item.maximum;
			if (apply_) apply_(item.setting, item.value);
		} else {
			const int count = static_cast<int>(Setting::Count);
			selected_ = static_cast<uint8_t>((selected_ + direction + count) % count);
		}
		renderCurrent();
	}

	void renderCurrent() {
		if (render_) {
			const MenuItem &item = items_[selected_];
			render_("Camera", item.label, item.value, editing_);
		}
	}
};

}  // namespace SnapBuddyMenu
