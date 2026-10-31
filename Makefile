MUPDF  ?= $(shell brew --prefix mupdf)
CXX     = xcrun clang++
FLAGS   = -std=c++17 -O2 -fobjc-arc -Wall -mmacosx-version-min=11.0 -I$(MUPDF)/include
LIBS    = -L$(MUPDF)/lib -lmupdf -Wl,-rpath,$(MUPDF)/lib \
          -framework Cocoa -framework PDFKit -framework UniformTypeIdentifiers -framework Security -framework ImageIO
APP     = build/LeanPDF.app

all: $(APP)

$(APP): main.mm Info.plist AppIcon.icns
	mkdir -p $(APP)/Contents/MacOS $(APP)/Contents/Resources
	cp Info.plist $(APP)/Contents/Info.plist
	cp AppIcon.icns $(APP)/Contents/Resources/AppIcon.icns
	$(CXX) $(FLAGS) main.mm -o $(APP)/Contents/MacOS/LeanPDF $(LIBS)
	codesign --force -s - $(APP)

# The app icon, rendered from icon.svg at every size macOS wants.
AppIcon.icns: icon.svg svg2png.swift
	rm -rf build/AppIcon.iconset && mkdir -p build/AppIcon.iconset
	for s in 16 32 128 256 512; do \
		swift svg2png.swift icon.svg build/AppIcon.iconset/icon_$${s}x$${s}.png $$s; \
		swift svg2png.swift icon.svg build/AppIcon.iconset/icon_$${s}x$${s}@2x.png $$((s*2)); \
	done
	iconutil -c icns build/AppIcon.iconset -o AppIcon.icns

run: $(APP)
	open $(APP)

clean:
	rm -rf build

.PHONY: all run clean
