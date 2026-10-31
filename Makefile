CXX     = xcrun clang++
OPT     = -O3 -mcpu=apple-m1 -flto=thin -mmacosx-version-min=11.0
APP     = build/LeanPDF.app

# --- MuPDF, built from source as static libraries ---
#
# Only what a PDF viewer needs: no HTML/EPUB/XPS/SVG, JavaScript, OCR, barcodes or
# signatures (OpenSSL), and no fallback fonts beyond the Base14 set PDFs rely on.
# JPEG decoding uses libjpeg-turbo (SIMD) instead of MuPDF's bundled plain libjpeg.
#
# If pgo/mupdf.profdata exists, MuPDF is compiled with it (profile-guided optimization).
# Regenerate it with `make pgo-train`, e.g. after changing MuPDF version or flags.

MUPDF_VER = 1.28.6
MUPDF_SHA = dc85000640a45d90ca9b77b061f6ca67cce0c4d4fbecf8819647baf573eef101
MUPDF_SRC = build/mupdf-$(MUPDF_VER)-source
MUPDF_OUT = $(CURDIR)/build/mupdf
MUPDF_GEN = $(CURDIR)/build/mupdf-pgo-gen
MUPDF_LIBS = $(MUPDF_OUT)/libmupdf.a $(MUPDF_OUT)/libmupdf-third.a
JPEG     := $(shell brew --prefix jpeg-turbo)

PROFILE   = pgo/mupdf.profdata
TRAIN_PDF ?= $(HOME)/Documents/SPEC/Books/Kaplan SAT Total Prep 2026.pdf

MUPDF_ARGS = build=release shared=no CC="xcrun clang" CXX="xcrun clang++" \
             HAVE_LIBCRYPTO=no tesseract=no barcode=no html=no mujs=no brotli=no \
             extract=no xps=no svg=no tofu=yes \
             USE_SYSTEM_LIBJPEG=yes SYS_LIBJPEG_CFLAGS="-I$(JPEG)/include" \
             SYS_LIBJPEG_LIBS="$(JPEG)/lib/libjpeg.a"
MUPDF_CFLAGS = $(OPT) -DTOFU_CJK

ifneq ($(wildcard $(PROFILE)),)
  PGO_USE = -fprofile-use=$(CURDIR)/$(PROFILE) -Wno-profile-instr-unprofiled
endif

# --- The app ---

FLAGS   = -std=c++17 $(OPT) -fobjc-arc -Wall -I$(MUPDF_SRC)/include
LIBS    = $(MUPDF_LIBS) $(JPEG)/lib/libjpeg.a -Wl,-dead_strip \
          -framework Cocoa -framework PDFKit -framework UniformTypeIdentifiers -framework Security -framework ImageIO -framework Accelerate

all: $(APP)

$(APP): main.mm Info.plist AppIcon.icns $(MUPDF_LIBS)
	mkdir -p $(APP)/Contents/MacOS $(APP)/Contents/Resources
	cp Info.plist $(APP)/Contents/Info.plist
	cp AppIcon.icns $(APP)/Contents/Resources/AppIcon.icns
	$(CXX) $(FLAGS) main.mm -o $(APP)/Contents/MacOS/LeanPDF $(LIBS)
	codesign --force -s - $(APP)

$(MUPDF_SRC)/Makefile:
	mkdir -p build
	curl -fL -o build/mupdf.tar.gz https://mupdf.com/downloads/archive/mupdf-$(MUPDF_VER)-source.tar.gz
	echo "$(MUPDF_SHA)  build/mupdf.tar.gz" | shasum -a 256 -c
	tar -xzf build/mupdf.tar.gz -C build
	rm build/mupdf.tar.gz
	touch $@

# MuPDF's own make doesn't notice flag changes, so rebuild from scratch when the profile changes.
$(MUPDF_LIBS): $(MUPDF_OUT)/.built
$(MUPDF_OUT)/.built: $(MUPDF_SRC)/Makefile $(wildcard $(PROFILE))
	rm -rf $(MUPDF_OUT)
	$(MAKE) -C $(MUPDF_SRC) $(MUPDF_ARGS) OUT=$(MUPDF_OUT) \
		XCFLAGS="$(MUPDF_CFLAGS) $(PGO_USE)" XLDFLAGS="-flto=thin" libs
	touch $@

# Builds an instrumented mutool, renders TRAIN_PDF the way the app does (fit to window,
# zoomed in, thumbnails) and merges the recorded profile into $(PROFILE).
pgo-train: $(MUPDF_SRC)/Makefile
	rm -rf $(MUPDF_GEN) build/pgo-raw && mkdir -p build/pgo-raw pgo
	$(MAKE) -C $(MUPDF_SRC) $(MUPDF_ARGS) OUT=$(MUPDF_GEN) \
		XCFLAGS="$(MUPDF_CFLAGS) -fprofile-generate" XLDFLAGS="-flto=thin -fprofile-generate" tools
	export LLVM_PROFILE_FILE="$(CURDIR)/build/pgo-raw/%p.profraw"; \
	$(MUPDF_GEN)/mutool draw -q -c rgb -r 1000 -w 1700 -h 2200 "$(TRAIN_PDF)" 1-N && \
	$(MUPDF_GEN)/mutool draw -q -c rgb -r 1000 -w 3400 -h 4400 "$(TRAIN_PDF)" 1-300 && \
	$(MUPDF_GEN)/mutool draw -q -c rgb -r 1000 -w 200 -h 260 "$(TRAIN_PDF)" 1-N
	xcrun llvm-profdata merge -o $(PROFILE) build/pgo-raw/*.profraw

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

install: $(APP)
	rm -rf $(HOME)/Applications/LeanPDF.app
	ditto $(APP) $(HOME)/Applications/LeanPDF.app

clean:
	rm -rf build

.PHONY: all run install clean pgo-train
