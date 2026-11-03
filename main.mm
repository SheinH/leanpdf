// LeanPDF — a barebones Preview. Cocoa + MuPDF, one file.
//
// Threading: every MuPDF call (either context, any document) happens while
// holding g_doc_lock. The main thread renders the visible page; one worker
// thread renders sidebar thumbnails and prefetches neighbouring pages.
//
// Memory: with more than kIdleMinDocs documents open, a window left in the background for
// kIdleDelay goes dormant. It drops its rendered
// pages and thumbnails and stops prefetching until it is used again. Re-rendering a page is about
// as fast as reading it back from disk, so nothing is saved; the window's own backing store keeps
// showing the page meanwhile.

#import <Cocoa/Cocoa.h>
#import <PDFKit/PDFKit.h>
#import <UniformTypeIdentifiers/UniformTypeIdentifiers.h>
#import <Security/Security.h>
#import <ImageIO/ImageIO.h>
#import <Accelerate/Accelerate.h>
#import <QuartzCore/QuartzCore.h>
#import <IOSurface/IOSurface.h>
#import <CommonCrypto/CommonDigest.h>
#include <mupdf/fitz.h>
#include <mupdf/pdf.h>
#include <malloc/malloc.h>
#include <pthread.h>
#include <atomic>
#include <cstdlib>
#include <map>
#include <vector>

static fz_context *g_ctx;        // main thread
static fz_context *g_worker_ctx; // worker thread
static pthread_mutex_t g_fz_locks[FZ_LOCK_MAX];
static pthread_mutex_t g_doc_lock = PTHREAD_MUTEX_INITIALIZER;

struct DocLock {
	DocLock() { pthread_mutex_lock(&g_doc_lock); }
	~DocLock() { pthread_mutex_unlock(&g_doc_lock); }
};

static void fz_lock_cb(void *, int i) { pthread_mutex_lock(&g_fz_locks[i]); }
static void fz_unlock_cb(void *, int i) { pthread_mutex_unlock(&g_fz_locks[i]); }

static const NSTimeInterval kIdleDelay = 60;
static const NSUInteger kIdleMinDocs = 3;
static const CGFloat kThumbW = 130, kThumbH = 160, kPageMargin = 12, kRingPad = 6;
// Preview's sidebar item: kRingPad around the page, its label 1pt below and 16pt tall, 2pt of
// padding under the label, and 10pt between items. Thumbnails keep their size; items stay centred.
// Thumbnails don't scale, so their sidebar is a fixed width: the item plus 13pt either side, as in Preview.
static const CGFloat kThumbSideW = kThumbW + 2 * kRingPad + 2 * 13;
static const CGFloat kLabelGap = 1, kLabelH = 16, kItemBottomPad = 2, kItemGap = 10;
// Zoom, relative to the page fitted to the window. Zoom In/Out step through kZoomLevels.
static const CGFloat kZoomLevels[] = {1, 1.25, 1.5, 2, 2.5, 3, 4};
static const CGFloat kZoomMax = 4;
// Zoomed in, the sharp render covers what's in view plus this fraction of it past each edge.
static const CGFloat kDetailMargin = 0.1;
static bool SameZoom(CGFloat a, CGFloat b) { return fabs(a - b) < 1e-4; }

// The Mistral API key lives in the login keychain as a generic password.
static NSDictionary *KeyQuery()
{
	return @{(id)kSecClass : (id)kSecClassGenericPassword, (id)kSecAttrService : @"LeanPDF Mistral API Key",
	         (id)kSecAttrAccount : @"mistral"};
}

static NSString *LoadAPIKey()
{
	NSMutableDictionary *q = [KeyQuery() mutableCopy];
	q[(id)kSecReturnData] = @YES;
	q[(id)kSecMatchLimit] = (id)kSecMatchLimitOne;
	CFTypeRef data = NULL;
	if (SecItemCopyMatching((CFDictionaryRef)q, &data) != errSecSuccess) return nil;
	NSString *key = [[NSString alloc] initWithData:(__bridge_transfer NSData *)data encoding:NSUTF8StringEncoding];
	return key.length ? key : nil;
}

// An empty key removes the item.
static void SaveAPIKey(NSString *key)
{
	key = [key stringByTrimmingCharactersInSet:NSCharacterSet.whitespaceAndNewlineCharacterSet];
	if ([key isEqualToString:LoadAPIKey() ?: @""]) return;
	SecItemDelete((CFDictionaryRef)KeyQuery());
	if (!key.length) return;
	NSMutableDictionary *q = [KeyQuery() mutableCopy];
	q[(id)kSecValueData] = [key dataUsingEncoding:NSUTF8StringEncoding];
	SecItemAdd((CFDictionaryRef)q, NULL);
}

// --- thumbnails on disk -------------------------------------------------------
// Rendering a thumbnail costs nearly as much as rendering the page, while a saved JPEG (~30 KB)
// loads in about a millisecond. Each document gets a folder in ~/Library/Caches named after its
// path, size and modification date, so an edited file gets fresh thumbnails.

static const unsigned long long kThumbDiskLimit = 500ull << 20;

static NSString *ThumbCacheRoot()
{
	NSURL *caches = [NSFileManager.defaultManager URLsForDirectory:NSCachesDirectory inDomains:NSUserDomainMask].firstObject;
	return [caches.path stringByAppendingPathComponent:@"LeanPDF/Thumbnails"];
}

// Creates the document's folder and marks it as just used. Returns nil if that fails.
static NSString *ThumbDirFor(NSString *path)
{
	NSFileManager *fm = NSFileManager.defaultManager;
	NSDictionary *a = [fm attributesOfItemAtPath:path error:nil];
	if (!a) return nil;
	NSString *key = [NSString stringWithFormat:@"%@|%llu|%.0f", path, a.fileSize, a.fileModificationDate.timeIntervalSince1970];
	NSData *bytes = [key dataUsingEncoding:NSUTF8StringEncoding];
	unsigned char h[CC_SHA256_DIGEST_LENGTH];
	CC_SHA256(bytes.bytes, (CC_LONG)bytes.length, h);
	NSMutableString *name = [NSMutableString string];
	for (int i = 0; i < 16; i++) [name appendFormat:@"%02x", h[i]];
	NSString *dir = [ThumbCacheRoot() stringByAppendingPathComponent:name];
	if (![fm createDirectoryAtPath:dir withIntermediateDirectories:YES attributes:nil error:nil]) return nil;
	[fm setAttributes:@{NSFileModificationDate : NSDate.date} ofItemAtPath:dir error:nil];
	return dir;
}

static CGImageRef LoadThumbFile(NSString *file) // +1 or NULL
{
	CGImageSourceRef src = CGImageSourceCreateWithURL((__bridge CFURLRef)[NSURL fileURLWithPath:file], NULL);
	if (!src) return NULL;
	CGImageRef img = CGImageSourceGetCount(src) ? CGImageSourceCreateImageAtIndex(src, 0,
		(__bridge CFDictionaryRef)@{(id)kCGImageSourceShouldCacheImmediately : @YES}) : NULL;
	CFRelease(src);
	return img;
}

static void SaveThumbFile(CGImageRef img, NSString *file)
{
	NSMutableData *d = [NSMutableData data];
	CGImageDestinationRef dst = CGImageDestinationCreateWithData((__bridge CFMutableDataRef)d, CFSTR("public.jpeg"), 1, NULL);
	if (!dst) return;
	CGImageDestinationAddImage(dst, img, (__bridge CFDictionaryRef)@{(id)kCGImageDestinationLossyCompressionQuality : @0.85});
	if (CGImageDestinationFinalize(dst)) [d writeToFile:file atomically:YES];
	CFRelease(dst);
}

// Keeps the cache under kThumbDiskLimit by deleting the least recently opened documents' folders.
static void PruneThumbCache()
{
	NSFileManager *fm = NSFileManager.defaultManager;
	NSURL *root = [NSURL fileURLWithPath:ThumbCacheRoot()];
	NSMutableArray *dirs = [NSMutableArray array];
	unsigned long long total = 0;
	for (NSURL *d in [fm contentsOfDirectoryAtURL:root includingPropertiesForKeys:@[ NSURLContentModificationDateKey ] options:0 error:nil]) {
		unsigned long long size = 0;
		for (NSURL *f in [fm contentsOfDirectoryAtURL:d includingPropertiesForKeys:@[ NSURLTotalFileAllocatedSizeKey ] options:0 error:nil]) {
			NSNumber *n = nil;
			[f getResourceValue:&n forKey:NSURLTotalFileAllocatedSizeKey error:nil];
			size += n.unsignedLongLongValue;
		}
		NSDate *date = nil;
		[d getResourceValue:&date forKey:NSURLContentModificationDateKey error:nil];
		[dirs addObject:@{@"url" : d, @"size" : @(size), @"date" : date ?: NSDate.distantPast}];
		total += size;
	}
	[dirs sortUsingDescriptors:@[ [NSSortDescriptor sortDescriptorWithKey:@"date" ascending:YES] ]];
	for (NSDictionary *d in dirs) {
		if (total <= kThumbDiskLimit) break;
		[fm removeItemAtURL:d[@"url"] error:nil];
		total -= [d[@"size"] unsignedLongLongValue];
	}
}

static NSImage *ThumbImage(CGImageRef img, CGFloat scale)
{
	return [[NSImage alloc] initWithCGImage:img size:NSMakeSize(CGImageGetWidth(img) / scale, CGImageGetHeight(img) / scale)];
}

// --- fast path for scanned pages --------------------------------------------
// A scanned book is usually one full-page image per page. MuPDF's renderer spends about half its
// time on such a page resampling the image, so for these pages we decode the image with MuPDF and
// scale it with vImage instead, which is several times faster. A grayscale scan also stays
// grayscale: a third of the memory of RGB. Pages with anything else on them take the normal path.

static bool g_fast_scans = true;

// A device that records a page's drawing and gives up at the first thing that isn't one image.
struct ScanProbe {
	fz_device super;
	fz_image *image;
	fz_matrix ctm;
	bool not_scan;
};

// Throwing stops the interpreter early, but some of its operators (drawing an image, for one)
// catch and swallow errors, so the flag is what decides.
static void ProbeGiveUp(fz_context *ctx, fz_device *dev)
{
	((ScanProbe *)dev)->not_scan = true;
	fz_throw(ctx, FZ_ERROR_ABORT, "not a scan");
}

static void ProbeFillImage(fz_context *ctx, fz_device *dev, fz_image *img, fz_matrix ctm, float alpha, fz_color_params)
{
	ScanProbe *p = (ScanProbe *)dev;
	if (p->image || alpha < 1) ProbeGiveUp(ctx, dev);
	p->image = fz_keep_image(ctx, img);
	p->ctm = ctm;
}

static fz_device *NewScanProbe(fz_context *ctx)
{
	ScanProbe *p = fz_new_derived_device(ctx, ScanProbe);
	fz_device *d = &p->super;
	d->drop_device = [](fz_context *ctx, fz_device *d) { fz_drop_image(ctx, ((ScanProbe *)d)->image); };
	d->fill_image = ProbeFillImage;
	// Everything that draws, clips or composites. Invisible (OCR) text, layers and structure
	// tags don't change the pixels, so those callbacks stay unset and are ignored.
	d->fill_path = [](fz_context *c, fz_device *d, const fz_path *, int, fz_matrix, fz_colorspace *, const float *, float, fz_color_params) { ProbeGiveUp(c, d); };
	d->stroke_path = [](fz_context *c, fz_device *d, const fz_path *, const fz_stroke_state *, fz_matrix, fz_colorspace *, const float *, float, fz_color_params) { ProbeGiveUp(c, d); };
	d->clip_path = [](fz_context *c, fz_device *d, const fz_path *, int, fz_matrix, fz_rect) { ProbeGiveUp(c, d); };
	d->clip_stroke_path = [](fz_context *c, fz_device *d, const fz_path *, const fz_stroke_state *, fz_matrix, fz_rect) { ProbeGiveUp(c, d); };
	d->fill_text = [](fz_context *c, fz_device *d, const fz_text *, fz_matrix, fz_colorspace *, const float *, float, fz_color_params) { ProbeGiveUp(c, d); };
	d->stroke_text = [](fz_context *c, fz_device *d, const fz_text *, const fz_stroke_state *, fz_matrix, fz_colorspace *, const float *, float, fz_color_params) { ProbeGiveUp(c, d); };
	d->clip_text = [](fz_context *c, fz_device *d, const fz_text *, fz_matrix, fz_rect) { ProbeGiveUp(c, d); };
	d->clip_stroke_text = [](fz_context *c, fz_device *d, const fz_text *, const fz_stroke_state *, fz_matrix, fz_rect) { ProbeGiveUp(c, d); };
	d->fill_shade = [](fz_context *c, fz_device *d, fz_shade *, fz_matrix, float, fz_color_params) { ProbeGiveUp(c, d); };
	d->fill_image_mask = [](fz_context *c, fz_device *d, fz_image *, fz_matrix, fz_colorspace *, const float *, float, fz_color_params) { ProbeGiveUp(c, d); };
	d->clip_image_mask = [](fz_context *c, fz_device *d, fz_image *, fz_matrix, fz_rect) { ProbeGiveUp(c, d); };
	d->begin_mask = [](fz_context *c, fz_device *d, fz_rect, int, fz_colorspace *, const float *, fz_color_params) { ProbeGiveUp(c, d); };
	d->begin_group = [](fz_context *c, fz_device *d, fz_rect, fz_colorspace *, int, int, int, float) { ProbeGiveUp(c, d); };
	d->begin_tile = [](fz_context *c, fz_device *d, fz_rect, fz_rect, float, float, fz_matrix, int, int) -> int { ProbeGiveUp(c, d); return 0; };
	return d;
}

static void FreeBuffer(void *, const void *data, size_t) { free((void *)data); }

// If the page is a single upright image covering it, returns that image scaled for ctm. Otherwise
// returns NULL and the caller renders normally. With region NULL the result covers the bbox the
// normal renderer would produce. Otherwise it covers region, a part of that bbox, scaled with the
// higher-quality Lanczos5: the crop is snapped to whole source pixels, so it may reach a little past
// region, and *placed says exactly where it lands in device pixels.
static CGImageRef RenderScan(fz_context *ctx, fz_page *page, fz_matrix ctm, const fz_irect *region = NULL,
                             fz_rect *placed = NULL)
{
	fz_device *dev = NULL;
	fz_image *image = NULL;
	fz_pixmap *pix = NULL;
	CGImageRef img = NULL;
	fz_var(dev);
	fz_var(image);
	fz_var(pix);
	fz_try(ctx) {
		dev = NewScanProbe(ctx);
		fz_run_page(ctx, page, dev, ctm, NULL);
		fz_close_device(ctx, dev);
		ScanProbe *p = (ScanProbe *)dev;
		image = p->image && !p->not_scan ? fz_keep_image(ctx, p->image) : NULL;
		fz_matrix m = p->ctm;
		if (!image || image->imagemask || image->mask || image->use_colorkey || image->orientation > 1)
			break;
		// Plain DeviceGray/RGB, or gray/RGB with an embedded ICC profile that Core Graphics applies.
		fz_colorspace *cs = image->colorspace;
		if (!cs || !(fz_colorspace_is_gray(ctx, cs) || fz_colorspace_is_rgb(ctx, cs)))
			break;
		bool device = fz_colorspace_is_device(ctx, cs);
		if (!device && !(fz_colorspace_is_icc(ctx, cs) && cs->u.icc.buffer))
			break;

		// Upright (no rotation or flip) and covering the page to within a pixel.
		fz_rect page_r = fz_transform_rect(fz_bound_page(ctx, page), ctm);
		fz_irect bbox = fz_round_rect(page_r);
		fz_rect img_r = fz_transform_rect(fz_unit_rect, m);
		if (fabsf(m.b) > 1e-3f * m.a || fabsf(m.c) > 1e-3f * m.d || m.a <= 0 || m.d <= 0)
			break;
		if (fabsf(img_r.x0 - page_r.x0) > 1 || fabsf(img_r.y0 - page_r.y0) > 1 ||
		    fabsf(img_r.x1 - page_r.x1) > 1 || fabsf(img_r.y1 - page_r.y1) > 1)
			break;

		// Decodes at a reduced size when the target is much smaller (thumbnails).
		pix = fz_get_pixmap_from_image(ctx, image, NULL, &m, NULL, NULL);
		int n = fz_pixmap_components(ctx, pix);
		if (fz_pixmap_alpha(ctx, pix) || (n != 1 && n != 3))
			break;

		vImage_Buffer src = {fz_pixmap_samples(ctx, pix), (vImagePixelCount)fz_pixmap_height(ctx, pix),
		                     (vImagePixelCount)fz_pixmap_width(ctx, pix), (size_t)fz_pixmap_stride(ctx, pix)};
		fz_rect out = fz_rect_from_irect(bbox);
		vImage_Flags quality = kvImageNoFlags;
		if (region) {
			// Source pixels per device pixel, and the whole source pixels the region needs.
			float kx = src.width / (img_r.x1 - img_r.x0), ky = src.height / (img_r.y1 - img_r.y0);
			int sx0 = MAX(0, (int)floorf((region->x0 - img_r.x0) * kx));
			int sy0 = MAX(0, (int)floorf((region->y0 - img_r.y0) * ky));
			int sx1 = MIN((int)src.width, (int)ceilf((region->x1 - img_r.x0) * kx));
			int sy1 = MIN((int)src.height, (int)ceilf((region->y1 - img_r.y0) * ky));
			if (sx1 <= sx0 || sy1 <= sy0)
				break;
			src.data = (uint8_t *)src.data + sy0 * src.rowBytes + sx0 * n;
			src.width = sx1 - sx0;
			src.height = sy1 - sy0;
			out = {img_r.x0 + sx0 / kx, img_r.y0 + sy0 / ky, img_r.x0 + sx1 / kx, img_r.y0 + sy1 / ky};
			quality = kvImageHighQualityResampling;
		}
		int ow = (int)lroundf(out.x1 - out.x0), oh = (int)lroundf(out.y1 - out.y0);
		if (ow <= 0 || oh <= 0)
			break;
		// Land on whole pixels (a shift of under half a pixel) so it's shown without resampling.
		out.x0 = roundf(out.x0);
		out.y0 = roundf(out.y0);
		out.x1 = out.x0 + ow;
		out.y1 = out.y0 + oh;
		vImage_Buffer dst = {malloc((size_t)ow * oh * n), (vImagePixelCount)oh, (vImagePixelCount)ow, (size_t)ow * n};
		if (!dst.data)
			fz_throw(ctx, FZ_ERROR_SYSTEM, "out of memory");
		vImage_Error err;
		if (n == 1) {
			err = vImageScale_Planar8(&src, &dst, NULL, quality);
		} else {
			// vImage has no 3-channel scaler: widen to XRGB, scale, then pack back to RGB.
			vImage_Buffer wide = {malloc(src.width * src.height * 4), src.height, src.width, src.width * 4};
			vImage_Buffer scaled = {malloc((size_t)ow * oh * 4), (vImagePixelCount)oh, (vImagePixelCount)ow, (size_t)ow * 4};
			err = wide.data && scaled.data ? kvImageNoError : kvImageMemoryAllocationError;
			if (err == kvImageNoError) err = vImageConvert_RGB888toARGB8888(&src, NULL, 255, &wide, false, kvImageNoFlags);
			if (err == kvImageNoError) err = vImageScale_ARGB8888(&wide, &scaled, NULL, quality);
			if (err == kvImageNoError) err = vImageConvert_ARGB8888toRGB888(&scaled, &dst, kvImageNoFlags);
			free(wide.data);
			free(scaled.data);
		}
		if (err != kvImageNoError) {
			free(dst.data);
			break;
		}

		CGDataProviderRef prov = CGDataProviderCreateWithData(NULL, dst.data, dst.rowBytes * oh, FreeBuffer);
		CGColorSpaceRef cgcs = NULL;
		if (!device) {
			unsigned char *icc;
			size_t len = fz_buffer_storage(ctx, cs->u.icc.buffer, &icc);
			CFDataRef data = CFDataCreate(NULL, icc, len);
			cgcs = CGColorSpaceCreateWithICCData(data);
			CFRelease(data);
		}
		if (!cgcs) // DeviceGray/RGB, or a profile Core Graphics can't read: same as MuPDF's defaults
			cgcs = CGColorSpaceCreateWithName(n == 1 ? kCGColorSpaceExtendedGray : kCGColorSpaceSRGB);
		img = CGImageCreate(ow, oh, 8, n * 8, dst.rowBytes, cgcs, kCGImageAlphaNone, prov, NULL, true, kCGRenderingIntentDefault);
		CGColorSpaceRelease(cgcs);
		CGDataProviderRelease(prov);
		if (placed) *placed = out;
	}
	fz_always(ctx) {
		fz_drop_pixmap(ctx, pix);
		fz_drop_image(ctx, image);
		fz_drop_device(ctx, dev);
	}
	fz_catch(ctx) {
		// Not a scan, or something went wrong; the normal renderer reports any real error.
		fz_ignore_error(ctx);
	}
	return img;
}

// img as a GPU surface: opaque BGRA in the display's colour space. Core Animation shows that as it
// is. A CGImage it would copy, and convert unless it already matched the display, on the main thread
// when it goes on screen, which drops frames. Returns +1 or NULL.
static IOSurfaceRef SurfaceFromImage(CGImageRef img, CGColorSpaceRef display)
{
	if (!img) return NULL;
	size_t w = CGImageGetWidth(img), h = CGImageGetHeight(img);
	NSDictionary *props = @{
		(id)kIOSurfaceWidth : @(w),
		(id)kIOSurfaceHeight : @(h),
		(id)kIOSurfaceBytesPerElement : @4,
		(id)kIOSurfaceBytesPerRow : @(IOSurfaceAlignProperty(kIOSurfaceBytesPerRow, w * 4)),
		(id)kIOSurfacePixelFormat : @((uint32_t)'BGRA'),
	};
	IOSurfaceRef surf = IOSurfaceCreate((__bridge CFDictionaryRef)props);
	if (!surf) return NULL;
	CGColorSpaceRef cs = display ? CGColorSpaceRetain(display) : CGColorSpaceCreateWithName(kCGColorSpaceSRGB);
	IOSurfaceLock(surf, 0, NULL);
	CGContextRef c = CGBitmapContextCreate(IOSurfaceGetBaseAddress(surf), w, h, 8, IOSurfaceGetBytesPerRow(surf), cs,
	                                       kCGImageAlphaNoneSkipFirst | kCGBitmapByteOrder32Little);
	if (c) {
		CGContextSetInterpolationQuality(c, kCGInterpolationNone);
		CGContextDrawImage(c, CGRectMake(0, 0, w, h), img);
		CGContextRelease(c);
	}
	IOSurfaceUnlock(surf, 0, NULL);
	CFPropertyListRef pl = CGColorSpaceCopyPropertyList(cs);
	if (pl) {
		IOSurfaceSetValue(surf, kIOSurfaceColorSpace, pl);
		CFRelease(pl);
	}
	CGColorSpaceRelease(cs);
	if (!c) {
		CFRelease(surf);
		return NULL;
	}
	return surf;
}

// Draws page into buf, the pixel box r with rows of (r width × components) bytes, which the caller
// has filled with the background. A big box is split into strips of kStripRows that GCD draws in
// parallel on up to `cores` threads, each strip with its own clone of ctx (MuPDF needs
// one context per thread) from a display list recorded once. Small boxes, like thumbnails, are
// drawn directly: splitting them costs more than it saves.
static const int kStripRows = 256;
static const long kParallelMinPixels = 1 << 20;

// How many threads draw strips at once. A page flip uses every core. Zoomed-in renders, which
// arrive while the user pans, use a quarter of them: drawing on every core then competes with the
// system compositing the scroll and costs dropped frames (measured: ~1 per 10 s pan at a quarter,
// ~6 with all cores, ~5 with one).
static int AllCores() { return MAX(1, (int)NSProcessInfo.processInfo.activeProcessorCount); }
static int PanCores() { return MAX(1, AllCores() / 4); }

static void DrawPage(fz_context *ctx, fz_page *page, fz_matrix ctm, fz_irect r, fz_colorspace *cs, int alpha,
                     unsigned char *buf, int cores)
{
	int w = r.x1 - r.x0, h = r.y1 - r.y0;
	size_t stride = (size_t)w * (fz_colorspace_n(ctx, cs) + alpha);
	fz_pixmap *pix = NULL;
	fz_device *dev = NULL;
	fz_display_list *list = NULL;
	fz_var(pix);
	fz_var(dev);
	fz_var(list);
	if ((long)w * h < kParallelMinPixels) {
		fz_try(ctx) {
			pix = fz_new_pixmap_with_bbox_and_data(ctx, cs, r, NULL, alpha, buf);
			dev = fz_new_draw_device(ctx, fz_identity, pix);
			fz_run_page(ctx, page, dev, ctm, NULL);
			fz_close_device(ctx, dev);
		}
		fz_always(ctx) {
			fz_drop_device(ctx, dev);
			fz_drop_pixmap(ctx, pix);
		}
		fz_catch(ctx) fz_rethrow(ctx);
		return;
	}

	list = fz_new_display_list_from_page(ctx, page);
	int strips = (h + kStripRows - 1) / kStripRows;
	int lanes = MIN(strips, cores);
	std::vector<fz_context *> ctxs(lanes);
	for (auto &c : ctxs) c = fz_clone_context(ctx);
	fz_context **cp = ctxs.data();
	__block bool failed = false;
	std::atomic<int> nextStrip{0};
	std::atomic<int> *next = &nextStrip;
	dispatch_apply(lanes, dispatch_get_global_queue(qos_class_self(), 0), ^(size_t lane) {
		fz_context *c = cp[lane];
		if (!c) {
			failed = true;
			return;
		}
		for (int i; (i = next->fetch_add(1)) < strips;) {
			int y0 = r.y0 + i * kStripRows, y1 = MIN(r.y1, y0 + kStripRows);
			fz_irect sr = fz_make_irect(r.x0, y0, r.x1, y1);
			fz_pixmap *spix = NULL;
			fz_device *sdev = NULL;
			fz_var(spix);
			fz_var(sdev);
			fz_try(c) {
				spix = fz_new_pixmap_with_bbox_and_data(c, cs, sr, NULL, alpha, buf + (size_t)(y0 - r.y0) * stride);
				sdev = fz_new_draw_device(c, fz_identity, spix);
				fz_run_display_list(c, list, sdev, ctm, fz_rect_from_irect(sr), NULL);
				fz_close_device(c, sdev);
			}
			fz_always(c) {
				fz_drop_device(c, sdev);
				fz_drop_pixmap(c, spix);
			}
			fz_catch(c) {
				fz_report_error(c);
				failed = true;
			}
		}
	});
	for (fz_context *c : ctxs) fz_drop_context(c);
	fz_drop_display_list(ctx, list);
	if (failed) fz_throw(ctx, FZ_ERROR_GENERIC, "page could not be drawn");
}

// Renders page n to fit inside w x h pixels. Caller holds g_doc_lock. Returns +1 or NULL.
static CGImageRef RenderPage(fz_context *ctx, fz_document *doc, int n, int w, int h)
{
	fz_page *page = NULL;
	unsigned char *buf = NULL;
	CGImageRef img = NULL;
	fz_var(page);
	fz_var(buf);
	fz_try(ctx) {
		page = fz_load_page(ctx, doc, n);
		fz_rect b = fz_bound_page(ctx, page);
		float s = fminf(w / fmaxf(b.x1 - b.x0, 1), h / fmaxf(b.y1 - b.y0, 1));
		if (g_fast_scans && (img = RenderScan(ctx, page, fz_scale(s, s))))
			break;
		// RGB on white, like fz_new_pixmap_from_page, drawn on all cores.
		fz_irect r = fz_round_rect(fz_transform_rect(b, fz_scale(s, s)));
		int pw = r.x1 - r.x0, ph = r.y1 - r.y0;
		size_t stride = (size_t)pw * 3;
		if (pw <= 0 || ph <= 0) break;
		buf = (unsigned char *)malloc(stride * ph);
		if (!buf) fz_throw(ctx, FZ_ERROR_SYSTEM, "out of memory");
		memset(buf, 255, stride * ph);
		DrawPage(ctx, page, fz_scale(s, s), r, fz_device_rgb(ctx), 0, buf, AllCores());
		CGDataProviderRef prov = CGDataProviderCreateWithData(NULL, buf, stride * ph, FreeBuffer);
		buf = NULL; // the image owns it now
		CGColorSpaceRef cs = CGColorSpaceCreateWithName(kCGColorSpaceSRGB);
		img = CGImageCreate(pw, ph, 8, 24, stride, cs, kCGImageAlphaNone, prov, NULL, true, kCGRenderingIntentDefault);
		CGColorSpaceRelease(cs);
		CGDataProviderRelease(prov);
	}
	fz_always(ctx) {
		free(buf);
		fz_drop_page(ctx, page);
	}
	fz_catch(ctx) {
		fz_report_error(ctx);
	}
	return img;
}

// Renders part of page n at zoom times the size RenderPage(w, h) gives it. Lengths are in points
// of that 100% page, of which there are scale pixels each. With top, the part is a vis-sized view
// scrolled to the top of the page and centred across it (where a page opens when zoomed), plus
// kDetailMargin; otherwise it is *region. On return *region is the part rendered, *placed where the
// image lands (it may reach a little past *region) and *size the 100% page's size. Caller holds
// g_doc_lock. Returns +1 or NULL.
static CGImageRef RenderDetail(fz_context *ctx, fz_document *doc, int n, int w, int h, CGFloat zoom, CGFloat scale,
                               bool top, NSSize vis, NSRect *region, NSRect *placed, NSSize *size)
{
	fz_page *page = NULL;
	CGImageRef img = NULL;
	fz_var(page);
	fz_try(ctx) {
		page = fz_load_page(ctx, doc, n);
		fz_rect b = fz_bound_page(ctx, page);
		float s0 = fminf(w / fmaxf(b.x1 - b.x0, 1), h / fmaxf(b.y1 - b.y0, 1));
		fz_irect fit = fz_round_rect(fz_transform_rect(b, fz_scale(s0, s0)));
		*size = NSMakeSize((fit.x1 - fit.x0) / scale, (fit.y1 - fit.y0) / scale);
		NSRect whole = {NSZeroPoint, *size};
		if (top) {
			NSRect v = NSMakeRect((size->width - vis.width) / 2, -kPageMargin, vis.width, vis.height);
			*region = NSInsetRect(v, -vis.width * kDetailMargin, -vis.height * kDetailMargin);
		}
		*region = NSIntersectionRect(*region, whole);
		if (NSIsEmptyRect(*region))
			break;

		float s = s0 * zoom;   // device pixels per PDF point
		CGFloat k = zoom * scale; // device pixels per page point
		fz_matrix ctm = fz_scale(s, s);
		fz_irect full = fz_round_rect(fz_transform_rect(b, ctm));
		fz_irect r = fz_intersect_irect(fz_make_irect(full.x0 + (int)floor(NSMinX(*region) * k), full.y0 + (int)floor(NSMinY(*region) * k),
		                                              full.x0 + (int)ceil(NSMaxX(*region) * k), full.y0 + (int)ceil(NSMaxY(*region) * k)),
		                                full);
		if (fz_is_empty_irect(r))
			break;
		fz_rect out = fz_rect_from_irect(r);
		if (!(g_fast_scans && (img = RenderScan(ctx, page, ctm, &r, &out)))) {
			// Straight into opaque BGRA, the layout Core Animation uses, so it's shown without conversion.
			int pw = r.x1 - r.x0, ph = r.y1 - r.y0;
			size_t stride = (size_t)pw * 4;
			unsigned char *buf = (unsigned char *)malloc(stride * ph);
			if (!buf) fz_throw(ctx, FZ_ERROR_SYSTEM, "out of memory");
			memset(buf, 255, stride * ph);
			fz_try(ctx) DrawPage(ctx, page, ctm, r, fz_device_bgr(ctx), 1, buf, PanCores());
			fz_catch(ctx) {
				free(buf);
				fz_rethrow(ctx);
			}
			CGDataProviderRef prov = CGDataProviderCreateWithData(NULL, buf, stride * ph, FreeBuffer);
			CGColorSpaceRef cs = CGColorSpaceCreateWithName(kCGColorSpaceSRGB);
			img = CGImageCreate(pw, ph, 8, 32, stride, cs, kCGImageAlphaNoneSkipFirst | kCGBitmapByteOrder32Little,
			                    prov, NULL, true, kCGRenderingIntentDefault);
			CGColorSpaceRelease(cs);
			CGDataProviderRelease(prov);
		}
		*placed = NSMakeRect((out.x0 - full.x0) / k, (out.y0 - full.y0) / k, (out.x1 - out.x0) / k, (out.y1 - out.y0) / k);
	}
	fz_always(ctx) {
		fz_drop_page(ctx, page);
	}
	fz_catch(ctx) {
		fz_report_error(ctx);
	}
	return img;
}

// "3–5, 9" style summary of a page set (1-based).
static NSString *RangeString(NSIndexSet *set)
{
	NSMutableArray *parts = [NSMutableArray array];
	[set enumerateRangesUsingBlock:^(NSRange r, BOOL *) {
		if (r.length == 1) [parts addObject:[NSString stringWithFormat:@"%lu", r.location + 1]];
		else [parts addObject:[NSString stringWithFormat:@"%lu–%lu", r.location + 1, NSMaxRange(r)]];
	}];
	return [parts componentsJoinedByString:@", "];
}

// ---------------------------------------------------------------------------

@interface TocItem : NSObject
@property (copy) NSString *title;
@property int page;
@property (strong) NSArray<TocItem *> *kids;
@end
@implementation TocItem
@end

static NSArray<TocItem *> *BuildToc(fz_context *ctx, fz_document *doc, fz_outline *o)
{
	NSMutableArray *a = [NSMutableArray array];
	for (; o; o = o->next) {
		TocItem *t = [TocItem new];
		NSString *title = (o->title ? [NSString stringWithUTF8String:o->title] : nil) ?: @"";
		t.title = [[title componentsSeparatedByCharactersInSet:NSCharacterSet.newlineCharacterSet] componentsJoinedByString:@" "];
		t.page = fz_page_number_from_location(ctx, doc, o->page);
		t.kids = o->down ? BuildToc(ctx, doc, o->down) : nil;
		[a addObject:t];
	}
	return a;
}

// ---------------------------------------------------------------------------

@class Viewer;

enum JobKind { kJobThumb, kJobPrefetch, kJobDetail };

@interface Job : NSObject {
@public
	__weak Viewer *viewer;
	int page, kind, w, h;
	bool force;          // thumbnail: render even if scrolled out of the sidebar
	bool top;            // detail: for a neighbouring page, kept only if it has none at this zoom
	CGFloat zoom, scale; // detail
	NSRect region;       // detail: page points
	unsigned gen;        // detail: skipped once stale
	id space;            // detail: the display's CGColorSpace, which the result is converted to
}
@end
@implementation Job
@end

static NSMutableArray<Job *> *g_jobs;
static dispatch_semaphore_t g_jobSem;

static Job *NewJob(Viewer *v, int page, int kind, int w, int h)
{
	Job *j = [Job new];
	j->viewer = v;
	j->page = page;
	j->kind = kind;
	j->w = w;
	j->h = h;
	return j;
}

static void Push(Job *j)
{
	@synchronized(g_jobs) { [g_jobs addObject:j]; }
	dispatch_semaphore_signal(g_jobSem);
}

static void Enqueue(Viewer *v, int page, int kind, int w, int h) { Push(NewJob(v, page, kind, w, h)); }

// ---------------------------------------------------------------------------
// OCR status: a panel at the bottom of the sidebar with a title, a progress bar that turns red on
// failure, and a button that cancels the run or dismisses the result.

@interface OCRBar : NSView
@property (nonatomic) double fraction;
@property (nonatomic) BOOL failed;
@end

@implementation OCRBar

- (void)setFraction:(double)f { _fraction = f; self.needsDisplay = YES; }
- (void)setFailed:(BOOL)f { _failed = f; self.needsDisplay = YES; }

- (void)drawRect:(NSRect)dirty
{
	NSRect b = self.bounds;
	CGFloat r = b.size.height / 2;
	[[NSColor.labelColor colorWithAlphaComponent:0.12] setFill];
	[[NSBezierPath bezierPathWithRoundedRect:b xRadius:r yRadius:r] fill];
	if (self.fraction <= 0) return;
	NSRect f = b;
	f.size.width = fmax(b.size.height, round(b.size.width * fmin(1, self.fraction)));
	[(self.failed ? NSColor.systemRedColor : NSColor.controlAccentColor) setFill];
	[[NSBezierPath bezierPathWithRoundedRect:f xRadius:r yRadius:r] fill];
}

@end

@interface OCRStatusView : NSView
@property (strong) NSTextField *title, *detail, *countLabel;
@property (strong) OCRBar *bar;
@property (strong) NSButton *close;
@property (strong) NSLayoutConstraint *barBelowTitle, *barBelowDetail;
@end

@implementation OCRStatusView

- (instancetype)initWithFrame:(NSRect)frame
{
	if (!(self = [super initWithFrame:frame])) return nil;
	self.translatesAutoresizingMaskIntoConstraints = NO;
	NSBox *line = [NSBox new];
	line.boxType = NSBoxSeparator;
	self.title = [NSTextField labelWithString:@""];
	self.title.font = [NSFont systemFontOfSize:NSFont.smallSystemFontSize weight:NSFontWeightMedium];
	self.title.lineBreakMode = NSLineBreakByTruncatingTail;
	[self.title setContentCompressionResistancePriority:NSLayoutPriorityDefaultLow
	                                     forOrientation:NSLayoutConstraintOrientationHorizontal];
	self.detail = [NSTextField wrappingLabelWithString:@""];
	self.detail.font = [NSFont systemFontOfSize:NSFont.smallSystemFontSize];
	self.detail.textColor = NSColor.secondaryLabelColor;
	self.detail.hidden = YES;
	self.countLabel = [NSTextField labelWithString:@""];
	self.countLabel.font = [NSFont monospacedDigitSystemFontOfSize:NSFont.smallSystemFontSize weight:NSFontWeightRegular];
	self.countLabel.textColor = NSColor.secondaryLabelColor;
	[self.countLabel setContentCompressionResistancePriority:NSLayoutPriorityRequired
	                                          forOrientation:NSLayoutConstraintOrientationHorizontal];
	self.bar = [OCRBar new];
	self.close = [NSButton buttonWithImage:[NSImage imageWithSystemSymbolName:@"xmark.circle.fill"
	                                                 accessibilityDescription:@"Close"]
	                                target:nil action:nil];
	self.close.bordered = NO;
	self.close.contentTintColor = NSColor.tertiaryLabelColor;
	for (NSView *v in @[ line, self.title, self.detail, self.countLabel, self.bar, self.close ]) {
		v.translatesAutoresizingMaskIntoConstraints = NO;
		[self addSubview:v];
	}
	self.barBelowTitle = [self.bar.topAnchor constraintEqualToAnchor:self.title.bottomAnchor constant:6];
	self.barBelowDetail = [self.bar.topAnchor constraintEqualToAnchor:self.detail.bottomAnchor constant:6];
	[NSLayoutConstraint activateConstraints:@[
		[line.topAnchor constraintEqualToAnchor:self.topAnchor],
		[line.leadingAnchor constraintEqualToAnchor:self.leadingAnchor],
		[line.trailingAnchor constraintEqualToAnchor:self.trailingAnchor],
		[self.title.topAnchor constraintEqualToAnchor:self.topAnchor constant:8],
		[self.title.leadingAnchor constraintEqualToAnchor:self.leadingAnchor constant:12],
		[self.title.trailingAnchor constraintLessThanOrEqualToAnchor:self.close.leadingAnchor constant:-4],
		[self.close.centerYAnchor constraintEqualToAnchor:self.title.centerYAnchor],
		[self.close.trailingAnchor constraintEqualToAnchor:self.trailingAnchor constant:-10],
		[self.detail.topAnchor constraintEqualToAnchor:self.title.bottomAnchor constant:2],
		[self.detail.leadingAnchor constraintEqualToAnchor:self.title.leadingAnchor],
		[self.detail.trailingAnchor constraintEqualToAnchor:self.trailingAnchor constant:-12],
		self.barBelowTitle,
		[self.bar.leadingAnchor constraintEqualToAnchor:self.title.leadingAnchor],
		[self.bar.trailingAnchor constraintEqualToAnchor:self.countLabel.leadingAnchor constant:-8],
		[self.bar.heightAnchor constraintEqualToConstant:4],
		[self.bar.bottomAnchor constraintEqualToAnchor:self.bottomAnchor constant:-12],
		[self.countLabel.centerYAnchor constraintEqualToAnchor:self.bar.centerYAnchor],
		[self.countLabel.trailingAnchor constraintEqualToAnchor:self.trailingAnchor constant:-12],
	]];
	return self;
}

// Lets the error message wrap to the sidebar's width.
- (void)layout
{
	[super layout];
	CGFloat w = self.detail.frame.size.width;
	if (w > 0 && self.detail.preferredMaxLayoutWidth != w) {
		self.detail.preferredMaxLayoutWidth = w;
		self.needsLayout = YES;
	}
}

- (void)setDetailText:(NSString *)d
{
	self.detail.stringValue = d ?: @"";
	self.detail.hidden = d == nil;
	NSLayoutConstraint *on = d ? self.barBelowDetail : self.barBelowTitle, *off = d ? self.barBelowTitle : self.barBelowDetail;
	off.active = NO;
	on.active = YES;
}

- (void)running:(NSString *)title total:(NSUInteger)n
{
	self.title.stringValue = title;
	[self setDetailText:nil];
	self.bar.failed = NO;
	self.close.toolTip = @"Cancel OCR";
	[self progress:0 total:n];
}

- (void)progress:(NSUInteger)done total:(NSUInteger)n
{
	self.bar.fraction = n ? (double)done / n : 0;
	self.countLabel.stringValue = [NSString stringWithFormat:@"%lu/%lu", done, n];
}

- (void)success:(NSString *)title
{
	self.title.stringValue = title;
	self.bar.fraction = 1;
	self.close.toolTip = @"Dismiss";
}

- (void)failure:(NSString *)message
{
	self.title.stringValue = @"OCR failed";
	[self setDetailText:message];
	self.bar.failed = YES;
	self.bar.fraction = 1;
	self.countLabel.stringValue = @"";
	self.close.toolTip = @"Dismiss";
}

@end

// One OCR run: each page goes to Mistral as its own request so the bar can show real progress.
@interface OCRJob : NSObject
@property (strong) NSString *key;
@property (strong) NSArray<NSNumber *> *pages;
@property (strong) NSMutableArray *results; // Markdown per page, NSNull until it arrives
@property (strong) NSMutableSet<NSURLSessionDataTask *> *tasks;
@property NSUInteger next, done, waiting; // waiting: rate-limited pages due to be retried
@end
@implementation OCRJob
@end

// ---------------------------------------------------------------------------

@interface PageView : NSView
@property (nonatomic, weak) Viewer *viewer;
@property (nonatomic) CGFloat zoom; // 1 = fit to window
- (void)dropCache;
- (void)reload; // the page changed, or needs rendering again
- (void)detailReady:(int)n;
- (void)thumbReady:(int)n;
- (void)mapMovedTo:(NSPoint)unit;
@end

// A sharp render of part of a page at some zoom (see RenderDetail).
struct PageDetail { int w, h; CGFloat zoom; NSRect region, placed; NSSize size; id surf; int pw, ph; }; // surf: IOSurface

@interface Viewer : NSObject <NSWindowDelegate, NSTableViewDataSource, NSTableViewDelegate,
                              NSOutlineViewDataSource, NSOutlineViewDelegate, NSMenuItemValidation,
                              NSToolbarDelegate> {
@public
	fz_document *doc; // guarded by g_doc_lock; NULL once closed
	pdf_document *pdf;
	int count;
	std::atomic<int> current, visLo, visHi;
	int selAnchor; // fixed end of the Shift range in progress (current is the moving end), or -1
	struct Cached { int w, h; CGImageRef img; };
	std::map<int, Cached> pageCache; // guarded by g_doc_lock
	std::atomic<bool> dormant;       // idle in the background: no caches, no prefetch
	// Sharp renders of part of a page when zoomed in, for the current page and its neighbours.
	std::map<int, PageDetail> detailCache; // guarded by g_doc_lock
	std::atomic<unsigned> detailGen;   // bumped when zoom or window size change
	std::atomic<unsigned> detailReq;   // the latest request for the current page
}
@property (strong) NSToolbarItemGroup *zoomItem;
@property (strong) NSTimer *idleTimer;
@property (strong) NSWindow *window;
@property (strong) NSString *path;
@property (strong) PageView *pageView;
@property (strong) NSTableView *thumbs;
@property (strong) NSOutlineView *toc;
@property (strong) NSScrollView *thumbScroll, *tocScroll;
@property (strong) NSSplitViewItem *sideItem;
@property (strong) NSArray<TocItem *> *tocRoots;
@property (strong) NSArray<NSString *> *pageLabels; // the PDF's own page labels, or nil if it has none
@property (strong) NSCache<NSNumber *, NSImage *> *thumbCache;
@property (strong) NSString *thumbDir; // on-disk thumbnails, or nil
@property (strong) NSMutableIndexSet *thumbPending;
@property (strong) PDFDocument *printDoc;
@property (weak) NSTextField *gotoField; // field of the open Go to Page sheet
@property (strong) OCRJob *ocrJob; // the run in progress, or nil
@property (strong) OCRStatusView *ocrStatus;
@property (strong) NSArray<NSLayoutConstraint *> *listsToBottom, *listsToStatus;
@property (strong) NSIndexSet *selBase; // selection from before the Shift range in progress
- (void)goToPage:(int)n;
- (void)extendSelectionTo:(int)r;
- (IBAction)selectAll:(id)s;
- (void)selectCurrent;
- (void)clearSelection;
- (void)thumbClicked:(int)row modifiers:(NSEventModifierFlags)m;
- (CGImageRef)copyImageForPage:(int)n width:(int)w height:(int)h;
- (CGImageRef)copyThumbForPage:(int)n request:(BOOL)request;
- (void)requestDetail:(int)n width:(int)w height:(int)h zoom:(CGFloat)z scale:(CGFloat)s region:(NSRect)r;
- (void)prefetchDetail:(int)n width:(int)w height:(int)h zoom:(CGFloat)z scale:(CGFloat)s region:(NSRect)r;
- (void)dropDetails;
- (void)zoomChanged;
- (IBAction)zoomIn:(id)s;
- (IBAction)zoomOut:(id)s;
- (IBAction)resetZoom:(id)s;
@end

@interface ThumbTable : NSTableView
@property (weak) Viewer *viewer;
@end

// A page thumbnail with rounded corners, as in Preview.
@interface ThumbView : NSView
@property (strong, nonatomic) NSImage *image;
@end

@implementation ThumbView

- (void)setImage:(NSImage *)i
{
	_image = i;
	self.needsDisplay = YES;
	self.superview.needsDisplay = YES; // the cell's highlight hugs the image
}

// Where the image is drawn: fitted and centred in the bounds.
- (NSRect)imageRect
{
	NSRect box = NSInsetRect(self.bounds, kRingPad, kRingPad);
	if (!self.image) return box;
	NSSize s = self.image.size;
	CGFloat k = fmin(1, fmin(box.size.width / fmax(s.width, 1), box.size.height / fmax(s.height, 1)));
	return NSMakeRect(round(NSMidX(box) - s.width * k / 2), round(NSMidY(box) - s.height * k / 2),
	                  round(s.width * k), round(s.height * k));
}

- (void)drawRect:(NSRect)dirty
{
	if (!self.image) return;
	NSRect r = self.imageRect;
	NSBezierPath *clip = [NSBezierPath bezierPathWithRoundedRect:r xRadius:4 yRadius:4];
	[NSGraphicsContext saveGraphicsState];
	[clip addClip];
	[self.image drawInRect:r];
	[NSGraphicsContext restoreGraphicsState];
	[[NSColor.labelColor colorWithAlphaComponent:0.1] setStroke];
	NSBezierPath *edge = [NSBezierPath bezierPathWithRoundedRect:NSInsetRect(r, 0.25, 0.25) xRadius:4 yRadius:4];
	edge.lineWidth = 0.5;
	[edge stroke];
}

@end

// Preview-style highlight: a rounded box behind the page and its label. The viewed page's box is
// the accent colour with a white label; other selected pages get a gray box.
@interface ThumbCell : NSTableCellView
- (void)restyle;
@property (strong) ThumbView *thumb;
@property (nonatomic) BOOL current, selected;
@end

@implementation ThumbCell

- (void)setCurrent:(BOOL)c { if (c != _current) { _current = c; [self restyle]; } }
- (void)setSelected:(BOOL)s { if (s != _selected) { _selected = s; [self restyle]; } }

// A selected row hands its cells the "emphasized" background style, under which labelColor
// itself draws white. This cell draws its own highlight and picks its own label colour (see
// restyle), so it always stays on the normal style.
- (void)setBackgroundStyle:(NSBackgroundStyle)style { [super setBackgroundStyle:NSBackgroundStyleNormal]; }

// The label gets a fixed colour, resolved here for the light or dark appearance. A dynamic colour
// like labelColor is resolved again at draw time against the selection style of the row around
// it, which can still turn it white.
- (void)restyle
{
	NSColor *c = self.current ? NSColor.whiteColor : NSColor.labelColor;
	__block NSColor *fixed = c;
	[self.effectiveAppearance performAsCurrentDrawingAppearance:^{
		fixed = [c colorUsingColorSpace:NSColorSpace.sRGBColorSpace] ?: c;
	}];
	self.textField.textColor = fixed;
	self.needsDisplay = YES;
}

- (void)viewDidChangeEffectiveAppearance
{
	[super viewDidChangeEffectiveAppearance];
	[self restyle];
}

- (void)drawRect:(NSRect)dirty
{
	if (!self.current && !self.selected) return;
	NSRect img = [self convertRect:self.thumb.imageRect fromView:self.thumb];
	NSRect box = NSUnionRect(img, self.textField.frame);
	CGFloat top = kRingPad, bottom = kItemBottomPad; // the cell is flipped inside a table row
	box.origin.x -= kRingPad;
	box.size.width += 2 * kRingPad;
	box.origin.y -= self.isFlipped ? top : bottom;
	box.size.height += top + bottom;
	[(self.current ? NSColor.controlAccentColor : NSColor.unemphasizedSelectedContentBackgroundColor) setFill];
	[[NSBezierPath bezierPathWithRoundedRect:box xRadius:10 yRadius:10] fill];
}

@end

// The cell draws the selection itself (see ThumbCell), so the row draws none.
@interface ThumbRowView : NSTableRowView
@end

@implementation ThumbRowView
- (void)setEmphasized:(BOOL)e { [super setEmphasized:NO]; }
- (void)drawSelectionInRect:(NSRect)r {}
- (void)setSelected:(BOOL)s
{
	[super setSelected:s];
	id cell = self.numberOfColumns ? [self viewAtColumn:0] : nil;
	if ([cell isKindOfClass:ThumbCell.class]) ((ThumbCell *)cell).selected = s;
}
- (void)didAddSubview:(NSView *)v
{
	[super didAddSubview:v];
	if ([v isKindOfClass:ThumbCell.class]) ((ThumbCell *)v).selected = self.selected;
}
@end

// Page keys, identical in the page view and the thumbnail list:
// arrows / Page Up/Down / Home / End move the viewed page,
// Shift+Up/Down move it while extending the selection, Space selects the viewed page, Delete clears the selection.
// + / = zoom in, - zooms out, 0 resets the zoom.
// Returns NO for keys it doesn't handle.
static BOOL HandlePageKey(Viewer *v, NSEvent *e)
{
	if (!v) return NO;
	unichar c = e.charactersIgnoringModifiers.length ? [e.charactersIgnoringModifiers characterAtIndex:0] : 0;
	BOOL shift = (e.modifierFlags & NSEventModifierFlagShift) != 0;
	int n = v->current;
	switch (c) {
	case NSDownArrowFunctionKey: if (shift) [v extendSelectionTo:n + 1]; else [v goToPage:n + 1]; return YES;
	case NSUpArrowFunctionKey: if (shift) [v extendSelectionTo:n - 1]; else [v goToPage:n - 1]; return YES;
	case NSRightArrowFunctionKey: case NSPageDownFunctionKey: [v goToPage:n + 1]; return YES;
	case NSLeftArrowFunctionKey: case NSPageUpFunctionKey: [v goToPage:n - 1]; return YES;
	case NSHomeFunctionKey: [v goToPage:0]; return YES;
	case NSEndFunctionKey: [v goToPage:v->count - 1]; return YES;
	case ' ': [v selectCurrent]; return YES;
	case NSDeleteCharacter: [v clearSelection]; return YES;
	case '+': case '=': [v zoomIn:nil]; return YES;
	case '-': [v zoomOut:nil]; return YES;
	case '0': [v resetZoom:nil]; return YES;
	}
	return NO;
}

static NSMutableSet<Viewer *> *g_viewers;
static void ReleaseMemory();
static void UpdateIdleTimers();
static void OpenURL(NSURL *url);

// ---------------------------------------------------------------------------

// --- zoomable page -----------------------------------------------------------
// PageView holds a scroll view whose document is the page plus a margin. At 100% the page is the
// fitted render from copyImageForPage:, shown 1:1 as a layer's contents. Zooming is the scroll
// view's magnification, so the GPU scales the layers. Once a zoom settles, a sharp render of what's
// in view (the "detail") is laid over the page.

// Keeps the page centred while it's smaller than the clip view, on whole pixels.
@interface CenteringClipView : NSClipView
@end
@implementation CenteringClipView
- (NSRect)constrainBoundsRect:(NSRect)r
{
	r = [super constrainBoundsRect:r];
	NSView *d = self.documentView;
	if (!d) return r;
	NSSize ds = d.frame.size;
	CGFloat s = self.window.backingScaleFactor ?: 2;
	// Centre in the part not under the toolbar or sidebar. Insets are in view points; bounds are
	// in document units, which differ by the zoom.
	NSEdgeInsets in = self.contentInsets;
	CGFloat m = r.size.width > 0 ? self.frame.size.width / r.size.width : 1;
	CGFloat vw = r.size.width - (in.left + in.right) / m, vh = r.size.height - (in.top + in.bottom) / m;
	if (vw > ds.width) r.origin.x = round(((ds.width - vw) / 2 - in.left / m) * s) / s;
	if (vh > ds.height) r.origin.y = round(((ds.height - vh) / 2 - in.top / m) * s) / s;
	return r;
}
@end

// At 100%, trackpad / wheel flips pages; zoomed in, it pans. No double-tap smart zoom.
@interface PageScrollView : NSScrollView
@property (weak) Viewer *viewer;
@end
@implementation PageScrollView {
	CGFloat _scrollAcc;
}
- (void)smartMagnifyWithEvent:(NSEvent *)e {}
- (void)scrollWheel:(NSEvent *)e
{
	if (self.magnification > 1.001) {
		[super scrollWheel:e];
		return;
	}
	// Momentum is ignored so one swipe ≈ one flip.
	if (e.momentumPhase != NSEventPhaseNone) return;
	if (e.phase == NSEventPhaseBegan) _scrollAcc = 0;
	CGFloat d = fabs(e.scrollingDeltaY) >= fabs(e.scrollingDeltaX) ? e.scrollingDeltaY : e.scrollingDeltaX;
	if (!e.hasPreciseScrollingDeltas) d *= 40;
	_scrollAcc += d;
	if (fabs(_scrollAcc) >= 40) {
		[self.viewer goToPage:self.viewer->current + (_scrollAcc < 0 ? 1 : -1)];
		_scrollAcc = 0;
	}
}
@end

// The scroll view's document: the page plus kPageMargin all round. Clicks focus the page view.
@interface DocView : NSView
@end
@implementation DocView
- (BOOL)isFlipped { return YES; }
- (void)mouseDown:(NSEvent *)e { [self.window makeFirstResponder:self.enclosingScrollView.superview]; }
@end

// A view that shows a CGImage as its layer's contents, stretched to its bounds.
@interface ImageLayerView : NSView
@property (nonatomic) CGImageRef image;
@property (nonatomic, strong) id contents; // anything else a layer can show (an IOSurface); wins over image
@end
@implementation ImageLayerView {
	CGImageRef _image;
}
- (instancetype)initWithFrame:(NSRect)f
{
	if ((self = [super initWithFrame:f])) {
		self.wantsLayer = YES;
		self.layerContentsRedrawPolicy = NSViewLayerContentsRedrawOnSetNeedsDisplay;
	}
	return self;
}
- (void)dealloc { CGImageRelease(_image); }
- (BOOL)isFlipped { return YES; }
- (BOOL)wantsUpdateLayer { return YES; }
- (NSView *)hitTest:(NSPoint)p { return nil; }
- (CGImageRef)image { return _image; }
- (void)setImage:(CGImageRef)img
{
	if (img == _image) return;
	CGImageRetain(img);
	CGImageRelease(_image);
	_image = img;
	self.needsDisplay = YES;
}
- (void)setContents:(id)c
{
	if (c == _contents) return;
	_contents = c;
	self.needsDisplay = YES;
}
- (void)updateLayer
{
	CALayer *l = self.layer;
	l.contents = _contents ?: (__bridge id)_image;
	l.magnificationFilter = kCAFilterLinear;
	l.minificationFilter = kCAFilterTrilinear;
}
@end

// The page itself: white, with the soft Preview-style shadow so it stays visible on white.
@interface PageSurface : ImageLayerView
@end
@implementation PageSurface
- (void)setFrameSize:(NSSize)s
{
	[super setFrameSize:s];
	self.needsDisplay = YES;
}
- (void)updateLayer
{
	[super updateLayer];
	CALayer *l = self.layer;
	l.backgroundColor = NSColor.whiteColor.CGColor;
	l.shadowColor = NSColor.blackColor.CGColor;
	l.shadowOpacity = 0.3;
	l.shadowRadius = 3;
	l.shadowOffset = CGSizeMake(0, -1);
	CGPathRef p = CGPathCreateWithRect(l.bounds, NULL);
	l.shadowPath = p;
	CGPathRelease(p);
}
@end

// --- mini-map ----------------------------------------------------------------
// Shown while zoomed in, at the bottom right: the page's thumbnail as a small floating card, the
// part outside the view dimmed, and a pane of clear glass over the part in view. Drag the pane to
// pan, or click elsewhere on the card to jump there.

static const CGFloat kMapW = 120, kMapMaxH = 160, kMapInset = 16, kMapRadius = 8;

@interface MiniMap : NSView
@property (weak) PageView *pageView;
@property (weak) NSScrollView *target; // scrolls and pinches over the map go here
- (void)setImage:(CGImageRef)img;
- (void)setViewport:(NSRect)unit; // the part in view, in fractions of the page (y down)
+ (NSSize)sizeForPage:(NSSize)page;
@end

@interface FlippedView : NSView
@end
@implementation FlippedView
- (BOOL)isFlipped { return YES; }
@end

// Dims the map outside the viewport: four plain strips around the hole, moved by the GPU, never
// redrawn. The hole is square; the lens fills in its rounded corners.
static const CGFloat kMapDimAlpha = 0.22;
@interface MapDim : NSView
@property (nonatomic) NSRect hole;
@end
@implementation MapDim {
	NSView *_strips[4];
}
- (instancetype)initWithFrame:(NSRect)f
{
	if ((self = [super initWithFrame:f])) {
		self.wantsLayer = YES;
		for (int i = 0; i < 4; i++) {
			NSView *v = _strips[i] = [NSView new];
			v.wantsLayer = YES;
			v.layer.backgroundColor = CGColorGetConstantColor(kCGColorBlack);
			v.alphaValue = kMapDimAlpha;
			[self addSubview:v];
		}
	}
	return self;
}
- (BOOL)isFlipped { return YES; }
- (NSView *)hitTest:(NSPoint)p { return nil; }
- (void)setHole:(NSRect)h
{
	_hole = h;
	[self place];
}
- (void)layout
{
	[super layout];
	[self place];
}
- (void)place
{
	NSRect b = self.bounds, h = NSIntersectionRect(_hole, b);
	if (NSIsEmptyRect(h)) h = NSMakeRect(NSMidX(b), NSMidY(b), 0, 0);
	_strips[0].frame = NSMakeRect(0, 0, b.size.width, NSMinY(h));                                    // above
	_strips[1].frame = NSMakeRect(0, NSMaxY(h), b.size.width, b.size.height - NSMaxY(h));            // below
	_strips[2].frame = NSMakeRect(0, NSMinY(h), NSMinX(h), h.size.height);                           // left
	_strips[3].frame = NSMakeRect(NSMaxX(h), NSMinY(h), b.size.width - NSMaxX(h), h.size.height);    // right
}
@end

// A pane of clear glass: no blur or tint, only a bright rim, a faint sheen along its top edge and a
// soft shadow that lifts it off the page. Drawn once into a small image that the GPU stretches to
// any size (only the clear middle stretches), so moving or resizing it costs no drawing.
// The image reaches kLensPad past the pane to leave room for the shadow.
static const CGFloat kLensPad = 4, kLensRadius = 5, kLensCap = kLensPad + 7;
@interface MapLens : NSView
@end
@implementation MapLens {
	CGImageRef _art;
	CGFloat _artScale;
}
- (instancetype)initWithFrame:(NSRect)f
{
	if ((self = [super initWithFrame:f])) {
		self.wantsLayer = YES;
		self.layerContentsRedrawPolicy = NSViewLayerContentsRedrawOnSetNeedsDisplay;
	}
	return self;
}
- (void)dealloc { CGImageRelease(_art); }
- (BOOL)wantsUpdateLayer { return YES; }
- (NSView *)hitTest:(NSPoint)p { return nil; }
- (void)viewDidChangeBackingProperties
{
	[super viewDidChangeBackingProperties];
	self.needsDisplay = YES;
}

// The pane at its smallest: the caps plus one stretchable point.
+ (CGImageRef)newArtAtScale:(CGFloat)scale
{
	CGFloat side = 2 * kLensCap + 1;
	size_t px = (size_t)ceil(side * scale);
	CGColorSpaceRef cs = CGColorSpaceCreateWithName(kCGColorSpaceSRGB);
	CGContextRef c = CGBitmapContextCreate(NULL, px, px, 8, px * 4, cs, kCGImageAlphaPremultipliedFirst | kCGBitmapByteOrder32Little);
	CGColorSpaceRelease(cs);
	CGContextScaleCTM(c, scale, scale);
	NSGraphicsContext *old = NSGraphicsContext.currentContext;
	NSGraphicsContext.currentContext = [NSGraphicsContext graphicsContextWithCGContext:c flipped:NO];

	NSRect bounds = NSMakeRect(0, 0, side, side);
	NSRect r = NSInsetRect(bounds, kLensPad, kLensPad);
	NSBezierPath *pane = [NSBezierPath bezierPathWithRoundedRect:r xRadius:kLensRadius yRadius:kLensRadius];

	// The dimming in the hole's corners, outside the pane's rounded ones.
	[NSGraphicsContext saveGraphicsState];
	NSBezierPath *corners = [NSBezierPath bezierPathWithRect:r];
	[corners appendBezierPath:pane];
	corners.windingRule = NSWindingRuleEvenOdd;
	[[NSColor colorWithWhite:0 alpha:kMapDimAlpha] setFill];
	[corners fill];
	[NSGraphicsContext restoreGraphicsState];

	// Shadow, only outside the pane so the glass stays clear.
	[NSGraphicsContext saveGraphicsState];
	NSBezierPath *outside = [NSBezierPath bezierPathWithRect:bounds];
	[outside appendBezierPath:pane];
	outside.windingRule = NSWindingRuleEvenOdd;
	[outside addClip];
	NSShadow *sh = [NSShadow new];
	sh.shadowColor = [NSColor colorWithWhite:0 alpha:0.35];
	sh.shadowBlurRadius = 3;
	sh.shadowOffset = NSMakeSize(0, -1);
	[sh set];
	[NSColor.blackColor setFill];
	[pane fill];
	[NSGraphicsContext restoreGraphicsState];

	// Sheen: light catching the top edge of the glass (y is up here).
	[NSGraphicsContext saveGraphicsState];
	[pane addClip];
	NSGradient *g = [[NSGradient alloc] initWithColors:@[ [NSColor colorWithWhite:1 alpha:0.32], [NSColor colorWithWhite:1 alpha:0] ]];
	[g drawFromPoint:NSMakePoint(0, NSMaxY(r)) toPoint:NSMakePoint(0, NSMaxY(r) - (kLensCap - kLensPad)) options:0];
	[NSGraphicsContext restoreGraphicsState];

	// Rim: a thin dark edge for contrast on white pages, and a bright edge just inside it.
	pane.lineWidth = 1;
	[[NSColor colorWithWhite:0 alpha:0.30] setStroke];
	[pane stroke];
	NSBezierPath *inner = [NSBezierPath bezierPathWithRoundedRect:NSInsetRect(r, 1, 1) xRadius:kLensRadius - 1 yRadius:kLensRadius - 1];
	inner.lineWidth = 1;
	[[NSColor colorWithWhite:1 alpha:0.85] setStroke];
	[inner stroke];

	NSGraphicsContext.currentContext = old;
	CGImageRef img = CGBitmapContextCreateImage(c);
	CGContextRelease(c);
	return img;
}

- (void)updateLayer
{
	CGFloat scale = self.window.backingScaleFactor ?: 2;
	if (!_art || _artScale != scale) {
		CGImageRelease(_art);
		_art = [MapLens newArtAtScale:scale];
		_artScale = scale;
	}
	CALayer *l = self.layer;
	l.contents = (__bridge id)_art;
	l.contentsScale = scale;
	CGFloat side = 2 * kLensCap + 1;
	l.contentsCenter = CGRectMake(kLensCap / side, kLensCap / side, 1 / side, 1 / side);
}
@end

@implementation MiniMap {
	NSView *_card;          // rounded, clips the thumbnail and dimming
	ImageLayerView *_img;
	MapDim *_dim;
	MapLens *_lens;
	NSRect _unit, _vp;      // viewport in fractions, and in points
	NSPoint _grab;          // where in the pane the drag holds it, from its centre
}

+ (NSSize)sizeForPage:(NSSize)p
{
	if (p.width <= 0 || p.height <= 0) return NSZeroSize;
	CGFloat w = kMapW, h = w * p.height / p.width;
	if (h > kMapMaxH) {
		h = kMapMaxH;
		w = h * p.width / p.height;
	}
	return NSMakeSize(round(w), round(h));
}

- (instancetype)initWithFrame:(NSRect)f
{
	if (!(self = [super initWithFrame:f])) return nil;
	self.wantsLayer = YES;
	self.layerContentsRedrawPolicy = NSViewLayerContentsRedrawOnSetNeedsDisplay;

	_card = [[FlippedView alloc] initWithFrame:self.bounds];
	_card.wantsLayer = YES;
	_card.layer.cornerRadius = kMapRadius;
	if (@available(macOS 10.15, *)) _card.layer.cornerCurve = kCACornerCurveContinuous;
	_card.layer.masksToBounds = YES;
	_card.layer.borderWidth = 0.5;
	_card.layer.backgroundColor = NSColor.whiteColor.CGColor;
	_img = [ImageLayerView new];
	_dim = [MapDim new];
	[_card addSubview:_img];
	[_card addSubview:_dim];
	[self addSubview:_card];
	_lens = [MapLens new];
	[self addSubview:_lens];
	[self updateColors];
	return self;
}

- (BOOL)isFlipped { return YES; }
- (BOOL)wantsUpdateLayer { return YES; }
- (BOOL)acceptsFirstMouse:(NSEvent *)e { return YES; }

- (void)updateLayer
{
	// Floating card shadow.
	CALayer *l = self.layer;
	l.shadowColor = NSColor.blackColor.CGColor;
	l.shadowOpacity = 0.22;
	l.shadowRadius = 10;
	l.shadowOffset = CGSizeMake(0, -3);
	CGPathRef p = CGPathCreateWithRoundedRect(l.bounds, kMapRadius, kMapRadius, NULL);
	l.shadowPath = p;
	CGPathRelease(p);
}

- (void)viewDidChangeEffectiveAppearance
{
	[super viewDidChangeEffectiveAppearance];
	[self updateColors];
}

- (void)updateColors
{
	[self.effectiveAppearance performAsCurrentDrawingAppearance:^{
		self->_card.layer.borderColor = [NSColor.labelColor colorWithAlphaComponent:0.18].CGColor;
	}];
}

- (void)setImage:(CGImageRef)img { _img.image = img; }

- (void)setViewport:(NSRect)unit
{
	if (NSEqualRects(unit, _unit)) return;
	_unit = unit;
	[self place];
}

- (void)layout
{
	[super layout];
	_card.frame = self.bounds;
	_img.frame = _card.bounds;
	_dim.frame = _card.bounds;
	self.needsDisplay = YES;
	[self place];
}

- (void)place
{
	NSSize s = self.bounds.size;
	NSRect vp = NSMakeRect(_unit.origin.x * s.width, _unit.origin.y * s.height, _unit.size.width * s.width,
	                       _unit.size.height * s.height);
	// Never smaller than something you can grab.
	CGFloat minSide = 10;
	if (vp.size.width < minSide) vp = NSInsetRect(vp, (vp.size.width - minSide) / 2, 0);
	if (vp.size.height < minSide) vp = NSInsetRect(vp, 0, (vp.size.height - minSide) / 2);
	_vp = vp;
	_dim.hole = vp;
	_lens.frame = NSInsetRect(vp, -kLensPad, -kLensPad);
	[self.window invalidateCursorRectsForView:self];
}

- (NSView *)hitTest:(NSPoint)p { return [super hitTest:p] ? self : nil; }
- (void)resetCursorRects
{
	if (!NSIsEmptyRect(_vp)) [self addCursorRect:_vp cursor:NSCursor.openHandCursor];
}

- (void)mouseDown:(NSEvent *)e
{
	NSPoint p = [self convertPoint:e.locationInWindow fromView:nil];
	_grab = NSPointInRect(p, _vp) ? NSMakePoint(p.x - NSMidX(_vp), p.y - NSMidY(_vp)) : NSZeroPoint;
	[NSCursor.closedHandCursor push];
	[self moveTo:p];
}
- (void)mouseDragged:(NSEvent *)e { [self moveTo:[self convertPoint:e.locationInWindow fromView:nil]]; }
- (void)mouseUp:(NSEvent *)e { [NSCursor pop]; }

- (void)moveTo:(NSPoint)p
{
	NSSize s = self.bounds.size;
	[self.pageView mapMovedTo:NSMakePoint((p.x - _grab.x) / s.width, (p.y - _grab.y) / s.height)];
}

- (void)scrollWheel:(NSEvent *)e { [self.target scrollWheel:e]; }
- (void)magnifyWithEvent:(NSEvent *)e { [self.target magnifyWithEvent:e]; }
@end

// --- the page view -------------------------------------------------------------

static bool Covers(NSRect outer, NSRect inner) { return NSContainsRect(NSInsetRect(outer, -0.5, -0.5), inner); }

@implementation PageView {
	PageScrollView *_scroll;
	DocView *_doc;
	PageSurface *_surface;
	ImageLayerView *_detail;
	MiniMap *_map;
	CGImageRef _base;   // the fitted page image
	int _basePage;      // its page, or -1 to re-render
	int _bw, _bh;       // the pixel box it was fitted into
	int _shownPage;
	NSSize _page;       // the page at 100%, in points
	// The detail on show: page, zoom and box it was rendered for, what it covers, where it lands.
	bool _dShown;
	int _dPage, _dw, _dh;
	CGFloat _dZoom;
	NSRect _dRegion, _dPlaced;
	NSSize _dSize, _dPx; // _dPx: its size in pixels
	// The detail asked for and not yet arrived.
	bool _pending;
	int _pPage;
	NSRect _pRegion;
	// Zoom and box of the last request: neighbour renders for others are stale.
	CGFloat _kZoom;
	int _kw, _kh, _prefetched; // _prefetched: page whose neighbours were queued for this key
	BOOL _liveMagnify;
	int _mapPage, _mapAsked;
	bool _mapIsThumb;
}

- (BOOL)acceptsFirstResponder { return YES; }
- (BOOL)isOpaque { return YES; }

- (instancetype)initWithFrame:(NSRect)f
{
	if (!(self = [super initWithFrame:f])) return nil;
	[self registerForDraggedTypes:@[ NSPasteboardTypeFileURL ]];
	_basePage = _shownPage = _mapPage = _mapAsked = _prefetched = -1;

	_scroll = [PageScrollView new];
	_scroll.contentView = [CenteringClipView new];
	_scroll.drawsBackground = NO;
	_scroll.hasVerticalScroller = YES;
	_scroll.hasHorizontalScroller = YES;
	_scroll.autohidesScrollers = YES;
	_scroll.automaticallyAdjustsContentInsets = NO;
	_scroll.allowsMagnification = YES;
	_scroll.minMagnification = 1;
	_scroll.maxMagnification = kZoomMax;
	_doc = [DocView new];
	_surface = [PageSurface new];
	_detail = [ImageLayerView new];
	_detail.hidden = YES;
	[_surface addSubview:_detail];
	[_doc addSubview:_surface];
	_scroll.documentView = _doc;
	_scroll.translatesAutoresizingMaskIntoConstraints = NO;
	[self addSubview:_scroll];
	// The scroll view fills the window, under the glass toolbar and sidebar; its content insets
	// keep the page clear of them until it's zoomed and scrolled under.
	[NSLayoutConstraint activateConstraints:@[
		[_scroll.topAnchor constraintEqualToAnchor:self.topAnchor],
		[_scroll.leadingAnchor constraintEqualToAnchor:self.leadingAnchor],
		[_scroll.trailingAnchor constraintEqualToAnchor:self.trailingAnchor],
		[_scroll.bottomAnchor constraintEqualToAnchor:self.bottomAnchor],
	]];

	_map = [MiniMap new];
	_map.pageView = self;
	_map.target = _scroll;
	_map.hidden = YES;
	[self addSubview:_map];

	NSNotificationCenter *nc = NSNotificationCenter.defaultCenter;
	_scroll.contentView.postsBoundsChangedNotifications = YES;
	[nc addObserver:self selector:@selector(viewChanged:) name:NSViewBoundsDidChangeNotification object:_scroll.contentView];
	[nc addObserver:self selector:@selector(magnifyStarted:) name:NSScrollViewWillStartLiveMagnifyNotification object:_scroll];
	[nc addObserver:self selector:@selector(magnifyEnded:) name:NSScrollViewDidEndLiveMagnifyNotification object:_scroll];
	return self;
}

- (void)dealloc { CGImageRelease(_base); }

- (void)setViewer:(Viewer *)v
{
	_viewer = v;
	_scroll.viewer = v;
}

- (void)drawRect:(NSRect)dirty
{
	[[NSColor textBackgroundColor] setFill];
	NSRectFill(dirty);
}

- (void)dropCache
{
	_basePage = -1; // the page stays on screen; it's re-rendered when used again
	[self hideDetail];
	_pending = false;
	_prefetched = -1;
}

- (void)layout
{
	[super layout];
	NSEdgeInsets in = self.safeAreaInsets, cur = _scroll.contentInsets;
	if (in.top != cur.top || in.left != cur.left || in.bottom != cur.bottom || in.right != cur.right) {
		_scroll.contentInsets = in;
		[self scrollTo:_scroll.contentView.bounds.origin];
	}
	[self reload];
}

- (void)viewDidEndLiveResize
{
	[super viewDidEndLiveResize];
	self.needsLayout = YES;
}

// Lays out the current page, rendering it if the page or the space for it changed.
- (void)reload
{
	Viewer *v = self.viewer;
	if (!v) return;
	int n = v->current;
	NSEdgeInsets in = _scroll.contentInsets;
	NSSize clip = _scroll.contentSize;
	clip.width -= in.left + in.right;
	clip.height -= in.top + in.bottom;
	NSRect px = [self convertRectToBacking:NSMakeRect(0, 0, clip.width - 2 * kPageMargin, clip.height - 2 * kPageMargin)];
	int w = (int)floor(px.size.width), h = (int)floor(px.size.height);
	if (w <= 0 || h <= 0) return;

	// During a live resize the last image is stretched; it's re-rendered when the resize ends.
	if (!(_base && _basePage == n && ((_bw == w && _bh == h) || self.inLiveResize))) {
		CGImageRef img = [v copyImageForPage:n width:w height:h];
		if (!img) return;
		CGImageRelease(_base);
		_base = img;
		_basePage = n;
		_bw = w;
		_bh = h;
		_surface.image = img;
	}

	// The page in points, pixel-aligned. Only a live resize scales the image up.
	CGFloat scale = self.window.backingScaleFactor ?: 2;
	CGFloat iw = CGImageGetWidth(_base), ih = CGImageGetHeight(_base);
	CGFloat s = fmin(w / iw, h / ih);
	if (!self.inLiveResize) s = fmin(1, s);
	NSSize page = NSMakeSize(round(iw * s) / scale, round(ih * s) / scale);
	if (!NSEqualSizes(page, _page)) {
		_page = page;
		_surface.frame = NSMakeRect(kPageMargin, kPageMargin, page.width, page.height);
		[_doc setFrameSize:NSMakeSize(page.width + 2 * kPageMargin, page.height + 2 * kPageMargin)];
		[self scrollTo:_scroll.contentView.bounds.origin];
	}

	if (n != _shownPage) {
		// A new page opens at its top, centred across, at the same zoom.
		_shownPage = n;
		_pending = false;
		[self hideDetail];
		[self scrollTo:[self topOrigin]];
		[self showCachedDetail];
	}
	[self placeDetail];
	[self updateMap];
	[self updateDetail];
}

- (void)scrollTo:(NSPoint)origin
{
	NSClipView *c = _scroll.contentView;
	NSRect b = c.bounds;
	b.origin = origin;
	[c scrollToPoint:[c constrainBoundsRect:b].origin];
	[_scroll reflectScrolledClipView:c];
}

// What's on screen, in page points (y down), not clipped to the page. Includes what shows through
// the toolbar and sidebar.
- (NSRect)visiblePage { return NSOffsetRect(_scroll.contentView.bounds, -kPageMargin, -kPageMargin); }

// The part of the clip view's bounds not under the toolbar or sidebar, in document units.
- (NSRect)unobscured
{
	NSRect b = _scroll.contentView.bounds;
	NSEdgeInsets in = _scroll.contentInsets;
	CGFloat m = _scroll.magnification;
	return NSMakeRect(b.origin.x + in.left / m, b.origin.y + in.top / m, b.size.width - (in.left + in.right) / m,
	                  b.size.height - (in.top + in.bottom) / m);
}

// Bounds origin that puts the unobscured part at the top of the page, centred across.
- (NSPoint)topOrigin
{
	NSRect u = [self unobscured];
	NSEdgeInsets in = _scroll.contentInsets;
	CGFloat m = _scroll.magnification;
	return NSMakePoint((_doc.frame.size.width - u.size.width) / 2 - in.left / m, -in.top / m);
}

// --- zoom ---

- (CGFloat)zoom { return _scroll.magnification; }

// Instant, about the middle of the view.
- (void)setZoom:(CGFloat)z
{
	z = fmin(fmax(z, 1), kZoomMax);
	NSRect u = [self unobscured];
	[_scroll setMagnification:z centeredAtPoint:NSMakePoint(NSMidX(u), NSMidY(u))];
}

- (void)viewChanged:(NSNotification *)note
{
	[self placeDetail];
	[self updateMap];
	[self updateDetail];
	[self.viewer zoomChanged];
}

- (void)magnifyStarted:(NSNotification *)note { _liveMagnify = YES; }
- (void)magnifyEnded:(NSNotification *)note
{
	_liveMagnify = NO;
	[self placeDetail];
	[self updateDetail];
}

// --- detail ---

- (void)hideDetail
{
	_dShown = false;
	_detail.hidden = YES;
	_detail.contents = nil;
}

- (void)placeDetail
{
	if (!_dShown || _dSize.width <= 0 || _dSize.height <= 0) return;
	CGFloat fx = _page.width / _dSize.width, fy = _page.height / _dSize.height;
	NSRect f = NSMakeRect(_dPlaced.origin.x * fx, _dPlaced.origin.y * fy, _dPlaced.size.width * fx,
	                      _dPlaced.size.height * fy);
	// At its own zoom the render maps 1:1 to screen pixels: snap it onto them so the GPU doesn't
	// resample it (a shift of under half a pixel).
	NSWindow *win = self.window;
	if (win && SameZoom(_dZoom, _scroll.magnification) && !_liveMagnify) {
		NSRect b = [win convertRectToBacking:[_surface convertRect:f toView:nil]];
		b.origin.x = round(b.origin.x);
		b.origin.y = round(b.origin.y);
		b.size = _dPx;
		f = [_surface convertRect:[win convertRectFromBacking:b] fromView:nil];
	}
	if (!NSEqualRects(f, _detail.frame)) _detail.frame = f;
}

// Shows the cached detail for the current page if it was rendered for this zoom and box.
- (void)showCachedDetail
{
	Viewer *v = self.viewer;
	if (!v) return;
	int n = v->current;
	CGFloat z = _scroll.magnification;
	PageDetail d = {};
	{
		DocLock lock;
		auto it = v->detailCache.find(n);
		if (it == v->detailCache.end() || it->second.w != _bw || it->second.h != _bh || !SameZoom(it->second.zoom, z))
			return;
		d = it->second;
	}
	_detail.contents = d.surf;
	_dPx = NSMakeSize(d.pw, d.ph);
	_dShown = true;
	_dPage = n;
	_dZoom = d.zoom;
	_dw = d.w;
	_dh = d.h;
	_dRegion = d.region;
	_dPlaced = d.placed;
	_dSize = d.size;
	_detail.hidden = NO;
	[self placeDetail];
}

// Asks for a sharp render of what's in view once zoomed in and settled, unless one covers it.
- (void)updateDetail
{
	Viewer *v = self.viewer;
	if (!v || !_base || _basePage < 0) return;
	CGFloat z = _scroll.magnification;
	if (z <= 1.001) {
		if (_dShown || _pending || _prefetched >= 0) {
			[self hideDetail];
			_pending = false;
			_prefetched = -1;
			[v dropDetails];
		}
		return;
	}
	if (_liveMagnify || self.inLiveResize) return;
	if (!SameZoom(z, _kZoom) || _kw != _bw || _kh != _bh) {
		_kZoom = z;
		_kw = _bw;
		_kh = _bh;
		v->detailGen++;
		_pending = false;
		_prefetched = -1;
	}
	int n = v->current;
	NSRect vis = NSIntersectionRect([self visiblePage], NSMakeRect(0, 0, _page.width, _page.height));
	if (NSIsEmptyRect(vis)) return;
	CGFloat scale = self.window.backingScaleFactor ?: 2;
	if (_dShown && _dPage == n && SameZoom(_dZoom, z) && _dw == _bw && _dh == _bh && Covers(_dRegion, vis)) {
		// Sharp: get the neighbouring pages ready too, at the view they open with.
		if (_prefetched != n) {
			_prefetched = n;
			// The view a page opens at, taking the neighbours to be this page's size.
			NSClipView *c = _scroll.contentView;
			NSRect t = c.bounds;
			t.origin = [self topOrigin];
			t = NSOffsetRect([c constrainBoundsRect:t], -kPageMargin, -kPageMargin);
			t = NSInsetRect(t, -t.size.width * kDetailMargin, -t.size.height * kDetailMargin);
			for (int m : {n - 1, n + 1})
				if (m >= 0 && m < v->count)
					[v prefetchDetail:m width:_bw height:_bh zoom:z scale:scale region:t];
		}
		return;
	}
	if (_pending && _pPage == n && Covers(_pRegion, vis)) return;
	_pending = true;
	_pPage = n;
	_pRegion = NSInsetRect(vis, -vis.size.width * kDetailMargin, -vis.size.height * kDetailMargin);
	[v requestDetail:n width:_bw height:_bh zoom:z scale:scale region:_pRegion];
}

- (void)detailReady:(int)n
{
	Viewer *v = self.viewer;
	if (!v || n != v->current) return;
	[self showCachedDetail];
	NSRect page = NSMakeRect(0, 0, _page.width, _page.height);
	if (_pending && _dShown && Covers(_dRegion, NSIntersectionRect(_pRegion, page))) _pending = false;
	[self updateDetail];
}

// --- mini-map ---

- (void)updateMap
{
	Viewer *v = self.viewer;
	BOOL show = v && _base && _scroll.magnification > 1.001;
	_map.hidden = !show;
	if (!show) return;
	int n = v->current;
	if (_mapPage != n || !_mapIsThumb) {
		// The page's sidebar thumbnail; the page image until that's ready.
		CGImageRef t = [v copyThumbForPage:n request:_mapAsked != n];
		_mapAsked = n;
		_mapPage = n;
		_mapIsThumb = t != NULL;
		[_map setImage:t ?: _base];
		CGImageRelease(t);
	}
	NSSize ms = [MiniMap sizeForPage:_page];
	NSRect f = NSMakeRect(NSMaxX(self.bounds) - kMapInset - ms.width, kMapInset, ms.width, ms.height);
	if (!NSEqualRects(f, _map.frame)) _map.frame = f;
	NSRect vis = NSOffsetRect([self unobscured], -kPageMargin, -kPageMargin);
	NSRect unit = NSMakeRect(vis.origin.x / _page.width, vis.origin.y / _page.height, vis.size.width / _page.width,
	                         vis.size.height / _page.height);
	[_map setViewport:NSIntersectionRect(unit, NSMakeRect(0, 0, 1, 1))];
}

- (void)thumbReady:(int)n
{
	if (n == _mapPage && !_mapIsThumb) {
		_mapPage = -1;
		[self updateMap];
	}
}

// Centres the view on a point of the page given in fractions of it.
- (void)mapMovedTo:(NSPoint)unit
{
	NSRect u = [self unobscured];
	NSPoint o = _scroll.contentView.bounds.origin;
	CGFloat dx = kPageMargin + unit.x * _page.width - NSMidX(u), dy = kPageMargin + unit.y * _page.height - NSMidY(u);
	[self scrollTo:NSMakePoint(o.x + dx, o.y + dy)];
}

// --- pan benchmark (LEANPDF_PANBENCH=1): zooms in, pans for 10 s, reports frame pacing ---

- (void)runPanBench
{
	self.zoom = 2.5;
	if (@available(macOS 14.0, *)) {
		CADisplayLink *l = [self displayLinkWithTarget:self selector:@selector(benchTick:)];
		[l addToRunLoop:NSRunLoop.mainRunLoop forMode:NSRunLoopCommonModes];
	}
}

- (void)benchTick:(CADisplayLink *)l API_AVAILABLE(macos(14.0))
{
	static double last, start, worst, dir = 1, work;
	static int frames, late, missed;
	double t = l.timestamp, period = l.targetTimestamp - l.timestamp;
	if (start == 0) start = t;
	if (last) {
		double iv = t - last;
		frames++;
		if (iv > period * 1.5) { late++; missed += (int)lround(iv / period) - 1; }
		worst = fmax(worst, iv);
	}
	last = t;
	double t0 = CACurrentMediaTime();
	NSRect b = _scroll.contentView.bounds;
	CGFloat spanX = _doc.frame.size.width - b.size.width, spanY = _doc.frame.size.height - b.size.height;
	NSPoint o = b.origin;
	o.y += 6 * dir;
	if (o.y > spanY || o.y < 0) dir = -dir;
	o.x = spanX / 2 + sin((t - start) * 1.3) * spanX / 2;
	[self scrollTo:o];
	work += CACurrentMediaTime() - t0;
	if (t - start > 10) {
		printf("panbench: %.0f Hz, %d frames, %d late (%d missed), worst %.1f ms, main-thread work %.2f ms/frame\n",
		       1 / period, frames, late, missed, worst * 1000, work * 1000 / frames);
		fflush(stdout);
		exit(0);
	}
}

// --- input ---

- (void)keyDown:(NSEvent *)e
{
	if (!HandlePageKey(self.viewer, e)) [super keyDown:e];
}

- (void)scrollWheel:(NSEvent *)e { [_scroll scrollWheel:e]; }

- (NSDragOperation)draggingEntered:(id<NSDraggingInfo>)s { return NSDragOperationCopy; }

- (BOOL)performDragOperation:(id<NSDraggingInfo>)s
{
	NSArray *urls = [s.draggingPasteboard readObjectsForClasses:@[ NSURL.class ]
	                                                    options:@{NSPasteboardURLReadingFileURLsOnlyKey : @YES}];
	for (NSURL *u in urls) OpenURL(u);
	return urls.count > 0;
}

@end

@implementation ThumbTable

- (void)keyDown:(NSEvent *)e
{
	if (!HandlePageKey(self.viewer, e)) [super keyDown:e];
}

// Clicks never go through NSTableView's own selection tracking; the viewer decides what they do.
- (void)mouseDown:(NSEvent *)e
{
	[self.window makeFirstResponder:self];
	NSInteger r = [self rowAtPoint:[self convertPoint:e.locationInWindow fromView:nil]];
	if (r >= 0) [self.viewer thumbClicked:(int)r modifiers:e.modifierFlags];
}

// Cmd-A goes through the viewer so it ends any Shift range like every other selection change.
- (void)selectAll:(id)s { [self.viewer selectAll:s]; }

@end

// ---------------------------------------------------------------------------

static const NSUInteger kOCRParallel = 4, kOCRConfirmOver = 50;

// The Markdown of every page in one OCR response.
static NSString *OCRPagesMarkdown(NSDictionary *json)
{
	NSMutableArray *parts = [NSMutableArray array];
	for (NSDictionary *page in json[@"pages"])
		if ([page isKindOfClass:NSDictionary.class] && [page[@"markdown"] isKindOfClass:NSString.class])
			[parts addObject:page[@"markdown"]];
	return [parts componentsJoinedByString:@"\n\n"];
}

// Drops image placeholders like ![img-0.jpeg](img-0.jpeg) and squeezes the gaps they leave.
static NSString *OCRClean(NSString *text)
{
	NSMutableString *md = [text mutableCopy];
	NSRegularExpression *img = [NSRegularExpression regularExpressionWithPattern:@"!\\[[^\\]]*\\]\\([^)]*\\)" options:0 error:nil];
	NSRegularExpression *gaps = [NSRegularExpression regularExpressionWithPattern:@"\\n{3,}" options:0 error:nil];
	[img replaceMatchesInString:md options:0 range:NSMakeRange(0, md.length) withTemplate:@""];
	[gaps replaceMatchesInString:md options:0 range:NSMakeRange(0, md.length) withTemplate:@"\n\n"];
	return [md stringByTrimmingCharactersInSet:NSCharacterSet.whitespaceAndNewlineCharacterSet];
}

static NSString *OCRErrorMessage(NSInteger status, id json, NSData *data)
{
	if (status == 401) return @"The Mistral API key was rejected. Check it in Settings.";
	if ([json isKindOfClass:NSDictionary.class]) {
		id m = json[@"message"] ?: json[@"detail"];
		if ([m isKindOfClass:NSString.class]) return [NSString stringWithFormat:@"%@ (HTTP %ld)", m, (long)status];
	}
	NSString *text = data ? [[NSString alloc] initWithData:data encoding:NSUTF8StringEncoding] : nil;
	return [NSString stringWithFormat:@"HTTP %ld %@", (long)status, text.length ? [text substringToIndex:MIN(text.length, 300)] : @""];
}

// Asks for Markdown with inline LaTeX math; images, running headers and footers are left out.
static NSURLRequest *OCRRequest(NSData *pdfData, NSString *key)
{
	NSDictionary *body = @{
		@"model" : @"mistral-ocr-latest",
		@"document" : @{
			@"type" : @"document_url",
			@"document_url" : [@"data:application/pdf;base64," stringByAppendingString:[pdfData base64EncodedStringWithOptions:0]],
		},
		@"include_image_base64" : @NO,
		@"extract_header" : @YES,
		@"extract_footer" : @YES,
	};
	NSMutableURLRequest *req = [NSMutableURLRequest requestWithURL:[NSURL URLWithString:@"https://api.mistral.ai/v1/ocr"]];
	req.HTTPMethod = @"POST";
	req.timeoutInterval = 120;
	[req setValue:@"application/json" forHTTPHeaderField:@"Content-Type"];
	[req setValue:[@"Bearer " stringByAppendingString:key] forHTTPHeaderField:@"Authorization"];
	req.HTTPBody = [NSJSONSerialization dataWithJSONObject:body options:0 error:nil];
	return req;
}

// The PDF's page labels ("i", "ii", "1", "A-1"…), or nil if it defines none. Caller holds g_doc_lock.
static NSArray<NSString *> *LoadPageLabels(pdf_document *pdf, int count)
{
	if (!pdf) return nil;
	NSMutableArray *labels = nil;
	fz_var(labels);
	fz_try(g_ctx) {
		if (pdf_dict_getp(g_ctx, pdf_trailer(g_ctx, pdf), "Root/PageLabels")) {
			labels = [NSMutableArray arrayWithCapacity:count];
			char buf[256];
			for (int i = 0; i < count; i++) {
				buf[0] = 0;
				pdf_page_label(g_ctx, pdf, i, buf, sizeof buf);
				NSString *l = [NSString stringWithUTF8String:buf];
				[labels addObject:l.length ? l : [NSString stringWithFormat:@"%d", i + 1]];
			}
		}
	}
	fz_catch(g_ctx) { fz_report_error(g_ctx); labels = nil; }
	return labels;
}

@implementation Viewer

+ (instancetype)viewerWithPath:(NSString *)path error:(NSString **)err
{
	Viewer *v = [Viewer new];
	v.path = path;
	fz_document *doc = NULL;
	fz_outline *outline = NULL;
	NSArray *toc = nil;
	int count = 0;
	fz_var(doc);
	fz_var(outline);
	{
		DocLock lock;
		fz_try(g_ctx) {
			doc = fz_open_document(g_ctx, path.fileSystemRepresentation);
			if (fz_needs_password(g_ctx, doc) && !fz_authenticate_password(g_ctx, doc, ""))
				fz_throw(g_ctx, FZ_ERROR_GENERIC, "password-protected documents are not supported");
			count = fz_count_pages(g_ctx, doc);
			if (count <= 0) fz_throw(g_ctx, FZ_ERROR_GENERIC, "document has no pages");
		}
		fz_catch(g_ctx) {
			if (err) *err = [NSString stringWithUTF8String:fz_caught_message(g_ctx)];
			fz_drop_document(g_ctx, doc);
			return nil;
		}
		fz_try(g_ctx) {
			outline = fz_load_outline(g_ctx, doc);
			toc = BuildToc(g_ctx, doc, outline);
		}
		fz_always(g_ctx) { fz_drop_outline(g_ctx, outline); }
		fz_catch(g_ctx) { fz_report_error(g_ctx); toc = nil; }
		v->doc = doc;
		v->pdf = pdf_specifics(g_ctx, doc);
		v.pageLabels = LoadPageLabels(v->pdf, count);
	}
	v->count = count;
	v->current = 0;
	v->selAnchor = -1;
	v->visLo = 0;
	v->visHi = -1;
	v.tocRoots = toc.count ? toc : nil;
	v.thumbCache = [NSCache new];
	v.thumbCache.totalCostLimit = 32 << 20; // ~130 thumbnails; the rest reload from disk
	v.thumbDir = ThumbDirFor(path);
	v.thumbPending = [NSMutableIndexSet indexSet];
	[v buildWindow];
	return v;
}

- (NSScrollView *)scrollFor:(NSTableView *)t
{
	NSScrollView *s = [NSScrollView new];
	s.documentView = t;
	s.hasVerticalScroller = YES;
	s.autohidesScrollers = YES;
	s.drawsBackground = NO;
	s.translatesAutoresizingMaskIntoConstraints = NO;
	t.columnAutoresizingStyle = NSTableViewFirstColumnOnlyAutoresizingStyle;
	t.tableColumns.firstObject.resizingMask = NSTableColumnAutoresizingMask;
	return s;
}

- (void)buildWindow
{
	// Sidebar: a thumbnail table or TOC outline, picked from the toolbar's sidebar menu.
	NSView *side = [[NSView alloc] initWithFrame:NSMakeRect(0, 0, kThumbSideW, 700)];

	ThumbTable *thumbs = [ThumbTable new];
	thumbs.viewer = self;
	self.thumbs = thumbs;
	[self.thumbs addTableColumn:[[NSTableColumn alloc] initWithIdentifier:@"p"]];
	self.thumbs.headerView = nil;
	self.thumbs.style = NSTableViewStyleSourceList;
	self.thumbs.rowHeight = kRingPad + kThumbH + kLabelGap + kLabelH + kItemBottomPad + kItemGap;
	self.thumbs.allowsMultipleSelection = YES;
	self.thumbs.allowsTypeSelect = NO;
	self.thumbs.dataSource = self;
	self.thumbs.delegate = self;
	self.thumbScroll = [self scrollFor:self.thumbs];

	self.toc = [NSOutlineView new];
	NSTableColumn *col = [[NSTableColumn alloc] initWithIdentifier:@"t"];
	[self.toc addTableColumn:col];
	self.toc.outlineTableColumn = col;
	self.toc.headerView = nil;
	self.toc.style = NSTableViewStyleSourceList;
	self.toc.dataSource = self;
	self.toc.delegate = self;
	self.tocScroll = [self scrollFor:self.toc];
	self.tocScroll.hidden = YES;

	self.ocrStatus = [OCRStatusView new];
	self.ocrStatus.hidden = YES;
	self.ocrStatus.close.target = self;
	self.ocrStatus.close.action = @selector(closeOCRStatus:);

	[side addSubview:self.thumbScroll];
	[side addSubview:self.tocScroll];
	[side addSubview:self.ocrStatus];
	NSMutableArray *cs = [NSMutableArray arrayWithArray:@[
		[side.widthAnchor constraintGreaterThanOrEqualToConstant:150],
		[self.ocrStatus.leadingAnchor constraintEqualToAnchor:side.leadingAnchor],
		[self.ocrStatus.trailingAnchor constraintEqualToAnchor:side.trailingAnchor],
		[self.ocrStatus.bottomAnchor constraintEqualToAnchor:side.bottomAnchor],
	]];
	NSMutableArray *toBottom = [NSMutableArray array], *toStatus = [NSMutableArray array];
	for (NSScrollView *s in @[ self.thumbScroll, self.tocScroll ]) {
		[cs addObjectsFromArray:@[
			[s.topAnchor constraintEqualToAnchor:side.safeAreaLayoutGuide.topAnchor],
			[s.leadingAnchor constraintEqualToAnchor:side.leadingAnchor],
			[s.trailingAnchor constraintEqualToAnchor:side.trailingAnchor],
		]];
		[toBottom addObject:[s.bottomAnchor constraintEqualToAnchor:side.bottomAnchor]];
		[toStatus addObject:[s.bottomAnchor constraintEqualToAnchor:self.ocrStatus.topAnchor]];
	}
	self.listsToBottom = toBottom;
	self.listsToStatus = toStatus;
	[cs addObjectsFromArray:toBottom];
	[NSLayoutConstraint activateConstraints:cs];

	self.pageView = [[PageView alloc] initWithFrame:NSMakeRect(0, 0, 600, 700)];
	self.pageView.viewer = self;

	NSViewController *sideVC = [NSViewController new], *mainVC = [NSViewController new];
	// The initial width comes from side's frame. No width constraint: it would keep
	// beating the split view's holding priority and snap the divider back after every drag.
	sideVC.view = side;
	mainVC.view = self.pageView;
	NSSplitViewController *split = [NSSplitViewController new];
	NSSplitViewItem *sideItem = [NSSplitViewItem sidebarWithViewController:sideVC];
	[split addSplitViewItem:sideItem];
	self.sideItem = sideItem;
	[self fitSidebarWidth:NO];
	NSSplitViewItem *mainItem = [NSSplitViewItem splitViewItemWithViewController:mainVC];
	// As in Preview: the page runs under the floating glass sidebar when zoomed.
	if (@available(macOS 26.0, *)) mainItem.automaticallyAdjustsSafeAreaInsets = YES;
	[split addSplitViewItem:mainItem];
	split.splitView.autosaveName = @"LeanPDFSplit";

	self.window = [NSWindow windowWithContentViewController:split];
	self.window.delegate = self;
	self.window.title = self.path.lastPathComponent;
	self.window.representedURL = [NSURL fileURLWithPath:self.path];
	self.window.tabbingMode = NSWindowTabbingModeDisallowed;
	// Full-height glass sidebar, as in Preview: content runs under a unified toolbar whose
	// sidebar toggle sits in the sidebar, next to the traffic lights.
	self.window.styleMask |= NSWindowStyleMaskFullSizeContentView;
	NSToolbar *bar = [[NSToolbar alloc] initWithIdentifier:@"LeanPDFToolbar"];
	bar.delegate = self;
	bar.displayMode = NSToolbarDisplayModeIconOnly;
	self.window.toolbar = bar;
	self.window.toolbarStyle = NSWindowToolbarStyleUnified;
	[self.window setContentSize:NSMakeSize(900, 1000)];
	[self.window setFrameAutosaveName:@"LeanPDFWindow"];

	[NSNotificationCenter.defaultCenter addObserver:self selector:@selector(thumbsScrolled:)
	                                           name:NSViewBoundsDidChangeNotification
	                                         object:self.thumbScroll.contentView];
	self.thumbScroll.contentView.postsBoundsChangedNotifications = YES;

	[self.thumbs reloadData];
	[self.toc reloadData];
	[self goToPage:0];
	[self.window makeFirstResponder:self.pageView];
	if (getenv("LEANPDF_PANBENCH"))
		dispatch_after(dispatch_time(DISPATCH_TIME_NOW, NSEC_PER_SEC), dispatch_get_main_queue(), ^{
			[self.pageView performSelector:@selector(runPanBench)];
		});
}

- (NSArray<NSToolbarItemIdentifier> *)toolbarDefaultItemIdentifiers:(NSToolbar *)t
{
	return @[ NSToolbarFlexibleSpaceItemIdentifier, @"sidebar",
	          NSToolbarSidebarTrackingSeparatorItemIdentifier, NSToolbarFlexibleSpaceItemIdentifier, @"zoom" ];
}

- (NSArray<NSToolbarItemIdentifier> *)toolbarAllowedItemIdentifiers:(NSToolbar *)t
{
	return [self toolbarDefaultItemIdentifiers:t];
}

- (NSToolbarItem *)toolbar:(NSToolbar *)t itemForItemIdentifier:(NSToolbarItemIdentifier)i willBeInsertedIntoToolbar:(BOOL)f
{
	if ([i isEqualToString:@"zoom"]) {
		NSArray *images = @[
			[NSImage imageWithSystemSymbolName:@"minus.magnifyingglass" accessibilityDescription:@"Zoom Out"],
			[NSImage imageWithSystemSymbolName:@"plus.magnifyingglass" accessibilityDescription:@"Zoom In"],
		];
		NSToolbarItemGroup *g = [NSToolbarItemGroup groupWithItemIdentifier:i images:images
		                                                       selectionMode:NSToolbarItemGroupSelectionModeMomentary
		                                                              labels:@[ @"Zoom Out", @"Zoom In" ]
		                                                              target:self action:@selector(zoomGroup:)];
		g.label = @"Zoom";
		g.autovalidates = NO;
		for (NSToolbarItem *s in g.subitems) {
			s.autovalidates = NO;
			s.toolTip = s.label;
		}
		self.zoomItem = g;
		[self zoomChanged];
		return g;
	}
	if (![i isEqualToString:@"sidebar"]) return nil;
	// Like Preview: one button whose menu hides the sidebar or picks what it shows.
	NSMenu *m = [NSMenu new];
	[m addItemWithTitle:@"Hide Sidebar" action:@selector(toggleSidebarFromMenu:) keyEquivalent:@""].target = self;
	[m addItem:NSMenuItem.separatorItem];
	NSMenuItem *pages = [m addItemWithTitle:@"Thumbnails" action:@selector(switchSidebar:) keyEquivalent:@""];
	NSMenuItem *contents = [m addItemWithTitle:@"Table of Contents" action:@selector(switchSidebar:) keyEquivalent:@""];
	pages.target = contents.target = self;
	pages.tag = 0;
	contents.tag = 1;
	NSMenuToolbarItem *item = [[NSMenuToolbarItem alloc] initWithItemIdentifier:i];
	item.image = [NSImage imageWithSystemSymbolName:@"sidebar.left" accessibilityDescription:@"Sidebar"];
	item.label = @"Sidebar";
	item.toolTip = @"Sidebar";
	item.menu = m;
	return item;
}

- (void)toggleSidebarFromMenu:(id)sender { self.sideItem.animator.collapsed = !self.sideItem.collapsed; }

// --- zoom --------------------------------------------------------------------
// Steps through kZoomLevels, instantly. Pinching is the scroll view's own.

- (void)stepZoom:(int)dir
{
	CGFloat z = self.pageView.zoom, next = z;
	int levels = sizeof kZoomLevels / sizeof *kZoomLevels;
	if (dir > 0) {
		for (int i = 0; i < levels; i++)
			if (kZoomLevels[i] > z + 1e-3) { next = kZoomLevels[i]; break; }
	} else {
		for (int i = levels - 1; i >= 0; i--)
			if (kZoomLevels[i] < z - 1e-3) { next = kZoomLevels[i]; break; }
	}
	self.pageView.zoom = next;
}

- (IBAction)zoomIn:(id)s { [self stepZoom:1]; }
- (IBAction)zoomOut:(id)s { [self stepZoom:-1]; }
- (IBAction)resetZoom:(id)s { self.pageView.zoom = 1; }
- (void)zoomGroup:(NSToolbarItemGroup *)g { [self stepZoom:g.selectedIndex == 0 ? -1 : 1]; }

- (void)zoomChanged
{
	CGFloat z = self.pageView.zoom;
	NSArray<NSToolbarItem *> *subs = self.zoomItem.subitems;
	if (subs.count != 2) return;
	BOOL canOut = z > 1.001, canIn = z < kZoomMax - 1e-3;
	if (subs[0].enabled != canOut) subs[0].enabled = canOut;
	if (subs[1].enabled != canIn) subs[1].enabled = canIn;
}

// --- navigation ------------------------------------------------------------

// Any plain navigation ends a Shift range, so the next one starts from the page being viewed.
- (void)goToPage:(int)n
{
	if (n < 0 || n >= count) return;
	selAnchor = -1;
	[self showPage:n];
}

- (void)showPage:(int)n
{
	[self touch];
	int old = current;
	current = n;
	[self updateSubtitle];
	[self.pageView reload];
	for (int r : {old, n})
		[self markCurrent:[self.thumbs viewAtColumn:0 row:r makeIfNecessary:NO] row:r];
	[self.thumbs scrollRowToVisible:n];
}

- (void)updateSubtitle
{
	self.window.subtitle = [NSString stringWithFormat:@"Page %d of %d", current + 1, count];
}

// --- page selection ----------------------------------------------------------
// The viewed page is the selection's only cursor. Shift+Up/Down and Shift-click move it and select
// from the anchor (where that Shift run began) to it, on top of what was selected before the run.
// Every other change goes through setSelection: and ends the run.

- (void)setSelection:(NSIndexSet *)sel
{
	selAnchor = -1;
	[self.thumbs selectRowIndexes:sel byExtendingSelection:NO];
}

- (void)extendSelectionTo:(int)r
{
	r = MAX(0, MIN(count - 1, r));
	if (selAnchor < 0) {
		selAnchor = current;
		self.selBase = [self.thumbs.selectedRowIndexes copy];
	}
	NSMutableIndexSet *sel = [self.selBase mutableCopy];
	[sel addIndexesInRange:NSMakeRange(MIN(selAnchor, r), abs(r - selAnchor) + 1)];
	[self.thumbs selectRowIndexes:sel byExtendingSelection:NO];
	[self showPage:r];
}

// Shift-click extends the selection to the row; Cmd-click toggles the row. Either way the row is viewed.
- (void)thumbClicked:(int)r modifiers:(NSEventModifierFlags)m
{
	if (m & NSEventModifierFlagShift) {
		[self extendSelectionTo:r];
		return;
	}
	if (m & NSEventModifierFlagCommand) {
		NSMutableIndexSet *sel = [self.thumbs.selectedRowIndexes mutableCopy];
		if ([sel containsIndex:r]) [sel removeIndex:r];
		else [sel addIndex:r];
		[self setSelection:sel];
	}
	[self goToPage:r];
}

- (void)clearSelection { [self setSelection:[NSIndexSet indexSet]]; }

// Space: add the viewed page to the selection.
- (void)selectCurrent
{
	NSMutableIndexSet *sel = [self.thumbs.selectedRowIndexes mutableCopy];
	[sel addIndex:current];
	[self setSelection:sel];
}

- (IBAction)selectAll:(id)s { [self setSelection:[NSIndexSet indexSetWithIndexesInRange:NSMakeRange(0, count)]]; }

// Gives the viewed page's thumbnail the accent highlight.
- (void)markCurrent:(ThumbCell *)cell row:(int)row
{
	cell.current = row == current;
}

// Only the table of contents can be resized; the thumbnail list is pinned to kThumbSideW.
- (void)fitSidebarWidth:(BOOL)resizable
{
	self.sideItem.minimumThickness = resizable ? 150 : kThumbSideW;
	self.sideItem.maximumThickness = resizable ? 400 : kThumbSideW;
}

- (void)switchSidebar:(id)sender
{
	BOOL showToc = [sender tag] == 1;
	if (self.sideItem.collapsed) self.sideItem.animator.collapsed = NO;
	self.tocScroll.hidden = !showToc;
	self.thumbScroll.hidden = showToc;
	[self fitSidebarWidth:showToc];
	if (showToc) [self.toc sizeLastColumnToFit];
}

- (IBAction)nextPage:(id)s { [self goToPage:current + 1]; }
- (IBAction)previousPage:(id)s { [self goToPage:current - 1]; }
- (IBAction)firstPage:(id)s { [self goToPage:0]; }
- (IBAction)lastPage:(id)s { [self goToPage:count - 1]; }

// Page index for what the user typed, or -1. If the PDF has page labels, the first page with a
// matching label (case-insensitive) wins; otherwise, or if no label matches, it's a page number.
- (int)pageForString:(NSString *)str
{
	str = [str stringByTrimmingCharactersInSet:NSCharacterSet.whitespaceCharacterSet];
	if (!str.length) return -1;
	for (int i = 0; i < (int)self.pageLabels.count; i++)
		if ([self.pageLabels[i] caseInsensitiveCompare:str] == NSOrderedSame) return i;
	NSScanner *sc = [NSScanner scannerWithString:str];
	int n;
	if ([sc scanInt:&n] && sc.atEnd && n >= 1 && n <= count) return n - 1;
	return -1;
}

// A compact sheet like Preview's: "Go to page: [    ]" over Cancel / OK.
- (IBAction)goToPageNumber:(id)sender
{
	NSTextField *field = [NSTextField textFieldWithString:@""];
	[field.widthAnchor constraintEqualToConstant:130].active = YES;
	self.gotoField = field;
	NSStackView *row = [NSStackView stackViewWithViews:@[ [NSTextField labelWithString:@"Go to page:"], field ]];
	row.spacing = 8;

	NSButton *cancel = [NSButton buttonWithTitle:@"Cancel" target:self action:@selector(endGoToSheet:)];
	cancel.keyEquivalent = @"\033";
	cancel.tag = NSModalResponseCancel;
	NSButton *ok = [NSButton buttonWithTitle:@"OK" target:self action:@selector(endGoToSheet:)];
	ok.keyEquivalent = @"\r";
	ok.tag = NSModalResponseOK;
	NSStackView *buttons = [NSStackView stackViewWithViews:@[ cancel, ok ]];
	buttons.distribution = NSStackViewDistributionFillEqually;
	buttons.spacing = 12;

	NSStackView *content = [NSStackView stackViewWithViews:@[ row, buttons ]];
	content.orientation = NSUserInterfaceLayoutOrientationVertical;
	content.spacing = 20;
	content.edgeInsets = NSEdgeInsetsMake(24, 24, 20, 24);
	[buttons.widthAnchor constraintEqualToAnchor:row.widthAnchor].active = YES;

	NSPanel *sheet = [[NSPanel alloc] initWithContentRect:NSZeroRect styleMask:NSWindowStyleMaskTitled
	                                              backing:NSBackingStoreBuffered defer:YES];
	sheet.contentView = content;
	[sheet setContentSize:content.fittingSize];
	sheet.initialFirstResponder = field;
	[self.window beginSheet:sheet completionHandler:nil];
}

// OK with input that isn't a page beeps and leaves the sheet up so it can be corrected.
- (void)endGoToSheet:(NSButton *)b
{
	if (b.tag == NSModalResponseOK) {
		int n = [self pageForString:self.gotoField.stringValue];
		if (n < 0) { NSBeep(); return; }
		[self goToPage:n];
	}
	[self.window endSheet:b.window returnCode:b.tag];
}

// --- page rendering ----------------------------------------------------------

- (CGImageRef)copyImageForPage:(int)n width:(int)w height:(int)h
{
	CGImageRef img = NULL;
	{
		DocLock lock;
		if (!doc) return NULL;
		if (dormant) return RenderPage(g_ctx, doc, n, w, h); // a redraw while idle: keep nothing
		auto it = pageCache.find(n);
		if (it != pageCache.end() && it->second.w == w && it->second.h == h) {
			img = CGImageRetain(it->second.img);
		} else {
			img = RenderPage(g_ctx, doc, n, w, h);
			if (it != pageCache.end()) CGImageRelease(it->second.img);
			if (img) pageCache[n] = {w, h, CGImageRetain(img)};
			else if (it != pageCache.end()) pageCache.erase(it);
		}
		for (auto e = pageCache.begin(); e != pageCache.end();) {
			if (abs(e->first - n) > 1) { CGImageRelease(e->second.img); e = pageCache.erase(e); }
			else ++e;
		}
		for (auto e = detailCache.begin(); e != detailCache.end();) {
			if (abs(e->first - n) > 1) e = detailCache.erase(e);
			else ++e;
		}
	}
	// Stack is LIFO: queue previous first so the next page is rendered first.
	if (n > 0) Enqueue(self, n - 1, kJobPrefetch, w, h);
	if (n + 1 < count) Enqueue(self, n + 1, kJobPrefetch, w, h);
	return img;
}

- (void)requestDetail:(int)n width:(int)w height:(int)h zoom:(CGFloat)z scale:(CGFloat)s region:(NSRect)r
{
	Job *j = NewJob(self, n, kJobDetail, w, h);
	j->zoom = z;
	j->scale = s;
	j->region = r;
	j->gen = ++detailReq;
	j->space = (__bridge id)self.window.colorSpace.CGColorSpace;
	Push(j);
}

- (void)prefetchDetail:(int)n width:(int)w height:(int)h zoom:(CGFloat)z scale:(CGFloat)s region:(NSRect)r
{
	Job *j = NewJob(self, n, kJobDetail, w, h);
	j->zoom = z;
	j->scale = s;
	j->top = true;
	j->region = r;
	j->gen = detailGen;
	j->space = (__bridge id)self.window.colorSpace.CGColorSpace;
	Push(j);
}

- (void)dropDetails
{
	DocLock lock;
	detailCache.clear();
}

// The sidebar thumbnail of page n, from memory or disk. If there's none and request is set, one is
// rendered and the page view hears of it through thumbReady:. Returns +1 or NULL.
- (CGImageRef)copyThumbForPage:(int)n request:(BOOL)request
{
	NSImage *img = [self.thumbCache objectForKey:@(n)];
	if (img) return CGImageRetain([img CGImageForProposedRect:NULL context:nil hints:nil]);
	CGFloat s = self.window.backingScaleFactor ?: 2;
	CGImageRef c = self.thumbDir ? LoadThumbFile([self thumbFile:n scale:s]) : NULL;
	if (c) {
		[self.thumbCache setObject:ThumbImage(c, s) forKey:@(n) cost:CGImageGetBytesPerRow(c) * CGImageGetHeight(c)];
		return c;
	}
	if (request) {
		[self.thumbPending addIndex:n];
		Job *j = NewJob(self, n, kJobThumb, (int)(kThumbW * s), (int)(kThumbH * s));
		j->force = true;
		Push(j);
	}
	return NULL;
}

// Called on the worker thread.
- (void)runJob:(Job *)j
{
	int n = j->page;
	if (j->kind == kJobDetail) {
		NSRect region = j->region, placed;
		NSSize size;
		CGImageRef img;
		auto fresh = [&] {
			if (!doc || dormant || abs(n - current) > 1) return false;
			if (j->gen != (j->top ? detailGen : detailReq)) return false;
			auto it = detailCache.find(n);
			return !(j->top && it != detailCache.end() && it->second.w == j->w && it->second.h == j->h &&
			         SameZoom(it->second.zoom, j->zoom));
		};
		{
			DocLock lock;
			if (!fresh()) return;
			img = RenderDetail(g_worker_ctx, doc, n, j->w, j->h, j->zoom, j->scale, false, NSZeroSize, &region, &placed, &size);
		}
		if (!img) return;
		// Outside the lock, so page flips needn't wait for it.
		id surf = (__bridge_transfer id)SurfaceFromImage(img, (__bridge CGColorSpaceRef)j->space);
		int pw = (int)CGImageGetWidth(img), ph = (int)CGImageGetHeight(img);
		CGImageRelease(img);
		if (!surf) return;
		{
			DocLock lock;
			if (!fresh()) return;
			detailCache[n] = {j->w, j->h, j->zoom, region, placed, size, surf, pw, ph};
		}
		dispatch_async(dispatch_get_main_queue(), ^{ [self.pageView detailReady:n]; });
		return;
	}
	if (j->kind == kJobPrefetch) {
		DocLock lock;
		if (!doc || dormant || abs(n - current) > 1) return;
		auto it = pageCache.find(n);
		if (it != pageCache.end() && it->second.w == j->w && it->second.h == j->h) return;
		CGImageRef img = RenderPage(g_worker_ctx, doc, n, j->w, j->h);
		if (!img) return;
		if (it != pageCache.end()) CGImageRelease(it->second.img);
		pageCache[n] = {j->w, j->h, img};
		return;
	}

	CGImageRef img = NULL;
	if (j->force || (n >= visLo && n <= visHi)) {
		DocLock lock;
		if (doc) img = RenderPage(g_worker_ctx, doc, n, j->w, j->h);
	}
	CGFloat scale = (CGFloat)j->w / kThumbW;
	if (img && self.thumbDir) SaveThumbFile(img, [self thumbFile:n scale:scale]);
	NSImage *thumb = img ? ThumbImage(img, scale) : nil;
	NSUInteger cost = img ? CGImageGetBytesPerRow(img) * CGImageGetHeight(img) : 0;
	CGImageRelease(img);
	dispatch_async(dispatch_get_main_queue(), ^{
		[self.thumbPending removeIndex:n];
		if (!thumb) return;
		[self.thumbCache setObject:thumb forKey:@(n) cost:cost];
		ThumbCell *cell = [self.thumbs viewAtColumn:0 row:n makeIfNecessary:NO];
		cell.thumb.image = thumb;
		[self.pageView thumbReady:n];
	});
}

// --- thumbnails table ------------------------------------------------------

- (NSString *)thumbFile:(int)n scale:(CGFloat)s
{
	return [self.thumbDir stringByAppendingPathComponent:[NSString stringWithFormat:@"%d@%dx.jpg", n + 1, (int)lround(s)]];
}

- (void)thumbsScrolled:(NSNotification *)note
{
	NSRange r = [self.thumbs rowsInRect:self.thumbs.visibleRect];
	visLo = (int)r.location;
	visHi = (int)NSMaxRange(r) - 1;
}

- (NSInteger)numberOfRowsInTableView:(NSTableView *)t { return count; }

static NSTableCellView *MakeCell(NSTableView *t, NSString *ident, BOOL withImage)
{
	NSTableCellView *cell = [t makeViewWithIdentifier:ident owner:nil];
	if (cell) return cell;
	cell = withImage ? [ThumbCell new] : [NSTableCellView new];
	cell.identifier = ident;
	NSTextField *label = [NSTextField labelWithString:@""];
	label.translatesAutoresizingMaskIntoConstraints = NO;
	label.lineBreakMode = NSLineBreakByTruncatingTail;
	label.maximumNumberOfLines = 1;
	[cell addSubview:label];
	cell.textField = label;
	if (!withImage) {
		[NSLayoutConstraint activateConstraints:@[
			[label.leadingAnchor constraintEqualToAnchor:cell.leadingAnchor constant:2],
			[label.trailingAnchor constraintEqualToAnchor:cell.trailingAnchor],
			[label.centerYAnchor constraintEqualToAnchor:cell.centerYAnchor],
		]];
		return cell;
	}
	label.alignment = NSTextAlignmentCenter;
	label.font = [NSFont systemFontOfSize:NSFont.systemFontSize weight:NSFontWeightMedium];
	[(ThumbCell *)cell restyle]; // fixed label colour from the start
	ThumbView *tv = [ThumbView new];
	tv.translatesAutoresizingMaskIntoConstraints = NO;
	[cell addSubview:tv];
	((ThumbCell *)cell).thumb = tv;
	[NSLayoutConstraint activateConstraints:@[
		[tv.topAnchor constraintEqualToAnchor:cell.topAnchor],
		[tv.centerXAnchor constraintEqualToAnchor:cell.centerXAnchor],
		[tv.widthAnchor constraintEqualToConstant:kThumbW + 2 * kRingPad],
		[tv.heightAnchor constraintEqualToConstant:kThumbH + 2 * kRingPad],
		[label.topAnchor constraintEqualToAnchor:tv.bottomAnchor constant:kLabelGap - kRingPad],
			[label.heightAnchor constraintEqualToConstant:kLabelH],
		[label.centerXAnchor constraintEqualToAnchor:cell.centerXAnchor],
	]];
	return cell;
}

- (NSView *)tableView:(NSTableView *)t viewForTableColumn:(NSTableColumn *)col row:(NSInteger)row
{
	ThumbCell *cell = (ThumbCell *)MakeCell(t, @"thumb", YES);
	cell.textField.stringValue = self.pageLabels ? self.pageLabels[row] : [NSString stringWithFormat:@"%ld", row + 1];
	NSImage *img = [self.thumbCache objectForKey:@(row)];
	CGFloat s = self.window.backingScaleFactor ?: 2;
	if (!img && self.thumbDir) {
		CGImageRef c = LoadThumbFile([self thumbFile:(int)row scale:s]);
		if (c) {
			img = ThumbImage(c, s);
			[self.thumbCache setObject:img forKey:@(row) cost:CGImageGetBytesPerRow(c) * CGImageGetHeight(c)];
			CGImageRelease(c);
		}
	}
	cell.thumb.image = img;
	[self markCurrent:cell row:(int)row];
	if (!img &&![self.thumbPending containsIndex:row]) {
		// Make sure the worker sees this row as visible even before the first scroll.
		NSRange r = [t rowsInRect:t.visibleRect];
		visLo = MIN((int)r.location, (int)row);
		visHi = MAX((int)NSMaxRange(r) - 1, (int)row);
		[self.thumbPending addIndex:row];
		Enqueue(self, (int)row, kJobThumb, (int)(kThumbW * s), (int)(kThumbH * s));
	}
	return cell;
}

- (NSTableRowView *)tableView:(NSTableView *)t rowViewForRow:(NSInteger)row
{
	return t == self.thumbs ? [ThumbRowView new] : nil;
}

// --- TOC outline -----------------------------------------------------------

- (NSInteger)outlineView:(NSOutlineView *)o numberOfChildrenOfItem:(TocItem *)item
{
	return item ? item.kids.count : self.tocRoots.count;
}
- (id)outlineView:(NSOutlineView *)o child:(NSInteger)i ofItem:(TocItem *)item
{
	return item ? item.kids[i] : self.tocRoots[i];
}
- (BOOL)outlineView:(NSOutlineView *)o isItemExpandable:(TocItem *)item { return item.kids.count > 0; }

- (NSView *)outlineView:(NSOutlineView *)o viewForTableColumn:(NSTableColumn *)col item:(TocItem *)item
{
	NSTableCellView *cell = MakeCell(o, @"toc", NO);
	cell.textField.stringValue = item.title;
	cell.toolTip = item.title;
	return cell;
}

- (void)outlineViewSelectionDidChange:(NSNotification *)note
{
	TocItem *item = [self.toc itemAtRow:self.toc.selectedRow];
	if (item && item.page >= 0) [self goToPage:item.page];
}

// --- export & print --------------------------------------------------------

- (NSIndexSet *)selectedPages
{
	NSIndexSet *sel = self.thumbs.selectedRowIndexes;
	return sel.count ? sel : [NSIndexSet indexSetWithIndex:current];
}

// Copies the given pages (document order) into a new PDF. Lossless: objects are grafted, not re-rendered.
- (BOOL)writePages:(NSIndexSet *)pages to:(NSString *)out error:(NSString **)err
{
	DocLock lock;
	if (!pdf) return NO;
	__block std::vector<int> list;
	[pages enumerateIndexesUsingBlock:^(NSUInteger i, BOOL *) { list.push_back((int)i); }];
	pdf_document *dst = NULL;
	pdf_graft_map *map = NULL;
	BOOL ok = YES;
	fz_var(dst);
	fz_var(map);
	fz_var(ok);
	fz_try(g_ctx) {
		dst = pdf_create_document(g_ctx);
		map = pdf_new_graft_map(g_ctx, dst);
		for (size_t i = 0; i < list.size(); i++)
			pdf_graft_mapped_page(g_ctx, map, -1, pdf, list[i]);
		pdf_write_options opts = pdf_default_write_options;
		opts.do_garbage = 1;
		opts.do_compress = 1;
		pdf_save_document(g_ctx, dst, out.fileSystemRepresentation, &opts);
	}
	fz_always(g_ctx) {
		pdf_drop_graft_map(g_ctx, map);
		pdf_drop_document(g_ctx, dst);
	}
	fz_catch(g_ctx) {
		ok = NO;
		if (err) *err = [NSString stringWithUTF8String:fz_caught_message(g_ctx)];
	}
	return ok;
}

- (void)showError:(NSString *)msg
{
	NSAlert *a = [NSAlert new];
	a.messageText = msg ?: @"Unknown error";
	[a beginSheetModalForWindow:self.window completionHandler:nil];
}

- (IBAction)exportSelection:(id)sender
{
	NSIndexSet *pages = self.selectedPages;
	NSSavePanel *p = [NSSavePanel savePanel];
	p.allowedContentTypes = @[ UTTypePDF ];
	p.nameFieldStringValue = [NSString stringWithFormat:@"%@ (p. %@).pdf",
	                                   self.path.lastPathComponent.stringByDeletingPathExtension, RangeString(pages)];
	[p beginSheetModalForWindow:self.window completionHandler:^(NSModalResponse r) {
		if (r != NSModalResponseOK) return;
		NSString *err = nil;
		if (![self writePages:pages to:p.URL.path error:&err]) [self showError:err];
	}];
}

// Cmd-C: writes the selected pages to a fresh temp folder and puts that file on the clipboard,
// so it can be pasted into Finder, Mail, chat apps, etc. The previous copy's folder is removed.
- (IBAction)copy:(id)sender
{
	static NSString *lastDir;
	NSIndexSet *pages = self.selectedPages;
	NSString *dir = [NSTemporaryDirectory() stringByAppendingPathComponent:
	                 [NSString stringWithFormat:@"leanpdf-copy-%@", NSUUID.UUID.UUIDString]];
	NSString *out = [dir stringByAppendingPathComponent:[NSString stringWithFormat:@"%@ (p. %@).pdf",
	                 self.path.lastPathComponent.stringByDeletingPathExtension, RangeString(pages)]];
	NSError *e = nil;
	if (![NSFileManager.defaultManager createDirectoryAtPath:dir withIntermediateDirectories:YES attributes:nil error:&e]) {
		[self showError:e.localizedDescription];
		return;
	}
	NSString *err = nil;
	if (![self writePages:pages to:out error:&err]) {
		[NSFileManager.defaultManager removeItemAtPath:dir error:nil];
		[self showError:err];
		return;
	}
	NSPasteboard *pb = NSPasteboard.generalPasteboard;
	[pb clearContents];
	[pb writeObjects:@[ [NSURL fileURLWithPath:out] ]];
	if (lastDir) [NSFileManager.defaultManager removeItemAtPath:lastDir error:nil];
	lastDir = dir;
}

// Sends the selected pages to Mistral OCR, or the whole document when nothing is selected, and puts
// the result on the clipboard as Markdown. Progress and errors show in the sidebar's status panel.
- (IBAction)copyOCRText:(id)sender
{
	NSString *key = LoadAPIKey();
	if (!key) {
		[NSApp sendAction:@selector(showSettings:) to:nil from:self];
		return;
	}
	NSIndexSet *sel = self.thumbs.selectedRowIndexes;
	NSIndexSet *pages = sel.count ? sel : [NSIndexSet indexSetWithIndexesInRange:NSMakeRange(0, count)];
	if (pages.count <= kOCRConfirmOver) { [self runOCR:pages key:key]; return; }
	NSAlert *a = [NSAlert new];
	a.messageText = [NSString stringWithFormat:@"Run OCR on %lu pages?", pages.count];
	a.informativeText = sel.count ? @"Mistral bills OCR per page."
	                              : @"No pages are selected, so the whole document will be sent. Mistral bills OCR per page.";
	[a addButtonWithTitle:@"Run OCR"];
	[a addButtonWithTitle:@"Cancel"];
	[a beginSheetModalForWindow:self.window completionHandler:^(NSModalResponse r) {
		if (r == NSAlertFirstButtonReturn) [self runOCR:pages key:key];
	}];
}

- (void)runOCR:(NSIndexSet *)pages key:(NSString *)key
{
	if (self.ocrJob || !pdf || !pages.count) return;
	OCRJob *job = [OCRJob new];
	job.key = key;
	NSMutableArray *list = [NSMutableArray array], *results = [NSMutableArray array];
	for (NSUInteger i = pages.firstIndex; i != NSNotFound; i = [pages indexGreaterThanIndex:i]) {
		[list addObject:@(i)];
		[results addObject:NSNull.null];
	}
	job.pages = list;
	job.results = results;
	job.tasks = [NSMutableSet set];
	self.ocrJob = job;

	NSString *what = pages.count == (NSUInteger)count && count > 1 ? [NSString stringWithFormat:@"all %d pages", count]
	               : [NSString stringWithFormat:@"%@ %@", pages.count == 1 ? @"page" : @"pages", RangeString(pages)];
	[self.ocrStatus running:[@"OCR · " stringByAppendingString:what] total:list.count];
	[self showOCRStatus:YES];
	[self pumpOCR:job];
}

// Keeps up to kOCRParallel page requests in flight.
- (void)pumpOCR:(OCRJob *)job
{
	while (self.ocrJob == job && job.next < job.pages.count && job.tasks.count + job.waiting < kOCRParallel)
		[self sendOCR:job index:job.next++ attempt:0];
}

- (void)sendOCR:(OCRJob *)job index:(NSUInteger)k attempt:(int)attempt
{
	NSString *tmp = [NSTemporaryDirectory() stringByAppendingPathComponent:
	                 [NSString stringWithFormat:@"leanpdf-ocr-%@.pdf", NSUUID.UUID.UUIDString]];
	NSString *err = nil;
	BOOL ok = [self writePages:[NSIndexSet indexSetWithIndex:job.pages[k].unsignedIntegerValue] to:tmp error:&err];
	NSData *pdfData = ok ? [NSData dataWithContentsOfFile:tmp] : nil;
	[NSFileManager.defaultManager removeItemAtPath:tmp error:nil];
	if (!pdfData) { [self failOCR:job index:k message:err ?: @"Couldn't write the page for OCR."]; return; }

	__block __weak NSURLSessionDataTask *weakTask;
	NSURLSessionDataTask *task = [NSURLSession.sharedSession dataTaskWithRequest:OCRRequest(pdfData, job.key)
	                                                           completionHandler:^(NSData *data, NSURLResponse *resp, NSError *e) {
		NSURLSessionDataTask *t = weakTask;
		NSInteger status = [(NSHTTPURLResponse *)resp statusCode];
		id json = data ? [NSJSONSerialization JSONObjectWithData:data options:0 error:nil] : nil;
		NSString *md = nil, *fail = nil;
		if (e) fail = e.localizedDescription;
		else if (status != 200 || ![json isKindOfClass:NSDictionary.class]) fail = OCRErrorMessage(status, json, data);
		else md = OCRPagesMarkdown(json);
		dispatch_async(dispatch_get_main_queue(), ^{
			if (self.ocrJob != job) return; // cancelled, failed or window closed
			if (t) [job.tasks removeObject:t];
			if (status == 429 && attempt < 3) { // rate limited: back off and try this page again
				job.waiting++;
				dispatch_after(dispatch_time(DISPATCH_TIME_NOW, (int64_t)(2 << attempt) * NSEC_PER_SEC), dispatch_get_main_queue(), ^{
					job.waiting--;
					if (self.ocrJob == job) [self sendOCR:job index:k attempt:attempt + 1];
				});
				return;
			}
			if (fail) { [self failOCR:job index:k message:fail]; return; }
			job.results[k] = md;
			job.done++;
			[self.ocrStatus progress:job.done total:job.pages.count];
			if (job.done == job.pages.count) [self finishOCR:job];
			else [self pumpOCR:job];
		});
	}];
	weakTask = task;
	[job.tasks addObject:task];
	[task resume];
}

- (void)finishOCR:(OCRJob *)job
{
	self.ocrJob = nil;
	NSString *md = OCRClean([job.results componentsJoinedByString:@"\n\n"]);
	if (md.length) {
		NSPasteboard *pb = NSPasteboard.generalPasteboard;
		[pb clearContents];
		[pb setString:md forType:NSPasteboardTypeString];
		[self.ocrStatus success:[NSString stringWithFormat:@"Copied %@ characters",
		                         [NSNumberFormatter localizedStringFromNumber:@(md.length) numberStyle:NSNumberFormatterDecimalStyle]]];
	} else {
		[self.ocrStatus success:@"No text found"];
	}
	OCRStatusView *status = self.ocrStatus;
	NSString *shown = status.title.stringValue;
	dispatch_after(dispatch_time(DISPATCH_TIME_NOW, 3 * NSEC_PER_SEC), dispatch_get_main_queue(), ^{
		// Only hide this result: not a newer run or an error that replaced it.
		if (!self.ocrJob && !status.bar.failed && [status.title.stringValue isEqualToString:shown]) [self showOCRStatus:NO];
	});
}

- (void)failOCR:(OCRJob *)job index:(NSUInteger)k message:(NSString *)msg
{
	[self cancelOCR];
	if (job.pages.count > 1) msg = [NSString stringWithFormat:@"Page %lu: %@", job.pages[k].unsignedIntegerValue + 1, msg];
	[self.ocrStatus failure:msg];
	[self showOCRStatus:YES];
}

- (void)cancelOCR
{
	for (NSURLSessionDataTask *t in self.ocrJob.tasks) [t cancel];
	self.ocrJob = nil;
}

// The panel's ✕: cancels a run in progress, or dismisses a finished one.
- (IBAction)closeOCRStatus:(id)sender
{
	[self cancelOCR];
	[self showOCRStatus:NO];
}

- (void)showOCRStatus:(BOOL)show
{
	if (self.ocrStatus.hidden == !show) return;
	self.ocrStatus.hidden = !show;
	[NSLayoutConstraint deactivateConstraints:show ? self.listsToBottom : self.listsToStatus];
	[NSLayoutConstraint activateConstraints:show ? self.listsToStatus : self.listsToBottom];
}

// Prints the selected pages, or the whole document when only one page is selected.
- (IBAction)printDocument:(id)sender
{
	NSIndexSet *pages = self.thumbs.selectedRowIndexes;
	if (pages.count <= 1) pages = [NSIndexSet indexSetWithIndexesInRange:NSMakeRange(0, count)];
	NSString *tmp = [NSTemporaryDirectory() stringByAppendingPathComponent:
	                 [NSString stringWithFormat:@"leanpdf-print-%@.pdf", NSUUID.UUID.UUIDString]];
	NSString *err = nil;
	if (![self writePages:pages to:tmp error:&err]) { [self showError:err]; return; }
	self.printDoc = [[PDFDocument alloc] initWithURL:[NSURL fileURLWithPath:tmp]];
	NSPrintOperation *op = [self.printDoc printOperationForPrintInfo:NSPrintInfo.sharedPrintInfo
	                                                     scalingMode:kPDFPrintPageScaleToFit autoRotate:YES];
	op.jobTitle = self.window.title;
	[op runOperationModalForWindow:self.window delegate:self
	                didRunSelector:@selector(printDone:success:context:) contextInfo:(__bridge_retained void *)tmp];
}

- (void)printDone:(NSPrintOperation *)op success:(BOOL)ok context:(void *)ctx
{
	NSString *tmp = (__bridge_transfer NSString *)ctx;
	self.printDoc = nil;
	[NSFileManager.defaultManager removeItemAtPath:tmp error:nil];
}

- (BOOL)validateMenuItem:(NSMenuItem *)item
{
	if (item.action == @selector(toggleSidebarFromMenu:)) {
		item.title = self.sideItem.collapsed ? @"Show Sidebar" : @"Hide Sidebar";
		return YES;
	}
	if (item.action == @selector(switchSidebar:)) {
		BOOL toc = item.tag == 1;
		item.state = !self.sideItem.collapsed && toc == self.thumbScroll.hidden ? NSControlStateValueOn : NSControlStateValueOff;
		return !toc || self.tocRoots != nil;
	}
	if (item.action == @selector(exportSelection:) || item.action == @selector(printDocument:) || item.action == @selector(copy:))
		return pdf != NULL;
	if (item.action == @selector(copyOCRText:)) return pdf != NULL && !self.ocrJob;
	if (item.action == @selector(zoomIn:)) return self.pageView.zoom < kZoomMax - 1e-3;
	if (item.action == @selector(zoomOut:) || item.action == @selector(resetZoom:)) return self.pageView.zoom > 1.001;
	if (item.action == @selector(nextPage:) || item.action == @selector(lastPage:)) return current + 1 < count;
	if (item.action == @selector(previousPage:) || item.action == @selector(firstPage:)) return current > 0;
	return YES;
}

// --- idling ----------------------------------------------------------------

- (void)windowDidBecomeKey:(NSNotification *)note
{
	BOOL wasDormant = dormant;
	[self touch];
	if (wasDormant) [self.pageView reload]; // re-render the page and prefetch its neighbours
}

- (void)windowDidResignKey:(NSNotification *)note { [self startIdleTimer]; }

// The window is being used. It stays awake while key, or for kIdleDelay after its last use.
- (void)touch
{
	dormant = false;
	if (self.window.isKeyWindow) {
		[self.idleTimer invalidate];
		self.idleTimer = nil;
	} else {
		[self startIdleTimer];
	}
}

- (void)startIdleTimer
{
	[self.idleTimer invalidate];
	self.idleTimer = nil;
	if (g_viewers.count <= kIdleMinDocs) return;
	__weak Viewer *weak = self;
	self.idleTimer = [NSTimer scheduledTimerWithTimeInterval:kIdleDelay repeats:NO block:^(NSTimer *) {
		[weak goDormant];
	}];
	self.idleTimer.tolerance = 10;
}

- (void)goDormant
{
	[self.idleTimer invalidate];
	self.idleTimer = nil;
	if (dormant) return;
	dormant = true;
	@synchronized(g_jobs) {
		NSIndexSet *mine = [g_jobs indexesOfObjectsPassingTest:^BOOL(Job *j, NSUInteger, BOOL *) {
			return j->viewer == self && j->kind != kJobThumb;
		}];
		[g_jobs removeObjectsAtIndexes:mine];
	}
	{
		DocLock lock;
		for (auto &e : pageCache) CGImageRelease(e.second.img);
		pageCache.clear();
	}
	[self dropDetails];
	[self.pageView dropCache];
	[self.thumbCache removeAllObjects];
	ReleaseMemory();
}

// --- lifetime --------------------------------------------------------------

- (void)windowWillClose:(NSNotification *)note
{
	[NSNotificationCenter.defaultCenter removeObserver:self];
	[self.idleTimer invalidate];
	self.idleTimer = nil;
	[self cancelOCR];
	{
		DocLock lock;
		for (auto &e : pageCache) CGImageRelease(e.second.img);
		pageCache.clear();
		detailCache.clear();
		fz_drop_document(g_ctx, doc);
		doc = NULL;
		pdf = NULL;
	}
	self.pageView.viewer = nil;
	[g_viewers removeObject:self];
	UpdateIdleTimers();
	ReleaseMemory();
}

@end

// ---------------------------------------------------------------------------



// Idling only pays off with many documents open. Crossing kIdleMinDocs starts the countdown in
// every background window; dropping back to it stops them. Dormant windows stay so until used.
static void UpdateIdleTimers()
{
	BOOL many = g_viewers.count > kIdleMinDocs;
	for (Viewer *v in g_viewers) {
		if (!many) {
			[v.idleTimer invalidate];
			v.idleTimer = nil;
		} else if (!v.window.isKeyWindow && !v->dormant && !v.idleTimer) {
			[v startIdleTimer];
		}
	}
}

// Once every window is idle, MuPDF's cache of fonts and decoded images goes too. Freed memory
// is then handed back to the system so the app's footprint actually shrinks.
static void ReleaseMemory()
{
	BOOL allIdle = YES;
	for (Viewer *v in g_viewers)
		if (!v->dormant) allIdle = NO;
	if (allIdle) {
		DocLock lock;
		fz_empty_store(g_ctx);
	}
	malloc_zone_pressure_relief(NULL, 0);
}

// When the system runs short of memory, background windows go dormant right away.
static void OnMemoryPressure()
{
	for (Viewer *v in [g_viewers copy])
		if (!v.window.isKeyWindow) [v goDormant];
	{
		DocLock lock;
		fz_shrink_store(g_ctx, 50);
	}
	malloc_zone_pressure_relief(NULL, 0);
}

static void OpenURL(NSURL *url)
{
	NSString *path = url.URLByResolvingSymlinksInPath.path;
	for (Viewer *v in g_viewers)
		if ([v.path isEqualToString:path]) { [v.window makeKeyAndOrderFront:nil]; return; }
	NSString *err = nil;
	Viewer *v = [Viewer viewerWithPath:path error:&err];
	if (!v) {
		NSAlert *a = [NSAlert new];
		a.messageText = [NSString stringWithFormat:@"Couldn't open “%@”", path.lastPathComponent];
		a.informativeText = err ?: @"";
		[a runModal];
		return;
	}
	if (g_viewers.count) {
		NSWindow *top = g_viewers.anyObject.window;
		[v.window setFrameTopLeftPoint:NSMakePoint(NSMinX(top.frame) + 24, NSMaxY(top.frame) - 24)];
	}
	[g_viewers addObject:v];
	[v.window makeKeyAndOrderFront:nil];
	UpdateIdleTimers();
	[NSDocumentController.sharedDocumentController noteNewRecentDocumentURL:url];
}

@interface AppDelegate : NSObject <NSApplicationDelegate, NSWindowDelegate>
@property (strong) NSWindow *settings;
@property (strong) NSSecureTextField *keyField;
@end

@implementation AppDelegate

// Settings: the Mistral API key, saved to the keychain when editing ends or the window closes.
- (IBAction)showSettings:(id)sender
{
	if (!self.settings) {
		self.keyField = [NSSecureTextField new];
		self.keyField.placeholderString = @"Paste your API key";
		self.keyField.target = self;
		self.keyField.action = @selector(saveKey:);
		self.keyField.cell.sendsActionOnEndEditing = YES;
		[self.keyField.widthAnchor constraintEqualToConstant:300].active = YES;
		NSStackView *row = [NSStackView stackViewWithViews:@[ [NSTextField labelWithString:@"Mistral API key:"], self.keyField ]];
		row.spacing = 8;
		NSTextField *note = [NSTextField wrappingLabelWithString:@"Used for Copy Text with OCR. Stored in your login keychain."];
		note.font = [NSFont systemFontOfSize:NSFont.smallSystemFontSize];
		note.textColor = NSColor.secondaryLabelColor;
		NSStackView *content = [NSStackView stackViewWithViews:@[ row, note ]];
		content.orientation = NSUserInterfaceLayoutOrientationVertical;
		content.alignment = NSLayoutAttributeLeading;
		content.spacing = 8;
		content.edgeInsets = NSEdgeInsetsMake(20, 20, 20, 20);
		[note.widthAnchor constraintEqualToAnchor:row.widthAnchor].active = YES;

		self.settings = [[NSWindow alloc] initWithContentRect:NSZeroRect
		                                            styleMask:NSWindowStyleMaskTitled | NSWindowStyleMaskClosable
		                                              backing:NSBackingStoreBuffered defer:YES];
		self.settings.title = @"Settings";
		self.settings.releasedWhenClosed = NO;
		self.settings.delegate = self;
		self.settings.contentView = content;
		[self.settings setContentSize:content.fittingSize];
		[self.settings center];
	}
	self.keyField.stringValue = LoadAPIKey() ?: @"";
	[self.settings makeKeyAndOrderFront:nil];
	[self.settings makeFirstResponder:self.keyField];
}

- (void)saveKey:(id)sender { SaveAPIKey(self.keyField.stringValue); }

- (void)windowWillClose:(NSNotification *)n
{
	if (n.object != self.settings) return;
	[self.settings makeFirstResponder:nil];
	[self saveKey:nil];
}

- (void)application:(NSApplication *)app openURLs:(NSArray<NSURL *> *)urls
{
	for (NSURL *u in urls) OpenURL(u);
}

- (IBAction)openDocument:(id)sender
{
	NSOpenPanel *p = [NSOpenPanel openPanel];
	p.allowedContentTypes = @[ UTTypePDF ];
	p.allowsMultipleSelection = YES;
	if ([p runModal] == NSModalResponseOK)
		for (NSURL *u in p.URLs) OpenURL(u);
}

- (void)applicationDidFinishLaunching:(NSNotification *)n
{
	dispatch_after(dispatch_time(DISPATCH_TIME_NOW, 10 * NSEC_PER_SEC), dispatch_get_global_queue(QOS_CLASS_BACKGROUND, 0), ^{
		PruneThumbCache();
	});
	[NSApp activateIgnoringOtherApps:YES];
	if (!g_viewers.count)
		dispatch_async(dispatch_get_main_queue(), ^{ if (!g_viewers.count) [self openDocument:nil]; });
}

- (BOOL)applicationShouldTerminateAfterLastWindowClosed:(NSApplication *)app { return YES; }

@end

static NSMenuItem *Item(NSMenu *m, NSString *title, SEL action, NSString *key, NSEventModifierFlags mods = NSEventModifierFlagCommand)
{
	NSMenuItem *i = [m addItemWithTitle:title action:action keyEquivalent:key];
	i.keyEquivalentModifierMask = mods;
	return i;
}

static NSMenu *Submenu(NSMenu *bar, NSString *title)
{
	NSMenu *m = [[NSMenu alloc] initWithTitle:title];
	[bar addItemWithTitle:title action:nil keyEquivalent:@""].submenu = m;
	return m;
}

static void BuildMenus()
{
	NSMenu *bar = [NSMenu new];
	NSMenu *app = Submenu(bar, @"LeanPDF");
	Item(app, @"About LeanPDF", @selector(orderFrontStandardAboutPanel:), @"");
	[app addItem:NSMenuItem.separatorItem];
	Item(app, @"Settings…", @selector(showSettings:), @",");
	[app addItem:NSMenuItem.separatorItem];
	Item(app, @"Hide LeanPDF", @selector(hide:), @"h");
	Item(app, @"Hide Others", @selector(hideOtherApplications:), @"h", NSEventModifierFlagCommand | NSEventModifierFlagOption);
	Item(app, @"Show All", @selector(unhideAllApplications:), @"");
	[app addItem:NSMenuItem.separatorItem];
	Item(app, @"Quit LeanPDF", @selector(terminate:), @"q");

	NSMenu *file = Submenu(bar, @"File");
	Item(file, @"Open…", @selector(openDocument:), @"o");
	Item(file, @"Close", @selector(performClose:), @"w");
	[file addItem:NSMenuItem.separatorItem];
	Item(file, @"Export Selected Pages…", @selector(exportSelection:), @"e", NSEventModifierFlagCommand | NSEventModifierFlagShift);
	Item(file, @"Print…", @selector(printDocument:), @"p");

	NSMenu *edit = Submenu(bar, @"Edit");
	Item(edit, @"Copy Selected Pages", @selector(copy:), @"c");
	Item(edit, @"Copy Text with OCR", @selector(copyOCRText:), @"c", NSEventModifierFlagCommand | NSEventModifierFlagShift);
	Item(edit, @"Select All", @selector(selectAll:), @"a");

	NSMenu *view = Submenu(bar, @"View");
	Item(view, @"Zoom In", @selector(zoomIn:), @"+");
	NSMenuItem *zoomIn = Item(view, @"Zoom In", @selector(zoomIn:), @"="); // ⌘= without Shift
	zoomIn.hidden = YES;
	zoomIn.allowsKeyEquivalentWhenHidden = YES;
	Item(view, @"Zoom Out", @selector(zoomOut:), @"-");
	Item(view, @"Reset Zoom", @selector(resetZoom:), @"0");
	[view addItem:NSMenuItem.separatorItem];
	Item(view, @"Toggle Sidebar", @selector(toggleSidebar:), @"s", NSEventModifierFlagCommand | NSEventModifierFlagOption);
	Item(view, @"Enter Full Screen", @selector(toggleFullScreen:), @"f", NSEventModifierFlagCommand | NSEventModifierFlagControl);

	NSMenu *go = Submenu(bar, @"Go");
	Item(go, @"Previous Page", @selector(previousPage:), @"", NSEventModifierFlagOption | NSEventModifierFlagCommand);
	Item(go, @"Next Page", @selector(nextPage:), @"", NSEventModifierFlagOption | NSEventModifierFlagCommand);
	Item(go, @"First Page", @selector(firstPage:), @"", 0);
	Item(go, @"Last Page", @selector(lastPage:), @"", 0);
	[go addItem:NSMenuItem.separatorItem];
	Item(go, @"Go to Page…", @selector(goToPageNumber:), @"g", NSEventModifierFlagCommand | NSEventModifierFlagOption);

	NSMenu *win = Submenu(bar, @"Window");
	Item(win, @"Minimize", @selector(performMiniaturize:), @"m");
	Item(win, @"Zoom", @selector(performZoom:), @"");
	NSApp.windowsMenu = win;
	NSApp.mainMenu = bar;
}

int main(int argc, const char **argv)
{
	@autoreleasepool {
		for (auto &m : g_fz_locks) pthread_mutex_init(&m, NULL);
		fz_locks_context locks = {NULL, fz_lock_cb, fz_unlock_cb};
		// Decoded images and fonts, shared by every window. Enough for a page and its neighbours.
		g_ctx = fz_new_context(NULL, &locks, 96 << 20);
		if (!g_ctx) return 1;
		fz_register_document_handlers(g_ctx);
		g_worker_ctx = fz_clone_context(g_ctx);
		g_viewers = [NSMutableSet set];
		g_jobs = [NSMutableArray array];
		g_jobSem = dispatch_semaphore_create(0);

		NSThread *worker = [[NSThread alloc] initWithBlock:^{
			for (;;) {
				dispatch_semaphore_wait(g_jobSem, DISPATCH_TIME_FOREVER);
				Job *j = nil;
				@synchronized(g_jobs) {
					j = g_jobs.lastObject;
					if (j) [g_jobs removeLastObject];
				}
				@autoreleasepool {
					Viewer *v = j ? j->viewer : nil;
					if (v) [v runJob:j];
				}
			}
		}];
		worker.qualityOfService = NSQualityOfServiceUserInitiated;
		[worker start];

		static dispatch_source_t pressure = dispatch_source_create(DISPATCH_SOURCE_TYPE_MEMORYPRESSURE, 0,
			DISPATCH_MEMORYPRESSURE_WARN | DISPATCH_MEMORYPRESSURE_CRITICAL, dispatch_get_main_queue());
		dispatch_source_set_event_handler(pressure, ^{ OnMemoryPressure(); });
		dispatch_resume(pressure);

		NSApplication *app = NSApplication.sharedApplication;
		AppDelegate *delegate = [AppDelegate new];
		app.delegate = delegate;
		BuildMenus();
		// Plain command-line paths (when run as LeanPDF.app/Contents/MacOS/LeanPDF file.pdf).
		for (int i = 1; i < argc; i++)
			if (argv[i][0] != '-' && [NSFileManager.defaultManager fileExistsAtPath:@(argv[i])])
				dispatch_async(dispatch_get_main_queue(), ^{ OpenURL([NSURL fileURLWithPath:@(argv[i])]); });
		[app run];
	}
	return 0;
}
