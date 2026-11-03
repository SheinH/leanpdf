// PGO training: renders a PDF through LeanPDF's own render functions, the way the app does,
// with MuPDF built for profiling. Run by `make pgo-train`.
//   pages fit to the window   RenderPage, RGB, drawn in parallel strips
//   zoomed in                 RenderDetail, BGRA with alpha, in strips
//   thumbnails                RenderPage at thumbnail size, drawn directly
// The scan fast path is off so MuPDF's own image drawing is trained too.
#define main leanpdf_main
#include "../main.mm"
#undef main

int main(int argc, const char **argv)
{
	if (argc < 2) {
		fprintf(stderr, "usage: train file.pdf\n");
		return 1;
	}
	for (auto &m : g_fz_locks) pthread_mutex_init(&m, NULL);
	fz_locks_context locks = {NULL, fz_lock_cb, fz_unlock_cb};
	fz_context *ctx = fz_new_context(NULL, &locks, 96 << 20);
	fz_register_document_handlers(ctx);
	fz_set_warning_callback(ctx, [](void *, const char *) {}, NULL);
	fz_document *doc = fz_open_document(ctx, argv[1]);
	int count = fz_count_pages(ctx, doc);
	g_fast_scans = false;
	auto progress = [&](const char *what, int n, int of) {
		if (n % 50 == 0 || n == of - 1) fprintf(stderr, "\rtraining: %s %d/%d   %s", what, n + 1, of, n == of - 1 ? "\n" : "");
	};
	for (int n = 0; n < count; n++) {
		CGImageRelease(RenderPage(ctx, doc, n, 1700, 2200));
		progress("pages", n, count);
	}
	for (int n = 0; n < count && n < 300; n++) {
		progress("zoomed", n, MIN(count, 300));
		NSRect region = NSMakeRect(100, 150, 500, 600), placed;
		NSSize size;
		CGImageRelease(RenderDetail(ctx, doc, n, 1700, 2200, 2.5, 2, false, NSZeroSize, &region, &placed, &size));
	}
	for (int n = 0; n < count; n++) {
		CGImageRelease(RenderPage(ctx, doc, n, 260, 320));
		progress("thumbnails", n, count);
	}
	fz_drop_document(ctx, doc);
	fz_drop_context(ctx);
	return 0;
}
