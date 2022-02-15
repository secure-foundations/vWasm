TOPLEVEL=t
DIRS=dependencies common semantics compiler parser

all: wasi-integration/target/release/libwasi.a
	@$(MAKE) verify
	@echo "Finished verifying. Now building application."
	@$(MAKE) build-main.native
	@echo "Finished building."

include scripts/Makefile.dir

build-main.native: extract

wasi-integration/target/release/libwasi.a:
	(cd wasi-integration && cargo build --release)
