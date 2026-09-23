VEST    := cargo run --locked --manifest-path ../Cargo.toml -p vest --

FORMATS := flat table nest tlv varint bits bounded_list tail_list

.PHONY: generate test bench report all

# Regenerate every format module from its schema.
generate:
	@for f in $(FORMATS); do \
		echo "  $$f"; \
		$(VEST) formats/$$f.vest -o src/$$f.rs; \
	done

# Layout parity and wire compatibility against the hand-written baselines.
test:
	cargo test --locked --release

# One process per format. Override FORMATS to measure a subset, e.g.
#   make bench FORMATS="bounded_list tail_list"
bench:
	@for f in $(FORMATS); do \
		echo "== $$f =="; \
		cargo bench --locked --bench formats -- "$$f/" >/dev/null 2>&1 || exit 1; \
	done
	@$(MAKE) --no-print-directory report

# Reprint the collected results without re-measuring.
report:
	@python3 report.py $(FORMATS)

all: generate test bench
