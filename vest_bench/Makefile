VEST    := cargo run --locked --manifest-path ../Cargo.toml -p vest --

FORMATS := flat table nest tlv varint bits bounded_list tail_list
REAL_BENCHES := tls bitcoin cms cbor

.PHONY: generate test smoke bench bench-formats bench-real report all

# Regenerate every format module from its schema.
generate:
	@for f in $(FORMATS); do \
		echo "  $$f"; \
		$(VEST) formats/$$f.vest -o src/$$f.rs; \
	done

# Layout parity and wire compatibility against the hand-written baselines.
test:
	cargo test --locked --release

# Compile every benchmark and run its validation/setup once.
smoke:
	cargo bench --locked --no-run
	@for b in formats $(REAL_BENCHES); do \
		echo "== $$b =="; \
		cargo bench --locked --bench $$b -- --test || exit 1; \
	done

# Run microformats and real formats.
bench: bench-formats bench-real

# One process per microformat. Override FORMATS to measure a subset, e.g.
#   make bench-formats FORMATS="bounded_list tail_list"
bench-formats:
	@for f in $(FORMATS); do \
		echo "== $$f =="; \
		cargo bench --locked --bench formats -- "$$f/" >/dev/null 2>&1 || exit 1; \
	done
	@$(MAKE) --no-print-directory report

# One process per real-world benchmark family.
bench-real:
	@for b in $(REAL_BENCHES); do \
		echo "== $$b =="; \
		cargo bench --locked --bench $$b || exit 1; \
	done

# Reprint the collected results without re-measuring.
report:
	@python3 report.py $(TARGETS)

all: generate test smoke bench
