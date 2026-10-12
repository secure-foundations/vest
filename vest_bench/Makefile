VEST    := cargo run --locked --manifest-path ../Cargo.toml -p vest --

FORMATS := flat table nest tlv varint bits bounded_list tail_list
REAL_BENCHES := tls bitcoin cms cbor

.PHONY: generate test smoke bench bench-formats bench-real report help all

# Regenerate every format module from its schema.
generate:
	@for f in $(FORMATS); do \
		echo "  $$f"; \
		$(VEST) formats/$$f.vest -o src/generated/$$f.rs || exit 1; \
	done

# Layout parity and wire compatibility against the hand-written baselines.
test:
	cargo test --locked --release
	python3 -B -m unittest discover -s scripts/tests -t scripts

# Compile every benchmark and run its validation/setup once.
smoke:
	cargo bench --locked --no-run
	@for b in formats $(REAL_BENCHES); do \
		echo "== $$b =="; \
		cargo bench --locked --bench $$b -- --test || exit 1; \
	done

# One recorded run, one implementation/group per process, randomized order.
bench:
	python3 -B scripts/run.py --allocations $(TARGETS) $(RUN_ARGS)

# One process per microformat. Override FORMATS to measure a subset, e.g.
#   make bench-formats FORMATS="bounded_list tail_list"
bench-formats:
	python3 -B scripts/run.py --allocations $(FORMATS) $(RUN_ARGS)
	@$(MAKE) --no-print-directory report

# One process per implementation/group, not one process for the whole family.
bench-real:
	python3 -B scripts/run.py --allocations $(REAL_BENCHES) $(RUN_ARGS)

# Reprint the collected results without re-measuring.
report:
	@python3 -B scripts/report.py $(TARGETS) $(REPORT_ARGS)

help:
	@echo 'make test / smoke       validate codecs, scripts, and benchmark setup'
	@echo 'make bench              run all comparisons and untimed allocation audits'
	@echo 'make bench TARGETS=cms  run one family; RUN_ARGS="--offline --seed 1234"'
	@echo 'make report             report the latest non-quick run without measuring'

all: generate test smoke bench
