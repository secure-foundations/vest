VEST    := cargo run --locked --manifest-path ../Cargo.toml -p vest --

.PHONY: help generate test smoke list bench report

help:
	@echo "make generate   Regenerate the microformat codecs"
	@echo "make test       Run release codec/corpus and Python tests"
	@echo "make smoke      Validate every benchmark without measuring"
	@echo "make list       List workloads, item counts, and input byte counts"
	@echo "make bench      Measure the whole suite and audit allocations"
	@echo "make report     Report the latest whole-suite, non-quick run"
	@echo "TARGETS='tls micro/bits' selects complete-component ID prefixes."
	@echo "LIST_ARGS, RUN_ARGS, REPORT_ARGS forward options to scripts/bench.py."
	@echo "For a selected/quick run: make report REPORT_ARGS='--run /path/to/run'"
	@echo "See README.md for settings, provenance, and profiling."

# Regenerate every format module from its schema.
generate:
	@for schema in src/micro/*/*.vest; do \
		echo "  $$schema"; \
		$(VEST) "$$schema" -o "$$(dirname "$$schema")/generated.rs" || exit 1; \
	done

# Release wire/corpus tests; layout parity is checked at compile time.
test:
	cargo test --locked --release
	python3 -B -m unittest discover -s tests

# Compile every benchmark and run its validation/setup once.
smoke:
	cargo bench --locked --benches -- --test

list:
	@python3 -B scripts/bench.py list $(TARGETS) $(LIST_ARGS)

# One recorded run, one implementation/group per process, randomized order.
bench:
	python3 -B scripts/bench.py run --allocations $(TARGETS) $(RUN_ARGS)

# Reprint the collected results without re-measuring.
report:
	@python3 -B scripts/bench.py report $(TARGETS) $(REPORT_ARGS)
