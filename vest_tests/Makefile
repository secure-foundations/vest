.PHONY: all build-vest vest format-generated bad verus

CARGO        := cargo
ROOT_MANIFEST := ../Cargo.toml
VEST_DSL     := ../target/debug/vest
VERUSFMT     := verusfmt
# selected .vest files in the src directory
VEST_FILES   := ./src/codegen.vest ./src/elab.vest ./src/enums.vest ./src/enum_constraints.vest ./src/josh.vest ./src/matches.vest ./src/opt.vest ./src/repeat.vest ./src/length_expr.vest ./src/bits.vest ./src/bits_little.vest ./src/tlv.vest ./src/tls.vest ./src/bitcoin.vest ./src/anonymous_nested.vest ./src/projected_argument_deref.vest ./src/nested_access.vest ./src/nested_bytes.vest ./src/stress_depth.vest ./src/stress_width.vest ./src/names.vest ./src/client_ergonomics.vest
VEST_FILES += ./src/stress_dynamic_depth.vest
VEST_FILES += ./src/compiler_regressions.vest
# The Vest compiler lays out the files it generates; only the hand-written
# harness is formatted here.
VERUSFMT_FILES := ./src/lib.rs ./src/client_ergonomics_checks.rs
# ./src/ikev2.vest
all: vest bad verus

build-vest:
	$(CARGO) build --locked --manifest-path $(ROOT_MANIFEST) -p vest

vest: build-vest
	@set -e; for file in $(VEST_FILES); do \
		echo "==================================="; \
		echo "Processing $$file"; \
		$(VEST_DSL) $$file; \
	done
	$(MAKE) format-generated

format-generated:
	$(VERUSFMT) $(VERUSFMT_FILES)

bad:
	$(CARGO) test --locked --manifest-path $(ROOT_MANIFEST) -p vest --test diagnostics

verus:
	cargo verus verify --locked --check-toolchain -- --expand-errors
