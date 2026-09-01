.PHONY: all build-vest vest format-generated bad verus

CARGO        := cargo
ROOT_MANIFEST := ../Cargo.toml
VEST_DSL     := ../target/debug/vest
VERUSFMT     := verusfmt
# selected .vest files in the src directory
VEST_FILES   := ./src/codegen.vest ./src/elab.vest ./src/enums.vest ./src/enum_constraints.vest ./src/josh.vest ./src/matches.vest ./src/opt.vest ./src/repeat.vest ./src/length_expr.vest ./src/bits.vest ./src/bits_little.vest ./src/tlv.vest ./src/tls.vest ./src/bitcoin.vest ./src/anonymous_nested.vest ./src/nested_access.vest ./src/nested_bytes.vest ./src/stress_depth.vest ./src/stress_width.vest
# Keep this list explicit: verusfmt can stall on the deeply nested stress fixtures.
VERUSFMT_FILES := ./src/anonymous_nested.rs ./src/bitcoin.rs ./src/bits_little.rs ./src/bits.rs ./src/codegen.rs ./src/elab.rs ./src/enum_constraints.rs ./src/enums.rs ./src/length_expr.rs ./src/lib.rs ./src/matches.rs ./src/mutual_rec.rs ./src/nested_access.rs ./src/nested_bytes.rs ./src/opt.rs ./src/repeat.rs ./src/tlv.rs
# ./src/ikev2.vest
# all files in ./bad/
BAD_VEST_FILES := $(wildcard ./bad/*.vest)

all: vest bad verus

build-vest:
	$(CARGO) build --manifest-path $(ROOT_MANIFEST) -p vest

vest: build-vest
	@for file in $(VEST_FILES); do \
		echo "==================================="; \
		echo "Processing $$file"; \
		$(VEST_DSL) $$file; \
	done
	$(MAKE) format-generated

format-generated:
	$(VERUSFMT) $(VERUSFMT_FILES)

bad: build-vest
	@for file in $(BAD_VEST_FILES); do \
		echo "==================================="; \
		echo "Expecting failure for $$file"; \
		if $(VEST_DSL) $$file -o /dev/null >/tmp/vest_bad.log 2>&1; then \
			echo "⚠️ Expected failure but succeeded for $$file"; \
			cat /tmp/vest_bad.log; \
			exit 1; \
		else \
			echo "✅ Got expected failure for $$file"; \
		fi \
	done

verus:
	cargo verus verify -- --expand-errors
