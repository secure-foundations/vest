.PHONY: all build-vest-vps generate bad verify

CARGO        := cargo
ROOT_MANIFEST := ../Cargo.toml
VEST_VPS     := ../target/debug/vest-vps
# selected .vest files in the src directory
VEST_FILES   := ./src/codegen.vest ./src/elab.vest ./src/enums.vest ./src/enum_constraints.vest ./src/josh.vest ./src/matches.vest ./src/opt.vest ./src/repeat.vest ./src/length_expr.vest ./src/bits.vest ./src/bits_little.vest ./src/tlv.vest ./src/tls.vest ./src/bitcoin.vest ./src/anonymous_nested.vest ./src/nested_access.vest ./src/mutual_rec.vest ./src/nested_bytes.vest ./src/stress_depth.vest ./src/stress_width.vest
# ./src/ikev2.vest
# all files in ./bad/
BAD_VEST_FILES := $(wildcard ./bad/*.vest)

all: generate bad verify

build-vest-vps:
	$(CARGO) build --manifest-path $(ROOT_MANIFEST) -p vest-dsl-vps

generate: build-vest-vps
	@for file in $(VEST_FILES); do \
		echo "==================================="; \
		echo "Processing $$file"; \
		$(VEST_VPS) $$file; \
	done

bad: build-vest-vps
	@for file in $(BAD_VEST_FILES); do \
		echo "==================================="; \
		echo "Expecting failure for $$file"; \
		if $(VEST_VPS) $$file >/tmp/vps_bad.log 2>&1; then \
			echo "⚠️ Expected failure but succeeded for $$file"; \
			cat /tmp/vps_bad.log; \
			exit 1; \
		else \
			echo "✅ Got expected failure for $$file"; \
		fi \
	done

verify:
	cargo verus verify -- --expand-errors
