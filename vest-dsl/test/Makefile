.PHONY: all vest bad verus

CARGO        := cargo
ROOT_MANIFEST := ../Cargo.toml
VEST_DSL     := ../target/debug/vest
# selected .vest files in the src directory
VEST_FILES   := ./src/codegen.vest ./src/elab.vest ./src/enums.vest ./src/enum_constraints.vest ./src/josh.vest ./src/matches.vest ./src/opt.vest ./src/repeat.vest
# all files in ./bad/
BAD_VEST_FILES := $(wildcard ./bad/*.vest)

all: vest bad verus

$(VEST_DSL):
	$(CARGO) build --manifest-path $(ROOT_MANIFEST) -p vest

vest: $(VEST_DSL)
	@for file in $(VEST_FILES); do \
		echo "==================================="; \
		echo "Processing $$file"; \
		$(VEST_DSL) $$file; \
	done

bad: $(VEST_DSL)
	@for file in $(BAD_VEST_FILES); do \
		echo "==================================="; \
		echo "Expecting failure for $$file"; \
		if $(VEST_DSL) $$file >/tmp/vest_bad.log 2>&1; then \
			echo "⚠️ Expected failure but succeeded for $$file"; \
			cat /tmp/vest_bad.log; \
			exit 1; \
		else \
			echo "✅ Got expected failure for $$file"; \
		fi \
	done

verus:
	cargo verus verify -- --expand-errors
