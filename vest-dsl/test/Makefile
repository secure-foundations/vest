all: vest verus

# List all .vest files in the src directory
VEST_FILES := ./src/codegen.vest ./src/elab.vest ./src/enums.vest ./src/josh.vest ./src/matches.vest ./src/opt.vest ./src/repeat.vest
# Path to the vest-dsl binary
VEST_DSL := ../target/debug/vest-dsl
vest:
	@for file in $(VEST_FILES); do \
		echo "==================================="; \
		echo "Processing $$file"; \
		$(VEST_DSL) $$file; \
	done
	 
verus:
	verus --crate-type=lib  --import vest=../../vest/vest.verusdata --extern vest=../../vest/libvest.rlib src/lib.rs --trace --time
