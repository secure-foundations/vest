all: vest verus

# List all .vest files in the src directory
VEST_FILES := ./src/codegen.vest ./src/elab.vest ./src/enums.vest ./src/josh.vest ./src/matches.vest ./src/opt.vest ./src/repeat.vest
# Path to the vest-dsl binary
VEST_DSL := ../target/debug/vest
vest:
	@for file in $(VEST_FILES); do \
		echo "==================================="; \
		echo "Processing $$file"; \
		$(VEST_DSL) $$file; \
	done
	 
verus:
	verus --crate-type=lib  --import vest_lib=../../vest/vest_lib.verusdata --extern vest_lib=../../vest/libvest_lib.rlib src/lib.rs --trace --time
