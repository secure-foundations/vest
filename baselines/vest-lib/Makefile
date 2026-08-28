all:
	verus --crate-type=lib src/lib.rs --multiple-errors 5 --compile --export vest_lib.verusdata --rlimit 50

clean:
	rm vest.verusdata
	rm libvest_lib.rlib
	cargo clean
