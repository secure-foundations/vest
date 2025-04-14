all:
	verus --crate-type=lib src/lib.rs --multiple-errors 5 --compile --export vest.verusdata --rlimit 50

clean:
	rm vest.verusdata
	rm libvest.rlib
	cargo clean
