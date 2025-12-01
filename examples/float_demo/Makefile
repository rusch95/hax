.PHONY: default lean fstar clean test

default: lean

lean:
	cargo hax into lean

fstar:
	cargo hax into -i '-** +**' fstar

test:
	cargo test

clean:
	rm -rf proofs/lean/extraction/*.lean
	rm -rf proofs/fstar/extraction/*.fst
	cargo clean
