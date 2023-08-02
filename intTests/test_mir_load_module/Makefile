all: test.linked-mir.json

test.linked-mir.json: test.rs
	saw-rustc $<
	rm test libtest.mir libtest.rlib

.PHONY: clean
clean:
	rm -f test.linked-mir.json
