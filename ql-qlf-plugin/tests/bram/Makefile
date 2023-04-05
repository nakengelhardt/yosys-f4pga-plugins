ROOT_DIR=../..
PLUGIN=$(ROOT_DIR)/build/ql-qlf.so

test: generate $(PLUGIN)
	make -C generated all

generate: generate.py
	mkdir -p generated
	python $^

$(PLUGIN):
	make -C $(ROOT_DIR)

clean:
	make -C generated clean

.PHONY: test generate clean