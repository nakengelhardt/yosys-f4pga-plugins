QL_PLUGIN=../../../../build/ql-qlf.so

formal: top.new.il params.vh top.v equiv.sby
	sby -f equiv.sby

top.new.il: params.vh top.v make_gate.ys $(QL_PLUGIN) ../../../../qlf_k6n10f/libmap_brams.txt ../../../../qlf_k6n10f/libmap_brams_map.v
	yosys -m $(QL_PLUGIN) make_gate.ys

clean:
	rm -rf top.new.il top.old.il top.TDP36K.new.il top.TDP36K.old.il top.new top.old equiv top.log


.PHONY: formal clean