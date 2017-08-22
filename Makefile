libs =	PV/Types.vo \
	PV/Nat.vo \
	PV/Lists.vo \
	PV/SetoidLists.vo


all: deps $(libs)

deps: make/proof.deps

%.vo: %.v
	coqc -R PV PV $<
clean:
	rm PV/*.vo

# Find Coq proof scripts
src_coq_v \
 =  	$(shell find PV   -name "*.v" -follow)

# Coqc makes a .vo and a .glob from each .v file.
src_coq_vo	= $(patsubst %.v,%.vo,$(src_coq_v))

make/proof.deps: $(src_coq_v)
	@echo "Building proof dependencies"
	coqdep -R PV PV \
		$(src_coq_v) > make/proof.deps
	@cp make/proof.deps make/proof.deps.inc

-include make/proof.deps.inc
