all: PV/Types.vo PV/Nat.vo PV/Lists.vo PV/SetoidList.vo
%.vo: %.v
	coqc $@
clean: rm PV/*.vo
