COQC = coqc
COQDEP = coqdep

COQ_FLAG = -Q "./VST" VST -Q "./Heaps" Heaps -Q "./Libs" Contracts -Q "./Core" Contracts -Q "./Contracts" Contracts -Q "../mathcomp/ssreflect" mathcomp.ssreflect -Q "../ssl_coq" SSL

SOURCE := $(shell find "." -type f -name '*.v')
VO_FILE := $(shell find "." -type f -name '*.vo')
GLOB_FILE := $(shell find "." -type f -name '*.glob')
AUX_FILE := $(shell find "." -type f -name '*.vo.aux')

$(SOURCE:%.v=%.vo): %.vo: %.v
	@echo COQC $*.v
	@$(COQC) $(COQ_FLAG) $*.v

dep:
	@$(COQDEP) $(COQ_FLAG) $(SOURCE) > .depend

all: $(SOURCE:%.v=%.vo)

clean:
	@rm $(VO_FILE) $(GLOB_FILE) $(AUX_FILE)

.DEFAULT_GOAL := all

include .depend
