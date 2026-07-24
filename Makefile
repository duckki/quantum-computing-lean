.PHONY: all build fmt-check fmt

all: build

build:
	time lake build

FMT_OPT=--recursive .

fmt-check:
	time lake exe fmt ${FMT_OPT} --check

fmt:
	time lake exe fmt ${FMT_OPT}
