.PHONY: all build fmt-check fmt

all: build fmt-check

get-cache:
	time lake exe cache get

build:
	time lake build

FMT_OPT=--recursive .

fmt-check:
	time lake exe fmt ${FMT_OPT} --check

fmt:
	time lake exe fmt ${FMT_OPT}
