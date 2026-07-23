.PHONY: all build fmt-check fmt

all: build

build:
	time lake build

fmt-check:
	time lake exe fmt --check --recursive .

fmt:
	time lake exe fmt --recursive .
