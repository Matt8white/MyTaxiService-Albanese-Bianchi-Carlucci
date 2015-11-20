OUT = out
SRC = src
TEX = pdflatex -shell-escape -interaction=nonstopmode -file-line-error -output-directory=$(OUT)/

.PHONY: all view clean

VIEW :=
ifeq ($(OS),Windows_NT)
	VIEW := start
else
	UNAME_S := $(shell uname -s)
	ifeq ($(UNAME_S),Linux)
		VIEW := xdg-open
	endif
	ifeq ($(UNAME_S),Darwin)
		VIEW := open
	endif
endif

all: rasd.pdf

view: rasd.pdf
	$(VIEW) $(OUT)/rasd.pdf

clean: 
	rm -f $(OUT)/*

rasd.pdf: 
	$(TEX) $(SRC)/rasd.tex
