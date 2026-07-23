.PHONY: all verify pdf clean

SOURCE_DATE_EPOCH ?= 1784764800
export SOURCE_DATE_EPOCH
export FORCE_SOURCE_DATE = 1

MANUSCRIPT_DIR := manuscript
VERIFICATION_DIR := verification
TEX_NAME := hardin_window_covering_words

all: verify pdf

verify:
	python3 $(VERIFICATION_DIR)/verify_hardin_family.py \
		--emit-tex $(MANUSCRIPT_DIR)/generated_numerators.tex \
		> $(VERIFICATION_DIR)/verification_output.txt
	cat $(VERIFICATION_DIR)/verification_output.txt

pdf: verify
	cd $(MANUSCRIPT_DIR) && \
		latexmk -pdf -interaction=nonstopmode -halt-on-error $(TEX_NAME).tex

clean:
	cd $(MANUSCRIPT_DIR) && latexmk -c $(TEX_NAME).tex

.PHONY: check distclean

check:
	shasum -a 256 -c checksums.sha256

distclean:
	cd $(MANUSCRIPT_DIR) && latexmk -C $(TEX_NAME).tex
