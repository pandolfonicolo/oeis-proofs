# SPDX-License-Identifier: MIT

.PHONY: all verify pdf check clean

SOURCE_DATE_EPOCH ?= 1784764800
export SOURCE_DATE_EPOCH
export FORCE_SOURCE_DATE = 1

MANUSCRIPT_DIR := manuscript
TEX_NAME := two_slack_covering_words

all: verify pdf

verify:
	python3 verification/verify_a242322_feasibility.py \
		> verification/feasibility_output.txt
	python3 verification/verify_a242322_theorems.py \
		> verification/verification_output.txt
	cat verification/feasibility_output.txt
	cat verification/verification_output.txt

pdf:
	cd $(MANUSCRIPT_DIR) && \
		latexmk -pdf -interaction=nonstopmode -halt-on-error $(TEX_NAME).tex

check:
	shasum -a 256 -c checksums.sha256

clean:
	rm -f verification/feasibility_output.txt verification/verification_output.txt
	cd $(MANUSCRIPT_DIR) && latexmk -c $(TEX_NAME).tex
