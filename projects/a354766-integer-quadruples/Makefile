# SPDX-License-Identifier: MIT

.PHONY: all verify formal pdf check clean clean-current

PYTHON ?= python3
SOURCE_DATE_EPOCH ?= 1792713600
export SOURCE_DATE_EPOCH
export FORCE_SOURCE_DATE = 1

all: verify pdf

verify:
	$(PYTHON) verification/verify_package.py
	$(PYTHON) verification/cloud/exact_counts.py --max-n 40 --max-r3 25 --workers 2 --output verification/current/numerical

formal:
	$(PYTHON) verification/prepare_formal.py
	cd verification/current/formal && lake exe cache get
	cd verification/current/formal && $(PYTHON) tools/compile_modules.py > verification/standalone.log 2>&1
	cd verification/current/formal && $(PYTHON) tools/audit_no_admissions.py --axioms-log verification/standalone.log

pdf:
	cd manuscript && latexmk -pdf -interaction=nonstopmode -halt-on-error main.tex

check:
	shasum -a 256 -c checksums.sha256

clean-current:
	$(PYTHON) verification/prepare_formal.py --clean

clean: clean-current
