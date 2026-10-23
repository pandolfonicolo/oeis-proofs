# SPDX-License-Identifier: MIT

PROJECTS := \
	projects/a242239-window-covering-words \
	projects/a242322-two-slack-covering-words \
	projects/a354766-integer-quadruples

.PHONY: all verify pdf check formal clean

all:
	@set -e; for project in $(PROJECTS); do $(MAKE) -C "$$project" all; done

verify:
	@set -e; for project in $(PROJECTS); do $(MAKE) -C "$$project" verify; done

pdf:
	@set -e; for project in $(PROJECTS); do $(MAKE) -C "$$project" pdf; done

check:
	@set -e; for project in $(PROJECTS); do $(MAKE) -C "$$project" check; done

clean:
	@set -e; for project in $(PROJECTS); do $(MAKE) -C "$$project" clean; done

formal:
	$(MAKE) -C projects/a354766-integer-quadruples formal
