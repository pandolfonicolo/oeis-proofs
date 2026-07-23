PROJECTS := projects/a242239-window-covering-words

.PHONY: all verify pdf check clean

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
