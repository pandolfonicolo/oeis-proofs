# Project conventions

Create one directory per primary OEIS entry:

```text
projects/aNNNNNN-short-descriptive-name/
├── README.md
├── Makefile
├── checksums.sha256
├── metadata.yaml
├── docs/
├── manuscript/
├── oeis/
└── verification/
```

Use lowercase ASCII directory names and retain descriptive manuscript and
verification filenames. Generated artifacts should be reproducible from the
project Makefile. A project is ready to commit when:

1. `make verify` passes from its project directory;
2. `make pdf` completes without unresolved references or layout warnings;
3. the compiled PDF has been visually inspected;
4. `checksums.sha256` reflects the final public artifacts;
5. `make check` passes;
6. claims about current OEIS status have been checked against the live entries.

Keep exploratory scratch files outside the repository. Do not commit LaTeX
intermediates, Python caches, credentials, or editor metadata.

New source code and build automation use MIT; new original research content,
notes, and documentation use CC BY 4.0. Record third-party provenance and
license restrictions explicitly.

Before preparing an OEIS contribution, read the current
[OEIS AI policy](https://oeis.org/wiki/Use_of_AI_for_OEIS_Submissions). Do not
paste AI-generated comments or Pink Box responses. The human contributor must
personally verify every term, formula, program, and statement and write the
final submission text.
