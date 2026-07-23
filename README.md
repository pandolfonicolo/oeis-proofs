# OEIS proofs

Reproducible manuscripts, proofs, verification programs, and submission notes
for results connected to the [Online Encyclopedia of Integer
Sequences](https://oeis.org/).

## Projects

| OEIS entries | Project | Result |
| --- | --- | --- |
| [A242239](https://oeis.org/A242239), [A242235](https://oeis.org/A242235) | [Window-covering words](projects/a242239-window-covering-words/) | Exact generating function, column recurrence, stable rows, and Mathar's identity |

## Repository conventions

Each directory under `projects/` is a self-contained reproducibility package:

- `manuscript/` contains the LaTeX source, generated tables, and compiled PDF;
- `verification/` contains deterministic verification code and recorded output;
- `oeis/` contains concise notes prepared for OEIS review;
- `docs/` contains revision and review notes;
- `checksums.sha256` records the integrity of the project's public artifacts.

See [CONTRIBUTING.md](CONTRIBUTING.md) before adding another project.

## Reproduce everything

```bash
make all
make check
```

The current verification code uses only the Python standard library. Building
the manuscript additionally requires `latexmk` and a standard LaTeX
installation. GitHub Actions reruns the mathematical verifier and integrity
checks on every push and pull request.
