# OEIS proofs

Reproducible manuscripts, proofs, verification programs, and submission notes
for results connected to the [Online Encyclopedia of Integer
Sequences](https://oeis.org/).

## Projects

| OEIS entries | Project | Result |
| --- | --- | --- |
| [A242239](https://oeis.org/A242239), [A242235](https://oeis.org/A242235) | [Window-covering words](projects/a242239-window-covering-words/) | Exact generating function, column recurrence, stable rows, and Mathar's identity |
| [A242322](https://oeis.org/A242322) | [Two-slack window-covering words](projects/a242322-two-slack-covering-words/) | Exact transfer recurrence and stable quartic rows; general minimality proved in [PR #7](https://github.com/pandolfonicolo/oeis-proofs/pull/7) |
| [A354766](https://oeis.org/A354766), [A278085](https://oeis.org/A278085) | [Integer quadruples and three squares](projects/a354766-integer-quadruples/) | Multiplicativity, prime-power formulas, equality characterization, and density zero; complete Lean proof |

All three families have complete written proofs for the stated results. The
A354766/A278085 conclusions also have a complete Lean verification. Internal
checks and kernel verification are recorded explicitly; external human
mathematical review remains pending. See [publication status](docs/publication_status.md)
for the exact scope, publication boundary, and remaining optional conjectures.

## Repository conventions

Each directory under `projects/` is a self-contained reproducibility package:

- `manuscript/` contains the LaTeX source, generated tables, and compiled PDF;
- `verification/` contains deterministic verification code and recorded output;
- `oeis/` contains concise notes prepared for OEIS review;
- `docs/` contains revision and review notes;
- `checksums.sha256` records the integrity of the project's public artifacts.

See [CONTRIBUTING.md](CONTRIBUTING.md) before adding another project.

## Citation

Citation metadata is available in [CITATION.cff](CITATION.cff). Cite the
specific manuscript when using a result from an individual project.
Versioned public snapshots are archived through Zenodo from GitHub releases.

## License

Code and build tooling are available under MIT. Original manuscripts, notes,
data, and documentation are available under CC BY 4.0. See
[LICENSE.md](LICENSE.md) for the exact scope.

## Reproduce everything

```bash
make all
make check
make formal
```

The numerical verifiers and recorded-proof audits use only the Python standard
library. Building the manuscripts additionally requires `latexmk` and a
standard LaTeX installation. Fresh formal verification uses Lean 4.27.0 and the
pinned Mathlib manifest; run `make formal` for A354766/A278085. The separate
Lean workflow recompiles all 43 modules and audits the 14 concluding axiom
reports. `make verify` audits recorded evidence and runs finite checks; it
does not substitute for recompiling Lean.

OEIS contributions must follow its current [AI policy](https://oeis.org/wiki/Use_of_AI_for_OEIS_Submissions).
The `oeis/` files are mathematical working notes. A human contributor must
verify the claims and write the final comments.
