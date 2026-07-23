# A242239 window-covering words

This project contains the revised proof for OEIS A242239 and its special column
A242235.

## Contents

- `manuscript/` — LaTeX source, generated numerator table, and compiled paper;
- `verification/` — standard-library-only verifier and recorded successful run;
- `oeis/` — formulas and proof notes prepared for OEIS review;
- `docs/` — corrections and review history;
- `metadata.yaml` — machine-readable project index;
- `checksums.sha256` — integrity manifest for the public artifacts.

## Reproduce

```bash
make all
```

The verification script has no third-party Python dependencies. The Makefile
also fixes the PDF source date so clean builds are byte-for-byte reproducible.

To verify artifact integrity:

```bash
make check
```
