# Original A242239 release checklist

This historical checklist records the first family release. Current scope and
publication status across all three families are tracked in
[publication_status.md](publication_status.md).

## Completed

- Repository structure and naming are stable.
- A242239/A242235 verification passes all nine layers.
- The manuscript builds without unresolved references or layout warnings.
- The PDF has been visually inspected.
- Clean PDF builds are byte-for-byte reproducible in the reference environment.
- Project checksums pass.
- GitHub Actions reruns verification and integrity checks.
- Citation metadata is present.
- OEIS change text and an external-review request are prepared.
- Repository publication is approved.
- Licensing is selected: MIT for code and build tooling; CC BY 4.0 for original
  manuscripts, notes, data, and documentation.
- `v0.1.0` is retained as a superseded review snapshot.
- `v0.2.0` is retained as the first public licensed prerelease.
- The OEIS A242239 link-only update has been proposed for editor review.

## Public release procedure

1. Enable the public GitHub repository in Zenodo.
2. Tag the metadata-aligned snapshot as `v0.2.1`.
3. Create a GitHub release containing the manuscript PDF, checksums, and license
   scope so Zenodo archives it.
4. Add the resulting concept DOI to `CITATION.cff` and the repository README.
5. Record the OEIS editor outcome in the project revision notes.
6. Obtain an independent human review only if a reviewed-release claim is
   desired.
7. Tag a reviewed commit as `v1.0.0`.
