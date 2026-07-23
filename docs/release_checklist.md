# Release and publication checklist

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

## Public release procedure

1. Apply the chosen licenses and update repository metadata.
2. Make the repository public and confirm links work without authentication.
3. Keep `v0.1.0` labeled as an unreviewed prerelease.
4. Obtain an independent human review if a reviewed-release claim is desired.
5. Tag the reviewed commit as `v1.0.0`.
6. Create a GitHub release containing the manuscript PDF and checksums.
7. Enable the GitHub repository in Zenodo and create a DOI-backed release.
8. Add the DOI to `CITATION.cff`, the manuscript, and the repository README.
9. After account approval, submit human-written changes to A242239 and A242235.
10. Record OEIS review outcomes in the project revision notes.
