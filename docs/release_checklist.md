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

## Decisions required before public release

- Choose repository visibility: keep private or make public.
- Choose licensing:
  - recommended for code: MIT;
  - recommended for manuscript, notes, and data: CC BY 4.0.
- Obtain an independent human review, or explicitly release as an unreviewed
  preprint.

## Public release procedure

1. Apply the chosen licenses and update repository metadata.
2. Make the repository public.
3. Confirm all links work without authentication.
4. Merge the release-preparation pull request.
5. Tag the reviewed commit as `v1.0.0`.
6. Create a GitHub release containing the manuscript PDF and checksums.
7. Enable the GitHub repository in Zenodo and create a DOI-backed release.
8. Add the DOI to `CITATION.cff`, the manuscript, and the repository README.
9. Submit the prepared changes to A242239 and A242235.
10. Record OEIS review outcomes in the project revision notes.
