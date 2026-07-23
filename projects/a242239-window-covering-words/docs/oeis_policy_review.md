# OEIS policy review and submission checklist

Reviewed: 2026-07-23

This document summarizes the official OEIS policies relevant to the proposed
updates to A242239 and A242235. The linked official pages control if this
summary ever differs from them.

## AI use

OEIS requires a human author who is responsible for every submitted claim.
The submitter must personally verify the name, terms, formulas, programs, and
comments.

OEIS specifically prohibits:

- pasting AI-generated text into Pink Boxes;
- naming an AI system as an author or co-author;
- using AI to generate the full text of comments;
- submitting AI-generated code the contributor does not understand;
- bulk or serial AI-generated submissions without prior permission.

Consequently, files in `oeis/` are internal research notes, not text to paste
verbatim. Before submission, Nicolò Pandolfo must independently verify the
mathematics and write the final OEIS prose in his own words. AI may help locate
issues or organize the verification process, but it must not supply the full
submitted comment or any Pink Box response.

Official policy:
https://oeis.org/wiki/Use_of_AI_for_OEIS_Submissions

## Account and authorship

- An approved account and login are required to edit an existing entry.
- Anonymous submissions are not accepted.
- Additions to formulas and comments should be signed with ` - ~~~~`; OEIS
  replaces the tildes with the contributor name and date.
- The existing Author field normally should not be changed.

Official pages:

- https://oeis.org/Submit.html
- https://oeis.org/wiki/Style_Sheet

## Accuracy and editorial workflow

- OEIS applies the standards of a mathematical reference work.
- The contributor must distinguish theorems from conjectures.
- Save changes in editing status while polishing them.
- Only mark the draft ready for review after all fields and editor questions
  are resolved.
- OEIS editors provide the formal editorial review. A privately arranged
  external reviewer is useful but is not a prerequisite for proposing a
  correction to an existing sequence.
- Pink Box discussions are permanently visible; answers must be concise,
  technical, courteous, and written by the human contributor without AI text.

Official pages:

- https://oeis.org/wiki/Overview_of_the_contribution_process
- https://oeis.org/wiki/Good_Behavior_Guide_For_Contributors_and_Editors

## Rights and provenance

Submitting binds the contributor to the OEIS Contributor's License Agreement.
The contributor grants broad perpetual rights to OEIS and represents that the
contribution is original, public-domain with provenance, or properly submitted
on behalf of a third party. Any relevant third-party rights or restrictions
must be disclosed.

Official pages:

- https://oeis.org/wiki/The_OEIS_Contributor%27s_License_Agreement
- https://oeis.org/wiki/Legal_Documents

## Pre-submit checklist for A242239 and A242235

- [ ] OEIS account has been approved and login succeeds.
- [ ] Read the current live entries and any pending draft edits.
- [ ] Re-derive or personally check every submitted formula against the paper.
- [ ] Run `make verify` and `make check`.
- [ ] Write the final formula notes in the contributor's own words.
- [ ] Do not paste AI-authored prose or AI responses into a Pink Box.
- [ ] Add ` - ~~~~` to each new formula or comment requiring attribution.
- [ ] Add the public manuscript/repository link.
- [ ] Keep the Author and Extensions fields unchanged unless an editor asks.
- [ ] Save as editing, proofread the rendered draft, then propose for review.
- [ ] Answer editor questions personally, precisely, and courteously.
