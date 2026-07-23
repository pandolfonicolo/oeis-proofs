# Acceptance criteria for an A242322 result

Status: binding research gate.

No formula, theorem, manuscript, or OEIS update is ready merely because the
feasibility verifier passes.  A result may advance only if every applicable
gate below is satisfied.

## 1. Definition and provenance

- State the indexing, alphabet size, word length, window length, and
  restricted-growth convention without relying on examples.
- Archive the exact displayed OEIS values used for comparison, with access
  date and source URL.
- Keep discovered claims separate from formulas already displayed on OEIS.

## 2. Independent computation

- A literal canonical-word enumerator must agree with the claimed values on
  small cases.
- A raw labeled last-block DFA, divided by the proven free relabeling action,
  must agree on a larger range.
- A quotient transfer system derived from equality patterns must agree with
  both implementations.
- At least one implementation must use only the original sliding-window
  definition and must not encode the candidate recurrence or formula.

## 3. Anti-overfitting

- Terms used to discover a recurrence or polynomial and terms used to test it
  must be disjoint.
- The claimed relation must predict exact held-out integer values.
- Minimality or exact order must not be inferred only from a successful fit.
- Failed candidate formulas and their counterexamples must be retained in the
  research notes.

## 4. Proof obligations

- Prove that canonical words are counted by relabeling orbits and that the
  action is free.
- Prove that the quotient states and all transition multiplicities are
  exhaustive and unambiguous.
- Derive any generating function or recurrence symbolically from the transfer
  system; finite agreement is not a proof.
- Prove the stated starting index and boundary of every eventual formula.
- If an order is claimed to be minimal, prove that no cancellation lowers it.

## 5. Verification of the proof

- Translate each proof dependency into a short audit checklist.
- Check symbolic identities with exact integer or rational arithmetic.
- Compare the final theorem against fresh cases outside all discovery ranges.
- Run the complete verifier from a clean checkout in CI.
- Make generated tables and recorded output reproducible.

## 6. Publication gate

- Conduct an internal adversarial review that searches for indexing,
  cancellation, orbit-size, boundary, and provenance errors.
- Clearly label the work as not independently peer reviewed until an external
  mathematical reader has reviewed it.
- The human author must understand the definitions, main construction,
  theorem, and limitations well enough to explain them without generated text.
- Recheck the live OEIS entry and current contribution policies immediately
  before preparing any update.

Possible outcomes are `proved`, `conjectural`, or `not viable`.  Only `proved`
may be presented as a theorem.  A negative outcome is an acceptable research
result and creates no obligation to submit or publish.

## Current gate status

- Definition and provenance: passed internally.
- Independent computation: passed with four enumeration routes.
- Anti-overfitting: passed for the discovery stage.
- Proof obligations: passed internally for the transfer and stable-row
  theorems.
- Proof verification: passed internally with exact arithmetic.
- Publication gate: internal adversarial review passed; independent
  mathematical review remains pending.

Accordingly, the current label is `proved-in-draft, external-review-pending`.
It is not `submission-ready`.
