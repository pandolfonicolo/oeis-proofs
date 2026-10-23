# A354766/A278085 — complete research proof, 2026-10-23

The representation formula and all OEIS arithmetic conclusions are proved
without admissions. The complete concluding Lean check has zero errors;
all 14 final axiom reports contain only `propext`, `Classical.choice`, and
`Quot.sound`. No representation-count formula or recurrence is an assumption
of the final result. Independent external human review remains pending.

## Exact scope and normalization

- `T = tqFinite / 4` counts all standard quads: OEIS A354766.
- `P = pqFinite / 4` counts primitive standard quads.
- `A278085Primary` uses the primary primitive sum-3n, norm-3n² definition.
  The explicit complement bijection proves it equals `P`, including at 3.
- The primitive three-square product, multiplicativity of P and T, all stated
  prime-power values, and the exact equality characterization are proved.
- The set of positive n with T(n)=n has natural density zero. Thus the
  positive-density conjecture in OEIS A354766 is false.

The corrected primitive bridge uses level `3*n²` for odd n, level
`3*(n/2)²` for n=2 mod4, and zero for 4 dividing n. Both normalized
counts divide the ordered raw quad count by four.

## Proof route

`SmallIntegralLattices` classifies integral positive lattices of rank at
most three and covolume one. `NeighborConstruction`, `IsotropicLift`,
`IsotropicLines`, and `NormalizedNeighborFamily` build the actual prime
neighbors and prove their finite projective incidence counts.
`NeighborShellCounts` supplies actual norm-shell equivalences and finiteness.
`PrimitiveNeighborAlgebra`, `InsideContentClassification`, `ShellPartitions`,
`NeighborFiberCounts`, `InsideNeighborSums`, and `ExteriorNeighborCount`
prove the primitive-vector double count. `PrimitiveNeighborCount` instantiates
every recurrence for the actual representation count. The independently
checked cloud module `EulerProductFromRecurrence` then supplies the product.

`Blueprint` contains the final arithmetic conclusions. `BadPrimeSieve` and
`DensityLimit` prove the finite-CRT density argument; no reciprocal-prime
series theorem is needed. `A278085Complement` closes the primary-definition
connection. `FinalAxioms` prints the 14 public dependency reports.

The finite bridge congruences and representation base used by the final
conclusions use kernel `decide`. An unused recovered base theorem in
`FiniteCounts` retains its old `native_decide`; it is not a dependency of
any of the 14 final conclusions, as the actual axiom reports demonstrate.

## Reproduce

Lean is pinned to 4.27.0. The included manifest pins Mathlib to
`a3a10db0e9d66acbebf76c5e6a135066525ac900`.

    lake exe cache get
    python3 tools/compile_modules.py > verification/standalone.log 2>&1
    python3 tools/make_joint_check.py
    python3 tools/audit_no_admissions.py --axioms-log verification/standalone.log

The portable compiler checks the actual Lean version and Mathlib commit,
compiles dependencies in order, records source/artifact hashes and exit
codes, and publishes artifacts only after a successful check. It always
reruns `FinalAxioms`, including when other module artifacts are reused.
`A354766_LEAN` can select an explicit compiler path when the elan shim is
not on PATH. Standard Lake builds are also supported by the project files.

The deterministic joint checker copies all 43 local proof bodies unchanged.
Its manifest identifies every source hash; standalone compilation validates
the separate module boundaries. The release verification folder records
both checks. Numerical checks through n=300 are supplemental consistency
checks and are not proof steps.

## Recovery and review boundary

The original July checkpoint, scratch files, and unfinished Formal
Conjectures integration template belong to the separately preserved
historical recovery. They are not the default proof library. Current status
is established by this README and the release verification evidence.
The conventional manuscript and internal audits disclose AI assistance;
external human review and editorial acceptance are separate from kernel
verification.
