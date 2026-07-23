#!/usr/bin/env python3
"""Independent verification for Hardin's window-covering words (OEIS A242239).

The script uses only the Python standard library.  It checks the closed
numerator formula against:
  1. direct walks on the quotient bouquet automaton;
  2. a raw last-block DFA built from the defining sliding-window condition;
  3. direct enumeration of canonical restricted-growth words for small cases;
  4. the first 10 x 8 values displayed on OEIS A242239;
  5. the stable-row formula;
  6. the A242235 and Mathar identities.

It can also emit the numerator table used by the LaTeX manuscript.
"""

from __future__ import annotations

import argparse
import itertools
import math
from collections import defaultdict
from pathlib import Path
from typing import Dict, Iterable, List, Sequence, Tuple


# First ten rows and first eight columns displayed on OEIS A242239,
# accessed 2026-07-23.  Rows are indexed by n=1,...,10 and columns by k=1,...,8.
OEIS_A242239_10_BY_8: Tuple[Tuple[int, ...], ...] = (
    (3, 6, 10, 15, 21, 28, 36, 45),
    (5, 12, 22, 35, 51, 70, 92, 117),
    (8, 22, 43, 71, 106, 148, 197, 253),
    (13, 40, 82, 139, 211, 298, 400, 517),
    (21, 74, 157, 271, 416, 592, 799, 1037),
    (34, 136, 304, 531, 821, 1174, 1590, 2069),
    (55, 250, 586, 1047, 1626, 2332, 3165, 4125),
    (89, 460, 1129, 2059, 3231, 4642, 6308, 8229),
    (144, 846, 2176, 4047, 6411, 9256, 12587, 16429),
    (233, 1556, 4195, 7955, 12716, 18442, 25138, 32821),
)


def numerator_coeffs(k: int) -> List[int]:
    """Return [c_1,...,c_{k+1}] for the exact numerator N_k(x)."""
    if k < 1:
        raise ValueError("k must be at least 1")
    return [((k + 2 - j) * (k * j + 2)) // 2 for j in range(1, k + 2)]


def formula_counts(k: int, n_max: int) -> List[int]:
    """Generate T(1,k),...,T(n_max,k) from N_k(x)/D_k(x)."""
    q = k + 1
    c = [0] + numerator_coeffs(k)
    t = [0] * (n_max + 1)
    for n in range(1, n_max + 1):
        forcing = c[n] if n <= q else 0
        t[n] = forcing + sum(t[n - i] for i in range(1, min(q, n - 1) + 1))
    return t[1:]


def bouquet_states(k: int) -> List[Tuple[int, int] | str]:
    """States R and (ell,d), where d is the forced distance to R on the ell-cycle."""
    q = k + 1
    states: List[Tuple[int, int] | str] = ["R"]
    for ell in range(2, q + 1):
        for d in range(1, ell):
            states.append((ell, d))
    return states


def bouquet_successors(k: int, state: Tuple[int, int] | str) -> Tuple[Tuple[int, int] | str, ...]:
    q = k + 1
    if state == "R":
        return ("R",) + tuple((ell, ell - 1) for ell in range(2, q + 1))
    ell, d = state
    return ("R",) if d == 1 else ((ell, d - 1),)


def bouquet_counts(k: int, n_max: int) -> List[int]:
    """Count length-n walks starting at any state and ending anywhere."""
    states = bouquet_states(k)
    counts: Dict[Tuple[int, int] | str, int] = {s: 1 for s in states}
    out: List[int] = []
    for _ in range(n_max):
        nxt = {s: 0 for s in states}
        for s, weight in counts.items():
            for u in bouquet_successors(k, s):
                nxt[u] += weight
        counts = nxt
        out.append(sum(counts.values()))
    return out


def raw_dfa_counts(k: int, n_max: int) -> List[int]:
    """Definition-only labeled count, divided by (k+1)!.

    A state is the last q=k+1 letters.  A transition is allowed exactly when
    the resulting q+1 window contains all q alphabet symbols.
    """
    q = k + 1
    alphabet = tuple(range(q))
    full = frozenset(alphabet)
    counts: Dict[Tuple[int, ...], int] = {
        block: 1 for block in itertools.product(alphabet, repeat=q)
    }
    out: List[int] = []
    divisor = math.factorial(q)
    for _ in range(n_max):
        nxt: Dict[Tuple[int, ...], int] = defaultdict(int)
        for block, weight in counts.items():
            for x in alphabet:
                if frozenset(block + (x,)) == full:
                    nxt[block[1:] + (x,)] += weight
        counts = nxt
        labeled = sum(counts.values())
        assert labeled % divisor == 0
        out.append(labeled // divisor)
    return out


def canonical_count(k: int, n: int) -> int:
    """Directly enumerate canonical restricted-growth words from the definition."""
    q = k + 1
    length = q + n
    full = set(range(q))
    word: List[int] = []
    total = 0

    def dfs(current_max: int) -> None:
        nonlocal total
        if len(word) == length:
            total += 1
            return
        upper = min(k, current_max + 1)
        for x in range(upper + 1):
            word.append(x)
            if len(word) < q + 1 or set(word[-(q + 1):]) == full:
                dfs(max(current_max, x))
            word.pop()

    # Canonical restricted-growth words necessarily begin with 0.
    word.append(0)
    dfs(0)
    return total


def stable_row_formula(n: int, k: int) -> int:
    numerator = (2**n - 1) * k * k + (2 * n + 1) * k
    assert numerator % 2 == 0
    return numerator // 2 + 1


def a145113_automaton(m_max: int) -> List[int]:
    """Count binary words with fewer than five zeros between consecutive ones."""
    # States: Z=no 1 yet; 0..4=zeros since last 1; 5=at least five zeros.
    counts: Dict[str | int, int] = {"Z": 1, 0: 0, 1: 0, 2: 0, 3: 0, 4: 0, 5: 0}
    out = [1]
    for _ in range(m_max):
        nxt: Dict[str | int, int] = {"Z": 0, 0: 0, 1: 0, 2: 0, 3: 0, 4: 0, 5: 0}
        # Read 0.
        nxt["Z"] += counts["Z"]
        for c in range(5):
            nxt[c + 1] += counts[c]
        nxt[5] += counts[5]
        # Read 1; forbidden from state 5.
        nxt[0] += counts["Z"] + sum(counts[c] for c in range(5))
        counts = nxt
        out.append(sum(counts.values()))
    return out


def poly_add(a: Sequence[int], b: Sequence[int]) -> List[int]:
    n = max(len(a), len(b))
    return [(a[i] if i < len(a) else 0) + (b[i] if i < len(b) else 0) for i in range(n)]


def poly_scale(a: Sequence[int], c: int) -> List[int]:
    return [c * x for x in a]


def poly_shift(a: Sequence[int], r: int) -> List[int]:
    return [0] * r + list(a)


def poly_mul(a: Sequence[int], b: Sequence[int]) -> List[int]:
    out = [0] * (len(a) + len(b) - 1)
    for i, ai in enumerate(a):
        for j, bj in enumerate(b):
            out[i + j] += ai * bj
    return out


def trim(a: Sequence[int]) -> List[int]:
    out = list(a)
    while len(out) > 1 and out[-1] == 0:
        out.pop()
    return out


def check_mathar_polynomial_identity() -> None:
    # Common denominator: (1-x)^2 D_4(x).
    d4 = [1, -1, -1, -1, -1, -1]
    one_minus_x = [1, -1]
    a_num = [0, 15, 20, 21, 18, 11]
    b_num = [1, -1, 0, 0, 0, 0, 1]

    lhs = poly_mul(a_num, poly_mul(one_minus_x, one_minus_x))
    rhs = [0]
    rhs = poly_add(rhs, poly_scale(poly_shift(b_num, 1), 16))
    rhs = poly_add(rhs, poly_scale(poly_shift(d4, 1), 4))
    rhs = poly_add(rhs, poly_scale(poly_shift(poly_mul(one_minus_x, d4), 1), -5))
    assert trim(lhs) == trim(rhs), (trim(lhs), trim(rhs))


def emit_latex_table(path: Path, k_max: int = 8) -> None:
    lines = [
        r"\begin{tabular}{c l}",
        r"\toprule",
        r"$k$ & $N_k(x)$ \\",
        r"\midrule",
    ]
    for k in range(1, k_max + 1):
        terms = []
        for j, c in enumerate(numerator_coeffs(k), start=1):
            power = "x" if j == 1 else rf"x^{{{j}}}"
            terms.append(rf"{c}{power}")
        lines.append(rf"{k} & ${' + '.join(terms)}$ \\")
    lines.extend([r"\bottomrule", r"\end{tabular}"])
    path.write_text("\n".join(lines) + "\n", encoding="utf-8")


def run_checks(verbose: bool = True) -> None:
    checks = 0

    # Exact numerator integrality and endpoint values.
    for k in range(1, 101):
        c = numerator_coeffs(k)
        assert c[0] == (k + 1) * (k + 2) // 2
        assert c[-1] == (k * k + k + 2) // 2
        assert all(x > 0 for x in c)
    checks += 1
    if verbose:
        print("PASS  exact numerator formula: integrality, positivity, endpoint coefficients")

    # Quotient bouquet versus the rational formula.
    for k in range(1, 21):
        assert bouquet_counts(k, 60) == formula_counts(k, 60)
    checks += 1
    if verbose:
        print("PASS  bouquet automaton vs. exact generating function (k=1..20, n=1..60)")

    # Raw definition-only DFA.
    for k in range(1, 6):
        assert raw_dfa_counts(k, 20) == formula_counts(k, 20)
    checks += 1
    if verbose:
        print("PASS  raw last-block DFA vs. formula (k=1..5, n=1..20)")

    # Canonical word enumeration from the literal definition.
    for k in range(1, 5):
        values = formula_counts(k, 7)
        for n in range(1, 8):
            assert canonical_count(k, n) == values[n - 1]
    checks += 1
    if verbose:
        print("PASS  direct canonical-word enumeration vs. formula (k=1..4, n=1..7)")

    # Current OEIS display table.
    for n, row in enumerate(OEIS_A242239_10_BY_8, start=1):
        for k, expected in enumerate(row, start=1):
            assert formula_counts(k, n)[-1] == expected
    checks += 1
    if verbose:
        print("PASS  first 10 x 8 displayed values of OEIS A242239")

    # Column recurrence and exact start range.
    for k in range(1, 30):
        q = k + 1
        vals = [0] + formula_counts(k, 100)
        for n in range(q + 1, 101):
            assert vals[n] == sum(vals[n - i] for i in range(1, q + 1))
        for n in range(2, q + 1):
            truncated = sum(vals[n - i] for i in range(1, min(q, n - 1) + 1))
            assert vals[n] != truncated
    checks += 1
    if verbose:
        print("PASS  (k+1)-bonacci recurrence and exact start n=k+2")

    # Stable rows and sharpness at the first excluded point.
    for n in range(1, 31):
        for k in range(max(1, n - 3), 41):
            assert formula_counts(k, n)[-1] == stable_row_formula(n, k)
    for n in range(5, 31):
        k = n - 4
        actual = formula_counts(k, n)[-1]
        assert actual == stable_row_formula(n, k) - k * k
    checks += 1
    if verbose:
        print("PASS  stable-row formula for k>=n-3; sharp defect k^2 at k=n-4")

    # A242235.
    a = formula_counts(4, 210)
    assert a[:10] == [15, 35, 71, 139, 271, 531, 1047, 2059, 4047, 7955]
    for n in range(6, 211):
        assert a[n - 1] == sum(a[n - i - 1] for i in range(1, 6))
    checks += 1
    if verbose:
        print("PASS  A242235 initial terms and pentanacci recurrence through n=210")

    # A145113 and Mathar.
    b = a145113_automaton(209)
    assert b[:17] == [1, 2, 4, 8, 16, 32, 64, 127, 251, 495, 975, 1919, 3775, 7424, 14598, 28702, 56430]
    check_mathar_polynomial_identity()
    for n in range(1, 211):
        assert a[n - 1] == 16 * b[n - 1] + 4 * n - 5
    checks += 1
    if verbose:
        print("PASS  A145113 automaton and exact Mathar rational-function identity")

    if verbose:
        print(f"\nALL {checks} VERIFICATION LAYERS PASSED")


def main() -> None:
    parser = argparse.ArgumentParser()
    parser.add_argument("--emit-tex", type=Path, help="write a LaTeX numerator table")
    parser.add_argument("--quiet", action="store_true")
    args = parser.parse_args()
    run_checks(verbose=not args.quiet)
    if args.emit_tex:
        emit_latex_table(args.emit_tex)
        if not args.quiet:
            print(f"WROTE {args.emit_tex}")


if __name__ == "__main__":
    main()
