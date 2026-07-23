#!/usr/bin/env python3
# SPDX-License-Identifier: MIT

"""Proof-oriented exact verification for OEIS A242322.

The theorem-side implementation uses last-occurrence ages.  It is compared
with the independent equality-pattern, raw-DFA, and literal enumerators in
verify_a242322_feasibility.py.
"""

from __future__ import annotations

import importlib.util
import math
from collections import defaultdict
from fractions import Fraction
from pathlib import Path
from typing import DefaultDict, Dict, Iterable, List, Sequence, Tuple


State = Tuple[int, int]


def load_feasibility_module():
    path = Path(__file__).with_name("verify_a242322_feasibility.py")
    spec = importlib.util.spec_from_file_location("a242322_feasibility", path)
    if spec is None or spec.loader is None:
        raise RuntimeError(f"cannot load {path}")
    module = importlib.util.module_from_spec(spec)
    spec.loader.exec_module(module)
    return module


def age_states(k: int) -> Tuple[State, ...]:
    """Pairs of missing positive ages; r=k+2."""
    if k < 1:
        raise ValueError("k must be positive")
    r = k + 2
    return tuple((i, j) for i in range(1, r) for j in range(i + 1, r + 1))


def age_successors(k: int, state: State) -> Tuple[State, ...]:
    """Allowed next states in the last-occurrence-age quotient."""
    r = k + 2
    i, j = state
    if j < r:
        return ((i + 1, j + 1),)
    vertex = i + 1
    return tuple(
        (min(vertex, other), max(vertex, other))
        for other in range(1, r + 1)
        if other != vertex
    )


def initial_weight(state: State) -> int:
    """Number of canonical first windows giving a state."""
    i, j = state
    return i * (j - 1)


def age_counts(k: int, n_max: int) -> List[int]:
    """T(1,k),...,T(n_max,k) from the triangular age automaton."""
    states = age_states(k)
    counts: Dict[State, int] = {state: initial_weight(state) for state in states}
    out = [sum(counts.values())]
    transitions = {state: age_successors(k, state) for state in states}
    for _ in range(2, n_max + 1):
        nxt: DefaultDict[State, int] = defaultdict(int)
        for state, weight in counts.items():
            for target in transitions[state]:
                nxt[target] += weight
        counts = nxt
        out.append(sum(counts.values()))
    return out


def transition_matrix(k: int) -> List[List[int]]:
    states = age_states(k)
    index = {state: position for position, state in enumerate(states)}
    matrix = [[0] * len(states) for _ in states]
    for row, state in enumerate(states):
        for target in age_successors(k, state):
            matrix[row][index[target]] += 1
    return matrix


def matrix_multiply(left: Sequence[Sequence[int]], right: Sequence[Sequence[int]]) -> List[List[int]]:
    size = len(left)
    product = [[0] * size for _ in range(size)]
    for i, left_row in enumerate(left):
        product_row = product[i]
        for pivot, coefficient in enumerate(left_row):
            if coefficient == 0:
                continue
            right_row = right[pivot]
            for j, value in enumerate(right_row):
                if value:
                    product_row[j] += coefficient * value
    return product


def characteristic_coefficients(matrix: Sequence[Sequence[int]]) -> List[int]:
    """Faddeev--LeVerrier coefficients of det(lambda I-A).

    The returned [1,c1,...,cN] are also the coefficients of det(I-xA)
    in increasing powers of x.
    """
    size = len(matrix)
    auxiliary = [[int(i == j) for j in range(size)] for i in range(size)]
    coefficients = [1]
    for degree in range(1, size + 1):
        product = matrix_multiply(matrix, auxiliary)
        trace = sum(product[i][i] for i in range(size))
        assert trace % degree == 0
        coefficient = -trace // degree
        coefficients.append(coefficient)
        for i in range(size):
            product[i][i] += coefficient
        auxiliary = product
    return coefficients


def numerator_coefficients(k: int, denominator: Sequence[int]) -> List[int]:
    """Coefficients of D_k(x) sum_{n>=1} T(n,k)x^n."""
    order = len(denominator) - 1
    values = [0] + age_counts(k, 2 * order + 2)
    numerator = [0]
    for n in range(1, order + 1):
        numerator.append(
            sum(denominator[j] * values[n - j] for j in range(0, min(n, order) + 1))
        )
    for n in range(order + 1, 2 * order + 2):
        residual = sum(denominator[j] * values[n - j] for j in range(order + 1))
        assert residual == 0
    while len(numerator) > 1 and numerator[-1] == 0:
        numerator.pop()
    return numerator


def stable_row_formula(n: int, k: int) -> int:
    """The proved stable-row polynomial, evaluated with exact arithmetic."""
    if n < 1 or k < 1:
        raise ValueError("n and k must be positive")
    a = 4 * 3 ** (n - 1) - 2 ** (n + 1) + 1
    b = -4 * 3**n + (6 * n + 9) * 2**n - 6 * n - 1
    c = 4 * 3 ** (n - 1) + (12 - 4 * n) * 2**n + 4 * n * n - 5
    d = 12 * n + 19
    value = (
        Fraction(a, 8) * k**4
        + Fraction(b, 12) * k**3
        + Fraction(c, 8) * k**2
        + Fraction(d, 12) * k
        + 1
    )
    assert value.denominator == 1
    return value.numerator


def boundary_walk_formula(steps: int, distance: int, r: int) -> int:
    """Closed boundary-walk count G_steps(distance) from the proof."""
    if not (steps >= 1 and 1 <= distance <= r - 1 and r >= steps - 1):
        raise ValueError("parameters outside the proved range")
    if distance >= steps:
        return 2 ** (steps - 1) * (r - 2) + 1
    p = steps - distance
    return (
        2 ** (distance - 1) * 3 ** (p - 1) * r * r
        + (
            2 ** (p - 1)
            + 2 ** (steps - 1)
            - 5 * 2 ** (distance - 1) * 3 ** (p - 1)
        )
        * r
        + 2**distance * 3**p
        - 2**steps
        - 2**p
        + 1
    )


def boundary_walk_counts(r: int, steps_max: int) -> Dict[int, Dict[int, int]]:
    """Direct dynamic program in distance coordinates for the proof lemma."""
    states = tuple((a, b) for a in range(r - 1) for b in range(a + 1, r))
    counts: Dict[State, int] = {state: 1 for state in states}
    boundary = {0: {b: 1 for b in range(1, r)}}
    for steps in range(1, steps_max + 1):
        nxt: Dict[State, int] = {}
        for a, b in states:
            if a:
                nxt[(a, b)] = counts[(a - 1, b - 1)]
            else:
                nxt[(a, b)] = sum(
                    counts[(min(b - 1, c), max(b - 1, c))]
                    for c in range(r)
                    if c != b - 1
                )
        counts = nxt
        boundary[steps] = {b: counts[(0, b)] for b in range(1, r)}
    return boundary


def stable_row_from_boundary_lemma(n: int, k: int) -> int:
    """Evaluate the row by summing the closed lemma, not by matrix walks."""
    if k < max(1, n - 4):
        raise ValueError("outside the stable range")
    r = k + 2
    steps = n - 1
    total = 0
    for a in range(r - 1):
        for b in range(a + 1, r):
            if steps <= a:
                continuations = 1
            else:
                continuations = boundary_walk_formula(steps - a, b - a, r)
            total += (r - b) * (r - a - 1) * continuations
    return total


def recurrence_holds(values: Sequence[int], coefficients: Sequence[int]) -> bool:
    order = len(coefficients) - 1
    return all(
        sum(coefficients[j] * values[index - j] for j in range(order + 1)) == 0
        for index in range(order, len(values))
    )


def run_checks() -> None:
    feasibility = load_feasibility_module()
    checks = 0

    # Exact state set and transition classification.
    for k in range(1, 41):
        r = k + 2
        states = age_states(k)
        assert len(states) == math.comb(k + 2, 2)
        state_set = set(states)
        for i, j in states:
            successors = age_successors(k, (i, j))
            assert set(successors).issubset(state_set)
            assert len(successors) == (1 if j < r else k + 1)
        assert sum(initial_weight(state) for state in states) == stable_row_formula(1, k)
    checks += 1
    print("PASS  triangular age-state classification and transitions (k=1..40)")

    # The new proof automaton versus the earlier equality-pattern quotient.
    for k in range(1, 13):
        assert age_counts(k, 50) == feasibility.quotient_counts(k, 50)
    checks += 1
    print("PASS  age automaton vs independent equality-pattern quotient (k=1..12, n=1..50)")

    # Definition-only routes remain independent of both quotient constructions.
    for k in range(1, 5):
        assert age_counts(k, 15) == feasibility.raw_dfa_counts(k, 15)
    for k in range(1, 4):
        values = age_counts(k, 6)
        for n in range(1, 7):
            assert values[n - 1] == feasibility.canonical_count(k, n)
    checks += 1
    print("PASS  age automaton vs raw DFA and literal canonical enumeration")

    # Displayed OEIS data.
    columns = {k: age_counts(k, 10) for k in range(1, 11)}
    for n, row in enumerate(feasibility.OEIS_A242322_10_BY_10, start=1):
        for k, expected in enumerate(row, start=1):
            assert columns[k][n - 1] == expected
    checks += 1
    print("PASS  first 10 x 10 displayed values of OEIS A242322")

    # Exact characteristic polynomials, unimodularity, and scalar minimality
    # as a finite computational check (minimality is not used in the theorem).
    for k in range(1, 11):
        matrix = transition_matrix(k)
        characteristic = characteristic_coefficients(matrix)
        assert abs(characteristic[-1]) == 1
        values = age_counts(k, 3 * len(characteristic))
        assert recurrence_holds(values, characteristic)
        bm = feasibility.berlekamp_massey(values)
        assert bm == [Fraction(value) for value in characteristic]
        numerator_coefficients(k, characteristic)
    checks += 1
    print("PASS  characteristic recurrences, unimodularity, and BM comparison (k=1..10)")

    expected_first_two = (
        (1, -1, -1, -1),
        (1, -1, -2, -2, -2, 1, 1),
    )
    for k, expected in enumerate(expected_first_two, start=1):
        assert tuple(characteristic_coefficients(transition_matrix(k))) == expected
    checks += 1
    print("PASS  column k=1 and k=2 recurrences displayed on OEIS")

    # Closed boundary-walk lemma, including the limiting r=steps-1 case.
    for r in range(3, 31):
        boundary = boundary_walk_counts(r, r + 1)
        for steps in range(1, r + 2):
            if r < steps - 1:
                continue
            for distance in range(1, r):
                expected = boundary_walk_formula(steps, distance, r)
                assert boundary[steps][distance] == expected
    checks += 1
    print("PASS  closed boundary-walk lemma including r=steps-1 (r=3..30)")

    # Stable rows and the exact boundary claimed in the theorem.
    for n in range(1, 41):
        first_k = max(1, n - 4)
        for k in range(first_k, first_k + 9):
            assert age_counts(k, n)[-1] == stable_row_formula(n, k)
            assert stable_row_from_boundary_lemma(n, k) == stable_row_formula(n, k)
    for n in range(1, 101):
        first_k = max(1, n - 4)
        for k in (first_k, first_k + 1, first_k + 7):
            assert stable_row_from_boundary_lemma(n, k) == stable_row_formula(n, k)
    assert age_counts(1, 6)[-1] == 149
    assert stable_row_formula(6, 1) == 151
    checks += 1
    print(
        "PASS  stable-row theorem via matrix and closed-lemma sums "
        "(through n=100; uniform boundary is sharp)"
    )

    print(f"ALL {checks} THEOREM-ORIENTED VERIFICATION LAYERS PASSED")


if __name__ == "__main__":
    run_checks()
