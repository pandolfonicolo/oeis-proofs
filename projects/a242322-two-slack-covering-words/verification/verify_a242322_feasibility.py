#!/usr/bin/env python3
# SPDX-License-Identifier: MIT

"""Exact feasibility checks for the two-slack covering words in OEIS A242322.

This is discovery infrastructure, not a proof of the empirical formulas on
OEIS.  It deliberately compares three routes:

1. literal enumeration of canonical restricted-growth words;
2. a raw labeled last-block DFA, divided by q!;
3. an equality-pattern quotient transfer system.

The quotient implementation also performs separated fit/hold-out experiments
for the empirical column recurrences and stable-row quartics.
"""

from __future__ import annotations

import itertools
import math
from collections import defaultdict
from fractions import Fraction
from typing import DefaultDict, Dict, Iterable, List, Sequence, Tuple


Pattern = Tuple[int, ...]


# First 10 rows and 10 columns displayed on OEIS A242322.
# Rows are n=1,...,10 and columns are k=1,...,10.
# Source: https://oeis.org/A242322, accessed 2026-07-23.
OEIS_A242322_10_BY_10: Tuple[Tuple[int, ...], ...] = (
    (7, 25, 65, 140, 266, 462, 750, 1155, 1705, 2431),
    (13, 61, 185, 440, 896, 1638, 2766, 4395, 6655, 9691),
    (24, 145, 503, 1300, 2801, 5334, 9290, 15123, 23350, 34551),
    (44, 337, 1316, 3648, 8231, 16194, 28897, 47931, 75118, 112511),
    (81, 781, 3398, 10012, 23486, 47466, 86381, 145443, 230647, 348771),
    (149, 1829, 8801, 27368, 66366, 137166, 253674, 432331, 692113, 1054531),
    (274, 4269, 23069, 75236, 187671, 395166, 740496, 1274419, 2055676, 3150991),
    (504, 9957, 60197, 208976, 533801, 1141290, 2161503, 3749211, 6083896, 9369751),
    (927, 23233, 156887, 577964, 1530356, 3312546, 6326951, 11042115, 18002245, 27827211),
    (1705, 54225, 408962, 1596216, 4371836, 9669270, 18590776, 32600811, 53341987, 82686971),
)


def canonicalize(values: Iterable[int]) -> Pattern:
    """Relabel values by order of first appearance."""
    labels: Dict[int, int] = {}
    out: List[int] = []
    for value in values:
        if value not in labels:
            labels[value] = len(labels)
        out.append(labels[value])
    return tuple(out)


def near_rainbow_patterns(length: int, blocks: int) -> Tuple[Pattern, ...]:
    """All set-partition patterns when length-blocks is at most two.

    The explicit construction avoids enumerating all set partitions.  Defect
    one is one pair.  Defect two is one triple or two disjoint pairs.
    """
    if not 1 <= blocks <= length:
        return ()
    defect = length - blocks
    patterns = set()
    if defect == 0:
        patterns.add(tuple(range(length)))
    elif defect == 1:
        for pair in itertools.combinations(range(length), 2):
            raw = list(range(length))
            raw[pair[1]] = raw[pair[0]]
            patterns.add(canonicalize(raw))
    elif defect == 2:
        for triple in itertools.combinations(range(length), 3):
            raw = list(range(length))
            raw[triple[1]] = raw[triple[0]]
            raw[triple[2]] = raw[triple[0]]
            patterns.add(canonicalize(raw))
        for four in itertools.combinations(range(length), 4):
            a, b, c, d = four
            for first, second in (
                ((a, b), (c, d)),
                ((a, c), (b, d)),
                ((a, d), (b, c)),
            ):
                raw = list(range(length))
                raw[first[1]] = raw[first[0]]
                raw[second[1]] = raw[second[0]]
                patterns.add(canonicalize(raw))
    else:
        raise ValueError("explicit generator supports defect at most two")
    result = tuple(sorted(patterns))
    assert all(len(set(pattern)) == blocks for pattern in result)
    return result


def quotient_states(q: int) -> Tuple[Pattern, ...]:
    """Possible equality patterns of the last q+1 symbols."""
    states = set(near_rainbow_patterns(q + 1, q))
    if q >= 2:
        states.update(near_rainbow_patterns(q + 1, q - 1))
    return tuple(sorted(states))


def quotient_transitions(q: int, state: Pattern) -> Dict[Pattern, int]:
    """Exact orbit-transition multiplicities from one suffix pattern."""
    symbols_present = len(set(state))
    transitions: DefaultDict[Pattern, int] = defaultdict(int)
    for symbol in range(q):
        if symbols_present == q - 1 and symbol != q - 1:
            continue
        target = canonicalize(state[1:] + (symbol,))
        assert len(set(target)) >= q - 1
        transitions[target] += 1
    return dict(transitions)


def quotient_counts(k: int, n_max: int) -> List[int]:
    """Count canonical words using the equality-pattern quotient."""
    if k < 1 or n_max < 1:
        raise ValueError("k and n_max must be positive")
    q = k + 1
    states = quotient_states(q)
    state_set = set(states)

    # At n=1 the whole word is one valid q+2 window.  Its canonical
    # representatives are exactly the patterns with q blocks.
    counts: DefaultDict[Pattern, int] = defaultdict(int)
    for word in near_rainbow_patterns(q + 2, q):
        counts[canonicalize(word[1:])] += 1
    assert set(counts).issubset(state_set)

    transitions = {state: quotient_transitions(q, state) for state in states}
    for state, outgoing in transitions.items():
        assert set(outgoing).issubset(state_set)
        expected_degree = q if len(set(state)) == q else 1
        assert sum(outgoing.values()) == expected_degree
    out = [sum(counts.values())]
    for _ in range(2, n_max + 1):
        nxt: DefaultDict[Pattern, int] = defaultdict(int)
        for state, weight in counts.items():
            for target, multiplicity in transitions[state].items():
                nxt[target] += weight * multiplicity
        counts = nxt
        out.append(sum(counts.values()))
    return out


def raw_dfa_counts(k: int, n_max: int) -> List[int]:
    """Definition-only labeled count, divided by the free q! action."""
    if k < 1 or n_max < 1:
        raise ValueError("k and n_max must be positive")
    q = k + 1
    alphabet = tuple(range(q))
    full = frozenset(alphabet)
    counts: Dict[Pattern, int] = {
        block: 1 for block in itertools.product(alphabet, repeat=q + 1)
    }
    divisor = math.factorial(q)
    out: List[int] = []
    for _ in range(n_max):
        nxt: DefaultDict[Pattern, int] = defaultdict(int)
        for block, weight in counts.items():
            for symbol in alphabet:
                if frozenset(block + (symbol,)) == full:
                    nxt[block[1:] + (symbol,)] += weight
        counts = nxt
        labeled = sum(counts.values())
        assert labeled % divisor == 0
        out.append(labeled // divisor)
    return out


def canonical_count(k: int, n: int) -> int:
    """Literal depth-first enumeration of restricted-growth words."""
    if k < 1 or n < 1:
        raise ValueError("k and n must be positive")
    q = k + 1
    length = n + q + 1
    full = set(range(q))
    word = [0]
    total = 0

    def dfs(current_max: int) -> None:
        nonlocal total
        if len(word) == length:
            total += 1
            return
        upper = min(q - 1, current_max + 1)
        for symbol in range(upper + 1):
            word.append(symbol)
            if len(word) < q + 2 or set(word[-(q + 2) :]) == full:
                dfs(max(current_max, symbol))
            word.pop()

    dfs(0)
    return total


def berlekamp_massey(values: Sequence[int]) -> List[Fraction]:
    """Return the minimal connection polynomial over the rationals."""
    sequence = [Fraction(value) for value in values]
    connection = [Fraction(1)]
    previous = [Fraction(1)]
    order = 0
    shift = 1
    last_discrepancy = Fraction(1)

    for index in range(len(sequence)):
        discrepancy = sequence[index]
        for j in range(1, order + 1):
            discrepancy += connection[j] * sequence[index - j]
        if discrepancy == 0:
            shift += 1
            continue

        saved = connection[:]
        factor = -discrepancy / last_discrepancy
        required = len(previous) + shift
        if len(connection) < required:
            connection.extend([Fraction(0)] * (required - len(connection)))
        for j, coefficient in enumerate(previous):
            connection[j + shift] += factor * coefficient

        if 2 * order <= index:
            order = index + 1 - order
            previous = saved
            last_discrepancy = discrepancy
            shift = 1
        else:
            shift += 1

    return connection[: order + 1]


def recurrence_holds(
    values: Sequence[int], connection: Sequence[Fraction], start: int
) -> bool:
    order = len(connection) - 1
    return all(
        sum(connection[j] * values[index - j] for j in range(order + 1)) == 0
        for index in range(max(order, start), len(values))
    )


def finite_differences(values: Sequence[int], times: int) -> List[int]:
    result = list(values)
    for _ in range(times):
        result = [b - a for a, b in zip(result, result[1:])]
    return result


def run_checks() -> None:
    checks = 0

    # Structural counts of near-rainbow equality patterns.
    for q in range(2, 31):
        one_defect = len(near_rainbow_patterns(q + 1, q))
        two_defects = len(near_rainbow_patterns(q + 1, q - 1))
        assert one_defect == math.comb(q + 1, 2)
        expected_two = math.comb(q + 1, 3) + 3 * math.comb(q + 1, 4)
        assert two_defects == expected_two
        initial_words = len(near_rainbow_patterns(q + 2, q))
        assert initial_words == math.comb(q + 2, 3) + 3 * math.comb(q + 2, 4)
    checks += 1
    print("PASS  explicit equality-pattern classification (q=2..30)")

    # Literal canonical enumeration is intentionally small and independent.
    for k in range(1, 4):
        quotient = quotient_counts(k, 6)
        for n in range(1, 7):
            assert canonical_count(k, n) == quotient[n - 1]
    checks += 1
    print("PASS  literal restricted-growth enumeration vs quotient (k=1..3, n=1..6)")

    # Raw definition-only DFA, without quotient-state assumptions.
    for k in range(1, 5):
        assert raw_dfa_counts(k, 15) == quotient_counts(k, 15)
    checks += 1
    print("PASS  raw labeled DFA vs quotient (k=1..4, n=1..15)")

    # Live OEIS display table.
    columns = {k: quotient_counts(k, 10) for k in range(1, 11)}
    for n, row in enumerate(OEIS_A242322_10_BY_10, start=1):
        for k, expected in enumerate(row, start=1):
            assert columns[k][n - 1] == expected
    checks += 1
    print("PASS  first 10 x 10 displayed values of OEIS A242322")

    # Fit each recurrence on the first 60 terms; validate on 40 fresh terms.
    inferred_orders = []
    for k in range(1, 7):
        values = quotient_counts(k, 100)
        connection = berlekamp_massey(values[:60])
        assert recurrence_holds(values[:60], connection, 0)
        assert recurrence_holds(values, connection, 60)
        inferred_orders.append(len(connection) - 1)
    expected_orders = [math.comb(k + 2, 2) for k in range(1, 7)]
    assert inferred_orders == expected_orders
    assert berlekamp_massey(quotient_counts(1, 60)) == [
        Fraction(1),
        Fraction(-1),
        Fraction(-1),
        Fraction(-1),
    ]
    assert berlekamp_massey(quotient_counts(2, 60)) == [
        Fraction(1),
        Fraction(-1),
        Fraction(-2),
        Fraction(-2),
        Fraction(-2),
        Fraction(1),
        Fraction(1),
    ]
    checks += 1
    print(
        "PASS  rational BM fit on n=1..60 and disjoint hold-out n=61..100; "
        f"orders={inferred_orders}"
    )

    # Eventual quarticity: use five stable-range values and four held-out
    # values.  Vanishing fifth differences over all nine values is equivalent.
    # The threshold k>=max(1,n-4) is itself only a tested candidate here.
    for n in range(1, 13):
        first_k = max(1, n - 4)
        row = [quotient_counts(k, n)[-1] for k in range(first_k, first_k + 9)]
        assert finite_differences(row, 5) == [0] * 4
    checks += 1
    print(
        "PASS  candidate stable-row quarticity with four held-out k-values "
        "(n=1..12, k>=max(1,n-4))"
    )

    print(f"PASS  all {checks} feasibility checks")
    print("STATUS feasibility checks only; theorem status is audited separately")


if __name__ == "__main__":
    run_checks()
