#!/usr/bin/env python3
# SPDX-License-Identifier: MIT

"""Exploratory exact checks for the A242322 minimal-order question.

The time-reversal identities checked here have a direct general proof recorded
in docs/minimality_research.md.  The controllability-determinant formula is a
conjecture: checking finitely many k does not prove it.
"""

from __future__ import annotations

import argparse
import math
from typing import List, Sequence

import verify_a242322_theorems as theorem


Matrix = List[List[int]]


def transpose(matrix: Sequence[Sequence[int]]) -> Matrix:
    return [list(column) for column in zip(*matrix)]


def matrix_vector(matrix: Sequence[Sequence[int]], vector: Sequence[int]) -> List[int]:
    return [
        sum(coefficient * value for coefficient, value in zip(row, vector))
        for row in matrix
    ]


def bareiss_determinant(matrix: Sequence[Sequence[int]]) -> int:
    """Return an exact integer determinant by fraction-free elimination."""
    work = [list(row) for row in matrix]
    size = len(work)
    if size == 0:
        return 1

    sign = 1
    previous = 1
    for pivot_index in range(size - 1):
        if work[pivot_index][pivot_index] == 0:
            swap_index = next(
                (
                    row
                    for row in range(pivot_index + 1, size)
                    if work[row][pivot_index] != 0
                ),
                None,
            )
            if swap_index is None:
                return 0
            work[pivot_index], work[swap_index] = (
                work[swap_index],
                work[pivot_index],
            )
            sign = -sign

        pivot = work[pivot_index][pivot_index]
        for row in range(pivot_index + 1, size):
            left = work[row][pivot_index]
            for column in range(pivot_index + 1, size):
                numerator = (
                    work[row][column] * pivot
                    - left * work[pivot_index][column]
                )
                assert numerator % previous == 0
                work[row][column] = numerator // previous
            work[row][pivot_index] = 0
        previous = pivot

    return sign * work[-1][-1]


def reversal_form(k: int) -> Matrix:
    states = theorem.age_states(k)
    r = k + 2
    return [
        [
            int(i + u >= r + 1 and j + v >= r + 1)
            + int(i + v >= r + 1 and j + u >= r + 1)
            for u, v in states
        ]
        for i, j in states
    ]


def column_reversal_indices(k: int) -> List[int]:
    states = theorem.age_states(k)
    index = {state: position for position, state in enumerate(states)}
    r = k + 2
    return [index[(r + 1 - v, r + 1 - u)] for u, v in states]


def controllability_matrix(k: int) -> Matrix:
    matrix = theorem.transition_matrix(k)
    size = len(matrix)
    columns: List[List[int]] = []
    vector = [1] * size
    for _ in range(size):
        columns.append(vector)
        vector = matrix_vector(matrix, vector)
    return [
        [columns[column][row] for column in range(size)]
        for row in range(size)
    ]


def determinant_exponent(k: int) -> int:
    if k % 2 == 0:
        m = k // 2
        return m * (m - 1) * (2 * m + 3) // 2
    m = (k - 1) // 2
    return m * m * (m + 2)


def predicted_controllability_determinant(k: int) -> int:
    if k == 1:
        return 1
    state_count = math.comb(k + 2, 2)
    previous_count = math.comb(k + 1, 2)
    return (
        2 ** determinant_exponent(k)
        * k ** (state_count - 1)
        * (k - 1) ** (previous_count - 1)
    )


def verify_reversal_form(k: int) -> None:
    matrix = theorem.transition_matrix(k)
    form = reversal_form(k)
    states = theorem.age_states(k)
    size = len(states)

    assert form == transpose(form)
    assert matrix_vector(form, [1] * size) == [
        theorem.initial_weight(state) for state in states
    ]
    assert theorem.matrix_multiply(transpose(matrix), form) == (
        theorem.matrix_multiply(form, matrix)
    )

    reversed_columns = column_reversal_indices(k)
    triangular = [
        [form[row][reversed_columns[column]] for column in range(size)]
        for row in range(size)
    ]
    assert all(
        triangular[row][column] == 0
        for row in range(size)
        for column in range(row + 1, size)
    )
    assert all(triangular[index][index] == 1 for index in range(size))


def main() -> None:
    parser = argparse.ArgumentParser()
    parser.add_argument(
        "--max-k",
        type=int,
        default=15,
        help="largest fixed k checked exactly (default: 15)",
    )
    args = parser.parse_args()
    if args.max_k < 1:
        parser.error("--max-k must be positive")

    for k in range(1, args.max_k + 1):
        verify_reversal_form(k)
        determinant = abs(bareiss_determinant(controllability_matrix(k)))
        predicted = predicted_controllability_determinant(k)
        assert determinant == predicted
        print(
            "PASS",
            f"k={k}",
            f"states={math.comb(k + 2, 2)}",
            "reversal identities",
            "determinant conjecture",
        )

    print(
        f"PASS all exploratory checks for k=1..{args.max_k}; "
        "finite checks are not a proof of the determinant conjecture"
    )


if __name__ == "__main__":
    main()
