#!/usr/bin/env python3
# SPDX-License-Identifier: MIT

"""Exact, dependency-free regression checks for the minimality proof.

The general proof is in docs/general_minimality_proof.md and the manuscript.
These finite checks catch transcription/sign errors in its identities; they
do not replace or justify the general proof.
"""

from __future__ import annotations

import argparse
from typing import Dict, Tuple, Union

import verify_a242322_theorems as theorem


class LaurentPolynomial:
    """An exact element of Z[t,t^-1,z,z^-1], stored by (t,z) exponents."""

    def __init__(self, value: Union[int, Dict[Tuple[int, int], int]] = 0):
        if isinstance(value, int):
            value = {(0, 0): value}
        self.terms = {powers: coefficient for powers, coefficient in value.items() if coefficient}

    @staticmethod
    def coerce(value: Union[int, LaurentPolynomial]) -> LaurentPolynomial:
        return value if isinstance(value, LaurentPolynomial) else LaurentPolynomial(value)

    def __add__(self, other: Union[int, LaurentPolynomial]) -> LaurentPolynomial:
        other = self.coerce(other)
        terms = self.terms.copy()
        for powers, coefficient in other.terms.items():
            terms[powers] = terms.get(powers, 0) + coefficient
        return LaurentPolynomial(terms)

    __radd__ = __add__

    def __neg__(self) -> LaurentPolynomial:
        return LaurentPolynomial({powers: -coefficient for powers, coefficient in self.terms.items()})

    def __sub__(self, other: Union[int, LaurentPolynomial]) -> LaurentPolynomial:
        return self + -self.coerce(other)

    def __rsub__(self, other: Union[int, LaurentPolynomial]) -> LaurentPolynomial:
        return self.coerce(other) + -self

    def __mul__(self, other: Union[int, LaurentPolynomial]) -> LaurentPolynomial:
        other = self.coerce(other)
        terms: Dict[Tuple[int, int], int] = {}
        for (a, b), left in self.terms.items():
            for (c, d), right in other.terms.items():
                powers = (a + c, b + d)
                terms[powers] = terms.get(powers, 0) + left * right
        return LaurentPolynomial(terms)

    __rmul__ = __mul__

    def __pow__(self, exponent: int) -> LaurentPolynomial:
        if exponent < 0:
            if len(self.terms) != 1:
                raise ValueError("Only Laurent monomial units have negative powers")
            (a, b), coefficient = next(iter(self.terms.items()))
            if abs(coefficient) != 1:
                raise ValueError("Only Laurent monomial units have negative powers")
            return LaurentPolynomial({(a * exponent, b * exponent): coefficient if exponent % 2 else 1})
        result, base = LaurentPolynomial(1), self
        while exponent:
            if exponent % 2:
                result = result * base
            base = base * base
            exponent //= 2
        return result

    def reflect(self) -> LaurentPolynomial:
        """Substitute t -> z/t, keeping z fixed."""
        return LaurentPolynomial({(-a, a + b): coefficient for (a, b), coefficient in self.terms.items()})

    def derivative_t(self) -> LaurentPolynomial:
        return LaurentPolynomial({(a - 1, b): a * coefficient for (a, b), coefficient in self.terms.items()})

    def at_t_one(self) -> LaurentPolynomial:
        terms: Dict[Tuple[int, int], int] = {}
        for (_, b), coefficient in self.terms.items():
            terms[(0, b)] = terms.get((0, b), 0) + coefficient
        return LaurentPolynomial(terms)

    def __eq__(self, other: object) -> bool:
        if isinstance(other, int):
            other = LaurentPolynomial(other)
        return isinstance(other, LaurentPolynomial) and self.terms == other.terms


T = LaurentPolynomial({(1, 0): 1})
Z = LaurentPolynomial({(0, 1): 1})


def zero(expression: LaurentPolynomial) -> None:
    assert expression == 0, expression.terms


def check_polynomial_engine() -> None:
    """Check the elementary operations used by the subsequent identities."""
    zero((T + Z) * (T - Z) - T**2 + Z**2)
    zero((T + 2 * Z).reflect().reflect() - T - 2 * Z)
    zero((T**-2 * Z**3).derivative_t() + 2 * T**-3 * Z**3)
    zero((T + T**-1 - 2).at_t_one())
    zero((T + 1)**3 - T**3 - 3 * T**2 - 3 * T - 1)


def check_case(m: int) -> None:
    a = (1 - T) * (2 * Z - T)
    h = -T ** (m + 2) * (Z - T)
    c = T * (Z + 1 - 2 * T)
    q = -2 * T**2 + (4 * Z + 1 - Z ** (m + 2)) * T - 2 * Z
    r = (Z + 1 - 2 * T) * (2 * T - 1) + T ** (m + 1) * ((Z + 1) * T - 2 * Z)

    zero(a * a.reflect() - h * h.reflect() - Z * (1 - T) * (T - Z) * T**-2 * q)
    zero(c * a.reflect() + h * c.reflect() - Z * (T - Z) * T**-1 * r)
    zero(r.at_t_one())
    zero(r.derivative_t().at_t_one() - (m - 2) * (1 - Z))
    zero(q.at_t_one() - 2 * Z + 1 + Z ** (m + 2))

    K = [
        [
            (Z ** (d + 1) if e + 1 <= m - d else LaurentPolynomial())
            + (Z ** (d - e) if e < d else LaurentPolynomial())
            for e in range(m)
        ]
        for d in range(m)
    ]
    M = [[int(d == e) - K[d][e] for e in range(m)] for d in range(m)]

    # Check the functional identity BEFORE imposing the nullvector condition.
    # Basis vectors suffice since each expression is linear in v.
    for d in range(1, m + 1):
        V = T**d
        residual = sum(M[d - 1][e - 1] * T**e for e in range(1, m + 1))
        zero(a * V - c * Z**d - h * V.reflect() - (1 - T) * (Z - T) * residual)

    k, r_size = m - 1, m + 1
    # Independently eliminate deterministic interior chains in the original
    # transition graph and compare every boundary coefficient with K.
    for d in range(1, m + 1):
        obtained = [LaurentPolynomial() for _ in range(m)]
        for i, j in theorem.age_successors(k, (r_size - d, r_size)):
            obtained[j - i - 1] += Z ** (r_size - j + 1)
        for e in range(m):
            zero(obtained[e] - K[d - 1][e])

    states = theorem.age_states(k)
    index = {pair: position for position, pair in enumerate(states)}
    matrix = theorem.transition_matrix(k)
    # Check the explicit coordinate action used for invertibility/reversal.
    for column, (i, j) in enumerate(states):
        expected = [0] * len(states)
        expected[index[(j - 1, r_size)]] += 1
        if i >= 2:
            expected[index[(i - 1, j - 1)]] += 1
            expected[index[(i - 1, r_size)]] += 1
        assert [row[column] for row in matrix] == expected

    print(f"PASS m={m}, k={k}: reflection algebra, boundary Schur complement, coordinate action")


def main() -> None:
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--max-m", type=int, default=10, help="largest boundary dimension checked (default: 10)")
    args = parser.parse_args()
    if args.max_m < 2:
        parser.error("--max-m must be at least 2")
    check_polynomial_engine()
    for m in range(2, args.max_m + 1):
        check_case(m)
    print("PASS all exact consistency checks; the general proof is supplied separately in the manuscript")


if __name__ == "__main__":
    main()
