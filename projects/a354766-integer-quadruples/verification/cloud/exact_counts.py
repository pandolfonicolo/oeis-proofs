#!/usr/bin/env python3
"""Finite exact checks only; this program is not a proof of the formulas.

No project code or external packages are imported.  Each model is enumerated
independently from its sum/norm equations, before comparison with formulas.
The complementary pair is recovered by its integer discriminant, avoiding
a dictionary and keeping enumeration memory constant per worker.
"""

import argparse
import base64
from concurrent.futures import ProcessPoolExecutor, as_completed
import csv
import gzip
import hashlib
from math import gcd, isqrt
from pathlib import Path
import time


def pair_count(S, Q, lo, hi):
    """Ordered quadruples with sum S, norm Q, and every coordinate in [lo,hi].

    Enumerate a<=b; then c<=d is uniquely determined by its sum and norm.
    With t0=S-a and R0=Q-a*a, the complementary discriminant D satisfies
      3*D = 6*R0 - 2*t0*t0 - (3*b-t0)**2.
    This gives exact integer bounds on b.  Weights restore both pair orders.
    """
    total = primitive = candidates = 0
    minimum = None
    for a in range(lo, hi + 1):
        t0, R0 = S - a, Q - a * a
        outer = 6 * R0 - 2 * t0 * t0
        if outer < 0:
            continue
        root = isqrt(outer)
        bmin = max(lo, a, (t0 - root + 2) // 3)
        bmax = min(hi, (t0 + root) // 3)
        for b in range(bmin, bmax + 1):
            candidates += 1
            t = t0 - b
            D = 2 * (R0 - b * b) - t * t
            assert D >= 0
            r = isqrt(D)
            if r * r != D or (t - r) % 2:
                continue
            c, d = (t - r) // 2, (t + r) // 2
            if c < lo or d > hi:
                continue
            assert a + b + c + d == S
            assert a * a + b * b + c * c + d * d == Q
            weight = (1 if a == b else 2) * (1 if c == d else 2)
            total += weight
            if gcd(a, b, c, d) == 1:
                primitive += weight
            vmin = min(a, b, c, d)
            minimum = vmin if minimum is None else min(minimum, vmin)
    return total, primitive, minimum, candidates


def dictionary_count(S, Q, lo, hi):
    """Separate small-case implementation using a full ordered-pair table."""
    pairs = {}
    for a in range(lo, hi + 1):
        for b in range(lo, hi + 1):
            q = a * a + b * b
            if q > Q:
                continue
            key = (a + b, q)
            g = gcd(a, b)
            if key in pairs:
                count, old_g = pairs[key]
                assert old_g == g
                pairs[key] = count + 1, g
            else:
                pairs[key] = 1, g
    total = primitive = 0
    for (s, q), (count, g) in pairs.items():
        other = pairs.get((S - s, Q - q))
        if other is not None:
            count2, g2 = other
            total += count * count2
            if gcd(g, g2) == 1:
                primitive += count * count2
    return total, primitive


def primitive_three_squares(Q):
    """Direct ordered signed triples, using two coordinates and integer sqrt."""
    result = 0
    radius = isqrt(Q)
    for x in range(-radius, radius + 1):
        rem = Q - x * x
        yradius = isqrt(rem)
        for y in range(-yradius, yradius + 1):
            z2 = rem - y * y
            z = isqrt(z2)
            if z * z == z2 and gcd(x, y, z) == 1:
                result += 1 if z == 0 else 2
    return result


def primitive_formula(n):
    if n % 4 == 0:
        return 0
    m = n if n % 2 else n // 2
    result, p = 1, 3
    while p * p <= m:
        exponent = 0
        while m % p == 0:
            m //= p
            exponent += 1
        if exponent:
            chi = 0 if p == 3 else (1 if p % 6 == 1 else -1)
            result *= p ** (exponent - 1) * (p - chi)
        p += 2
    if m > 1:
        chi = 0 if m == 3 else (1 if m % 6 == 1 else -1)
        result *= m - chi
    return result


def enumerate_level(args):
    n, max_r3 = args
    standard = pair_count(n, n * n, -n, n)
    radius = isqrt(3 * n * n)
    primary = pair_count(3 * n, 3 * n * n, 0, radius)
    r3 = primitive_three_squares(3 * n * n) if n % 2 and n <= max_r3 else None
    return n, standard, primary, r3


def write_csv(path, header, rows):
    with path.open("w", encoding="utf-8", newline="") as stream:
        writer = csv.writer(stream, lineterminator="\n")
        writer.writerow(header)
        writer.writerows(rows)


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--max-n", type=int, default=300)
    parser.add_argument("--max-r3", type=int, default=75)
    parser.add_argument("--workers", type=int, default=4)
    parser.add_argument("--output", type=Path, default=Path(__file__).resolve().parent)
    parser.add_argument("--emit-payloads", action="store_true")
    args = parser.parse_args()
    if args.max_n < 1 or not 1 <= args.workers <= 4:
        parser.error("max-n must be positive and workers must be in 1..4")
    started = time.monotonic()
    args.output.mkdir(parents=True, exist_ok=True)
    symmetric_rows = []
    for n in range(1, min(args.max_n, 20) + 1):
        radius = isqrt(3 * n * n)
        for S, Q, lo, hi in ((n, n*n, -n, n), (3*n, 3*n*n, 0, radius)):
            direct = pair_count(S, Q, lo, hi)
            assert direct[:2] == dictionary_count(S, Q, lo, hi), (n, S, direct)
        if n <= 12:
            bounded = pair_count(3*n, 3*n*n, 0, radius)
            symmetric = pair_count(3*n, 3*n*n, -radius, radius)
            assert bounded[:3] == symmetric[:3] and symmetric[2] == 0
            symmetric_rows.append((n, radius, *bounded[:3], *symmetric[:3]))
    print("PASS separate ordered-pair dictionary checks through n=20; symmetric primary bounds through n=12", flush=True)
    results = {}
    with ProcessPoolExecutor(max_workers=args.workers) as executor:
        futures = [executor.submit(enumerate_level, (n, args.max_r3))
                   for n in range(1, args.max_n + 1)]
        for future in as_completed(futures):
            n, standard, primary, r3 = future.result()
            results[n] = standard, primary, r3
            if len(results) % 25 == 0 or len(results) == args.max_n:
                print(f"enumerated {len(results)}/{args.max_n}, elapsed={time.monotonic()-started:.3f}s", flush=True)
    predictions = {n: primitive_formula(n) for n in range(1, args.max_n + 1)}
    rows, r3checks, candidates = [], 0, 0
    for n in range(1, args.max_n + 1):
        standard, primary, r3 = results[n]
        st, sp, _, sc = standard
        pt, pp, pmin, pc = primary
        candidates += sc + pc
        P = predictions[n]
        T = sum(predictions[d] for d in range(1, n + 1) if n % d == 0)
        assert all(value % 4 == 0 for value in (st, sp, pt, pp)), (n, standard, primary)
        assert st == pt and sp == pp, ("model mismatch", n, standard, primary)
        assert st == 4 * T and sp == 4 * P, ("formula mismatch", n, standard, T, P)
        assert pmin == 0
        expected_r3 = 8 * P if r3 is not None else ""
        if r3 is not None:
            assert r3 == expected_r3, ("three-square mismatch", n, r3, expected_r3)
            r3checks += 1
        rows.append((n, st, sp, pt, pp, st//4, sp//4, T, P,
                     r3 if r3 is not None else "", expected_r3))
    counts_path = args.output / "counts.csv"
    symmetric_path = args.output / "symmetric_checks.csv"
    write_csv(counts_path, ("n", "standard_total_raw", "standard_primitive_raw",
              "primary_total_raw", "primary_primitive_raw", "A354766_T", "A278085_P",
              "formula_T", "formula_P", "r3prim_3n2", "formula_r3prim_3n2"), rows)
    write_csv(symmetric_path, ("n", "radius", "nonnegative_total", "nonnegative_primitive",
              "nonnegative_min_coordinate", "symmetric_total", "symmetric_primitive",
              "symmetric_min_coordinate"), symmetric_rows)
    print(f"PASS all finite checks: n=1..{args.max_n}; r3 odd n<=min({args.max_r3},{args.max_n}): {r3checks} cases; candidate pairs={candidates}")
    print(f"elapsed_seconds={time.monotonic()-started:.3f}")
    for path in (Path(__file__).resolve(), counts_path, symmetric_path):
        data = path.read_bytes()
        print(f"SHA256 {hashlib.sha256(data).hexdigest()}  {path.name}")
        if args.emit_payloads and path.suffix == ".csv":
            print(f"BEGIN_GZIP_BASE64 {path.name}")
            print(base64.b64encode(gzip.compress(data, mtime=0)).decode("ascii"))
            print(f"END_GZIP_BASE64 {path.name}")


if __name__ == "__main__":
    main()
