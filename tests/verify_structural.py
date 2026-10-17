#!/usr/bin/env python3
"""Independent finite checks of proof reductions, never a proof in Lean."""
from math import gcd
from verify_zolotarev import permutation_sign_mod, jacobi


def primes_upto(n):
    return [p for p in range(3, n + 1, 2) if all(p % d for d in range(2, int(p**0.5) + 1))]


def gauss_flip_sign(a, n):
    assert n > 0 and n % 2 == 1 and gcd(a, n) == 1
    flips = sum((a * x) % n > n // 2 for x in range(1, n // 2 + 1))
    return -1 if flips % 2 else 1


def run():
    # The signed-pair reduction, across all odd positive n up to 501.
    gauss_checks = 0
    for n in range(1, 502, 2):
        for a in range(n):
            if gcd(a, n) != 1:
                continue
            s = gauss_flip_sign(a, n)
            assert s == permutation_sign_mod(a, n), (a, n, s)
            assert s == jacobi(a, n), (a, n, s)
            gauss_checks += 1

    # The prime-power reduction, using powers p^k up to 501.
    power_checks = 0
    for p in primes_upto(501):
        n, k = p, 1
        while n <= 501:
            for a in range(1, n):
                if a % p:
                    expected = jacobi(a, p)**k
                    actual = permutation_sign_mod(a, n)
                    assert actual == expected, (a, p, k, actual, expected)
                    power_checks += 1
            n *= p
            k += 1

    # CRT permutation-sign law for coprime odd m,n and every unit modulo mn,
    # restricting mn to keep the exhaustive check small and reproducible.
    crt_checks = 0
    for m in range(1, 38, 2):
        for n in range(1, 38, 2):
            if gcd(m, n) != 1 or m*n > 225:
                continue
            for a in range(m*n):
                if gcd(a, m*n) != 1:
                    continue
                lhs = permutation_sign_mod(a, m*n)
                rhs = (permutation_sign_mod(a, m)**n) * (permutation_sign_mod(a, n)**m)
                assert lhs == rhs, (a, m, n, lhs, rhs)
                crt_checks += 1
    print(f'PASS signed-pair / Jacobi checks: {gauss_checks:,}')
    print(f'PASS odd prime-power reduction checks: {power_checks:,}')
    print(f'PASS CRT sign identity checks: {crt_checks:,}')
    print('These are finite tests, NOT a Lean or mathematical proof.')


if __name__ == '__main__':
    run()
