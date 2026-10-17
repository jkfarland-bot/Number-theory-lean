#!/usr/bin/env python3
"""Independent FINITE checks only; NOT a Lean proof of Zolotarev's lemma."""
from math import gcd


def jacobi(a: int, n: int) -> int:
    assert n > 0 and n % 2 == 1
    a %= n
    value = 1
    while a:
        while a % 2 == 0:
            a //= 2
            if n % 8 in (3, 5):
                value = -value
        a, n = n, a
        if a % 4 == 3 and n % 4 == 3:
            value = -value
        a %= n
    return value if n == 1 else 0


def permutation_sign_mod(a: int, n: int) -> int:
    """Sign from cycle decomposition of x -> a*x (mod n)."""
    assert n > 0 and gcd(a, n) == 1
    visited = bytearray(n)
    cycles = 0
    for i in range(n):
        if not visited[i]:
            cycles += 1
            x = i
            while not visited[x]:
                visited[x] = True
                x = (a * x) % n
    return -1 if (n - cycles) % 2 else 1


def run(max_n: int = 501) -> int:
    count = 0
    for n in range(1, max_n + 1, 2):
        for a in range(n):
            if gcd(a, n) != 1:
                continue
            actual = permutation_sign_mod(a, n)
            expected = jacobi(a, n)
            if actual != expected:
                raise AssertionError(
                    f"COUNTEREXAMPLE a={a}, n={n}, sign={actual}, Jacobi={expected}"
                )
            count += 1
    print(f"PASS: {count:,} pairs (a,n); every odd n <= {max_n}, gcd(a,n)=1")
    print("This is a finite computational check, not a formal Lean proof.")
    return count


if __name__ == "__main__":
    run()
