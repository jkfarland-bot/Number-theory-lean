"""Independent permutation checks; these do NOT replace Lean verification."""
from math import gcd

def permutation_sign(p):
    n = len(p)
    if sorted(p) != list(range(n)):
        raise ValueError('not a permutation')
    seen = set()
    cycles = 0
    for i in range(n):
        if i not in seen:
            cycles += 1
            j = i
            while j not in seen:
                seen.add(j)
                j = p[j]
    return -1 if (n - cycles) % 2 else 1


def run():
    translations = 0
    affine = 0
    for n in range(1, 100, 2):
        for c in range(n):
            p = [(x+c) % n for x in range(n)]
            assert permutation_sign(p) == 1, (n,c)
            translations += 1
        for a in range(1, n + 1):
            if gcd(a, n) != 1:
                continue
            sigma = [(a*x) % n for x in range(n)]
            s = permutation_sign(sigma)
            for c in range(n):
                p = [(a*x+c)%n for x in range(n)]
                assert permutation_sign(p) == s, (n,a,c)
                affine += 1
    print(f'Passed {translations:,} odd-modulus translation checks')
    print(f'Passed {affine:,} odd-modulus affine sign checks')

if __name__ == '__main__':
    run()
