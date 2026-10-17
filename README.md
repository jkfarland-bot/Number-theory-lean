# Zolotarev's lemma for Mathlib — second development iteration

**Status: mathematical proof on paper, but incomplete Lean formalization.**

The module `Mathlib/NumberTheory/LegendreSymbol/Zolotarev.lean` has **one
explicit `sorry`** in the main theorem `zolotarev_unit`, and it has not yet
been compiled by Lean/Lake. This directory is not a proof certificate. It is
an AI-assisted development package intended for a Lean contributor to check
and finish. A dependent theorem (`zolotarev_nat`) is consequently unverified.

## New in this iteration

- Corrected/clarified the permutation inverse proof and checked the library API
  for `Units.mulLeft_symm`, `Equiv.Perm.sign`, and `jacobiSym.mod_left'`.
- Added power and inverse lemmas for the sign character.
- Added a standalone proof candidate for modulus 1 (`zolotarev_mod_one`).
- Worked out a **complete mathematical proof** reducing the theorem to odd
  prime-power units and CRT. See **`PROOF_PLAN.md`**. The proof uses Mathlib's
  existing `ZMod.isCyclic_units_of_prime_pow` theorem.
- Identified a generic product-permutation sign formula as a potentially useful
  independent Mathlib contribution.
- Added a second, independent proof target via signed pairs / the generalized
  Gauss lemma, suitable for a bridge to Meyer's inversion formula.
- Added exhaustive checks for three separate structural reductions.

## Files

- `Mathlib/NumberTheory/LegendreSymbol/Zolotarev.lean`: proposed theorem
  statements and supporting Lean definitions (uncompiled).
- `PROOF_PLAN.md`: mathematical proof and precise missing Lean obligations.
- `tests/Infrastructure.lean`: uncompiled Lean test cases.
- `tests/verify_zolotarev.py`: check the original theorem by cycle decomposition.
- `tests/verify_structural.py`: check signed pairs, prime-power factors and
  Chinese remainder sign factorization.

## Reproducible tests

From this directory:

```bash
python3 tests/verify_zolotarev.py
python3 tests/verify_structural.py
```

The independent numerical tests cover:

| Property | Passing finite cases |
| --- | ---: |
| Main sign = Jacobi (odd n through 501) | 51,033 |
| Signed-pair sign and Jacobi (odd n through 501) | 51,033 |
| Odd-prime-power factor formula | 23,016 |
| CRT sign product formula | 8,449 |

These are finite tests, not formal proofs.

## How to check Lean compilation

In a recent checkout of `mathlib4`:

1. Copy the `Mathlib/NumberTheory/LegendreSymbol/Zolotarev.lean` file into the
   corresponding Mathlib directory.
2. Copy `tests/Infrastructure.lean` into a separate scratch directory or root.
3. Run:

```bash
lake exe cache get
lake env lean Mathlib/NumberTheory/LegendreSymbol/Zolotarev.lean
lake env lean tests/Infrastructure.lean
```

Compilation with `sorry` does **not** prove the missing theorem. Replace every
`sorry`, check that compilation succeeds without any proof-hole warnings and
review all axioms/theorem dependencies before opening a Mathlib PR.

## Most promising next step

Implement the general sign of product permutations

`sign(f × g) = sign(f)^card(Y) * sign(g)^card(X)`

and the prime-power valuation-layer decomposition. Those two reusable
components are the main remaining tasks in turning the paper proof into Lean.

Do **not** submit the incomplete module as a proof or assert it has been
accepted to Mathlib. Follow Mathlib's AI-disclosure and human-review policies.
