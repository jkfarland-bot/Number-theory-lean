/-
Copyright (c) 2026.
Released under Apache 2.0 license as described in the file LICENSE.

Candidate Lean code for Lean 4.33.1 / Mathlib 4.33.1.
The mathematical identities are proved on paper and tested numerically,
but this file has NOT yet been compiled by Lean.
-/
import Mathlib.Data.ZMod.Basic
import Mathlib.Logic.Equiv.Fin.Basic
import Mathlib.Tactic

/-!
# Quotient–remainder coordinates for Zolotarev's lemma

For n>0, represent an integer by x = r + n*t. Multiplication by a
acts on those coordinates as

  r' = a*r % n
  t' = (a*t + a*r/n) % m

when the ambient modulus is n*m. The second coordinate is an affine
map (multiplication by a followed by a carry translation).

The key lemma is `Nat.mod_mul`, already in Lean's Init library.
This module contains no `sorry`. Build it before claiming verification.
-/

namespace Zolotarev

/-- The remainder of a multiplication is independent of the higher digit. -/
theorem mul_digit_remainder (a r t n : ℕ) :
    (a * (r + n * t)) % n = (a * r) % n := by
  calc
    (a * (r + n * t)) % n = (n * (a * t) + a * r) % n := by
      congr 1
      ring
    _ = (a * r) % n := Nat.mul_add_mod _ _ _

/-- The quotient receives a carry from multiplication of the lower digit. -/
theorem mul_digit_quotient (a r t n : ℕ) (hn : 0 < n) :
    (a * (r + n * t)) / n = a * t + (a * r) / n := by
  calc
    (a * (r + n * t)) / n = (n * (a * t) + a * r) / n := by
      congr 1
      ring
    _ = a * t + (a * r) / n := Nat.mul_add_div hn _ _

/-- **Carry identity** for multiplication modulo any product n*m.
No coprimality between n and m is required. -/
theorem mul_digit_mod_product (a r t n m : ℕ) (hn : 0 < n) :
    (a * (r + n * t)) % (n * m) =
      (a * r) % n + n * ((a * t + (a * r) / n) % m) := by
  rw [Nat.mod_mul]
  rw [mul_digit_remainder, mul_digit_quotient a r t n hn]

/-- Encode (low digit mod n, high digit mod m) as a residue in Fin (m*n).
This is purely a reindexing, not a Chinese remainder equivalence, and
therefore requires no coprimality assumption. -/
def digitEquiv (m n : ℕ) : Fin n × Fin m ≃ Fin (m * n) :=
  (Equiv.prodComm (Fin n) (Fin m)).trans finProdFinEquiv

@[simp]
theorem digitEquiv_apply_val (m n : ℕ) (r : Fin n) (t : Fin m) :
    (digitEquiv m n (r, t)).val = r.val + n * t.val := by
  rfl

end Zolotarev
