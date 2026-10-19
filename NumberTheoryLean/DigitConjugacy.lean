/-
Copyright (c) 2026. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.

AI-assisted proof candidate for Lean 4.33.1 and Mathlib v4.33.1.
NOT YET COMPILED. The existing general Zolotarev theorem still contains `sorry`.
-/
import NumberTheoryLean.CarryDigits
import NumberTheoryLean.AffineTransport
import NumberTheoryLean.Zolotarev
import Mathlib.Tactic

/-!
# Digit conjugacy and sign multiplicativity for an arbitrary odd modulus product

We use the quotient/remainder decomposition of `ZMod (m*n)` to prove
  S(a,m*n) = S(a,n) * S(a,m),
where `S` is the sign of multiplication by the unit represented by `a`.
No coprimality assumption on `m` and `n` is needed.

The only coprimality assumption is `a.Coprime (m*n)`.
This module is an experimental implementation requiring GitHub Actions
compilation before any theorem in it can be claimed Lean-verified.
-/

namespace Zolotarev

/-- Reindex residues by the low `n`-digit and high `m`-digit.
This is NOT the Chinese remainder theorem. -/
noncomputable def digitZModEquiv (m n : ℕ) [NeZero m] [NeZero n] :
    ZMod n × ZMod m ≃ ZMod (m * n) := by
  letI : NeZero (m * n) := ⟨mul_ne_zero (NeZero.ne m) (NeZero.ne n)⟩
  exact
    ((ZMod.finEquiv n).symm.toEquiv.prodCongr
      (ZMod.finEquiv m).symm.toEquiv).trans
      ((digitEquiv m n).trans (ZMod.finEquiv (m * n)).toEquiv)

/-- The value of the digit equivalence is precisely `r + n*t`. -/
theorem digitZModEquiv_val (m n : ℕ) [NeZero m] [NeZero n]
    (r : ZMod n) (t : ZMod m) :
    (digitZModEquiv m n (r, t)).val = r.val + n * t.val := by
  cases n with
  | zero => exact (NeZero.ne 0 rfl).elim
  | succ n =>
    cases m with
    | zero => exact (NeZero.ne 0 rfl).elim
    | succ m => rfl

/-- Conjugacy of multiplication on a product modulus with its affine digit action.
The two factor multipliers are obtained from the same natural number `a`.
The nonzero modulus instances are passed implicitly. -/
theorem digitZModEquiv_mul (m n a : ℕ) [NeZero m] [NeZero n] [NeZero (m * n)]
    (han : a.Coprime n) (ham : a.Coprime m)
    (hamn : a.Coprime (m * n)) (r : ZMod n) (t : ZMod m) :
    digitZModEquiv m n
      (mulPerm n (ZMod.unitOfCoprime a han) r,
        (((a * r.val) / n : ℕ) : ZMod m) +
          mulPerm m (ZMod.unitOfCoprime a ham) t) =
      mulPerm (m * n) (ZMod.unitOfCoprime a hamn)
        (digitZModEquiv m n (r, t)) := by
  letI : NeZero (m * n) := ⟨mul_ne_zero (NeZero.ne m) (NeZero.ne n)⟩
  have hlow :
      (mulPerm n (ZMod.unitOfCoprime a han) r).val = (a * r.val) % n := by
    rw [mulPerm_apply, ZMod.coe_unitOfCoprime, ZMod.val_mul, ZMod.val_natCast]
    simp [Nat.mul_mod]
  have hmulHigh :
      (mulPerm m (ZMod.unitOfCoprime a ham) t).val = (a * t.val) % m := by
    rw [mulPerm_apply, ZMod.coe_unitOfCoprime, ZMod.val_mul, ZMod.val_natCast]
    simp [Nat.mul_mod]
  have hhigh :
      ((((a * r.val) / n : ℕ) : ZMod m) +
          mulPerm m (ZMod.unitOfCoprime a ham) t).val =
        (a * t.val + (a * r.val) / n) % m := by
    rw [ZMod.val_add, ZMod.val_natCast, hmulHigh]
    simp [Nat.add_mod, Nat.add_comm]
  apply ZMod.val_injective (m * n)
  calc
    (digitZModEquiv m n
        (mulPerm n (ZMod.unitOfCoprime a han) r,
          ((((a * r.val) / n : ℕ) : ZMod m) +
            mulPerm m (ZMod.unitOfCoprime a ham) t))).val =
        (a * r.val) % n + n * ((a * t.val + (a * r.val) / n) % m) := by
      rw [digitZModEquiv_val, hlow, hhigh]
    _ = (a * (r.val + n * t.val)) % (n * m) := by
      exact (mul_digit_mod_product a r.val t.val n m (NeZero.pos n)).symm
    _ = (a * (r.val + n * t.val)) % (m * n) := by rw [Nat.mul_comm n m]
    _ = (mulPerm (m * n) (ZMod.unitOfCoprime a hamn)
          (digitZModEquiv m n (r, t))).val := by
      rw [mulPerm_apply, ZMod.coe_unitOfCoprime, ZMod.val_mul,
          ZMod.val_natCast, digitZModEquiv_val]
      simp [Nat.mul_mod]

/-- Multiplicativity of the permutation sign across any two odd factors.
It works even if `m` and `n` have common prime factors. -/
theorem sign_mul_modulus (m n a : ℕ) [NeZero m] [NeZero n] [NeZero (m * n)]
    (hm : Odd m) (hn : Odd n) (hamn : a.Coprime (m * n)) :
    Equiv.Perm.sign (mulPerm (m * n) (ZMod.unitOfCoprime a hamn)) =
      Equiv.Perm.sign
          (mulPerm n (ZMod.unitOfCoprime a
            (Nat.Coprime.of_dvd_right (dvd_mul_left n m) hamn))) *
        Equiv.Perm.sign
          (mulPerm m (ZMod.unitOfCoprime a
            (Nat.Coprime.of_dvd_right (dvd_mul_right m n) hamn))) := by
  letI : NeZero (m * n) := ⟨mul_ne_zero (NeZero.ne m) (NeZero.ne n)⟩
  let han : a.Coprime n := Nat.Coprime.of_dvd_right (dvd_mul_left n m) hamn
  let ham : a.Coprime m := Nat.Coprime.of_dvd_right (dvd_mul_right m n) hamn
  let f : Equiv.Perm (ZMod n) := mulPerm n (ZMod.unitOfCoprime a han)
  let g : Equiv.Perm (ZMod m) := mulPerm m (ZMod.unitOfCoprime a ham)
  let q : Equiv.Perm (ZMod (m * n)) :=
    mulPerm (m * n) (ZMod.unitOfCoprime a hamn)
  let carry : ZMod n → ZMod m := fun r => (((a * r.val) / n : ℕ) : ZMod m)
  have hconj : ∀ x : ZMod n × ZMod m,
      digitZModEquiv m n (f x.1, carry x.1 + g x.2) =
        q (digitZModEquiv m n x) := by
    rintro ⟨r, t⟩
    exact digitZModEquiv_mul m n a han ham hamn r t
  have hs := sign_of_affine_digit_conjugacy_odd
    (A := ZMod n) (B := ZMod m) (C := ZMod (m * n))
    (by simpa only [ZMod.card] using hn)
    (by simpa only [ZMod.card] using hm)
    f g carry q (digitZModEquiv m n) hconj
  exact hs

end Zolotarev
