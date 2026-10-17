/-
Copyright (c) 2026. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.

AI-assisted development draft. Not verified by Lean; contains an explicit `sorry`.
-/
import Mathlib.NumberTheory.LegendreSymbol.JacobiSymbol
import Mathlib.GroupTheory.Perm.Sign
import Mathlib.Algebra.Group.Units.Equiv
import Mathlib.Data.ZMod.Basic
import Mathlib.Tactic

/-!
# Zolotarev's lemma — Mathlib development draft

For odd positive `n`, multiplication by a unit `u : (ZMod n)ˣ` defines a
permutation of every residue class in `ZMod n`. Zolotarev's lemma says that
its sign is the Jacobi symbol of the canonical integer representative of `u`.

**Formal verification status:** The central `zolotarev_unit` proof is an explicit
`sorry`. No theorem depending upon it should be regarded as verified. This
source is also not yet Lean-compiled. The surrounding lemmas are candidate
proofs to be checked against Mathlib.

The proposed proof of the central theorem reduces via CRT to odd prime powers,
using the cyclicity of units of odd prime-power residue rings. See
`PROOF_PLAN.md` for a complete paper proof and exact Lean obligations.
-/

namespace Zolotarev

variable (n : ℕ) [NeZero n]

/-- Multiplication by a unit, acting on **all** residues, including zero. -/
def mulPerm (u : (ZMod n)ˣ) : Equiv.Perm (ZMod n) :=
  u.mulLeft

@[simp]
theorem mulPerm_apply (u : (ZMod n)ˣ) (x : ZMod n) :
    mulPerm n u x = (u : ZMod n) * x := by
  rfl

@[simp]
theorem mulPerm_zero (u : (ZMod n)ˣ) : mulPerm n u 0 = 0 := by
  simp

@[simp]
theorem mulPerm_one : mulPerm n (1 : (ZMod n)ˣ) = 1 := by
  ext x
  simp

/-- Multiplication of units becomes composition of permutations. -/
@[simp]
theorem mulPerm_mul (u v : (ZMod n)ˣ) :
    mulPerm n (u * v) = mulPerm n u * mulPerm n v := by
  ext x
  simp [mulPerm, mul_assoc, mul_comm, mul_left_comm]

@[simp]
theorem mulPerm_inv (u : (ZMod n)ˣ) :
    mulPerm n u⁻¹ = (mulPerm n u)⁻¹ := by
  change (u⁻¹).mulLeft = (u.mulLeft).symm
  exact (Units.mulLeft_symm u).symm

/-- The sign of multiplication is a homomorphism from the unit group to `ℤˣ`. -/
noncomputable def signHom : (ZMod n)ˣ →* ℤˣ where
  toFun u := Equiv.Perm.sign (mulPerm n u)
  map_one' := by simp
  map_mul' u v := by simp

@[simp]
theorem signHom_apply (u : (ZMod n)ˣ) :
    signHom n u = Equiv.Perm.sign (mulPerm n u) := rfl

/-- Integer-valued sign of multiplication by a unit. -/
noncomputable def signInt (u : (ZMod n)ˣ) : ℤ :=
  ((signHom n u : ℤˣ) : ℤ)

@[simp]
theorem signInt_one : signInt n (1 : (ZMod n)ˣ) = 1 := by
  simp [signInt]

@[simp]
theorem signInt_mul (u v : (ZMod n)ˣ) :
    signInt n (u * v) = signInt n u * signInt n v := by
  simp [signInt]

/-- Power compatibility, a useful reduction to a cyclic generator. -/

@[simp]
theorem signInt_pow (u : (ZMod n)ˣ) (k : ℕ) :
    signInt n (u ^ k) = signInt n u ^ k := by
  change ((signHom n (u ^ k) : ℤˣ) : ℤ) =
    ((signHom n u : ℤˣ) : ℤ) ^ k
  rw [map_pow, Units.val_pow_eq_pow_val]

/-- Taking the inverse of the multiplier does not change permutation sign. -/
@[simp]
theorem signInt_inv (u : (ZMod n)ˣ) :
    signInt n u⁻¹ = signInt n u := by
  simp [signInt, signHom, mulPerm_inv]

/-- The Jacobi symbol of the canonical representative of a unit. -/
def jacobiOfUnit (u : (ZMod n)ˣ) : ℤ :=
  jacobiSym (((u : ZMod n).val : ℤ)) n

/-- The Jacobi symbol is insensitive to replacing `a` by its residue modulo `n`. -/
theorem jacobiOfUnit_unitOfCoprime (a : ℕ) (ha : a.Coprime n) :
    jacobiOfUnit n (ZMod.unitOfCoprime a ha) = jacobiSym (a : ℤ) n := by
  simp only [jacobiOfUnit, ZMod.coe_unitOfCoprime, ZMod.val_natCast]
  apply jacobiSym.mod_left'
  simp [Int.natCast_mod]

/-- Zolotarev's lemma for modulus `1`, without using the general theorem. -/
theorem zolotarev_mod_one (u : (ZMod 1)ˣ) :
    signInt 1 u = jacobiOfUnit 1 u := by
  have hu : u = 1 := Subsingleton.elim _ _
  subst u
  simp [jacobiOfUnit]

/-- **THE SINGLE UNPROVED GENERAL MATHEMATICAL STEP.**

Zolotarev's lemma for odd modulus `n`: the sign of multiplication by `u`
on `ZMod n` is the Jacobi symbol of the underlying residue. See
`PROOF_PLAN.md` for a rigorous prime-power/CRT proof on paper.
-/
theorem zolotarev_unit (hn : Odd n) (u : (ZMod n)ˣ) :
    signInt n u = jacobiOfUnit n u := by
  sorry

/-- Natural-number formulation, which *depends on* `zolotarev_unit`. -/
theorem zolotarev_nat (hn : Odd n) (a : ℕ) (ha : a.Coprime n) :
    signInt n (ZMod.unitOfCoprime a ha) = jacobiSym (a : ℤ) n := by
  rw [zolotarev_unit n hn, jacobiOfUnit_unitOfCoprime]

end Zolotarev
