/-
Copyright (c) 2026. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
AI-assisted candidate Lean formalization; not yet kernel-checked.
-/
import NumberTheoryLean.ProductSign
import Mathlib.GroupTheory.OrderOfElement
import Mathlib.Data.ZMod.Basic

/-!
# Translation and affine permutation signs over finite additive groups

A translation of an odd-order finite group is an even permutation.
This fact yields the sign of affine maps `x ↦ u*x + c` on odd ZMod,
and the signs of block permutations with affine fibers.

There are no `sorry` placeholders in this module. Formal verification
requires a successful GitHub Actions run with this file imported.
-/

namespace Zolotarev

/-- The only possibilities for a unit in ℤ are 1 and -1, so an odd power
leaves the unit unchanged. This exact proof pattern already compiled in
`ProductSign.lean` during Actions run #15. -/
private theorem int_unit_pow_odd (x : ℤˣ) {k : ℕ} (hk : Odd k) : x ^ k = x := by
  rcases hk with ⟨t, rfl⟩
  calc
    x ^ (2 * t + 1) = (x ^ 2) ^ t * x := by rw [pow_add, pow_mul, pow_one]
    _ = x := by simp

section PermutationPower

variable {α : Type*} [Fintype α] [DecidableEq α]

/-- If an odd power of a finite permutation is the identity, its sign is +1. -/
theorem sign_eq_one_of_odd_power (f : Equiv.Perm α) {k : ℕ}
    (hk : Odd k) (hf : f ^ k = 1) : Equiv.Perm.sign f = 1 := by
  have h : (Equiv.Perm.sign f) ^ k = 1 := by
    rw [← map_pow, hf, map_one]
  rwa [int_unit_pow_odd _ hk] at h

end PermutationPower

section AdditiveTranslations

variable {G : Type*} [AddGroup G]

/-- Powering a translation is the same as translating by a multiple. -/
private theorem equiv_addLeft_pow (c : G) (k : ℕ) :
    (Equiv.addLeft c : Equiv.Perm G) ^ k = Equiv.addLeft (k • c) := by
  induction k with
  | zero => simp
  | succ k ih =>
      rw [pow_succ, ih, succ_nsmul]
      exact (Equiv.addLeft_add (k • c) c).symm

variable [Fintype G] [DecidableEq G]

/-- A translation of a finite additive group of odd cardinality has sign +1. -/
theorem sign_translation_odd (hG : Odd (Fintype.card G)) (c : G) :
    Equiv.Perm.sign (Equiv.addLeft c : Equiv.Perm G) = 1 := by
  apply sign_eq_one_of_odd_power _ hG
  rw [equiv_addLeft_pow]
  simp

/-- Translation after a permutation does not change its sign when the
underlying finite additive group has odd cardinality. -/
theorem sign_affine_odd (hG : Odd (Fintype.card G))
    (c : G) (g : Equiv.Perm G) :
    Equiv.Perm.sign ((Equiv.addLeft c : Equiv.Perm G) * g) =
      Equiv.Perm.sign g := by
  rw [Equiv.Perm.sign_mul, sign_translation_odd hG, one_mul]

end AdditiveTranslations

section ModularTranslations

variable (n : ℕ) [NeZero n]

/-- Every translation of `ZMod n`, with `n` odd, is even. -/
theorem sign_zmod_translation (hn : Odd n) (c : ZMod n) :
    Equiv.Perm.sign (Equiv.addLeft c : Equiv.Perm (ZMod n)) = 1 := by
  apply sign_translation_odd
  simpa only [ZMod.card] using hn

/-- Translation does not alter the sign of multiplication by a unit
modulo any odd positive modulus. -/
theorem sign_zmod_affine (hn : Odd n) (u : (ZMod n)ˣ) (c : ZMod n) :
    Equiv.Perm.sign
      ((Equiv.addLeft c : Equiv.Perm (ZMod n)) * u.mulLeft) =
        Equiv.Perm.sign u.mulLeft := by
  rw [Equiv.Perm.sign_mul, sign_zmod_translation n hn, one_mul]

end ModularTranslations

section AffineBlocks

variable {α G : Type*}
variable [Fintype α] [DecidableEq α]
variable [AddGroup G] [Fintype G] [DecidableEq G]

/-- Sign of a block permutation whose fibers all act by the same permutation
followed by fiber-dependent translations. -/
theorem sign_blockPerm_affine
    (hG : Odd (Fintype.card G))
    (f : Equiv.Perm α) (g : Equiv.Perm G) (c : α → G) :
    Equiv.Perm.sign
        (blockPerm f (fun a => (Equiv.addLeft (c a) : Equiv.Perm G) * g)) =
      (Equiv.Perm.sign f) ^ Fintype.card G *
        (Equiv.Perm.sign g) ^ Fintype.card α := by
  rw [sign_blockPerm]
  simp_rw [sign_affine_odd hG]
  simp

/-- With both coordinates of odd size, the affine block sign factors. -/
theorem sign_blockPerm_affine_odd
    (hα : Odd (Fintype.card α)) (hG : Odd (Fintype.card G))
    (f : Equiv.Perm α) (g : Equiv.Perm G) (c : α → G) :
    Equiv.Perm.sign
        (blockPerm f (fun a => (Equiv.addLeft (c a) : Equiv.Perm G) * g)) =
      Equiv.Perm.sign f * Equiv.Perm.sign g := by
  rw [sign_blockPerm_affine hG]
  rw [int_unit_pow_odd _ hG, int_unit_pow_odd _ hα]

end AffineBlocks

end Zolotarev
