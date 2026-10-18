/-
Copyright (c) 2026. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.

Candidate Lean proof. Verify by building with Lean 4.33.1 and Mathlib v4.33.1.
-/
import NumberTheoryLean.Zolotarev
import Mathlib.Algebra.Field.ZMod
import Mathlib.Algebra.GroupWithZero.Units.Basic
import Mathlib.GroupTheory.Perm.Sign

/-!
# Sign bridge: units versus all residues at prime modulus

If `p` is prime, multiplication by a unit `u` fixes zero and permutes
all nonzero residues. Restricting to the nonzero residues leaves its
permutation sign unchanged. The latter set is equivalent to `(ZMod p)ˣ`.

This does *not* depend on the external proof of the Legendre-symbol identity.
-/

namespace Zolotarev

section PrimeBridge

variable {p : ℕ} [Fact p.Prime] [NeZero p]

/-- Over a field, nonzero elements are the underlying values of units. -/
noncomputable def unitsEquivNonzero :
    (ZMod p)ˣ ≃ {x : ZMod p // x ≠ 0} where
  toFun u := ⟨(u : ZMod p), u.ne_zero⟩
  invFun x := Units.mk0 x.1 x.2
  left_inv u := by
    apply Units.ext
    rfl
  right_inv x := by
    apply Subtype.ext
    rfl

/-- The multiplication permutation on all residues and its regular action
on units have identical signs at prime modulus. -/
theorem sign_mulPerm_eq_sign_units (u : (ZMod p)ˣ) :
    Equiv.Perm.sign (mulPerm p u) =
      Equiv.Perm.sign (MulAction.toPerm u : Equiv.Perm (ZMod p)ˣ) := by
  classical
  have hpres : ∀ x : ZMod p,
      (mulPerm p u x ≠ 0 ↔ x ≠ 0) := by
    intro x
    simp [mulPerm_apply]
  have hfixed : ∀ x : ZMod p,
      mulPerm p u x ≠ x → x ≠ 0 := by
    intro x hx hzero
    subst x
    exact hx (by simp)
  have hconj :
      Equiv.Perm.sign (MulAction.toPerm u : Equiv.Perm (ZMod p)ˣ) =
        Equiv.Perm.sign ((mulPerm p u).subtypePerm (p := fun x : ZMod p => x ≠ 0) hpres) := by
    apply Equiv.Perm.sign_eq_sign_of_equiv
      (e := unitsEquivNonzero (p := p))
    intro x
    apply Subtype.ext
    change (((MulAction.toPerm u) x : (ZMod p)ˣ) : ZMod p) =
      (u : ZMod p) * (x : ZMod p)
    rw [MulAction.toPerm_apply, Units.smul_eq_mul]
    rfl
  calc
    Equiv.Perm.sign (mulPerm p u) =
        Equiv.Perm.sign ((mulPerm p u).subtypePerm (p := fun x : ZMod p => x ≠ 0) hpres) :=
      (Equiv.Perm.sign_subtypePerm (p := fun x : ZMod p => x ≠ 0) (mulPerm p u) hpres hfixed).symm
    _ = Equiv.Perm.sign (MulAction.toPerm u : Equiv.Perm (ZMod p)ˣ) :=
      hconj.symm

end PrimeBridge
end Zolotarev
