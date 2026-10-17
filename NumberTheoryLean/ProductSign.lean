/-
Copyright (c) 2026. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.

AI-assisted experimental proof code.
This file has NOT yet been compiled with Lean and is not a proof certificate.
-/
import Mathlib.GroupTheory.Perm.Sign
import Mathlib.Data.Int.Order.Units

/-!
# Sign of a Cartesian-product permutation

The sign of the coordinatewise action `(x, y) ↦ (f x, g y)` is

`sign f ^ card β * sign g ^ card α`.

This follows from Mathlib's already-formalized `sign_prodCongrLeft`
and `sign_prodCongrRight`; no new sign theory is needed.

This standalone module is an incremental build target for the
Zolotarev project. It does not use `sorry`, but has not yet been
compiled. Treat it as a *candidate formal proof* until CI passes.
-/

namespace Zolotarev

section ProductSign

variable {α β : Type*}
variable [Fintype α] [Fintype β]
variable [DecidableEq α] [DecidableEq β]

/-- Sign of a permutation acting independently on the two factors of a product.

This uses the sign of the fiberwise permutation actions already in Mathlib.
-/
theorem sign_prodCongr (f : Equiv.Perm α) (g : Equiv.Perm β) :
    Equiv.Perm.sign (f.prodCongr g) =
      (Equiv.Perm.sign f) ^ Fintype.card β *
        (Equiv.Perm.sign g) ^ Fintype.card α := by
  classical
  have hfactor : (f.prodCongr g : Equiv.Perm (α × β)) =
      (Equiv.prodCongrLeft (fun _ : β => f)) *
        (Equiv.prodCongrRight (fun _ : α => g)) := by  
    apply Equiv.ext
    rintro ⟨a, b⟩
    rfl
  rw [hfactor, Equiv.Perm.sign_mul,
    Equiv.Perm.sign_prodCongrLeft,
    Equiv.Perm.sign_prodCongrRight]
  simp

/-- Every integer unit is unchanged by an odd positive exponent. -/
private theorem intUnit_pow_odd (x : ℤˣ) {k : ℕ} (hk : Odd k) : x ^ k = x := by
  rcases hk with ⟨t, rfl⟩
  calc
    x ^ (2 * t + 1) = (x ^ 2) ^ t * x := by rw [pow_add, pow_mul, pow_one]
    _ = x := by simp

/-- Odd-cardinality specialization: the sign of the product action factors. -/
theorem sign_prodCongr_of_odd
    (f : Equiv.Perm α) (g : Equiv.Perm β)
    (hα : Odd (Fintype.card α))
    (hβ : Odd (Fintype.card β)) :
    Equiv.Perm.sign (f.prodCongr g) =
      Equiv.Perm.sign f * Equiv.Perm.sign g := by
  rw [sign_prodCongr, intUnit_pow_odd _ hβ, intUnit_pow_odd _ hα]


/-- A permutation of blocks, with a possibly different permutation in each
block. The fiber permutation is applied first, followed by the block permutation.

The sign computation is insensitive to the order of these two factors.
-/
noncomputable def blockPerm (f : Equiv.Perm α) (σ : α → Equiv.Perm β) :
    Equiv.Perm (α × β) :=
  (f.prodCongr (1 : Equiv.Perm β)) *
    Equiv.prodCongrRight σ

/-- Generic sign formula for a block permutation (a wreath-product action). -/
theorem sign_blockPerm (f : Equiv.Perm α) (σ : α → Equiv.Perm β) :
    Equiv.Perm.sign (blockPerm f σ) =
      (Equiv.Perm.sign f) ^ Fintype.card β *
        ∏ a : α, Equiv.Perm.sign (σ a) := by
  rw [blockPerm, Equiv.Perm.sign_mul,
    sign_prodCongr, Equiv.Perm.sign_prodCongrRight]
  simp

end ProductSign

end Zolotarev
