/-
Copyright (c) 2026.
Released under Apache 2.0 license as described in the file LICENSE.

AI-assisted candidate code. NOT YET VERIFIED BY LEAN.
-/
import NumberTheoryLean.OddAffineSign

/-!
# Transferring an affine-block permutation across an equivalence

This lemma packages the final permutation-theoretic argument needed in
Zolotarev's lemma. Once an equivariant digit decomposition is supplied,
the signature of modular multiplication is a product of two signatures.

No `sorry` occurs here. The file still requires a CI build.
-/

namespace Zolotarev

section AffineTransport

variable {A B C : Type*}
variable [Fintype A] [Fintype B] [Fintype C]
variable [DecidableEq A] [DecidableEq B] [DecidableEq C]
variable [AddGroup B]

/-- The action of our existing `blockPerm` on a pair has an explicit
coordinate formula, with base action `f` and affine fiber action. -/
theorem blockPerm_affine_apply
    (f : Equiv.Perm A) (g : Equiv.Perm B) (carry : A → B)
    (x : A × B) :
    blockPerm f
      (fun a => (Equiv.addLeft (carry a) : Equiv.Perm B) * g) x =
        (f x.1, carry x.1 + g x.2) := by
  cases x with
  | mk a b => rfl

/-- If a permutation is conjugate to an affine block action, its sign
is the product of the base/fiber signs with cardinality exponents.

The concrete Zolotarev application chooses
  A := ZMod n, B := ZMod m, C := ZMod (n*m).
-/
theorem sign_of_affine_digit_conjugacy
    (hB : Odd (Fintype.card B))
    (f : Equiv.Perm A) (g : Equiv.Perm B) (carry : A → B)
    (q : Equiv.Perm C) (e : A × B ≃ C)
    (he : ∀ x : A × B,
      e (f x.1, carry x.1 + g x.2) = q (e x)) :
    Equiv.Perm.sign q =
      (Equiv.Perm.sign f) ^ Fintype.card B *
        (Equiv.Perm.sign g) ^ Fintype.card A := by
  classical
  have hconj : ∀ x : A × B,
      e (blockPerm f
        (fun a => (Equiv.addLeft (carry a) : Equiv.Perm B) * g) x) =
      q (e x) := by
    intro x
    rw [blockPerm_affine_apply]
    exact he x
  calc
    Equiv.Perm.sign q = Equiv.Perm.sign
        (blockPerm f
          (fun a => (Equiv.addLeft (carry a) : Equiv.Perm B) * g)) :=
      (Equiv.Perm.sign_eq_sign_of_equiv _ _ e hconj).symm
    _ = (Equiv.Perm.sign f) ^ Fintype.card B *
        (Equiv.Perm.sign g) ^ Fintype.card A :=
      sign_blockPerm_affine hB f g carry

/-- Both coordinates odd: cardinality exponents disappear. -/
theorem sign_of_affine_digit_conjugacy_odd
    (hA : Odd (Fintype.card A)) (hB : Odd (Fintype.card B))
    (f : Equiv.Perm A) (g : Equiv.Perm B) (carry : A → B)
    (q : Equiv.Perm C) (e : A × B ≃ C)
    (he : ∀ x : A × B,
      e (f x.1, carry x.1 + g x.2) = q (e x)) :
    Equiv.Perm.sign q = Equiv.Perm.sign f * Equiv.Perm.sign g := by
  classical
  have hconj : ∀ x : A × B,
      e (blockPerm f
        (fun a => (Equiv.addLeft (carry a) : Equiv.Perm B) * g) x) =
      q (e x) := by
    intro x
    rw [blockPerm_affine_apply]
    exact he x
  calc
    Equiv.Perm.sign q = Equiv.Perm.sign
        (blockPerm f
          (fun a => (Equiv.addLeft (carry a) : Equiv.Perm B) * g)) :=
      (Equiv.Perm.sign_eq_sign_of_equiv _ _ e hconj).symm
    _ = Equiv.Perm.sign f * Equiv.Perm.sign g :=
      sign_blockPerm_affine_odd hA hB f g carry

end AffineTransport

end Zolotarev
