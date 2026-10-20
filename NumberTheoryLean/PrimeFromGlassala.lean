/-
Copyright (c) 2026. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.

Relies on a separately imported third-party theorem by Will Sweet
(https://github.com/glassala/zolotarev, Apache 2.0).
Please retain the original author's copyright header when copying source.

Candidate Lean proof. Verify with the pinned toolchain before relying on it.
-/
import NumberTheoryLean.PrimeBridge_fixed_v2
import NumberTheoryLean.GlassalaPrime
import Mathlib.NumberTheory.LegendreSymbol.JacobiSymbol

/-!
# Prime Zolotarev lemma derived from Will Sweet's unit-action theorem

The external theorem proves an equality in `ZMod p`.  For odd prime p,
two integers in {1,-1} whose residues agree modulo p are equal.
Combining this with `sign_mulPerm_eq_sign_units` yields our prime case.
-/

namespace Zolotarev

section PrimeResult
variable {p : ℕ} [Fact p.Prime] [NeZero p]

/-- Casting to `ZMod p` is injective on the two signs when p is odd. -/
private theorem signs_eq_of_cast_eq (hp : Odd p)
    (s t : ℤ) (hs : s = 1 ∨ s = -1) (ht : t = 1 ∨ t = -1)
    (he : (s : ZMod p) = (t : ZMod p)) : s = t := by
  have hneq : (1 : ZMod p) ≠ -1 := ZMod.ne_neg_self hp one_ne_zero
  rcases hs with rfl | rfl <;> rcases ht with rfl | rfl
  · rfl
  · exact (hneq (by simpa using he)).elim
  · exact (hneq (by simpa using he.symm)).elim
  · rfl

/-- The prime case in our original API, assuming the upstream theorem
`legendreSym_eq_sign_of_toPerm` compiles under the pinned Mathlib version. -/
theorem zolotarev_prime (hp : Odd p) (u : (ZMod p)ˣ) :
    signInt p u = jacobiOfUnit p u := by
  let a : ℤ := ((u : ZMod p).val : ℤ)
  have ha0 : (a : ZMod p) ≠ 0 := by
    simpa [a] using u.ne_zero
  have hleg : legendreSym p a = 1 ∨ legendreSym p a = -1 :=
    legendreSym.eq_one_or_neg_one p ha0
  have hsign : signInt p u = 1 ∨ signInt p u = -1 := by
    rcases Int.units_eq_one_or (signHom p u) with h | h
    · left
      change (((signHom p u : ℤˣ) : ℤ)) = 1
      rw [h]
      rfl
    · right
      change (((signHom p u : ℤˣ) : ℤ)) = -1
      rw [h]
      rfl
  have hglass : (legendreSym p a : ZMod p) =
      (Equiv.Perm.sign (MulAction.toPerm u : Equiv.Perm (ZMod p)ˣ) : ZMod p) := by
    simpa [a] using (legendreSym_eq_sign_of_toPerm (a := u) hp)
  have hcast : (legendreSym p a : ZMod p) = (signInt p u : ZMod p) := by
    rw [← sign_mulPerm_eq_sign_units (p := p) u] at hglass
    exact hglass
  have hmain : signInt p u = legendreSym p a :=
    signs_eq_of_cast_eq hp _ _ hsign hleg hcast.symm
  exact hmain.trans (by
    simpa [jacobiOfUnit, a] using
       (jacobiSym.legendreSym.to_jacobiSym p a)

end PrimeResult
end Zolotarev
