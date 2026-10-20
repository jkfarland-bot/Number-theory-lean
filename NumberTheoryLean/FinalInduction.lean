/-
Copyright (c) 2026. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.

Candidate proof: NOT YET LEAN-COMPILED.
Depends on the axiom-checked prime and composite sign lemmas from this project.
-/
import NumberTheoryLean.DigitConjugacy
import NumberTheoryLean.PrimeFromGlassala
import Mathlib.NumberTheory.LegendreSymbol.JacobiSymbol
import Mathlib.Tactic

/-!
# Zolotarev's lemma for all odd moduli

The composite-modulus sign theorem `sign_mul_modulus` does not require
coprimality of the modulus factors. This makes strong induction on the
modulus sufficient, avoiding prime-power lemmas and CRT.

The theorem `zolotarev_nat_induction` proves the natural-number multiplier
version, and `zolotarev_unit_final` proves the original unit-group statement.

Do not replace the existing `zolotarev_unit` until this module compiles and
`#print axioms` shows no dependency on `sorryAx`.
-/

namespace Zolotarev

/-! ## 1. Strong induction for natural-number multipliers -/

/-- The main induction. The `NeZero` instance is manufactured from oddness
inside the proposition, enabling strong induction without a dependent
instance parameter in the motive. -/
private theorem zolotarev_nat_induction_aux :
    ∀ (n : ℕ) (hn : Odd n) (a : ℕ) (ha : a.Coprime n),
      letI : NeZero n := ⟨(Odd.pos hn).ne'⟩
      signInt n (ZMod.unitOfCoprime a ha) = jacobiSym (a : ℤ) n := by
  intro n
  induction n using Nat.strong_induction_on with
  | h n ih =>
    intro hn a ha
    letI : NeZero n := ⟨(Odd.pos hn).ne'⟩
    change signInt n (ZMod.unitOfCoprime a ha) = jacobiSym (a : ℤ) n

    by_cases hn1 : n = 1
    · subst n
      exact (zolotarev_mod_one (ZMod.unitOfCoprime a ha)).trans
        (jacobiOfUnit_unitOfCoprime 1 a ha)

    · obtain ⟨p, hp, hpdvd⟩ := Nat.exists_prime_and_dvd hn1
      rcases hpdvd with ⟨k, rfl⟩
      obtain ⟨hpo, hko⟩ := Nat.odd_mul.mp hn
      letI : NeZero p := ⟨(Odd.pos hpo).ne'⟩
      letI : NeZero k := ⟨(Odd.pos hko).ne'⟩
      letI : Fact p.Prime := ⟨hp⟩

      have hap : a.Coprime p :=
        Nat.Coprime.of_dvd_right (dvd_mul_right p k) ha
      have hak : a.Coprime k :=
        Nat.Coprime.of_dvd_right (dvd_mul_left k p) ha

      have hklt : k < p * k := by
        calc
          k = 1 * k := (one_mul k).symm
          _ < p * k := mul_lt_mul_of_pos_right hp.one_lt (Odd.pos hko)

      have hkstep :
          signInt k (ZMod.unitOfCoprime a hak) = jacobiSym (a : ℤ) k :=
        ih k hklt hko a hak

      have hpstep :
          signInt p (ZMod.unitOfCoprime a hap) = jacobiSym (a : ℤ) p := by
        calc
          signInt p (ZMod.unitOfCoprime a hap) =
              jacobiOfUnit p (ZMod.unitOfCoprime a hap) :=
            zolotarev_prime hpo _
          _ = jacobiSym (a : ℤ) p :=
            jacobiOfUnit_unitOfCoprime p a hap

      have hsign :
          signInt (p * k) (ZMod.unitOfCoprime a ha) =
            signInt k (ZMod.unitOfCoprime a hak) *
              signInt p (ZMod.unitOfCoprime a hap) := by
        have h := sign_mul_modulus p k a hpo hko ha
        have hcast := congrArg (fun s : ℤˣ => (s : ℤ)) h
        simpa only [signInt, signHom_apply, Units.val_mul] using hcast

      calc
        signInt (p * k) (ZMod.unitOfCoprime a ha) =
            signInt k (ZMod.unitOfCoprime a hak) *
              signInt p (ZMod.unitOfCoprime a hap) := hsign
        _ = jacobiSym (a : ℤ) k * jacobiSym (a : ℤ) p := by
          rw [hkstep, hpstep]
        _ = jacobiSym (a : ℤ) (p * k) := by
          rw [jacobiSym.mul_right (a : ℤ) p k]
          ring

/-- The natural-number formulation is independent of the admitted
`zolotarev_unit` theorem in `Zolotarev.lean`. -/
theorem zolotarev_nat_final (n : ℕ) [NeZero n]
    (hn : Odd n) (a : ℕ) (ha : a.Coprime n) :
    signInt n (ZMod.unitOfCoprime a ha) = jacobiSym (a : ℤ) n := by
  exact zolotarev_nat_induction_aux n hn a ha

/-! ## 2. From arbitrary units to their canonical representatives -/

/-- A sorry-free candidate for the original general Zolotarev statement.
Once verified, this proof can replace `zolotarev_unit` in `Zolotarev.lean`
without changing its type. -/
theorem zolotarev_unit_final (n : ℕ) [NeZero n]
    (hn : Odd n) (u : (ZMod n)ˣ) :
    signInt n u = jacobiOfUnit n u := by
  let a : ℕ := (u : ZMod n).val
  have ha : a.Coprime n := ZMod.val_coe_unit_coprime u
  have hu : ZMod.unitOfCoprime a ha = u := by
    apply Units.ext
    simp [a]
  calc
    signInt n u = signInt n (ZMod.unitOfCoprime a ha) := by rw [hu]
    _ = jacobiSym (a : ℤ) n := zolotarev_nat_final n hn a ha
    _ = jacobiOfUnit n u := rfl

end Zolotarev

#print axioms Zolotarev.zolotarev_nat_final
#print axioms Zolotarev.zolotarev_unit_final
