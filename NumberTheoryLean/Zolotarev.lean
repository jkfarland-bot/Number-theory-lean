
/-
Copyright (c) 2026. All rights reserved.
Released under Apache 2.0 license as described
in the file LICENSE.
-/

import NumberTheoryLean.FinalInduction

/-!
# Zolotarev's lemma for all odd moduli

The sign of multiplication by a unit modulo
an odd positive integer is its Jacobi symbol.

The full proof is supplied by FinalInduction,
which uses the verified odd-prime theorem
and composite-modulus sign multiplicativity.
-/

namespace Zolotarev

/-- Zolotarev's lemma for every odd positive modulus. -/
theorem zolotarev_unit
    (n : ℕ) [NeZero n]
    (hn : Odd n) (u : (ZMod n)ˣ) :
    signInt n u = jacobiOfUnit n u := by
  exact zolotarev_unit_final n hn u

/-- Natural-number formulation of Zolotarev's lemma. -/
theorem zolotarev_nat
    (n : ℕ) [NeZero n]
    (hn : Odd n) (a : ℕ)
    (ha : a.Coprime n) :
    signInt n (ZMod.unitOfCoprime a ha) =
      jacobiSym (a : ℤ) n := by
  exact zolotarev_nat_final n hn a ha

end Zolotarev
