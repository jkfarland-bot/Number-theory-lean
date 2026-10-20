import NumberTheoryLean.Zolotarev

/-!
# Lean smoke tests for the infrastructure (not a proof of the general theorem)

IMPORTANT: This file has not been run through Lean in the authoring environment.
Run it inside a Mathlib checkout using `lake env lean tests/Infrastructure.lean`.
-/

open Zolotarev

example : mulPerm 5 (1 : (ZMod 5)ˣ) = 1 := by
  simp

example : signInt 5 (1 : (ZMod 5)ˣ) = 1 := by
  simp

example (u : (ZMod 15)ˣ) :
    signInt 15 (u ^ 3) = (signInt 15 u) ^ 3 := by
  simp

example (u : (ZMod 15)ˣ) :
    signInt 15 u⁻¹ = signInt 15 u := by
  simp

example : mulPerm 5 (ZMod.unitOfCoprime 2 (by decide)) (1 : ZMod 5) = 2 := by
  simp

example :
    jacobiOfUnit 5 (ZMod.unitOfCoprime 2 (by decide)) = jacobiSym 2 5 := by
  exact jacobiOfUnit_unitOfCoprime 5 2 (by decide)

example (u : (ZMod 1)ˣ) :
    signInt 1 u = jacobiOfUnit 1 u := by
  exact zolotarev_mod_one u
