Zolotarev's Lemma: Verified Proof Architecture and Mathematical Handoff
Status (October 20, 2026): Complete Lean formalization for all odd positive moduli.
The canonical theorems Zolotarev.zolotarev_unit and Zolotarev.zolotarev_nat compile with Lean 4.33.1 and Mathlib v4.33.1. GitHub Actions Run #53 successfully built the project and compiled the infrastructure tests. Lean's axiom audits for the canonical theorems, the odd-prime theorem, and the composite-sign theorem report only [propext, Classical.choice, Quot.sound]: no sorryAx.
This document describes the proof actually implemented, not the earlier proposed prime-power/Chinese-remainder proof. Its purpose is to make the mathematics, source dependencies, verification, and remaining library-integration work independently auditable. The formalization has not been merged into Mathlib.
1. Theorem and notation
Let (n\ge 1) be odd and let (a\in\mathbb Z) with (\gcd(a,n)=1). Multiplication by (a) induces a permutation
[ \sigma_{a,n}:\mathbb Z/n\mathbb Z\longrightarrow\mathbb Z/n\mathbb Z, \qquad x\longmapsto ax. ]
Write (S(a,n)=\operatorname{sgn}(\sigma_{a,n})\in{1,-1}). Zolotarev's lemma is
[ \boxed{S(a,n)=\left(\frac an\right),} ]
where the right side is the Jacobi symbol, and the convention at (n=1) is (\left(\frac a1\right)=1).
The formalization first works with a unit u : (ZMod n)ˣ. Zolotarev.mulPerm n u permutes all residues, including zero, and Zolotarev.signInt n u converts its sign from ℤˣ to ℤ. Zolotarev.jacobiOfUnit n u computes the Jacobi symbol using the canonical natural-number representative of u.
The two public declarations in NumberTheoryLean/Zolotarev.lean are:
zolotarev_unit (n : ℕ) [NeZero n] (hn : Odd n) (u : (ZMod n)ˣ) : signInt n u = jacobiOfUnit n u;
zolotarev_nat (n : ℕ) [NeZero n] (hn : Odd n) (a : ℕ) (ha : a.Coprime n) : signInt n (ZMod.unitOfCoprime a ha) = jacobiSym (a : ℤ) n.
The natural-number statement also captures the usual arbitrary-integer formulation, since the permutation and the Jacobi symbol depend only on the residue of (a) modulo (n). The implemented general induction directly proves the natural-number case and then transports it to arbitrary units.
2. Central observation: multiplicativity without CRT
The crucial structural theorem is
[ \boxed{S(a,mn)=S(a,m),S(a,n)} ]
whenever (m,n\ge1) are odd and (\gcd(a,mn)=1). Unlike a Chinese remainder factorization, this identity does not require (\gcd(m,n)=1).
Lean theorem: Zolotarev.sign_mul_modulus in NumberTheoryLean/DigitConjugacy.lean (stated using Equiv.Perm.sign in ℤˣ; the induction casts it into ℤ). The right-hand factors appear in the opposite order in the Lean statement, which is harmless because multiplication is commutative.
This is the reason the final proof needs neither a prime-power classification nor CRT. Once the identity is established, every odd modulus can be reduced by removing one prime factor at a time, even when that prime factor occurs repeatedly.
3. Quotient–remainder coordinates and the carry identity
Fix positive integers (m,n), with no coprimality hypothesis. Every residue modulo (nm) has unique coordinates
[ x=r+nt,\qquad 0\le r<n,\quad 0\le t<m. ]
These coordinates constitute a bijection of finite sets, not a ring isomorphism or CRT decomposition:
[ E:\big(\mathbb Z/n\mathbb Z\big)\times\big(\mathbb Z/m\mathbb Z\big) \simeq\mathbb Z/(nm)\mathbb Z, \quad (r,t)\mapsto r+nt. ]
For a natural-number multiplier (a), Euclidean division gives
[ ar=(ar\bmod n)+n\left\lfloor\frac{ar}{n}\right\rfloor. ]
Therefore
[ \boxed{ a(r+nt)\bmod(nm) =(ar\bmod n)+n\left(\left(at+\left\lfloor\frac{ar}{n}\right\rfloor\right)\bmod m\right). } ]
In coordinates, multiplication by (a) takes the triangular or affine-block form
[ (r,t)\longmapsto\big(f(r),,g(t)+c(r)\big), ]
with
[ f(r)=ar\bmod n,\qquad g(t)=at\bmod m,\qquad c(r)=\left\lfloor\frac{ar}{n}\right\rfloor\bmod m. ]
The second coordinate is multiplication by (a) followed by a translation whose amount depends on the first coordinate. The carry term (c(r)) is essential: multiplication does not act coordinatewise, so a bare product-permutation argument would be insufficient.
Formal source: NumberTheoryLean/CarryDigits.lean proves mul_digit_remainder, mul_digit_quotient, mul_digit_mod_product, and constructs digitEquiv. NumberTheoryLean/DigitConjugacy.lean constructs digitZModEquiv, establishes digitZModEquiv_val, and proves the precise equivariance relation digitZModEquiv_mul.
The digit identity and bijection themselves do not require (\gcd(m,n)=1); the multiplier must be coprime to (mn) to make the induced multiplication maps permutations.
4. Permutation signs: blocks and odd-order translations
4.1 Cartesian-product sign formula
For permutations (f) of a finite set (A) and (g) of a finite set (B), coordinatewise action satisfies
[ \operatorname{sgn}(f\times g) =\operatorname{sgn}(f)^{|B|}\operatorname{sgn}(g)^{|A|}. ]
This follows from separating the action on the first coordinate from that on the second; each factor acts on one copy of its coordinate set for each value of the other coordinate. ProductSign.lean proves this as sign_prodCongr, using Mathlib's product-permutation sign lemmas, and provides sign_prodCongr_of_odd.
4.2 General block permutations
For (f:A\to A) a permutation and fiber permutations (h_r:B\to B), consider
[ (r,t)\longmapsto\big(f(r),h_r(t)\big). ]
Its sign is
[ \operatorname{sgn}(f)^{|B|}\prod_{r\in A}\operatorname{sgn}(h_r). ]
ProductSign.lean defines blockPerm and proves this as sign_blockPerm.
4.3 Translation of an odd-order group
If (G) is a finite additive group of odd cardinality, every translation (T_c:x\mapsto x+c) has sign (+1). One proof is: (T_c^{|G|}=1); the sign is in ({1,-1}), so taking its odd (|G|)-th power leaves it unchanged. Because that power is (+1), the sign itself is (+1).
Thus on (G), an affine map (x\mapsto g(x)+c) has the same sign as (g).
OddAffineSign.lean proves sign_eq_one_of_odd_power, sign_translation_odd, sign_affine_odd, and the specialized sign_blockPerm_affine_odd. AffineTransport.lean proves that the computed sign is preserved when the affine-block action is conjugated through an equivalence (sign_of_affine_digit_conjugacy_odd).
4.4 The sign-multiplicativity calculation
Apply the block formula to the map from Section 3, with (A=\mathbb Z/n\mathbb Z), (B=\mathbb Z/m\mathbb Z), (f(r)=ar), and (g(t)=at).
For each (r), the fiber map (t\mapsto g(t)+c(r)) has sign (\operatorname{sgn}(g)), because (m) is odd. Hence
[ \operatorname{sgn}(\sigma_{a,nm}) =\operatorname{sgn}(f)^m\operatorname{sgn}(g)^n. ]
Since (m) and (n) are both odd, (\varepsilon^m=\varepsilon^n=\varepsilon) for any sign (\varepsilon\in{\pm1}). Consequently
[ \operatorname{sgn}(\sigma_{a,nm}) =\operatorname{sgn}(\sigma_{a,n})\operatorname{sgn}(\sigma_{a,m}). ]
This proves sign_mul_modulus without imposing coprimality between the modulus factors.
5. Odd-prime case
Let (p) be an odd prime. Multiplication by a unit fixes the zero residue. Its restriction to the nonzero residues is conjugate to the multiplication action on ((\mathbb Z/p\mathbb Z)^\times). Therefore the sign on all residues is the same as the sign of the action on units.
This is proved as sign_mulPerm_eq_sign_units in NumberTheoryLean/PrimeBridge_fixed_v2.lean, using unitsEquivNonzero and Mathlib's sign lemmas for restriction and conjugacy.
NumberTheoryLean/GlassalaPrime.lean adapts Will Sweet's Apache-2.0-licensed prime-case formalization, whose theorem legendreSym_eq_sign_of_toPerm identifies the Legendre symbol and unit-action permutation sign after casting to ZMod p.
The bridge in NumberTheoryLean/PrimeFromGlassala.lean obtains the integer-valued equality as follows:
Both the Legendre symbol of a nonzero residue and the integer permutation sign belong to ({+1,-1}).
Their casts to ZMod p agree by the imported prime theorem and sign_mulPerm_eq_sign_units.
Because (p) is odd, (1\ne-1) in ZMod p; therefore the equality of casts implies equality as integers.
Mathlib's jacobiSym.legendreSym.to_jacobiSym identifies the Legendre symbol at prime (p) with the Jacobi symbol.
The resulting theorem is Zolotarev.zolotarev_prime:
[ \boxed{S(a,p)=\left(\frac ap\right).} ]
The original prime-case author and repository are credited under Attribution below.
6. Strong induction: all odd positive moduli
NumberTheoryLean/FinalInduction.lean proves the natural-number-multiplier statement using Nat.strong_induction_on. The induction is on the modulus (n), not the multiplier. Oddness supplies positivity and the NeZero instances required by ZMod.
Base case: (n=1)
The residue ring ZMod 1 has a single element, so its multiplication permutation has sign (+1). The Jacobi symbol at modulus 1 is also (+1). This is zolotarev_mod_one together with jacobiOfUnit_unitOfCoprime, proved in ZolotarevCore.lean.
Induction step: (n>1)
Suppose the claim holds for every smaller odd positive modulus. Choose a prime divisor (p\mid n) using Nat.exists_prime_and_dvd, and write (n=pk). Because (n) is odd, (p) and (k) are odd. Because (p\ge2) and (k\ge1), we have (k<pk=n).
If (\gcd(a,n)=1), then (a) is coprime to both (p) and (k). We may therefore use the prime theorem at (p), the induction hypothesis at (k), and the sign-multiplicativity theorem:
[ \begin{aligned} S(a,n)&=S(a,pk)\ &=S(a,p)S(a,k)\ &=\left(\frac ap\right)\left(\frac ak\right)\ &=\left(\frac a{pk}\right)\ &=\left(\frac an\right). \end{aligned} ]
The fourth line uses Mathlib's jacobiSym.mul_right, valid for positive factors regardless of whether (p) divides (k). Thus the argument handles prime powers and arbitrary repeated factors automatically.
The internal induction is zolotarev_nat_induction_aux. It is exposed as zolotarev_nat_final.
Transport from natural multipliers to arbitrary units
For any u : (ZMod n)ˣ, choose (a=u.\mathrm{val}). Mathlib proves ZMod.val_coe_unit_coprime u, so (a) is coprime to (n). The unit ZMod.unitOfCoprime a ha equals (u) by Units.ext. Applying the natural-number result and unfolding jacobiOfUnit proves zolotarev_unit_final.
Finally, NumberTheoryLean/Zolotarev.lean exports the canonical names zolotarev_nat and zolotarev_unit as direct consequences of these verified theorems. ZolotarevCore.lean contains the shared definitions and elementary lemmas, preventing circular imports between the prime, composite, and final modules.
7. Exact dependency map
Module
Principal role
Key declaration(s)
ZolotarevCore.lean
Primitive definitions, sign character, modulus 1
mulPerm, signInt, jacobiOfUnit, zolotarev_mod_one
ProductSign.lean
Product and block permutation signs
sign_prodCongr, sign_blockPerm
OddAffineSign.lean
Odd-order translations and affine signs
sign_translation_odd, sign_blockPerm_affine_odd
CarryDigits.lean
Arithmetic of quotient/remainder digits
mul_digit_mod_product, digitEquiv
AffineTransport.lean
Sign invariance under block conjugacy
sign_of_affine_digit_conjugacy_odd
DigitConjugacy.lean
Explicit digit action; composite theorem
digitZModEquiv_mul, sign_mul_modulus
GlassalaPrime.lean
Adapted third-party prime character/sign result
legendreSym_eq_sign_of_toPerm
PrimeBridge_fixed_v2.lean
Sign on all residues equals sign on units
sign_mulPerm_eq_sign_units
PrimeFromGlassala.lean
Integer-valued prime case
zolotarev_prime
FinalInduction.lean
Strong induction and unit conversion
zolotarev_nat_final, zolotarev_unit_final
Zolotarev.lean
Stable public theorem names
zolotarev_nat, zolotarev_unit
The principal logical routes are:
ProductSign → OddAffineSign → AffineTransport → DigitConjugacy;
ZolotarevCore → PrimeBridge_fixed_v2 → PrimeFromGlassala, together with GlassalaPrime;
DigitConjugacy + PrimeFromGlassala → FinalInduction → public Zolotarev module.
8. Lean verification and reproducibility
The project pins leanprover/lean4:v4.33.1 in lean-toolchain and Mathlib v4.33.1 in lakefile.toml.
From the repository root, run:
lake update
lake exe cache get
lake build NumberTheoryLean
lake env lean tests/Infrastructure.lean
The top-level NumberTheoryLean.lean invokes:
#print axioms Zolotarev.zolotarev_prime
#print axioms Zolotarev.sign_mul_modulus
#print axioms Zolotarev.zolotarev_unit
#print axioms Zolotarev.zolotarev_nat
FinalInduction.lean also checks zolotarev_nat_final and zolotarev_unit_final.
GitHub Actions Run #53 (October 20, 2026) succeeded for the project build and the infrastructure tests:
https://github.com/jkfarland-bot/Number-theory-lean/actions/runs/39510608527
For each of the six audited prime, composite, induction, and canonical theorems, the reported axioms were:
[propext, Classical.choice, Quot.sound]
There was no sorryAx in those declarations' dependencies. This is the substantive kernel-level proof audit; successful compilation alone would not suffice if admitted steps were present.
The infrastructure suite also exercises the public theorem at (45=3^2\cdot5) and (225=3^2\cdot5^2). Separate Python scripts (tests/verify_zolotarev.py and tests/verify_structural.py) provide finite numerical checks, not additional formal proof.
9. Earlier approach: historical, not the implemented proof
An earlier project plan proposed:
cyclic generators of ((\mathbb Z/p^e\mathbb Z)^\times);
decomposition into valuation layers for odd prime powers;
a Chinese-remainder product-sign argument for pairwise coprime factors.
That route is mathematically reasonable but is not the path used by the verified Lean implementation. The direct digit-conjugacy identity and noncoprime sign multiplicativity make its prime-power and CRT steps unnecessary. Likewise, the signed-pair/generalized-Gauss-lemma approach remains an alternative research direction; it is not a theorem established by this project's final induction.
Do not describe these historical routes as prerequisites or unresolved proof obligations for zolotarev_unit.
10. Remaining work: presentation and upstream integration
No mathematical gap remains in the pinned-toolchain proof of the general Zolotarev theorem. Work remaining before a Mathlib contribution is principally engineering and review:
Audit source-level comments: several files retain obsolete statements such as “not yet compiled” or references to an admitted theorem; these must be corrected without disturbing their proofs.
Simplify linter warnings and redundant imports, maintaining passing builds and axiom audits after each change.
Decide which supporting permutation-sign and affine-digit lemmas belong in independent Mathlib modules and which should remain local.
Check API names, theorem statements, credits, file placement, and compatibility with the current Mathlib development branch; successful compilation against v4.33.1 alone does not establish compatibility with that branch.
Obtain independent human Lean review and comply with Mathlib's contribution and AI-assistance disclosure requirements.
In a separate research track, investigate whether the permutation-sign infrastructure supports formalization of Dedekind sums or Meyer's formula. Those results are not proved in this repository.
11. Attribution and scope
NumberTheoryLean/GlassalaPrime.lean adapts work by Will Sweet from https://github.com/glassala/zolotarev (Apache License 2.0). Retain the original copyright and author notices. The repository includes an Apache-2.0 LICENSE file.
The composite digit-decomposition proof, supporting permutation-sign machinery, and final induction were developed as part of this repository with substantial AI assistance. Lean kernel verification certifies the stated formal theorems under their recorded axioms; it does not itself establish originality, review quality, or acceptance for upstream Mathlib.
Conclusion: For all positive odd (n) and all (a) coprime to (n), the sign of multiplication by (a) on all residues modulo (n) equals the Jacobi symbol (\left(\frac an\right)). The Lean proof combines an odd-prime result, a noncoprime odd-factor sign theorem via affine digit conjugacy, and strong induction on the modulus. The canonical theorems are compiled and sorryAx-free in the pinned environment.
