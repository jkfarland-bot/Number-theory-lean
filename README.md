Zolotarev's Lemma — Lean 4 / Mathlib

Status: Formally verified for every odd positive modulus.

This repository contains a Lean 4 formalization of Zolotarev's lemma, establishing the relationship between permutation signs and Jacobi symbols.

The complete proof has been compiled successfully against Lean 4.33.1 and Mathlib v4.33.1. Lean's "#print axioms" checks confirm that the principal theorems do not depend on "sorryAx" or additional mathematical axioms.

The proof includes arbitrary odd composite moduli, repeated prime factors, and the modulus 1.

The repository is a standalone formalization project. Its results have not yet been merged into Mathlib.

1. The Mathematical Theorem

Let (n) be a positive odd integer and let (a) be an integer relatively prime to (n).

Multiplication by (a) permutes the residue classes modulo (n):

[
\sigma_{a,n}:x\longmapsto ax\pmod n.
]

Zolotarev's lemma states that the sign of this permutation equals the Jacobi symbol:

[
\boxed{\operatorname{sgn}(\sigma_{a,n})=\left(\frac an\right).}
]

For prime moduli, the Jacobi symbol reduces to the Legendre symbol. For composite moduli, including prime powers, the equality remains valid.

Our formalization proves this result for every odd positive modulus without assuming that its prime factors are distinct.

2. Main Lean Theorems

The canonical theorems are exported by "NumberTheoryLean/Zolotarev.lean", in the namespace "Zolotarev".

Unit-group formulation

"Zolotarev.zolotarev_unit"

For every odd positive modulus "n" and every unit "u : (ZMod n)ˣ":

"signInt n u = jacobiOfUnit n u"

Here:

- "signInt n u" is the integer-valued sign of multiplication by "u" on all residue classes in "ZMod n".
- "jacobiOfUnit n u" is the Jacobi symbol of the canonical integer representative of "u".

Natural-number formulation

"Zolotarev.zolotarev_nat"

For every odd positive "n" and natural number "a" satisfying "a.Coprime n":

"signInt n (ZMod.unitOfCoprime a ha) = jacobiSym (a : ℤ) n"

Both canonical theorems are consequences of the verified strong-induction proof in "FinalInduction.lean".

3. Proof Strategy

The formal proof is divided into three principal stages.

A. The prime-modulus theorem

The first stage proves Zolotarev's lemma for odd primes.

It adapts Will Sweet's formalization of the relationship between the Legendre symbol and the sign of the multiplication permutation on the unit group.

An additional bridge theorem establishes that, for prime moduli, the relevant permutation sign on all residue classes equals the sign on the unit group. The zero residue is fixed, so it contributes no change in sign.

The resulting theorem is:

"Zolotarev.zolotarev_prime"

B. Multiplicativity of permutation signs

The second stage establishes a structural result for composite moduli.

For odd positive integers (m,n) and a multiplier (a) coprime to (mn), define

[
S(a,n)=\operatorname{sgn}(x\mapsto ax\bmod n).
]

We prove:

[
\boxed{S(a,mn)=S(a,m)S(a,n).}
]

Crucially, this identity does not require (m) and (n) to be coprime.

The proof uses quotient–remainder digit coordinates to decompose multiplication modulo (mn) into an action on residue blocks.

The coordinate decomposition produces affine permutations within the blocks. Their translation components have positive sign because the relevant block sizes are odd.

This establishes the product formula through explicit permutation conjugacy.

The resulting theorem is:

"Zolotarev.sign_mul_modulus"

This approach avoids the need for the Chinese remainder theorem and eliminates the need for separate prime-power arguments.

C. Strong induction on the modulus

The third stage combines the prime theorem and the composite sign formula.

For an odd modulus (n>1), choose a prime divisor (p) and write

[
n=pk.
]

Both (p) and (k) are odd, and (k<n).

The composite sign theorem gives

[
S(a,n)=S(a,p)S(a,k).
]

The prime theorem identifies the first factor with the Legendre symbol. The induction hypothesis identifies the second factor with the Jacobi symbol modulo (k).

Mathlib's multiplicativity theorem for Jacobi symbols then gives

[
S(a,n)
=\left(\frac ap\right)\left(\frac ak\right)
=\left(\frac a{pk}\right)
=\left(\frac an\right).
]

The base case (n=1) is handled separately.

Because the composite sign theorem permits noncoprime factors, the induction works even when (p\mid k).

The complete general result is formalized in "FinalInduction.lean", first for natural-number multipliers and then for arbitrary units.

4. Repository Structure

File| Purpose
"NumberTheoryLean/Zolotarev.lean"| Canonical public theorems
"NumberTheoryLean/ZolotarevCore.lean"| Multiplication permutations, sign character, Jacobi definitions, elementary lemmas
"NumberTheoryLean/GlassalaPrime.lean"| Adapted prime-case formalization by Will Sweet
"NumberTheoryLean/PrimeBridge_fixed_v2.lean"| Relates signs on all residues and on units
"NumberTheoryLean/PrimeFromGlassala.lean"| Establishes the prime theorem in the project's API
"NumberTheoryLean/ProductSign.lean"| Signs of product and block permutations
"NumberTheoryLean/OddAffineSign.lean"| Signs of translations and affine permutations on odd-order structures
"NumberTheoryLean/CarryDigits.lean"| Quotient–remainder identities and digit decomposition
"NumberTheoryLean/AffineTransport.lean"| Transport of affine permutation signs through equivalences
"NumberTheoryLean/DigitConjugacy.lean"| Composite-modulus sign multiplicativity
"NumberTheoryLean/FinalInduction.lean"| Strong induction proving the general theorem
"tests/Infrastructure.lean"| Lean regression and infrastructure tests
"tests/verify_zolotarev.py"| Independent finite numerical checks
"tests/verify_structural.py"| Independent numerical checks of structural identities
"PROOF_PLAN.md"| Historical mathematical development and alternative proof route

The source architecture separates foundational definitions from the prime and composite proofs, preventing circular dependencies.

The canonical theorem is exposed only after importing the completed induction.

5. Build and Verification

Requirements

- Lean 4.33.1
- Mathlib v4.33.1
- Lake and Elan

The versions are specified by "lean-toolchain" and "lakefile.toml".

Build the project

From the repository root, run:

lake update
lake exe cache get
lake build NumberTheoryLean

Compile the infrastructure tests

lake env lean tests/Infrastructure.lean

The infrastructure tests exercise the fundamental definitions and include composite-modulus applications for (n=45) and (n=225).

These examples verify the theorem's usability in cases with repeated prime factors.

Independent numerical tests

The repository also provides numerical checking scripts:

python3 tests/verify_zolotarev.py
python3 tests/verify_structural.py

These computations provide additional regression checks but are not substitutes for the Lean proof.

6. Axiom Audit

Lean's "#print axioms" command was applied to the four principal results:

- "Zolotarev.zolotarev_prime"
- "Zolotarev.sign_mul_modulus"
- "Zolotarev.zolotarev_unit"
- "Zolotarev.zolotarev_nat"

All four reported precisely the standard Lean axioms:

"[propext, Classical.choice, Quot.sound]"

None depends on "sorryAx".

The independently named final-induction theorems, "zolotarev_nat_final" and "zolotarev_unit_final", passed the same audit.

Thus the general result is kernel-checked without admitted mathematical steps.

Continuous integration

The repository uses GitHub Actions to build the formalization and compile its infrastructure tests.

On October 20, 2026, GitHub Actions Run #53 completed successfully. It confirmed:

- Successful compilation of the full formalization.
- Successful compilation of the Lean regression tests.
- No "sorryAx" dependencies in the principal theorems.
- No active admitted-proof warnings.

The successful run is available at:

https://github.com/jkfarland-bot/Number-theory-lean/actions/runs/39510608527

7. Distinctive Features

The formalization has several features of potential independent interest.

Noncoprime modulus decomposition. The composite-modulus sign formula works for any two odd positive factors, including those sharing primes.

Digit-conjugacy proof. The method uses quotient–remainder coordinates instead of applying the Chinese remainder theorem.

Reusable permutation lemmas. Several results concerning product permutations, block permutations, translations, and affine transformations may be useful beyond Zolotarev's lemma.

Direct induction. The full theorem follows by strong induction on the modulus, without a separate classification of prime-power cases.

These are features of the present formalization, not claims that the underlying mathematics is new.

8. Attribution and Development

The prime-case formalization builds on work by Will Sweet, available in the repository:

https://github.com/glassala/zolotarev

The adapted source is retained in "GlassalaPrime.lean", with the original author's copyright and attribution.

The composite-modulus decomposition, supporting permutation-sign machinery, and final induction were developed as part of this project.

This project was developed with substantial AI assistance, including mathematical exploration, Lean code construction, error diagnosis, and proof refactoring. The results were checked by Lean through the project's GitHub Actions workflow.

Successful formal verification does not replace independent human review of mathematical exposition, library design, and code quality.

9. Future Development

The immediate goal is to prepare the completed formalization for review and possible integration into Mathlib.

Remaining work includes:

1. Reviewing the code for Mathlib naming, documentation, and style conventions.
2. Simplifying unnecessary tactics, removing linter warnings, and minimizing imports where appropriate.
3. Identifying reusable lemmas that may merit separate Mathlib contributions.
4. Obtaining independent review by experienced Lean contributors.
5. Porting the formalization to the current Mathlib development branch.
6. Preparing appropriately scoped pull requests with the necessary attribution and AI-use disclosure.

A broader research objective is to formalize related results involving Dedekind sums and Meyer's formula, building on the permutation-sign machinery developed here.

10. License

The repository is distributed under the Apache License, Version 2.0. See the root "LICENSE" file.

Third-party contributions retain their original copyright and attribution notices.

---

Project status: The general Zolotarev lemma is formally verified for all odd positive moduli. The standalone implementation is complete at the proof level; external review and upstream Mathlib integration remain future work.
