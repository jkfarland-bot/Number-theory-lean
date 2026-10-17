# Zolotarev's lemma: complete mathematical proof and Lean work plan

## Status

The following is a *paper proof* of the theorem. The Lean file retains one
explicit `sorry` and has not been compiled. Do not mistake the paper proof or
finite computations for kernel-checked formalization.

## Theorem

For any positive odd integer `n` and any integer `a` with `gcd(a,n)=1`, let
`σ_{a,n}` permute `Z/nZ` by multiplication by `a`. Then

`sign(σ_{a,n}) = Jacobi(a,n)`.

We use a different (and more efficient) proof decomposition from the first draft:
prove prime-power factors using the *existing cyclicity of the units*, then
assemble the general case through a permutation-sign law for Cartesian products.

## Lemma A: sign on Cartesian products

Let `f` be a permutation of a finite set `X` and `g` a permutation of a finite
set `Y`. The Cartesian-product permutation is `(x,y) ↦ (f(x),g(y))`. Then

`sign(f × g) = sign(f) ^ |Y| * sign(g) ^ |X|`.

**Proof.** Factor `f × g = (f × id) ∘ (id × g)`. The first factor is `|Y|`
copies of `f`, operating in disjoint fibers; the second is `|X|` copies of `g`.
Sign is multiplicative and the sign of a disjoint union is a product. QED.

For odd `|X|` and `|Y|`, the powers disappear:

`sign(f × g) = sign(f) * sign(g)`.

### Lean obligations

1. Provide a generic `Equiv.Perm.sign_prodCongr` theorem if none is available.
2. Transport sign through the CRT equivalence using
   `Equiv.Perm.sign_permCongr` (existing in Mathlib).
3. Express multiplication under `ZMod.chineseRemainder` as `f × g`.

## Lemma B: cyclic translation on a finite group

Let `G` be a cyclic finite group of even order `N`, and let `g` generate `G`.
The permutation `x ↦ gx` is a single `N`-cycle, hence has sign
`(-1)^(N-1) = -1`.

For any exponent `r`, multiplication by `g^r` has sign `(-1)^r`.

This relies only on `Equiv.Perm.sign_finRotate` / conjugacy invariance, or a
standard theorem on signs of cycles.

## Lemma C: sign modulo an odd prime power

Fix an odd prime `p` and `k ≥ 1`. The group `(ZMod (p^k))ˣ` is cyclic; Mathlib
already proves `ZMod.isCyclic_units_of_prime_pow`. Let `g` generate it.

The residues modulo `p^k` split into the disjoint invariant layers

`{0}` and `S_j = {p^j u : u a unit modulo p^(k-j)}` for `0 ≤ j < k`.

Multiplication by `g` acts on `S_j` as multiplication by the reduction of `g`
modulo `p^(k-j)`. This reduced generator still generates the unit group:
reduction of units modulo a lower prime power is surjective, and the image of
a cyclic generator generates the image group.

Each `S_j` has cardinality `φ(p^(k-j)) = p^(k-j-1)(p-1)`, which is even. The
permutation induced by `g` on the layer is one full cycle, with sign `-1`.
The zero residue is fixed.

There are exactly `k` nonzero layers, so:

`sign(σ_{g,p^k}) = (-1)^k`.

Every unit `a` equals `g^r`. By multiplicativity,

`sign(σ_{a,p^k}) = (-1)^(kr)`.

Modulo `p`, the reduction of `g` is a primitive root; hence Euler's criterion
(or the cyclic square/nonsquare criterion) gives `Legendre(g,p) = -1`, whence
`Legendre(a,p) = (-1)^r`.

Therefore

`sign(σ_{a,p^k}) = Legendre(a,p)^k = Jacobi(a,p^k)`.

**Case k=0:** `p^0=1`; the ring has one residue, and both the sign and Jacobi
symbol are `1`. Thus the prime-power identity remains true.

### Lean obligations

1. Use `ZMod.isCyclic_units_of_prime_pow` to choose a generator of units.
2. Build the valuation-layer partition of `ZMod (p^k)`.
3. Show generator reduction to `p^(k-j)` is a generator (surjectivity).
4. Show multiplication is a full even-length cycle on each layer.
5. Invoke Jacobi `pow_right` or prime-factor multiplicativity.

## Lemma D: Chinese remainder step

If `m,n` are coprime odd positive integers, CRT gives a ring equivalence

`ZMod(m*n) ≃+* ZMod m × ZMod n`.

The multiplication permutation is conjugate to the product of the respective
multiplication permutations. Lemma A yields

`sign(σ_{a,m*n}) = sign(σ_{a,m})^n * sign(σ_{a,n})^m`
                  `= sign(σ_{a,m}) * sign(σ_{a,n})`, because `m,n` are odd.

Mathlib's `jacobiSym.mul_right` gives exactly the corresponding factorization
for the Jacobi symbol.

## Conclusion

Factor `n` into pairwise coprime odd prime powers. Lemma C handles each factor.
Repeated application of Lemma D multiplies the signs, reproducing the product
of Legendre symbols defining Jacobi(a,n). QED.

## Alternative shorter parity bridge: signed pairs

For any odd `n`, the nonzero residues pair as `{x,-x}`. Choose their canonical
representatives `1 ≤ x ≤ (n-1)/2`. Multiplication by a unit `a` permutes those
pairs; the induced permutation of the pairs contributes its sign **twice**, so
its total contribution to the full residue permutation is `+1`. Only the swaps
of the two orientations in each pair determine the sign:

`sign(σ_{a,n}) = (-1)^F`, where

`F = #{1 ≤ x ≤ (n-1)/2 : (a*x mod n) > n/2}`.

This is a generalized Gauss lemma, valid even when `n` is composite. The last
step needed to connect it to Mathlib's Jacobi symbol is

`Jacobi(a,n) = (-1)^F`.

This is a useful **alternate dependency structure**; it does not by itself
prove Jacobi's equality inside Lean. The main advantage is that the pair
argument applies uniformly to all odd moduli and can be reused for Meyer.

## Mathlib API confirmed in online documentation (16 October 2026)

- `Units.mulLeft`, `Units.mulLeft_symm`;
- `Equiv.Perm.sign`, `Equiv.Perm.sign_permCongr`, `Equiv.Perm.sign_sumCongr`;
- `Equiv.Perm.sign_finRotate` (in `Mathlib.GroupTheory.Perm.Fin`);
- `ZMod.isCyclic_units_prime`, `ZMod.isCyclic_units_of_prime_pow`;
- `ZMod.unitOfCoprime`, `ZMod.val_natCast`;
- `jacobiSym.mod_left'`, `jacobiSym.mul_right`, `jacobiSym.pow_right`.

There does not appear to be a readily documented `sign_prodCongr` theorem:
this is a useful small Mathlib support contribution in its own right.
