# A uniform lower bound for Syracuse atoms

2026-09-08. The literal theorem below has compiled in Lean and passed the
complete package audit. It is a result about Syracuse random variables;
the full Collatz conjecture remains unproved. Historical priority and
independent mathematical review are not established by the local check.

## Statement

Let A₁,A₂,… be independent positive geometric variables with
P(Aᵢ=v)=2⁻ᵛ for v≥1. In Z/3ⁿZ, set

$$S_n=\sum_{j=1}^n3^{j-1}2^{-(A_1+\cdots+A_j)},\qquad
\mu_n(r)=\Pr(S_n=r).$$

Reversing the iid variables gives the equivalent recursive law
Sₙ₊₁ = 2⁻ᴬ(3Sₙ+1). This is the actual imported `Tao.syracPMF`, not a
surrogate distribution or an empirical trajectory histogram.

**Theorem.** There is an absolute c>0 such that

    μₙ(r) ≥ c / 3ⁿ

for every n≥1 and every unit r modulo 3ⁿ. The same c works for all n and r.
No convergence assumption appears in the theorem.

The [literal Lean endpoint](../ProofAtlasAttack/CollatzTargetDensity/SyracuseCylinderSpread.lean)
is `CollatzTargetDensity.SyracuseMinorant.syracuse_uniform_atom_lower_bound`:

```lean
theorem syracuse_uniform_atom_lower_bound :
    ∃ c : ℝ, 0 < c ∧ ∀ n : ℕ, 1 ≤ n → ∀ r : ZMod (3 ^ n),
      IsUnit r → c / (3 : ℝ) ^ n ≤ (Tao.syracPMF n r).toReal
```

If mₙ denotes the smallest unit atom, averaging over the 2·3ⁿ⁻¹ units also
gives mₙ≤(3/2)3⁻ⁿ. Thus the proved lower bound implies
$m_n=\Theta(3^{-n})$, and in particular $m_n=3^{-n+o(n)}$. This last asymptotic deduction
is mathematical exposition; the displayed uniform inequality is the
audited Lean endpoint.

This is stronger than the β=1 smallest-atom rate proposed in
[Tao's January 2020 note](https://terrytao.wordpress.com/2020/01/25/equidistribution-of-syracuse-random-variables-and-density-of-collatz-preimages/).
The abstract of [Nikpour and Rabbani's August 2026 preprint](https://papers.ssrn.com/sol3/papers.cfm?abstract_id=7239062)
reports β≤1.039979. That abstract was checked; its full proof was not reviewed.
Neither comparison establishes a first-in-the-literature claim.

## The proof connection

Write ρₙ=(2/3)3ⁿμₙ. The factor 2/3 is retained throughout: ρ has full-Haar
mean 2/3, not one. Every Haar mean below is taken over the full finite
ternary quotient.

The proof uses substantial existing work: Tao's fine-scale mixing and
projectivity, together with Mazur's filtered core construction, its positive
probability product, and its root-uniform summed variation estimate. These
are imported unchanged from Lech Mazur's Apache-2.0 source release for
[*Explicit Positive-Density Collatz Convergence in Logarithmic Time*](https://www.proofatlas.ai/formalizations/positive-density-log-time-collatz/),
corrected source commit `0aef8b0cfaaf6959500063472f2e328c60df8d54`.
The contribution here is the one-sided comparison and its connection,
through a fixed cylinder, to the uniform minimum of the actual law.

### 1. Compare only the positive part of the error

A finite prefix-free family of valuation words, with the full Syracuse
reference tail attached to each word, is a selected part of the full law.
Its density is therefore at most ρ. Replacing the tails by their k-digit
projections costs at most C_A/kᴬ in L1, uniformly in the prefix family.
The literal word weights satisfy the Kraft bound.

Rejected probability makes a lower estimate smaller. Charging its total
mass in an absolute-error estimate would lose useful information. Keeping
only max(selected−actual,0) removes this charge. The filtered positive
kernels contract the Haar mean of the positive part of a difference.

Induction over N stages consequently proves

    mean max(G_N − ρ_{q_N}, 0) ≤ N C_A / k_N^A.

Here Gₙ is the actual imported backward core mark, kₙ its terminal
conductor, and qₙ its ambient conductor. The constant is independent of
the initial floor, cap and width schedules, and physical root.

### 2. Freeze one positive cylinder

Fix b=32⁵, cap(j)=⌊j/100⌋, and the imported core widths. The floor
sequence bₙ depends only on b and N; let kₙ=⌊bₙ/4⌋.

The imported probability product has a lower bound p>0. At every finite
generation, some unit residue has Gₙ≥2p/3. The imported variation theorem
gives, for every eligible odd physical representative M, a limit ℓ_M and

    |ℓ_M − Gₙ(M)| ≤ Tₙ,      Tₙ → 0,

with the same Tₙ for every M. The singleton denominator is exactly one.

Choose N₀ so that Tⱼ<p/6 for all j≥N₀, then choose a favorable residue
y₀ at that one generation. Freeze its cylinder B modulo 3^q₀. For every
M in B and every j≥N₀,

    Gⱼ(M) ≥ G_{N₀}(M) − T_{N₀} − Tⱼ ≥ p/3.

Every finite ternary residue has arbitrarily large odd representatives.
Thus the same bound holds at every finite atom above B, once its ambient
conductor is at least q₀. Both B and a=p/3 are fixed before later
generations or finer test cylinders are chosen.

### 3. Transfer the cylinder to the actual law

The elementary floor estimate bₙ≥b+2N gives N≤2kₙ. Taking A=2 in the
one-sided comparison yields an error εₙ≤4C₂/N for N>0.

Now fix h≥q₀ and any h-digit residue x inside B. For sufficiently large
N, qₙ≥h and Gₙ≥a throughout the fiber over x. Summing over that fiber,
using projectivity of μ, and bounding its positive error by the full
positive error gives

    a ≤ ρ_h(x) + 3ʰ εₙ.

Let N grow with h and x fixed. It follows that ρ_h(x)≥a. The Lean proof
uses a finite contradiction and a sufficiently large integer N, so no
infinite 3-adic measure construction is required. The quantifier order
prevents an invalid pointwise inference at a moving conductor.

### 4. Spread to every unit with a bounded valuation

Fix any unit r modulo 3^{h+1}, with h≥q₀. An elementary inverse of its
canonical representative has 3c+1=2ᵉr.val with e∈{1,2}. Its siblings

    c_t = 4ᵗc + (4ᵗ−1)/3

cover every residue modulo 3^q₀ as 0≤t<3^q₀. This follows because
(4ᵗ−1)/3 permutes those residues and 3c+1 is a unit modulo 3.
Moreover 3c_t+1=2^{2t+e}r.val. Hence some child z lies in B, and the
corresponding valuation v is at most V=2·3^q₀+2, independent of h and r.

One term in the exact Syracuse recursion now gives

    ρ_{h+1}(r) ≥ 3·2⁻ᵛ ρ_h(z) ≥ 3·2⁻ⱽ a > 0.

Projectivity preserves this floor at smaller positive conductors: every
lift of a unit is a unit, and the lower density is the average over its
fiber. Finally convert from ρ back to μ. This proves the theorem.

## Verification and limits

Run from `ProofAtlasAttack`:

```sh
LEAN_NUM_THREADS=4 python3 scripts/verify.py
```

The completed check reports 38 audited endpoints, including the literal
uniform atom theorem. All 1,485 pinned upstream source hashes match.
The checked local and upstream source contains no proof escapes detected
by the integrity scan. Every audited endpoint depends only on `propext`,
`Classical.choice`, and `Quot.sound`.

Evidence: [verification report](../ProofAtlasAttack/verification/local-report.json),
[axiom audit](../ProofAtlasAttack/verification/syracuse-minorant-axioms.log),
[build transcript](../ProofAtlasAttack/verification/local-build.log).
The package uses Lean 4.30.0-rc2 and its pinned Mathlib dependencies.
This is local Lean verification with cached third-party dependencies,
not an independent checker replay or external peer review.

The argument gives an existential constant, not a useful numerical value.
It does not prove that every positive integer reaches 1, density-one
convergence, exclusion of every nontrivial cycle, or exclusion of every
divergent orbit. A theorem about these random variables cannot silently
be substituted for the required deterministic trajectory statement.
