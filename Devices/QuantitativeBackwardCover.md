# Uniform quantitative coverage of the inverse Collatz tree

Date: 2026-09-07. Status: **proved in Lean**, with finite certificates.
Novelty: new explicit bounds and a reusable certificate construction in this
repository; **no claim of priority in the mathematical literature**.

The qualitative fact that inverse Collatz trees meet prescribed arithmetic
progressions is classical. See Monks et al., *Strongly sufficient sets and the
distribution of arithmetic sequences in the 3x+1 graph*, especially the
introduction and Section 4 ([paper](https://arxiv.org/abs/1204.3904)), and the
prior-art audit in [BackwardMixing.md](BackwardMixing.md). This work targets
explicit size and time bounds uniform in the root, which the previous
`scripts/backward_cover.py` root samples did not establish.

## The result

Use the accelerated map

\[
T(n)=\begin{cases}n/2&n\text{ even},\\(3n+1)/2&n\text{ odd}.\end{cases}
\]

For **every positive integer** `a` with `a % 3 ≠ 0`, and every `r < M`, there
exist an odd positive integer `n` and a time `t` such that

\[
n\equiv r\pmod M,\qquad T^t(n)=a,\qquad n<B a,\qquad t\le V,
\]

with the following proved constants:

| Modulus M | Size factor B | Accelerated steps V | Maximum inverse word length used |
|---|---:|---:|---:|
| 9 | 720 | 19 | 6 |
| 27 | 19,419 | 22 | 5 |

All residues are covered, including multiples of three. The root may be even;
the constructed predecessor is always odd. No assumption that `a` reaches 1
is used. The quantifier over `a` has no upper cutoff.

The main declarations are `QuantitativeBackwardCover.cover_mod9` and
`QuantitativeBackwardCover.cover_mod27`. In particular, `cover_mod27_cube`
gives the simpler bound `n < 27^3 * a`.

## Mathematical mechanism

An inverse letter is

\[
P_v(a)=\frac{2^v a-1}{3},\quad v\ge1,\quad 2^v a\equiv1\pmod3.
\]

For an admissible word `w=(v₁,…,v_d)`, let `P_w(a)` apply these letters in
order, and put `V(w)=v₁+⋯+v_d`. The proof establishes:

1. **Actual orbit:** `T^(V(w))(P_w(a)) = a`.
2. **Strict size bound:** for nonempty `w`,
   `3^d * P_w(a) < 2^(V(w)) * a`.
3. **Precision transfer:** if `a ≡ b (mod 3^(k+d))` and `w` is admissible at
   `b`, it is admissible at `a`, and `P_w(a) ≡ P_w(b) (mod 3^k)`.

The third statement is the key to obtaining an infinite theorem from finite
certificates: each inverse division by three consumes exactly one available
ternary digit of the root.

A certificate starts with root class `1 mod 3` or `2 mod 3`. It either supplies
a word valid for the entire class, or splits the class into the three possible
next ternary digits. At a leaf of precision `e`, Lean checks

```
w is nonempty
k + length(w) ≤ e
w is admissible at the class representative b
P_w(b) % 3^k = target
sum(w) ≤ V
2^sum(w) ≤ B * 3^length(w)
```

The general theorem `InverseCover.check_sound` proves that a successful finite
tree covers every positive integer in its root class. For both certificates,
at most eight ternary digits are read. The trees have 406 and 7,222 leaves
respectively, shared conceptually across infinitely many integer lifts.

The search is adaptive: a successful short word stops refinement of that
class. This is more compact than separately storing a witness for every
root/target pair modulo `3^8`.

## What changed relative to one-generation coverage

The classical full-period construction uses at most `2M` accelerated steps
and yields the coarse bound `n < (2^(2M)/3)*a`. At modulus 27 this permits 54
steps and a factor about `6.0 × 10^15`. Allowing several inverse generations
gives the proved 22-step and 19,419-factor bounds above. This comparison is to
that elementary construction, **not a claim to improve a literature record**.

The proof also transports a hypothetical nonconvergent root to a
nonconvergent odd predecessor in every residue modulo 27, with the same size
bound (`nonconvergent_in_every_class`). Conversely, verifying convergence in
one class below `19419*N` implies convergence for all positive roots at most
`N` that are prime to three (`reachesOne_of_class_verified`). Its finite
verification hypothesis is explicit and is not asserted to hold here.

## Limits and unsuccessful extensions

This proves finite-modulus coverage. It does **not** prove that every number
belongs to the tree of 1, positive density of that tree, or a polynomial
covering bound uniform over `M=3^k`.

The promising general problem remains: are there absolute constants `C,D`
such that every eligible root and every residue modulo `M=3^k` have an odd
predecessor `n < C*M^D*a`? No such assertion is assumed in the Lean code.
The two proved values of `k` do not justify extrapolating one.

Some bounded searches failed. For example, at modulus 81, depth at most 6,
total valuation at most 28, and factor `81^3`, the search left root class
`46132 mod 59049`, target 11, uncovered. This is a failure of that restricted
certificate search, **not** a counterexample to polynomial coverage. Likewise,
the modulus-27 attempt with depth 8, valuation budget 28 and factor 2,000
left `46978 mod 177147`, target 0, uncovered. The reported successful constants
are not claimed optimal.

## Reproduction and trust

Run from the repository root:

```sh
python3 scripts/inverse_cover_certificate.py --output Collatz/Strategy/InverseCoverMod9.lean
python3 scripts/inverse_cover_certificate.py --k 3 --depth 5 --budget 22 --factor 19419 --output Collatz/Strategy/InverseCoverMod27.lean
bash scripts/check_integrity.sh
```

Python only searches for and emits witnesses. Each tree is checked using
Lean's ordinary `by decide`, and the checker is connected to the actual
`Collatz.acceleratedOrbit` by a proved soundness theorem. There are no proof
placeholders, added axioms, or native computation shortcuts. The repository
integrity script audits the new public theorems as well as the existing ones.

Source files: `Collatz/Strategy/InverseCover.lean` (semantics and soundness),
`InverseCoverMod9.lean` and `InverseCoverMod27.lean` (generated data and proofs),
`QuantitativeBackwardCover.lean` (public results).
