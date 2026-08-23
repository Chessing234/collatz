import Collatz.Strategy.CycleProduct
import Collatz.Strategy.AffineExact

/-!
# Reverse dynamics with exact magnitude: the shape of a reverse path is pinned

Round XV, brief section 15.

## The standing verdict, and why this is not it again

`ReverseTree` proved the reverse formulation is a **relabeling**
(`reverse_eq_forward`: `T^L(x) = y` *iff* `3^a x + C = 2^L y`), and `BackwardRange`
proved that the verified range costs the reverse tree a *constant factor and never
an exponent* — the branching factor stays `4/3`, the pruning lives entirely in the
window `[1086464, 1629696]`.  The brief forbids repeating "the reverse tree is just
relabelling", so this file carries **magnitude**, not symbols.

## What is proved

Let `T^k(x) = y` and suppose every node of the path is at least an integer floor
`B`.  Two exact inequalities bracket `2^k y` from both sides:

* below, from the affine identity with `C ≥ 0`:      `3^a · x ≤ 2^k · y`;
* above, from `CycleProduct.product_invariant`:      `2^k · y · B^a ≤ (3B+1)^a · x`.

Together (`reverse_shape_pinned`):

`1  ≤  (2^k · y) / (3^a · x)  ≤  (1 + 1/(3B))^a`.

Linearising the right side (`CycleProduct.pow_succ_le`) makes it explicit
(`reverse_pinch_one_bit`): whenever `2a ≤ 3B`,

`3^a · x  ≤  2^k · y  ≤  2 · 3^a · x`.

## The exact magnitude, and the precise obstruction

**Read as a statement about the reverse tree above a counterexample.**  Round XIV
showed every ancestor of a counterexample is itself a counterexample, so the whole
reverse tree lies above `B = 1086464`.  Then `2a ≤ 3B` holds for every

`a ≤ 1 629 696`

and the conclusion is: **for every reverse path with at most `1 629 696` odd
branches, `k·log 2 + log y − a·log 3 − log x` lies in `[0, 1)` — the pair `(k, a)`
is determined by the two endpoints to within one bit.**  The true width of the
window is `a · log₂(1+1/(3B)) = a / 2 259 238` bits, so the freedom does not reach
even one bit until

`a ≈ 2.26 · 10^6`.

So the reverse tree above a counterexample has, for every depth the verified range
can reach, **essentially one shape per endpoint pair**: all of its `(4/3)^k`
branching is in the *choice of divisibility class* (`BackwardRange.endpoint_class`:
a word with `a` ones cuts one class mod `3^a`), none of it in the shape `(k, a)`.

**And that is exactly why the branch stays dead.**  Shape-rigidity is a constraint
on `(k, a)`, and `ArchimedeanCeiling.sandwich_vacuous` already proved every
`(k,a)`-constraint of this family is capped.  The magnitude computation converts
"the reverse tree is a relabeling" into a number — `2.26 · 10^6` odd branches of
slack — and that number is a *ceiling on what the reverse reading can ever say*,
not a contradiction.  No modular obstruction is available either: `ReverseTree`
settled the mod-3 branching completely (branch iff `y ≡ 2 mod 3`, every odd step
lands on a branch point), and `ValuationBudget.word_residue_free` shows every odd
modulus is free.

## The `expStep` test

`reverse_pinch_one_bit` **fails for `expStep`**: it is built on
`product_invariant`, whose even-step case is `2·T(x) ≤ x`.  For `expStep`,
`2·expStep x = 3x > x` on the even branch.  Concretely, `x = 2^k`, all steps even,
`a = 0`, `y = 3^k`: the claim `1 ≤ 2^k·3^k / 1 ≤ 2` is false for `k ≥ 1`.  The
lower half (`3^a x ≤ 2^k y`, from `C ≥ 0`) does hold for `expStep`; only the upper
half discriminates, and it is the half carrying the even branch's contraction.
-/

namespace Collatz
namespace ReversePinch

open Reach Congruence AffineExact CycleProduct

/-- **Both ends of a reverse path, exactly.**  If `T^k(x) = y` and the whole path
stays at or above the integer floor `B`, then `2^k y` is caught between `3^a x`
and `3^a x · (1 + 1/(3B))^a`, cleared of denominators. -/
theorem reverse_shape_pinned {x y B k : Nat}
    (hB : ∀ i : Nat, B ≤ acceleratedOrbit i x) (hy : acceleratedOrbit k x = y) :
    3 ^ oddCount x k * x ≤ 2 ^ k * y
      ∧ (2 ^ k * y) * B ^ oddCount x k ≤ (3 * B + 1) ^ oddCount x k * x := by
  refine ⟨?_, ?_⟩
  · have haff := affine_exact x k
    rw [hy] at haff
    omega
  · have hinv := product_invariant hB k
    rw [hy] at hinv
    have hcomm : 2 ^ k * B ^ oddCount x k * y = (2 ^ k * y) * B ^ oddCount x k := by
      simp [Nat.mul_comm, Nat.mul_left_comm]
    omega

/-- **The reverse path's shape is pinned to one bit.**  With `a = oddCount x k`
and `2a ≤ 3B`, the endpoints determine `(k, a)` up to a factor of two:

`3^a · x ≤ 2^k · y ≤ 2 · 3^a · x`.

Above the verified range `B = 1086464` this covers every reverse path with at most
`1 629 696` odd branches. -/
theorem reverse_pinch_one_bit {x y B k : Nat} (hBpos : 0 < B)
    (hB : ∀ i : Nat, B ≤ acceleratedOrbit i x) (hy : acceleratedOrbit k x = y)
    (hsmall : 2 * oddCount x k ≤ 3 * B) :
    3 ^ oddCount x k * x ≤ 2 ^ k * y ∧ 2 ^ k * y ≤ 2 * (3 ^ oddCount x k * x) := by
  obtain ⟨hlow, hhigh⟩ := reverse_shape_pinned hB hy
  refine ⟨hlow, ?_⟩
  -- name `3B` so that no numeral folding interferes with the rearrangements
  obtain ⟨u, hu⟩ : ∃ u : Nat, 3 * B = u := ⟨3 * B, rfl⟩
  rw [hu] at hhigh
  have hupos : 0 < u := by omega
  have hBpow : 0 < B ^ oddCount x k := Nat.pow_pos hBpos
  -- linearise `(u+1)^a · u ≤ u^a · (u + 2a) ≤ u^a · 2u`
  have hlin := pow_succ_le (oddCount x k) u (by omega)
  have hcap : u ^ oddCount x k * (u + 2 * oddCount x k) ≤ u ^ oddCount x k * (u * 2) :=
    Nat.mul_le_mul_left _ (by omega)
  have hstep : (u + 1) ^ oddCount x k * u ≤ u ^ oddCount x k * (u * 2) :=
    Nat.le_trans hlin hcap
  have hsplit : u ^ oddCount x k = 3 ^ oddCount x k * B ^ oddCount x k := by
    rw [← hu, Nat.mul_pow]
  have hmul : ((2 ^ k * y) * B ^ oddCount x k) * u
      ≤ ((u + 1) ^ oddCount x k * x) * u := Nat.mul_le_mul_right _ hhigh
  have e1 : ((u + 1) ^ oddCount x k * x) * u = ((u + 1) ^ oddCount x k * u) * x := by
    simp [Nat.mul_comm, Nat.mul_left_comm]
  have h2 : ((u + 1) ^ oddCount x k * u) * x ≤ (u ^ oddCount x k * (u * 2)) * x :=
    Nat.mul_le_mul_right _ hstep
  have e2 : (u ^ oddCount x k * (u * 2)) * x
      = ((3 ^ oddCount x k * x) * 2) * (B ^ oddCount x k * u) := by
    rw [hsplit]; simp [Nat.mul_comm, Nat.mul_left_comm, Nat.mul_assoc]
  have e3 : ((2 ^ k * y) * B ^ oddCount x k) * u
      = (2 ^ k * y) * (B ^ oddCount x k * u) := by rw [Nat.mul_assoc]
  have hchain : (2 ^ k * y) * (B ^ oddCount x k * u)
      ≤ ((3 ^ oddCount x k * x) * 2) * (B ^ oddCount x k * u) := by omega
  have hposfac : 0 < B ^ oddCount x k * u := Nat.mul_pos hBpow hupos
  have hfin := Nat.le_of_mul_le_mul_right hchain hposfac
  omega

/-- **The pinch at the verified range.**  Every reverse path lying entirely above
`1 086 464` with at most `1 629 696` odd branches has its shape determined by its
endpoints to within one bit.  (`2 · 1629696 = 3 · 1086464`.) -/
theorem reverse_pinch_verified {x y k : Nat}
    (hB : ∀ i : Nat, 1086464 ≤ acceleratedOrbit i x) (hy : acceleratedOrbit k x = y)
    (hsmall : oddCount x k ≤ 1629696) :
    3 ^ oddCount x k * x ≤ 2 ^ k * y ∧ 2 ^ k * y ≤ 2 * (3 ^ oddCount x k * x) :=
  reverse_pinch_one_bit (by omega) hB hy (by omega)

end ReversePinch
end Collatz
