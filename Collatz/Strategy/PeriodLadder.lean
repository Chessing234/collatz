import Collatz.Strategy.ShallowChain
import Collatz.Strategy.CycleLength1539
import Collatz.Strategy.ExclusionRatio

/-!
# The Eliahou-type form at Barina scale — and why it is already ours

## The form, with current continued-fraction data

Eliahou's constants `301 994`, `17 087 915`, `85 137 581` are convergent numerators
of `log₂ 3`, at indices `13, 15, 16`.  Recomputing the expansion:

`…, 485, 1054, 24727, 50508, 125743, 176251, 301994, 16785921, 17087915, 85137581,
272500658, 357638239, 630138897, 9809721694, 10439860591, …`

At the Barina floor `c = 704·2^60 ≈ 8.117 × 10^20`, the product bound leaves
exactly the one-sided best approximations above its frontier.  Computed, the
surviving lengths begin

`114 208 327 604`, `217 976 794 617`,

and the first is `103 768 467 013 + 10 439 860 591` — the **sum of two consecutive
convergent numerators**, i.e. a semiconvergent.  So the Eliahou-type form at this
scale reads `p = αa + βb + γc` with `α, β, γ` the convergents around indices
`21–23` rather than `13, 15, 16`, `b ≥ 1`, `ac = 0`.

## The kill test fires

**This form is implied by what the repository already has**, which is exactly the
stated kill condition.

`ExclusionRatio.excluded_iff_gap` (Round XLIII) proved that `L` is excluded exactly
when `c` exceeds the ratio `r(L) = wt L / (3·dev L)`, a quantity depending on `L`
alone; and Rounds XLIII–XLIV established that the records of `r` — hence the
surviving lengths — are precisely the one-sided best approximations of `log₃ 2`,
the semiconvergent ladder `P + kP′`.  **That ladder is the Eliahou-shape set.**

So the semigroup membership is a restatement of `product_invariant`'s ratio form,
not a new constraint.  **No new theorem is claimed, and the kernel closes no length
beyond `RealizableFrontier6809`.**

What is formalised below is only the packaged arithmetic implication the mission
asked for, in the form the repository can state it.

## The implication

`period_not_excluded`: if every element of a cycle of period `L` is at least `c` —
which is what a verification floor gives — then `L` is **not** excluded at `c`.
Contrapositive of `CycleProduct.no_cycle_of_excludedLength`.  Combined with
`excluded_iff_gap` this says the period satisfies `3·c·dev L ≤ wt L`, i.e.
`r(L) ≥ c`: the period lies among the `r`-records, which is the ladder.

That is the whole content of "min-cycle-element `≥ 2^K` ⇒ `p` belongs to the
semigroup", and it is one rewrite away from what was already proved.
-/

namespace Collatz
namespace PeriodLadder

open CycleProduct ExclusionRatio CycleLength1539

/-- **The packaged implication.**  A cycle all of whose elements are at least `c`
cannot have an excluded period. -/
theorem period_not_excluded {x c L : Nat} (hx : 0 < x) (hcpos : 0 < c)
    (hc : ∀ k : Nat, c ≤ acceleratedOrbit k x) (hcyc : acceleratedOrbit L x = x)
    (hsmall : 2 * oddCount x L ≤ 3 * c) (hle : oddCount x L ≤ L)
    (hlt : 3 ^ oddCount x L < 2 ^ L) :
    excludedLength c L = false := by
  cases h : excludedLength c L with
  | false => rfl
  | true => exact (no_cycle_of_excludedLength hx hcpos hc hcyc hsmall hle hlt h).elim

/-- The same through the fast test: an admissible period fails `excludedFast` too. -/
theorem period_not_excludedFast {x c L : Nat} (hx : 0 < x) (hcpos : 0 < c)
    (hc : ∀ k : Nat, c ≤ acceleratedOrbit k x) (hcyc : acceleratedOrbit L x = x)
    (hsmall : 2 * oddCount x L ≤ 3 * c) (hle : oddCount x L ≤ L)
    (hlt : 3 ^ oddCount x L < 2 ^ L) :
    excludedFast c L = false := by
  cases h : excludedFast c L with
  | false => rfl
  | true =>
      have hL := excludedLength_of_excludedFast h
      exact (no_cycle_of_excludedLength hx hcpos hc hcyc hsmall hle hlt hL).elim

/-- **The ratio form.**  In the `wt`/`dev` coordinates of `ExclusionRatio`, an
admissible period satisfies `3·c·dev L ≤ wt L`, i.e. `r(L) ≥ c`.  Since the records
of `r` are the one-sided best approximations of `log₃ 2`, this is exactly the
statement that the period lies on the semiconvergent ladder. -/
theorem period_ratio_ge {c L : Nat} (hdev : 3 ^ topIndex L ≤ 2 ^ L)
    (h : ¬ (3 ^ topIndex L * (3 * c + 2 * topIndex L) < 3 * c * 2 ^ L)) :
    ¬ (wt L < 3 * c * dev L) := by
  rw [← excluded_iff_ratio hdev]
  exact h

end PeriodLadder
end Collatz
