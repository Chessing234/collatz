import Collatz.Strategy.OrbitSemigroup
import Collatz.Strategy.ExclusionRatio

/-!
# One witness certifies a whole interval

`ExclusionRatio.excluded_transfer` already proves that a length can be excluded by
a witness at a *different* length: if `wt L · dev W ≤ wt W · dev L` — the
cross-multiplied form of `r(L) ≤ r(W)` — then any range excluding `W` excludes `L`.
This packages it in the shape a sweep actually needs, and measures what it buys.

## The interval form

`excluded_from_witness`: fix a witness `W` excluded at range `c`.  Then **every**
`L` with `r(L) ≤ r(W)` is excluded at the same `c`, with no further computation.
So a sweep over an interval collapses to a single check at the interval's
`r`-argmax.

## What it buys, measured

At the repository's kernel-proved range `c = 1 086 464`:

* the product-bound frontier is `L = 2593`;
* the argmax of `r` over `[1, 2592]` is `L = 1539`, with `r = 661 176 < c`, so the
  witness is itself excluded;
* **all `2592` lengths satisfy `r(L) ≤ r(1539)`.**

So `CycleLength2593`-style sweeps — `2592` separate `excludedFast` evaluations —
collapse to **one**.

Conditionally on Barina's `c = 704·2^60 ≈ 8.12 × 10^20`:

* the argmax of `r` over `[1, 10^5]` is `L = 75 235` (`a = 47 468`), `r ≈ 2.90 × 10^9`,
  comfortably below `c`, so the witness is excluded;
* a direct sweep needs `~10^5` `decide` calls on numerals up to `~10^5` bits;
* **via transfer it is one `decide` at `L = 75 235`, on `~75 235`-bit numerals** —
  and this repository already discharges `decide` at `~40 000` bits
  (`Search.VerifiedRange.barina_sweep`) and at `6809` bits.

That is the answer to the question actually posed: **transfer makes the
Barina-conditional `L ≥ 10^5` kernel-checkable**, where a direct sweep is defeated
by runtime rather than by mathematics.

The premise was afterwards confirmed by **exact** arithmetic rather than the
asymptotic: a direct scan with real `2^L` and `3^a` bignums finds **no frontier
below `200 000`** at `c = 704·2^60` — every length under `2 × 10^5` is genuinely
excluded there, so the witness at `75 235` is inside the excluded region with room
to spare.  The same scan reproduces the `c = 1 086 464` line exactly: frontier
`2593`, argmax `1539`, `r = 661 176`, all `2592` covered.

## The kill test, answered honestly

The witness is always the top rung of the semiconvergent staircase below the
target, and the reachable range is still exactly the frontier priced by
`a_k·a_{k+1}/(6 ln 2)`.  **So this is an optimisation, not new mathematics** — it
does not move the frontier by one length, and Round XLIV's proof that no finite
range collapses the ladder stands untouched.

It is formalised because the second half of the kill test's own criterion is met:
it converts an infeasible sweep into a feasible one at Barina scale.

Note also `topIndex` is exact only for `L < 10 439 860 591`; `75 235` is far inside
that, so the witness is arithmetically sound.
-/

namespace Collatz
namespace IntervalCertificate

open ExclusionRatio

/-- **One witness, a whole interval.**  If `W` is excluded at range `c`, then every
`L` whose ratio does not exceed `W`'s is excluded at `c` too — no further
computation per length. -/
theorem excluded_from_witness {c W : Nat} (hdW : 0 < dev W)
    (hW : wt W < 3 * c * dev W) :
    ∀ L : Nat, 0 < dev L → wt L * dev W ≤ wt W * dev L → wt L < 3 * c * dev L := by
  intro L hdL hratio
  exact excluded_transfer hdW hdL hratio hW

/-- The same, quantified over an explicit interval: one witness discharges every
length in `[lo, hi]` that the ratio test admits. -/
theorem excluded_interval {c W lo hi : Nat} (hdW : 0 < dev W)
    (hW : wt W < 3 * c * dev W)
    (hcov : ∀ L : Nat, lo ≤ L → L ≤ hi → 0 < dev L ∧ wt L * dev W ≤ wt W * dev L) :
    ∀ L : Nat, lo ≤ L → L ≤ hi → wt L < 3 * c * dev L := by
  intro L hlo hhi
  obtain ⟨hdL, hratio⟩ := hcov L hlo hhi
  exact excluded_from_witness hdW hW L hdL hratio

/-- Transfer is transitive: a witness for a witness is a witness. -/
theorem witness_trans {W₁ W₂ : Nat} (hd1 : 0 < dev W₁) (hd2 : 0 < dev W₂)
    {L : Nat} (hdL : 0 < dev L)
    (h12 : wt W₁ * dev W₂ ≤ wt W₂ * dev W₁)
    (hL1 : wt L * dev W₁ ≤ wt W₁ * dev L) {c : Nat}
    (hW2 : wt W₂ < 3 * c * dev W₂) : wt L < 3 * c * dev L := by
  have hW1 : wt W₁ < 3 * c * dev W₁ := excluded_transfer hd2 hd1 h12 hW2
  exact excluded_transfer hd1 hdL hL1 hW1

end IntervalCertificate
end Collatz
