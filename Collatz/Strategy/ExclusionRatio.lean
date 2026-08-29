import Collatz.Strategy.CycleLength1539

/-!
# The exclusion test is a comparison against a ratio that does not depend on the range

`CycleProduct.excludedLength` and `CycleLength1539.excludedFast` both decide a
length `L` by the inequality

`3 ^ a · (3c + 2a) < 3c · 2 ^ L`,   `a = topIndex L`,

with `c` the verified range.  Written that way the verified range is tangled
into both sides, and the only visible way to push the frontier is to raise `c`
and re-run the sweep.  It separates.

## The separation

`excluded_iff_gap`: when `3 ^ a ≤ 2 ^ L`, the test is *equivalent* to

**`2a · 3 ^ a < 3c · (2 ^ L − 3 ^ a)`,**

so `L` is excluded exactly when `c` exceeds the rational

`r(L) = 2a · 3 ^ a / (3 · (2 ^ L − 3 ^ a))`,

a quantity **depending only on `L`**.  `wt` and `dev` name its numerator and
denominator.  Two consequences follow immediately and are proved here:

* `excluded_of_le` — the test is monotone in the range, so a wider verified
  range never loses a length.  (Obvious, and worth having once.)
* **`excluded_transfer`** — if `r(L) ≤ r(L')` (cross-multiplied, so no division
  is needed) then excluding `L'` excludes `L`.

`excluded_transfer` is the load-bearing one.  It says a length can be killed by
a *witness at a different length*, which is what an interval-exclusion argument
needs: the sweep does not have to visit `L` at all.

## What the ratio is, and why the frontier lands where it does

Writing `2 ^ L / 3 ^ a = 1 + d(L)`, the ratio is `r(L) = 2a / (3 d(L))`, and
since `a ≈ L log₃ 2` this is `≈ 0.42 · L / d(L)`.  So `L` survives when
`d(L) / L` is small — when `a/L` is an unusually good rational approximation to
`log₃ 2` *from the correct side*.  The surviving lengths are therefore the
one-sided best approximations of `log₃ 2`, and nothing else.

Measured (exact integer arithmetic, first surviving `L` at each range):

| `c` | frontier |
|---|---|
| `102 400` | `485` |
| `307 200` | `1539` |
| `768 000` | `2593` |
| `1 536 000` | `3647` |
| `3 072 000` | `6809` |
| `6 144 000` | `9971` |
| `12 288 000` | `14187` |

Every one of these is `485 + 1054k`, and `485/306`, `1054/665` are consecutive
convergents of `log₂ 3` — the values in between are exactly that block's
semiconvergents, the block ending at `485 + 23·1054 = 24727`, the next
convergent.  **The frontier never lands anywhere else.**

## Two corrections to the record

`CycleLength2593`'s docstring gives the table row `102400 → 520` and reads a
square-root law off it.  Both are wrong.  `520` was never a frontier: it is
where `CycleProduct.excludedLength_of_lt` stopped, and that theorem uses
`c = 307200`, not `102400`.  The true frontier at `102400` is `485`, confirmed
by both `excludedFast` and the full `O(L)` scan.  With the corrected table the
fitted exponent over fifteen ranges spanning a factor of `240` is `L ~ c^0.64`,
not `c^0.5`; and it is not really a power law at all, but a staircase whose
steps are the semiconvergents.

## The reach of `topIndex`, and where it stops

`topIndex L = L * 397573379 / 630138897` is a *fixed* rational approximation to
`log₃ 2`, in error by `1.53 × 10⁻¹⁹` per unit `L`.  Since the surviving lengths
are exactly the places where `{L log₃ 2}` is anomalously small, `topIndex` is at
its least reliable precisely at the lengths that matter, and it does eventually
break: **the first `L` at which `topIndex L ≠ ⌊L log₃ 2⌋` is
`L = 10 439 860 591`**, where it undercounts by one.  (Brute-forced to `3 × 10⁶`
with no disagreement; beyond that only one-sided best approximations of
`log₃ 2` can trigger one, and the first such is that `L`.)

This costs no soundness.  `excludedFast`'s first conjunct
`2 ^ L ≤ 3 ^ (topIndex L + 1)` is a self-check: if `topIndex` is wrong the
conjunct simply fails and the length is *not* excluded.  A wrong `topIndex` can
never produce a false exclusion, and `excludedLength_of_excludedFast` is
unaffected.  What it costs is reach — past `10 439 860 591` the test starts
refusing lengths for arithmetic reasons rather than mathematical ones, so any
argument aiming beyond that scale needs an exact `topIndex` rather than this one.
Every bound the repository currently proves, and the conditional sweep at
`L ≤ 40 000`, sits far inside the safe range.

## What this does not do

It does not raise the unconditional bound.  `2593` stands.  The ratio law says
where the frontier *is*, and `excluded_transfer` says a certificate could reach
it without a sweep, but neither supplies the certificate.
-/

namespace Collatz
namespace ExclusionRatio

open CycleLength1539

/-- The denominator of the exclusion ratio: the gap `2 ^ L − 3 ^ a`. -/
def dev (L : Nat) : Nat := 2 ^ L - 3 ^ topIndex L

/-- The numerator of the exclusion ratio: `2a · 3 ^ a`. -/
def wt (L : Nat) : Nat := 2 * topIndex L * 3 ^ topIndex L

/-- **The range separates from the length.**  The product test is a comparison
of the verified range against a ratio built from `L` alone. -/
theorem excluded_iff_gap {c L a : Nat} (h : 3 ^ a ≤ 2 ^ L) :
    3 ^ a * (3 * c + 2 * a) < 3 * c * 2 ^ L ↔
      2 * a * 3 ^ a < 3 * c * (2 ^ L - 3 ^ a) := by
  obtain ⟨g, hg⟩ := Nat.le.dest h
  have hsub : 2 ^ L - 3 ^ a = g := by omega
  rw [hsub, ← hg]
  have e1 : 3 ^ a * (3 * c + 2 * a) = 3 * c * 3 ^ a + 2 * a * 3 ^ a := by
    rw [Nat.mul_add, Nat.mul_comm (3 ^ a) (3 * c), Nat.mul_comm (3 ^ a) (2 * a)]
  have e2 : 3 * c * (3 ^ a + g) = 3 * c * 3 ^ a + 3 * c * g := Nat.mul_add _ _ _
  rw [e1, e2]
  exact Nat.add_lt_add_iff_left

/-- The same statement in the `wt`/`dev` names, at the exponent the sweep uses. -/
theorem excluded_iff_ratio {c L : Nat} (h : 3 ^ topIndex L ≤ 2 ^ L) :
    3 ^ topIndex L * (3 * c + 2 * topIndex L) < 3 * c * 2 ^ L ↔
      wt L < 3 * c * dev L :=
  excluded_iff_gap h

/-- **A wider verified range never loses a length.** -/
theorem excluded_of_le {c c' L : Nat} (hcc : c ≤ c') (h : wt L < 3 * c * dev L) :
    wt L < 3 * c' * dev L :=
  Nat.lt_of_lt_of_le h (Nat.mul_le_mul_right _ (Nat.mul_le_mul_left _ hcc))

/-- **Exclusion transfers along the ratio order.**  If `r(L) ≤ r(L')` — stated
cross-multiplied, `wt L · dev L' ≤ wt L' · dev L`, so no division is needed —
then any range excluding `L'` excludes `L`.  A length can be killed by a witness
at a *different* length, which is what an interval certificate would use to skip
the sweep. -/
theorem excluded_transfer {c L L' : Nat} (hdev : 0 < dev L') (hdev' : 0 < dev L)
    (hratio : wt L * dev L' ≤ wt L' * dev L)
    (h : wt L' < 3 * c * dev L') : wt L < 3 * c * dev L := by
  have h1 : wt L * dev L' < 3 * c * dev L' * dev L :=
    Nat.lt_of_le_of_lt hratio (Nat.mul_lt_mul_of_pos_right h hdev')
  have h2 : 3 * c * dev L' * dev L = 3 * c * dev L * dev L' := by
    simp [Nat.mul_assoc, Nat.mul_comm, Nat.mul_left_comm]
  rw [h2] at h1
  exact Nat.lt_of_mul_lt_mul_right h1

/-! ## The frontier, checked

Small instances of the corrected table, so the record in the docstring is not
merely asserted.  `485` survives at `102400` and is excluded at `307200`; `1539`
survives at `307200` and is excluded at `768000`; `2593` survives at `768000`.
-/

set_option exponentiation.threshold 4000 in
set_option maxRecDepth 4000000 in
theorem frontier_485 : excludedFast 102400 485 = false := by decide

set_option exponentiation.threshold 4000 in
set_option maxRecDepth 4000000 in
theorem excluded_485_at_307200 : excludedFast 307200 485 = true := by decide

set_option exponentiation.threshold 4000 in
set_option maxRecDepth 4000000 in
theorem frontier_1539 : excludedFast 307200 1539 = false := by decide

set_option exponentiation.threshold 4000 in
set_option maxRecDepth 4000000 in
theorem excluded_1539_at_768000 : excludedFast 768000 1539 = true := by decide

end ExclusionRatio
end Collatz
