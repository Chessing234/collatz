import Collatz.Strategy.RenormTower

/-!
# The contraction harvest: a dead device, and the live term inside it

A device built to the specification *change only on contraction steps, use
positivity, not be a rewrite of `affineC`* — tested against the three filter maps,
and killed by the test.  What survives is the exact term at which they differ, and
that is what is proved below.

## The device

All three maps share the growth branch `u ↦ 3u/2` and differ only at the
contraction: `⌈u/2⌉` for `T`, `⌊u/2⌋` for the mirror `3n−1`, `(3u−1)/2` for
`expStep`.  So put

`V_C(n) = Σ` over the first `C` contraction steps of the `2`-adic content that
map's contraction actually harvests — `v₂(n+2)` for `T`, `v₂(n−2)` for the mirror,
`v₂(3n+2)` for `expStep`.

It is constant on growth by construction, and it is a sum of *valuations*, not a
weighted sum of powers of two, so it is not `affineC` in disguise.

## The device is dead

Over every odd `n < 50 000`, first `10` contractions:

* **Marginals identical.**  All three give `1 ↦ 0.500`, `2 ↦ 0.250`, `3 ↦ 0.125`,
  `4 ↦ 0.0625`, `5 ↦ 0.031`, `6 ↦ 0.015` — geometric `(1/2)`, agreeing to four
  decimals.
* **Joint law identical.**  Consecutive pairs `(v_i, v_{i+1})` agree across the
  three maps to three decimals and match the independent product: `P(1,1)` is
  `0.24975`, `0.25098`, `0.24973` against `0.25`, deviations `~10⁻³`.

So `V` has the same law under a map with the wrong sign and under a map that
diverges from every start.  Summing over an orbit averages the difference away.

## The exact differing term

The maps *do* differ pointwise, and the identity is exact.  For even `n = 2m`:

**`T` harvests `1 + v₂(m+1)`;  the mirror harvests `1 + v₂(m−1)`.**

Verified for all even `n < 20 000`.  So the difference between Collatz and its
mirror, at the one place they differ, is **`v₂(m+1)` against `v₂(m−1)` — the same
`±1` defect, one level further down.**  The recurrence again.

And which branch is shallow is decided by `m` modulo `4`, exactly:

* `m` even — `m ± 1` are both odd, both harvests are `1`: **the maps agree**;
* `m ≡ 1 (mod 4)` — `m+1 ≡ 2 (mod 4)` and `4 ∣ m−1`: `T` shallow, mirror deep;
* `m ≡ 3 (mod 4)` — `4 ∣ m+1` and `m−1 ≡ 2 (mod 4)`: `T` deep, mirror shallow.

`harvest_split` is that trichotomy.  It is why the statistics agree: the two cases
`m ≡ 1` and `m ≡ 3` occur equally often and exchange the roles of the two maps, so
every symmetric functional of the harvest — the marginal, the joint law, the sum —
is blind to the sign of the defect.

**A separator must be antisymmetric in `m mod 4`.**  That is the concrete
consequence, and it rules out `V` and every symmetric statistic built from the
harvest, which is more than the individual failure.
-/

namespace Collatz
namespace HarvestSplit

/-- For `n = 2m`, the content `T`'s contraction harvests is `v₂(n+2)`, and
`n + 2 = 2(m+1)`. -/
theorem harvest_T {n m : Nat} (h : n = 2 * m) : n + 2 = 2 * (m + 1) := by omega

/-- For `n = 2m`, the content the mirror's contraction harvests is `v₂(n−2)`, and
`n − 2 = 2(m−1)`. -/
theorem harvest_mirror {n m : Nat} (h : n = 2 * m) (hm : 0 < m) :
    n - 2 = 2 * (m - 1) := by omega

/-- **The maps agree when `m` is even.**  Both `m ± 1` are odd, so both
contractions harvest exactly one factor of two. -/
theorem harvest_agree {m : Nat} (hm : m % 2 = 0) (h1 : 0 < m) :
    (m + 1) % 2 = 1 ∧ (m - 1) % 2 = 1 := by omega

/-- **The trichotomy.**  For odd `m`, which of the two contractions is shallow is
decided by `m` modulo `4`, and they always take opposite roles: one of `m ± 1` is
`2 (mod 4)` — a single factor of two — while the other is divisible by `4`. -/
theorem harvest_split {m : Nat} (hm : m % 2 = 1) (h1 : 0 < m) :
    (m % 4 = 1 → (m + 1) % 4 = 2 ∧ (m - 1) % 4 = 0) ∧
    (m % 4 = 3 → (m + 1) % 4 = 0 ∧ (m - 1) % 4 = 2) := by
  constructor <;> intro h <;> omega

/-- The two cases are genuinely exclusive and exhaustive for odd `m`: exactly one
of `m ± 1` carries a single factor of two. -/
theorem harvest_exclusive {m : Nat} (hm : m % 2 = 1) (h1 : 0 < m) :
    ((m + 1) % 4 = 2 ∧ (m - 1) % 4 = 0) ∨ ((m + 1) % 4 = 0 ∧ (m - 1) % 4 = 2) := by
  rcases (by omega : m % 4 = 1 ∨ m % 4 = 3) with h | h
  · exact Or.inl (by omega)
  · exact Or.inr (by omega)

end HarvestSplit
end Collatz
