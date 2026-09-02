import Collatz.Strategy.DriftSurvivors

/-!
# Asset (a), requantified

`CLOSURE.md` lists the verified range as the only `d = 1`-specific asset with a
number attached, and flags that number as stale:

> exactly `L = 183` of `6809` (2.7 %) — *stated at the range and frontier of its
> round; both have since moved, so the count needs recomputing before reuse*

The quantity is the **first empty level of the sieve tower**: the least `K` such
that no `x` below the verified range survives `K` steps without falling below
itself.  Equivalently `K = 1 + max σ(x)` over the range.  At `1 086 464` that
was `184`, witnessed by `σ(1 027 431) = 183` — the flagged entry says `183`
because it counts the largest *non-dropping* level, one less.

## Recomputed

At the current range `3 998 720` the maximum is `σ(1 126 015) = 224`, so the
first empty level is `225` and the largest non-dropping level is `224`.  Against
the current frontier `14187`:

| round | range | largest non-dropping `L` | frontier | share |
|---|---|---|---|---|
| then | `1 086 464` | `183` | `6809` | `2.69 %` |
| now | `3 998 720` | `224` | `14187` | `1.58 %` |

**The asset is worth relatively less than it was**, despite the range having
grown by a factor of `3.7`.  The reason is structural and already proved here:
the frontier advances `1054` per staircase rung
(`RouteCap`, the `306 + 665k` staircase) while `max σ` over a range grows like
`log` of it, so the numerator crawls and the denominator climbs.  Extending the
verified range dilutes asset (a) rather than strengthening it.

That is worth having explicitly, because "extend the range" is the reflex move on
the cycle side, and it makes the one `d = 1`-specific asset *less* of the total
each time.

## The two theorems

`drops_within_224` proves the bound — every `2 ≤ n < 3 998 720` falls below
itself within `224` accelerated steps — reusing the sweep of
`Search.VerifiedRung14187` exactly as `DriftSurvivors` does, with no new kernel
computation over the range.  `sigma_1126015_ge` proves it **sharp**: `1 126 015`
does not fall below itself before step `224`.
-/

namespace Collatz
namespace AssetA

open DriftSurvivors

/-- **Every `n` below the verified range drops within `224` steps.**  Below
`8192` this is the `C = 17` chunks (`17 · ⌊log₂ n⌋ ≤ 204`); above, it is the
level-`10` sieve plus the fuel-`224` block sweep. -/
theorem drops_within_224 {n : Nat} (h2 : 2 ≤ n) (hN : n < 3998720) :
    ∃ k : Nat, k ≤ 224 ∧ acceleratedOrbit k n < n := by
  rcases Nat.lt_or_ge n 8192 with hs | hb
  · obtain ⟨k, hk, hlt⟩ := logBlockDescentWithin_17_below_100000 h2 (by omega)
    have hpow : (2:Nat) ^ 13 = 8192 := by decide
    have hlog : Nat.log2 n < 13 := (Nat.log2_lt (by omega)).mpr (by omega)
    exact ⟨k, by omega, hlt⟩
  · have hp : (2:Nat) ^ 10 = 1024 := by decide
    by_cases hsv : Congruence.survives 10 (n % 2 ^ 10) = true
    · have hmem := Search.mem_survivors_of_survives hsv
      have hlt : n / 2 ^ 10 < 3905 := by rw [hp]; omega
      have hdec : 2 ^ 10 * (n / 2 ^ 10) + n % 2 ^ 10 = n := Nat.div_add_mod n (2 ^ 10)
      have hcheck := Search.drops_all_3905 hlt hmem
      rw [hdec] at hcheck
      exact exists_le_of_dropsWithin hcheck
    · obtain ⟨k, hk, hlt'⟩ :=
        exists_le_drop_of_not_survives (K := 10) (by omega) (Nat.le_refl 10) hsv
      exact ⟨k, by omega, hlt'⟩

set_option maxRecDepth 100000 in
/-- **The bound is sharp.**  `1 126 015` does not fall below itself at any step
before `224`, so `224` is attained and the first empty level is exactly `225`. -/
theorem sigma_1126015_ge : ∀ j : Nat, j ≤ 223 → 1126015 ≤ acceleratedOrbit j 1126015 := by
  decide

end AssetA
end Collatz
