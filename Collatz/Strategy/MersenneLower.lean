import Collatz.Strategy.RunLengthUnbounded
import Collatz.Strategy.Discrepancy
import Collatz.Strategy.RunLengthAny

/-!
# A lower bound for the `2^j − 1` family, sandwiching `MersenneDescent`

`Strategy.MersenneDescent` bounds the family's stopping time from **above**:
every `2 ≤ j ≤ 200` descends within `12j` accelerated steps.  That is a finite
check.  This file bounds it from **below**, for all `j` at once.

The mechanism is the mirror of the upper bound.  `climb_one` puts the orbit at
`3^j − 1` after `j` steps, and from there no single accelerated step can do
better than halve, so the orbit needs at least `log₂((3^j−1)/(2^j−1))` further
steps to get back under its start.  `Discrepancy.orbit_lower` supplies exactly
that: `3^q · n ≤ 2^i · T^i(n)`, hence `n ≤ 2^i · T^i(n)`.

Taking `j = 2m`, the gap is at least `2^m` because `8^m ≤ 9^m` — that is,
`2^(3m) ≤ 3^(2m)`.  So the family needs strictly more than `3m = 3j/2` steps.

## The sandwich

For even `j` with `2 ≤ j ≤ 200`:  `3j/2 < σ(2^j − 1) ≤ 12j`.

The lower half holds for every even `j`; only the upper half is a finite check.
Neither is tight — measurement puts `σ/j` between `1.6` and `11.2`, approaching
the random-walk rate `2·log(3/2)/log(4/3) ≈ 2.82` for large `j` — but the two
together pin the growth as linear in `j`, which is what the question in
`PROGRAM_STATUS` was really asking about this family.
-/

namespace Collatz
namespace MersenneLower

open MersenneDescent RunLengthUnbounded RunLengthAny

/-- No descent while the peak `3^j − 1` is still `2^t` above the start. -/
theorem mersenne_no_drop (j t : Nat) (ht : 2 ^ t * (2 ^ j - 1) ≤ 3 ^ j - 1) :
    ∀ s : Nat, s ≤ j + t → 2 ^ j - 1 ≤ acceleratedOrbit s (2 ^ j - 1) := by
  intro s hs
  rcases Nat.lt_or_ge s j with hlt | hge
  · -- still climbing
    rw [climb_mid j s (by omega)]
    have hmono : (2:Nat) ^ s ≤ 3 ^ s := Nat.pow_le_pow_left (by omega) _
    have hsplit : (2:Nat) ^ j = 2 ^ s * 2 ^ (j - s) := by
      rw [← Nat.pow_add]; congr 1; omega
    have : (2:Nat) ^ s * 2 ^ (j - s) ≤ 3 ^ s * 2 ^ (j - s) := Nat.mul_le_mul_right _ hmono
    omega
  · -- past the peak: each step at best halves
    obtain ⟨i, rfl⟩ : ∃ i, s = j + i := ⟨s - j, by omega⟩
    rw [show j + i = i + j from by omega, ← acceleratedOrbit_add, climb_one]
    have hlow := Discrepancy.orbit_lower (3 ^ j - 1) i
    have h3 : 1 ≤ (3:Nat) ^ oddCount (3 ^ j - 1) i := Nat.one_le_pow _ _ (by omega)
    have hpk : (3:Nat) ^ j - 1 ≤ 2 ^ i * acceleratedOrbit i (3 ^ j - 1) := by
      have := Nat.mul_le_mul_right (3 ^ j - 1) h3
      omega
    have hmono : (2:Nat) ^ i * (2 ^ j - 1) ≤ 2 ^ t * (2 ^ j - 1) :=
      Nat.mul_le_mul_right _ (Nat.pow_le_pow_right (by omega) (by omega))
    have hipos : (0:Nat) < 2 ^ i := Nat.pow_pos (by omega)
    have hchain : 2 ^ i * (2 ^ j - 1) ≤ 2 ^ i * acceleratedOrbit i (3 ^ j - 1) := by omega
    exact Nat.le_of_mul_le_mul_left hchain hipos

/-- **The `2^j − 1` family needs more than `3j/2` steps.**  At `j = 2m` the peak
`3^j − 1` sits at least `2^m` above the start, because `8^m ≤ 9^m`. -/
theorem mersenne_sigma_gt (m : Nat) :
    ∀ s : Nat, s ≤ 3 * m → 2 ^ (2 * m) - 1 ≤ acceleratedOrbit s (2 ^ (2 * m) - 1) := by
  have h89 : (8:Nat) ^ m ≤ 9 ^ m := Nat.pow_le_pow_left (by omega) _
  have h8 : (8:Nat) ^ m = 2 ^ (3 * m) := by
    rw [show (8:Nat) = 2 ^ 3 from by decide, ← Nat.pow_mul]
  have h9 : (9:Nat) ^ m = 3 ^ (2 * m) := by
    rw [show (9:Nat) = 3 ^ 2 from by decide, ← Nat.pow_mul]
  have hkey : (2:Nat) ^ (3 * m) ≤ 3 ^ (2 * m) := by omega
  have hsplit : (2:Nat) ^ (3 * m) = 2 ^ m * 2 ^ (2 * m) := by
    rw [← Nat.pow_add]; congr 1; omega
  have hmpos : 1 ≤ (2:Nat) ^ m := Nat.one_le_pow _ _ (by omega)
  have ht : 2 ^ m * (2 ^ (2 * m) - 1) ≤ 3 ^ (2 * m) - 1 := by
    rw [Nat.mul_sub, Nat.mul_one]
    omega
  intro s hs
  exact mersenne_no_drop (2 * m) m ht s (by omega)

/-! ## The same bound for every odd number

Nothing above used `E = 1`.  Replacing it by an arbitrary odd multiplier gives
the bound for the general odd `n` of even run length: the ascent is
`RunLengthAny.climb_gen_ge` instead of `climb_mid`, and the inequality
`8^m ≤ 9^m` carries through unchanged because it scales by `E`. -/

/-- No descent while the peak `3^r·E − 1` is still `2^t` above the start. -/
theorem run_no_drop (r t E : Nat) (hE : 0 < E)
    (ht : 2 ^ t * (2 ^ r * E - 1) ≤ 3 ^ r * E - 1) :
    ∀ s : Nat, s ≤ r + t → 2 ^ r * E - 1 ≤ acceleratedOrbit s (2 ^ r * E - 1) := by
  intro s hs
  rcases Nat.lt_or_ge s r with hlt | hge
  · exact climb_gen_ge r s E (by omega) hE
  · obtain ⟨i, rfl⟩ : ∃ i, s = r + i := ⟨s - r, by omega⟩
    have hpeak : acceleratedOrbit r (2 ^ r * E - 1) = 3 ^ r * E - 1 := by
      have := climb_gen r r E (by omega) hE
      simpa using this
    rw [show r + i = i + r from by omega, ← acceleratedOrbit_add, hpeak]
    have hlow := Discrepancy.orbit_lower (3 ^ r * E - 1) i
    have h3 : 1 ≤ (3:Nat) ^ oddCount (3 ^ r * E - 1) i := Nat.one_le_pow _ _ (by omega)
    have hpk : (3:Nat) ^ r * E - 1 ≤ 2 ^ i * acceleratedOrbit i (3 ^ r * E - 1) := by
      have := Nat.mul_le_mul_right (3 ^ r * E - 1) h3
      omega
    have hmono : (2:Nat) ^ i * (2 ^ r * E - 1) ≤ 2 ^ t * (2 ^ r * E - 1) :=
      Nat.mul_le_mul_right _ (Nat.pow_le_pow_right (by omega) (by omega))
    have hipos : (0:Nat) < 2 ^ i := Nat.pow_pos (by omega)
    exact Nat.le_of_mul_le_mul_left (by omega) hipos

/-- **Every odd number takes more than `3/2` times its run length to descend.**
For `n = 2^(2m)·E − 1` with `E` odd — the general odd `n` of run length `2m` —
no iterate falls below `n` within `3m` steps. -/
theorem sigma_gt_three_halves_run (m E : Nat) (hE : 0 < E) :
    ∀ s : Nat, s ≤ 3 * m → 2 ^ (2 * m) * E - 1 ≤ acceleratedOrbit s (2 ^ (2 * m) * E - 1) := by
  have h89 : (8:Nat) ^ m ≤ 9 ^ m := Nat.pow_le_pow_left (by omega) _
  have h8 : (8:Nat) ^ m = 2 ^ (3 * m) := by
    rw [show (8:Nat) = 2 ^ 3 from by decide, ← Nat.pow_mul]
  have h9 : (9:Nat) ^ m = 3 ^ (2 * m) := by
    rw [show (9:Nat) = 3 ^ 2 from by decide, ← Nat.pow_mul]
  have hkey : (2:Nat) ^ (3 * m) ≤ 3 ^ (2 * m) := by omega
  have hsplit : (2:Nat) ^ (3 * m) = 2 ^ m * 2 ^ (2 * m) := by
    rw [← Nat.pow_add]; congr 1; omega
  have hmpos : 1 ≤ (2:Nat) ^ m := Nat.one_le_pow _ _ (by omega)
  have hscale : 2 ^ m * (2 ^ (2 * m) * E) ≤ 3 ^ (2 * m) * E := by
    calc 2 ^ m * (2 ^ (2 * m) * E) = 2 ^ (3 * m) * E := by rw [hsplit, Nat.mul_assoc]
      _ ≤ 3 ^ (2 * m) * E := Nat.mul_le_mul_right _ hkey
  have hEpos : 0 < 3 ^ (2 * m) * E := Nat.mul_pos (Nat.pow_pos (by omega)) hE
  have ht : 2 ^ m * (2 ^ (2 * m) * E - 1) ≤ 3 ^ (2 * m) * E - 1 := by
    rw [Nat.mul_sub, Nat.mul_one]
    omega
  intro s hs
  exact run_no_drop (2 * m) m E hE ht s (by omega)

/-! ## Any run length, and a sharper constant

`sigma_gt_three_halves_run` needed an even run length and gave `3/2`.  Stating
the hypothesis in its natural form `2^(t+r) ≤ 3^r` removes both limitations: the
parity split is a two-line case analysis, and better constants are just better
rational approximations to `log₂ 3`.

The convergent `19/12` gives `σ > (19/12)·r = 1.58333·r`, against the true
ceiling `log₂ 3 = 1.58496·r` that no argument of this shape can pass — the run
lifts by exactly `(3/2)^r` and a step halves at best. -/

/-- The hypothesis in its natural form: the run lifts by `3^r/2^r`, so any `t`
with `2^(t+r) ≤ 3^r` is affordable. -/
theorem run_no_drop_pow (r t E : Nat) (hE : 0 < E) (h : 2 ^ (t + r) ≤ 3 ^ r) :
    ∀ s : Nat, s ≤ r + t → 2 ^ r * E - 1 ≤ acceleratedOrbit s (2 ^ r * E - 1) := by
  have hsplit : (2:Nat) ^ (t + r) = 2 ^ t * 2 ^ r := Nat.pow_add _ _ _
  have htpos : 1 ≤ (2:Nat) ^ t := Nat.one_le_pow _ _ (by omega)
  have hscale : 2 ^ t * (2 ^ r * E) ≤ 3 ^ r * E := by
    calc 2 ^ t * (2 ^ r * E) = 2 ^ (t + r) * E := by rw [hsplit, Nat.mul_assoc]
      _ ≤ 3 ^ r * E := Nat.mul_le_mul_right _ h
  have hEpos : 0 < 3 ^ r * E := Nat.mul_pos (Nat.pow_pos (by omega)) hE
  have ht : 2 ^ t * (2 ^ r * E - 1) ≤ 3 ^ r * E - 1 := by
    rw [Nat.mul_sub, Nat.mul_one]; omega
  exact run_no_drop r t E hE ht

/-- `2 ^ (r + r/2) ≤ 3 ^ r` for every `r`, by parity. -/
theorem pow_half_le (r : Nat) : 2 ^ (r + r / 2) ≤ 3 ^ r := by
  obtain ⟨m, hm⟩ : ∃ m, r = 2 * m ∨ r = 2 * m + 1 := ⟨r / 2, by omega⟩
  rcases hm with rfl | rfl
  · 
    have h89 : (8:Nat) ^ m ≤ 9 ^ m := Nat.pow_le_pow_left (by omega) _
    have h8 : (8:Nat) ^ m = 2 ^ (3 * m) := by
      rw [show (8:Nat) = 2 ^ 3 from by decide, ← Nat.pow_mul]
    have h9 : (9:Nat) ^ m = 3 ^ (2 * m) := by
      rw [show (9:Nat) = 3 ^ 2 from by decide, ← Nat.pow_mul]
    have he1 : 2 * m + (2 * m) / 2 = 3 * m := by omega
    rw [he1]; omega
  · have h89 : (8:Nat) ^ m ≤ 9 ^ m := Nat.pow_le_pow_left (by omega) _
    have h8 : (8:Nat) ^ m = 2 ^ (3 * m) := by
      rw [show (8:Nat) = 2 ^ 3 from by decide, ← Nat.pow_mul]
    have h9 : (9:Nat) ^ m = 3 ^ (2 * m) := by
      rw [show (9:Nat) = 3 ^ 2 from by decide, ← Nat.pow_mul]
    have he1 : 2 * m + 1 + (2 * m + 1) / 2 = 3 * m + 1 := by omega
    have hA : (2:Nat) ^ (3 * m + 1) = 2 ^ (3 * m) * 2 := Nat.pow_succ _ _
    have hB : (3:Nat) ^ (2 * m + 1) = 3 ^ (2 * m) * 3 := Nat.pow_succ _ _
    rw [he1]; omega

/-- **Every odd number takes more than `r + r/2` steps to descend**, where `r` is
its run length.  No parity assumption. -/
theorem sigma_gt_run_half (r E : Nat) (hE : 0 < E) :
    ∀ s : Nat, s ≤ r + r / 2 → 2 ^ r * E - 1 ≤ acceleratedOrbit s (2 ^ r * E - 1) := by
  intro s hs
  exact run_no_drop_pow r (r / 2) E hE (by rw [Nat.add_comm]; exact pow_half_le r) s (by omega)

/-- Sharper, at run lengths divisible by `12`: `2^19 ≤ 3^12` is the convergent
`19/12` of `log₂ 3`, giving `σ > (19/12)·r` against `(3/2)·r`. -/
theorem sigma_gt_nineteen_twelfths (k E : Nat) (hE : 0 < E) :
    ∀ s : Nat, s ≤ 19 * k →
      2 ^ (12 * k) * E - 1 ≤ acceleratedOrbit s (2 ^ (12 * k) * E - 1) := by
  have hconv : (2:Nat) ^ (19 * k) ≤ 3 ^ (12 * k) := by
    have h : ((2:Nat) ^ 19) ^ k ≤ ((3:Nat) ^ 12) ^ k := Nat.pow_le_pow_left (by decide) _
    rw [← Nat.pow_mul, ← Nat.pow_mul] at h
    exact h
  intro s hs
  refine run_no_drop_pow (12 * k) (7 * k) E hE ?_ s (by omega)
  have : 7 * k + 12 * k = 19 * k := by omega
  rw [this]; exact hconv

/-! ### The convergents of `log₂ 3`, in order

The bound needs `t/r ≤ log₂ 3 − 1`, so every rational approximation to `log₂ 3`
**from below** gives an instance, and the convergents alternate:

| convergent | `2^p ≤ 3^q` | ratio to `log₂ 3` |
|---|---|---|
| `19/12` | yes | `0.998972` |
| `65/41` | no | — |
| `84/53` | yes | `0.999964` |
| `485/306` | no | — |
| `1054/665` | yes | `0.99999994` |

`1054/665` comes within `6·10⁻⁸` of the ceiling.  Its denominator `665` is the
same one that spaces the risers of the cycle-frontier ladder
(`306 + 665k`, `Strategy.PreCertified`) — the two arguments are unrelated but
both are governed by the continued fraction of `log₂ 3`. -/

theorem sigma_gt_84_53 (k E : Nat) (hE : 0 < E) :
    ∀ s : Nat, s ≤ 84 * k →
      2 ^ (53 * k) * E - 1 ≤ acceleratedOrbit s (2 ^ (53 * k) * E - 1) := by
  have hconv : (2:Nat) ^ (84 * k) ≤ 3 ^ (53 * k) := by
    have h : ((2:Nat) ^ 84) ^ k ≤ ((3:Nat) ^ 53) ^ k := Nat.pow_le_pow_left (by decide) _
    rw [← Nat.pow_mul, ← Nat.pow_mul] at h
    exact h
  intro s hs
  refine run_no_drop_pow (53 * k) (31 * k) E hE ?_ s (by omega)
  have h : 31 * k + 53 * k = 84 * k := by omega
  rw [h]; exact hconv

set_option maxRecDepth 10000 in
theorem sigma_gt_1054_665 (k E : Nat) (hE : 0 < E) :
    ∀ s : Nat, s ≤ 1054 * k →
      2 ^ (665 * k) * E - 1 ≤ acceleratedOrbit s (2 ^ (665 * k) * E - 1) := by
  have hconv : (2:Nat) ^ (1054 * k) ≤ 3 ^ (665 * k) := by
    have h : ((2:Nat) ^ 1054) ^ k ≤ ((3:Nat) ^ 665) ^ k := Nat.pow_le_pow_left (by decide) _
    rw [← Nat.pow_mul, ← Nat.pow_mul] at h
    exact h
  intro s hs
  refine run_no_drop_pow (665 * k) (389 * k) E hE ?_ s (by omega)
  have h : 389 * k + 665 * k = 1054 * k := by omega
  rw [h]; exact hconv

end MersenneLower
end Collatz
