import Collatz.Structure.PowerTailCounting

/-!
# The 4/5 specialization of Korec's density theorem

For the actual accelerated Collatz map, almost every starting value has an
iterate m satisfying m^5<n^4. This proves one rational specialization of the
published theorem, not the full range c>log_4(3), and not universal convergence.
The proof uses rationally weighted parity moments, an affine orbit bound, and
a scale chosen separately for each counting cutoff.
-/
namespace Collatz.Papers.Korec1994
open NaturalDensity PowerTailCounting

/-- A quantitative all-cutoff bound on failures of the 4/5 power target.
The explicit threshold is coarse and not intended for numerical use. -/
theorem four_fifths_failure_precision (q : Nat) (hq : 0<q) :
    ∃ N0, ∀ N, N0≤N → q*predicateCount (fun n => ¬OrbitBelowPower 4 5 n) N≤N := by
  let D := 2*q
  let L := D*2^125
  let S := max ((4*q)*125^125) ((L+1)^5*3^315)
  refine ⟨D*2^(125*S), ?_⟩
  intro N hN
  obtain ⟨s, hs, hprefix, hscale⟩ :=
    PowerScaleSelection.scale_exists D S N (by dsimp [D]; omega) hN
  have htail : 4*q*ParityMoments.tailCount (125*s) (63*s)≤2^(125*s) := by
    exact Nat.le_of_lt (PowerTailPrecision.tail_precision (4*q) s
      (Nat.le_trans (Nat.le_max_left _ _) hs))
  have hcount := power_failure_count_upper L s N
    (Nat.le_trans (Nat.le_max_right _ _) hs) (Nat.le_of_lt hscale)
  exact prefix_and_period_precision q (2^(125*s)) N
    (ParityMoments.tailCount (125*s) (63*s))
    (predicateCount (fun n => ¬OrbitBelowPower 4 5 n) N) hq hprefix htail hcount

/-- The actual accelerated orbit goes below n^(4/5) for a natural-density-one
set of starts. This is a formalized classical result, not a claim of novelty. -/
theorem four_fifths_density_one : DensityOne (OrbitBelowPower 4 5) :=
  densityOne_of_complement_precision four_fifths_failure_precision

/-- Larger numerators with the same denominator inherit the checked bound. -/
theorem density_one_fifths {p : Nat} (hp : 4≤p) : DensityOne (OrbitBelowPower p 5) := by
  apply densityOne_mono (P := OrbitBelowPower 4 5) _ four_fifths_density_one
  intro n hn
  obtain ⟨k, hk⟩ := hn
  by_cases hz : n=0
  · subst n
    simp only [Nat.zero_pow (by decide : 0<4)] at hk
    omega
  · exact orbitBelowPower_mono (by omega) hp ⟨k, hk⟩

/-- Increasing the rational exponent from 4/5 weakens the strict power target.
This comparison uses integer powers only. -/
theorem orbit_power_of_four_fifths {p q n : Nat} (hq : 0<q) (hr : 4*q≤5*p)
    (h : OrbitBelowPower 4 5 n) : OrbitBelowPower p q n := by
  obtain ⟨k, hk⟩ := h
  have hn : 0<n := by
    by_cases hz : n=0
    · subst n
      simp only [Nat.zero_pow (by decide : 0<4)] at hk
      omega
    · omega
  have hp := Nat.pow_lt_pow_left hk (by omega : q≠0)
  have hm := Nat.pow_le_pow_right (by omega : 1≤n) hr
  have ht : (acceleratedOrbit k n)^(5*q)<n^(5*p) :=
    Nat.lt_of_lt_of_le (by simpa only [← Nat.pow_mul] using hp) hm
  refine ⟨k, (Nat.pow_lt_pow_iff_left (by decide : 5≠0)).mp ?_⟩
  simpa only [← Nat.pow_mul, Nat.mul_comm] using ht

/-- Every positive rational exponent at least 4/5 has a proved density-one
power target. The interval between log_4(3) and 4/5 is not covered here. -/
theorem density_one_exponent_ge_four_fifths {p q : Nat} (hq : 0<q) (hr : 4*q≤5*p) :
    DensityOne (OrbitBelowPower p q) :=
  densityOne_mono (fun _ h => orbit_power_of_four_fifths hq hr h) four_fifths_density_one

end Collatz.Papers.Korec1994
