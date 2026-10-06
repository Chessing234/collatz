import Collatz.Papers.Korec1994
import Collatz.Structure.CofiniteNaturalDensity

/-!
# Pointwise power bounds versus density assertions

For one fixed start n>1, access to arbitrarily small reciprocal-power targets
is equivalent to reaching 1. This has stronger quantifiers than an almost-all
statement at each exponent. No density-one theorem is used as a universal claim.
-/
namespace Collatz.Papers.Korec1994
open NaturalDensity

/-- Reaching 1 supplies every strict positive-power target above it. -/
theorem below_power_of_reaches_one {n p q : Nat} (hn : 1<n) (hp : 0<p)
    (hr : ∃ k, acceleratedOrbit k n=1) : OrbitBelowPower p q n := by
  obtain ⟨k, hk⟩ := hr
  refine ⟨k, ?_⟩
  rw [hk, Nat.one_pow]
  have hl : n≤n^p := by
    simpa using Nat.pow_le_pow_right (by omega : 1≤n) hp
  omega

/-- For each fixed start above 1, all reciprocal-power bounds force convergence. -/
theorem reaches_one_iff_all_reciprocal_powers {n : Nat} (hn : 1<n) :
    (∃ k, acceleratedOrbit k n=1) ↔ ∀ q : Nat, 0<q → OrbitBelowPower 1 q n := by
  constructor
  · intro h q _
    exact below_power_of_reaches_one hn (by decide) h
  · intro h
    obtain ⟨k, hk⟩ := h n (by omega)
    refine ⟨k, ?_⟩
    have hpos := acceleratedOrbit_positive (by omega : 0<n) k
    by_cases he : acceleratedOrbit k n=1
    · exact he
    · have htwo : 2≤acceleratedOrbit k n := by omega
      have hpow := Nat.pow_le_pow_left htwo n
      have hlarge : n < 2^n := Nat.lt_two_pow_self
      simp only [Nat.pow_one] at hk
      omega

/-- Under universal convergence, every positive rational power target holds
outside the two excluded starts and therefore has natural density one. -/
theorem density_below_power_of_universal_convergence
    (hc : ∀ n : Nat, 0<n → ∃ k, acceleratedOrbit k n=1)
    {p q : Nat} (hp : 0<p) : DensityOne (OrbitBelowPower p q) := by
  apply densityOne_of_eventually (B := 2)
  intro n hn
  exact below_power_of_reaches_one (by omega) hp (hc n (by omega))

/-- The repaired Korec statement follows from universal convergence, but that
hypothesis is not established by this implication. -/
theorem rational_statement_of_universal_convergence
    (hc : ∀ n : Nat, 0<n → ∃ k, acceleratedOrbit k n=1) :
    rationalExponentStatement := by
  intro p q _ hgap
  have hp : 0<p := by
    by_cases hz : p=0
    · rw [hz, Nat.pow_zero] at hgap
      have := Nat.one_le_pow q 3 (by decide)
      omega
    · omega
  exact density_below_power_of_universal_convergence hc hp

end Collatz.Papers.Korec1994
