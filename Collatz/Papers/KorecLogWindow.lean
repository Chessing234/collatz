import Collatz.Strategy.PowerStoppingTimeBarrier

/-!
# A logarithmic search window for Korec's power target

The certificate proof supplies a witness by floor(log2 n), at density one,
throughout the recorded rational-exponent range. This produces a finite
Boolean search whose success set has natural density one. It is not a
convergence algorithm and need not succeed on every input.
-/
namespace Collatz.Papers.Korec1994
open NaturalDensity PowerDensityParameters

/-- A power target reached within the input's binary-logarithmic time window. -/
def OrbitBelowPowerByLog (p q n : Nat) : Prop :=
  ∃ k, k≤n.log2 ∧ (acceleratedOrbit k n)^q<n^p

/-- The scale-selected certificate witness lies inside the logarithmic window. -/
theorem certified_log_window {p q n L s : Nat} (c : Certificate p q)
    (hs : (L+1)^q*3^(q*c.threshold)≤s)
    (hnlo : 2^(c.block*s)≤n) (hnhi : n≤L*2^(c.block*s))
    (ha : oddCount n (c.block*s)≤c.threshold*s) : OrbitBelowPowerByLog p q n := by
  have hn : 0<n := Nat.lt_of_lt_of_le (Nat.pow_pos (by decide)) hnlo
  exact ⟨c.block*s, (Nat.le_log2 (by omega : n≠0)).mpr hnlo,
    certified_endpoint_power c hs hnlo hnhi ha⟩

/-- The full recorded rational range has power hits within floor(log2 n)
for a natural-density-one set of starting values. -/
theorem logarithmic_power_density (p q : Nat) (_hq : 0<q) (hgap : 3^q<4^p) :
    DensityOne (OrbitBelowPowerByLog p q) := by
  obtain ⟨c⟩ := certificate_exists p q hgap
  apply density_one_of_scale_property c (OrbitBelowPowerByLog p q)
  intro L
  exact ⟨(L+1)^q*3^(q*c.threshold), fun _ hs _ hlo hhi ha =>
    certified_log_window c hs hlo hhi ha⟩

/-- Scan one orbit segment, retaining the current state between tests. -/
def powerScan (p q target : Nat) : Nat → Nat → Bool
  | 0, current => decide (current^q<target^p)
  | fuel+1, current => decide (current^q<target^p) ||
      powerScan p q target fuel (acceleratedStep current)

/-- The scan checks exactly the initial state and all iterates through its fuel. -/
theorem powerScan_iff (p q target fuel current : Nat) :
    powerScan p q target fuel current=true ↔
      ∃ k, k≤fuel ∧ (acceleratedOrbit k current)^q<target^p := by
  induction fuel generalizing current with
  | zero =>
    simp only [powerScan, decide_eq_true_eq]
    constructor
    · intro h; exact ⟨0, Nat.le_refl _, h⟩
    · rintro ⟨k, hk, h⟩
      have he : k=0 := by omega
      subst k
      exact h
  | succ fuel ih =>
    simp only [powerScan, Bool.or_eq_true, decide_eq_true_eq, ih]
    constructor
    · intro h
      rcases h with h | ⟨k, hk, hh⟩
      · exact ⟨0, by omega, h⟩
      · exact ⟨k+1, by omega, hh⟩
    · rintro ⟨k, hk, hh⟩
      cases k with
      | zero => exact Or.inl hh
      | succ k => exact Or.inr ⟨k, by omega, hh⟩

/-- An executable search with at most floor(log2 n) accelerated transitions. -/
def logPowerCheck (p q n : Nat) : Bool := powerScan p q n n.log2 n

/-- Exact semantics of the finite search, including its endpoint. -/
theorem logPowerCheck_iff (p q n : Nat) :
    logPowerCheck p q n=true ↔ OrbitBelowPowerByLog p q n :=
  powerScan_iff p q n n.log2 n

/-- The executable test succeeds on a density-one set in Korec's range. -/
theorem logPowerCheck_density_one (p q : Nat) (hq : 0<q) (hgap : 3^q<4^p) :
    DensityOne (fun n => logPowerCheck p q n=true) :=
  densityOne_mono (fun n h => (logPowerCheck_iff p q n).mpr h)
    (logarithmic_power_density p q hq hgap)

/-- The successful time can be bounded from both sides entirely with integers. -/
theorem density_one_power_time_window {p q : Nat} (hpq : p<q) (hgap : 3^q<4^p) :
    DensityOne (fun n => ∃ k, n^(q-p)<2^(k*q) ∧ k≤n.log2 ∧
      (acceleratedOrbit k n)^q<n^p) := by
  apply densityOne_mono (P := OrbitBelowPowerByLog p q) _
    (logarithmic_power_density p q (by omega) hgap)
  rintro n ⟨k, hk, hh⟩
  exact ⟨k, PowerStoppingTimeBarrier.power_gap_bound_of_hit hpq hh, hk, hh⟩

/-- Small examples check inclusion of the last search index and failure output. -/
theorem log_search_two : logPowerCheck 4 5 2=true := by decide

theorem log_search_one : logPowerCheck 4 5 1=false := by decide

/-- Failure of the bounded search does not imply failure at later times. -/
theorem log_failure_can_hit_later : logPowerCheck 4 5 3=false ∧
    (acceleratedOrbit 4 3)^5<3^4 := by decide

end Collatz.Papers.Korec1994
