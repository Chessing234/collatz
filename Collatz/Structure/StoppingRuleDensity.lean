import Collatz.Structure.StepDensityTransport

/-!
# Density transport through input-dependent times

A stopping rule need not have a global time bound. It suffices that, for every
requested density precision, its large-time tail is eventually that sparse.
This is a uniform tail condition, stronger than pointwise finiteness alone.
-/
namespace Collatz.StoppingRuleDensity
open NaturalDensity StepDensityTransport

/-- Large selected times occupy an arbitrarily small eventual proportion. -/
def DensityTight (time : Nat → Nat) : Prop :=
  ∀ q, 0<q → ∃ K N0, ∀ N, N0≤N → q*predicateCount (fun n => K<time n) N≤N

/-- A globally bounded rule preserves density one, even when its chosen time
varies arbitrarily with the input. -/
theorem density_one_bounded_rule {P : Nat → Prop} (hP : DensityOne P)
    (time : Nat → Nat) (K : Nat) (ht : ∀ n, time n≤K) :
    DensityOne (fun n => P (acceleratedOrbit (time n) n)) :=
  densityOne_mono (fun n hn => hn (time n) (ht n)) (density_one_allThrough hP K)

/-- The exceptional set for a selected time is covered by its time tail and
the exceptions in the corresponding fixed orbit window. -/
theorem selected_failure_count (P : Nat → Prop) (time : Nat → Nat) (K N : Nat) :
    predicateCount (fun n => ¬P (acceleratedOrbit (time n) n)) N ≤
      predicateCount (fun n => K<time n) N+
        predicateCount (fun n => ¬AllThrough P K n) N := by
  have hi := predicateCount_mono
    (P := fun n => ¬P (acceleratedOrbit (time n) n))
    (Q := fun n => ¬(¬K<time n ∧ AllThrough P K n)) (by
      intro n hf hn
      exact hf (hn.2 (time n) (by omega))) N
  have hc := complement_and_count (fun n => ¬K<time n) (AllThrough P K) N
  simpa only [Classical.not_not] using Nat.le_trans hi hc

/-- Density-tight input-dependent times preserve every density-one predicate. -/
theorem density_one_tight_rule {P : Nat → Prop} (hP : DensityOne P)
    (time : Nat → Nat) (ht : DensityTight time) :
    DensityOne (fun n => P (acceleratedOrbit (time n) n)) := by
  apply densityOne_of_complement_precision
  intro q hq
  obtain ⟨K, NT, htime⟩ := ht (2*q) (by omega)
  obtain ⟨NP, hwindow⟩ := complement_precision (density_one_allThrough hP K)
    (q := 2*q) (by omega)
  refine ⟨max NT NP, ?_⟩
  intro N hn
  have htc := htime N (by omega)
  have hwc := hwindow N (by omega)
  have hc := Nat.mul_le_mul_left (2*q) (selected_failure_count P time K N)
  simp only [Nat.mul_add, Nat.mul_assoc] at hc htc hwc
  omega

/-- A bounded rule is a special case of the uniform tail condition. -/
theorem tight_of_bounded (time : Nat → Nat) (K : Nat) (ht : ∀ n, time n≤K) :
    DensityTight time := by
  intro q _
  refine ⟨K, 0, ?_⟩
  intro N _
  have he : (fun n => K<time n)=(fun _ => False) := by
    funext n
    apply propext
    constructor
    · intro h; have := ht n; omega
    · exact False.elim
  rw [he, predicateCount_empty, Nat.mul_zero]
  exact Nat.zero_le _

end Collatz.StoppingRuleDensity
