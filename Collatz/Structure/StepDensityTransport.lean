import Collatz.Accelerated
import Collatz.Structure.DensityLocalCounting

/-!
# Transport of density one through fixed Collatz iterates

The accelerated map has two affine branches. Their finite counting bounds
show that pulling a density-one predicate back through any fixed number of
steps preserves natural density one. No uniform conclusion for an unbounded,
input-dependent stopping time is asserted.
-/
namespace Collatz.StepDensityTransport
open PeriodicCounting NaturalDensity

/-- Separate even and odd positions in a finite indicator count. -/
theorem count_even_odd (P : Nat → Bool) (N : Nat) :
    countBelow P (2*N)=countBelow (fun n => P (2*n)) N+
      countBelow (fun n => P (2*n+1)) N := by
  induction N with
  | zero => rfl
  | succ N ih =>
    have he : 2*(N+1)=2*N+1+1 := by omega
    rw [he, count_succ, count_succ, ih, count_succ, count_succ]
    omega

/-- Selecting one position in each stride block cannot increase the count. -/
theorem count_stride_le (P : Nat → Bool) (d r N : Nat) (hr : r<d) :
    countBelow (fun n => P (d*n+r)) N≤countBelow P (d*N) := by
  induction N with
  | zero => exact Nat.le_refl _
  | succ N ih =>
    rw [count_succ, Nat.mul_succ, count_add_shift]
    have ht : (if P (d*N+r) then 1 else 0)≤countBelow (fun n => P (d*N+n)) d := by
      rw [count_eq_countRange]
      exact Sum.le_sumRange (fun n => if P (d*N+n) then 1 else 0) hr
    omega

/-- The two affine branches of the accelerated map. -/
theorem step_even (n : Nat) : acceleratedStep (2*n)=n := by
  simp [acceleratedStep]

theorem step_odd (n : Nat) : acceleratedStep (2*n+1)=3*n+2 := by
  unfold acceleratedStep
  rw [if_neg (by omega : ¬(2*n+1)%2=0)]
  omega

/-- Exact branch decomposition of the pullback count on an even interval. -/
theorem step_count_even_interval (P : Nat → Bool) (N : Nat) :
    countBelow (fun n => P (acceleratedStep n)) (2*N)=
      countBelow P N+countBelow (fun n => P (3*n+2)) N := by
  simpa only [step_even, step_odd] using count_even_odd (fun n => P (acceleratedStep n)) N

/-- A uniform finite bound: preimages below N count at most twice as many
as target members below 3N. The constants are intentionally coarse. -/
theorem step_count_upper (P : Nat → Bool) (N : Nat) :
    countBelow (fun n => P (acceleratedStep n)) N≤2*countBelow P (3*N) := by
  have hpad := count_mono (fun n => P (acceleratedStep n)) (by omega : N≤2*N)
  rw [step_count_even_interval] at hpad
  have hs := count_stride_le P 3 2 N (by decide)
  have hm := count_mono P (by omega : N≤3*N)
  omega

/-- The same finite bound for arbitrary predicates and classical counting. -/
theorem step_predicate_count_upper (P : Nat → Prop) (N : Nat) :
    predicateCount (fun n => P (acceleratedStep n)) N≤2*predicateCount P (3*N) := by
  classical
  exact step_count_upper (fun n => decide (P n)) N

/-- Explicit count inflation after k fixed iterates. The factor and target
interval both grow with k, so this estimate is not uniform in time. -/
theorem orbit_predicate_count_upper (P : Nat → Prop) (k N : Nat) :
    predicateCount (fun n => P (acceleratedOrbit k n)) N≤
      2^k*predicateCount P (3^k*N) := by
  induction k generalizing N with
  | zero => simp only [acceleratedOrbit_zero, Nat.pow_zero, Nat.one_mul]; exact Nat.le_refl _
  | succ k ih =>
    have hs := step_predicate_count_upper (fun n => P (acceleratedOrbit k n)) N
    have ht := Nat.mul_le_mul_left 2 (ih (3*N))
    have hc := Nat.le_trans hs ht
    simpa only [acceleratedOrbit_succ, Nat.pow_succ, Nat.mul_assoc,
      Nat.mul_comm, Nat.mul_left_comm] using hc

/-- Natural density one is preserved by one accelerated preimage. -/
theorem density_one_step {P : Nat → Prop} (hP : DensityOne P) :
    DensityOne (fun n => P (acceleratedStep n)) := by
  apply densityOne_of_complement_precision
  intro q hq
  obtain ⟨N0, hN⟩ := complement_precision hP (q := 6*q) (by omega)
  refine ⟨N0, ?_⟩
  intro N hn
  have ht := hN (3*N) (by omega)
  have hc := step_predicate_count_upper (fun n => ¬P n) N
  have hm := Nat.mul_le_mul_left (3*q) hc
  simp only [Nat.mul_assoc] at ht hm
  rw [Nat.mul_left_comm q 2] at hm
  omega

/-- Every fixed iterate preserves natural density one under preimage. -/
theorem density_one_orbit {P : Nat → Prop} (hP : DensityOne P) (k : Nat) :
    DensityOne (fun n => P (acceleratedOrbit k n)) := by
  induction k with
  | zero => exact hP
  | succ k ih => exact density_one_step ih

/-- Failure of a conjunction is counted by at most the two failure counts. -/
theorem complement_and_count (P Q : Nat → Prop) (N : Nat) :
    predicateCount (fun n => ¬(P n ∧ Q n)) N ≤
      predicateCount (fun n => ¬P n) N+predicateCount (fun n => ¬Q n) N := by
  classical
  unfold predicateCount
  induction N with
  | zero => exact Nat.le_refl _
  | succ N ih =>
    rw [count_succ, count_succ, count_succ]
    by_cases hp : P N <;> by_cases hq : Q N <;> simp [hp, hq] at * <;> omega

/-- Finite intersection, expressed here for two density-one predicates. -/
theorem density_one_and {P Q : Nat → Prop} (hP : DensityOne P) (hQ : DensityOne Q) :
    DensityOne (fun n => P n ∧ Q n) := by
  apply densityOne_of_complement_precision
  intro q hq
  obtain ⟨NP, hp⟩ := complement_precision hP (q := 2*q) (by omega)
  obtain ⟨NQ, hq'⟩ := complement_precision hQ (q := 2*q) (by omega)
  refine ⟨max NP NQ, ?_⟩
  intro N hn
  have hpc := hp N (by omega)
  have hqc := hq' N (by omega)
  have hc := Nat.mul_le_mul_left (2*q) (complement_and_count P Q N)
  simp only [Nat.mul_add, Nat.mul_assoc] at hc hpc hqc
  omega

/-- A predicate holds along every state in the first K steps, including time zero. -/
def AllThrough (P : Nat → Prop) (K n : Nat) : Prop :=
  ∀ k, k≤K → P (acceleratedOrbit k n)

/-- Every fixed finite orbit window preserves a density-one property. -/
theorem density_one_allThrough {P : Nat → Prop} (hP : DensityOne P) (K : Nat) :
    DensityOne (AllThrough P K) := by
  induction K with
  | zero =>
    apply densityOne_mono (P := P) _ hP
    intro n hn k hk
    have he : k=0 := by omega
    subst k
    exact hn
  | succ K ih =>
    apply densityOne_mono (P := fun n => AllThrough P K n ∧ P (acceleratedOrbit (K+1) n))
      _ (density_one_and ih (density_one_orbit hP (K+1)))
    intro n hn k hk
    by_cases hle : k≤K
    · exact hn.1 k hle
    · have he : k=K+1 := by omega
      simpa only [he] using hn.2

end Collatz.StepDensityTransport
