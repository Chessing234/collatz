import Collatz.Strategy.ComparableHeightObstruction

/-!
# Explicit finite location of a bounded-height obstruction

The earlier obstruction rules out a global schedule. This module places a
failure on a specified finite all-odd run and bounds the size of the failing
input. The witness is a failure of the proposed height schedule, not a
counterexample to Collatz convergence.
-/
namespace Collatz.BoundedHeightWitness
open ComparableHeightObstruction ResidueMonotoneObstruction

/-- Local schedule choices suffice to concatenate within a finite orbit. -/
theorem concatenate_local (height : Nat → Nat) (B n rounds : Nat)
    (hlocal : ∀ t, t≤B*rounds → ∃ k, 0<k ∧ k≤B ∧
      height (acceleratedOrbit k (acceleratedOrbit t n))≤height (acceleratedOrbit t n)) :
    ∀ j, j≤rounds → ∃ t, j≤t ∧ t≤B*j ∧
      height (acceleratedOrbit t n)≤height n := by
  intro j
  induction j with
  | zero =>
    intro _
    exact ⟨0, by omega, by omega, Nat.le_refl _⟩
  | succ j ih =>
    intro hj
    obtain ⟨t, hjt, ht, hh⟩ := ih (by omega)
    have hb := Nat.mul_le_mul_left B (by omega : j≤rounds)
    obtain ⟨k, hk, hkB, hd⟩ := hlocal t (by omega)
    refine ⟨k+t, by omega, ?_, ?_⟩
    · rw [Nat.mul_succ]; omega
    · rw [← acceleratedOrbit_add]
      exact Nat.le_trans hd hh

/-- Every point in the specified odd run has an explicit common size bound. -/
theorem odd_run_upper (q K t : Nat) (hq : 0<q) (ht : t≤K) :
    acceleratedOrbit t (q*2^K-1)<q*3^K := by
  rw [orbit_mul_pow_pred q K hq t ht]
  have hp := Nat.pow_le_pow_left (by decide : 2≤3) (K-t)
  have hm := Nat.mul_le_mul_left (q*3^t) hp
  have he : q*3^t*3^(K-t)=q*3^K := by
    rw [Nat.mul_assoc, ← Nat.pow_add]
    congr 2
    omega
  rw [he] at hm
  have hpos : 0<q*3^t*2^(K-t) :=
    Nat.mul_pos (Nat.mul_pos hq (Nat.pow_pos (by decide))) (Nat.pow_pos (by decide))
  omega

/-- Some state on an explicit finite run has strictly larger height at every
positive time up to B. Only height bounds on this finite run are required. -/
theorem failure_on_odd_run (height : Nat → Nat) (C B q : Nat) (hq : 0<q)
    (hheight : ∀ t, t≤B*(2*C+1) →
      acceleratedOrbit t (q*2^(B*(2*C+1)+1)-1)+1 ≤
        height (acceleratedOrbit t (q*2^(B*(2*C+1)+1)-1)) ∧
      height (acceleratedOrbit t (q*2^(B*(2*C+1)+1)-1)) ≤
        C*(acceleratedOrbit t (q*2^(B*(2*C+1)+1)-1)+1)) :
    ∃ t, t≤B*(2*C+1) ∧ ∀ k, 0<k → k≤B →
      height (acceleratedOrbit t (q*2^(B*(2*C+1)+1)-1)) <
        height (acceleratedOrbit k (acceleratedOrbit t (q*2^(B*(2*C+1)+1)-1))) := by
  classical
  let n := q*2^(B*(2*C+1)+1)-1
  by_cases hex : ∃ t, t≤B*(2*C+1) ∧ ∀ k, 0<k → k≤B →
      height (acceleratedOrbit t n)<height (acceleratedOrbit k (acceleratedOrbit t n))
  · exact hex
  · have hlocal : ∀ t, t≤B*(2*C+1) → ∃ k, 0<k ∧ k≤B ∧
        height (acceleratedOrbit k (acceleratedOrbit t n))≤height (acceleratedOrbit t n) := by
      intro t ht
      by_cases hk : ∃ k, 0<k ∧ k≤B ∧
          height (acceleratedOrbit k (acceleratedOrbit t n))≤height (acceleratedOrbit t n)
      · exact hk
      · exact False.elim (hex ⟨t, ht, fun k hp hb => by
          have hnot : ¬height (acceleratedOrbit k (acceleratedOrbit t n))≤
              height (acceleratedOrbit t n) := fun h => hk ⟨k,hp,hb,h⟩
          omega⟩)
    obtain ⟨t, htmin, htmax, hh⟩ := concatenate_local height B n (2*C+1)
      hlocal (2*C+1) (Nat.le_refl _)
    have hg : C*(n+1)<acceleratedOrbit t n+1 :=
      odd_run_exceeds hq htmin (by omega)
    have hl := (hheight t htmax).1
    have hu := (hheight 0 (by omega)).2
    change height n≤C*(n+1) at hu
    change acceleratedOrbit t n+1≤height (acceleratedOrbit t n) at hl
    omega

/-- A fully quantitative counterexample to a proposed bounded schedule lies
below an explicit exponential bound and above any requested cutoff. -/
theorem bounded_failure_witness (height : Nat → Nat) (C B cutoff : Nat)
    (hheight : ∀ n, cutoff<n → 1<n → n+1≤height n ∧ height n≤C*(n+1)) :
    ∃ x, cutoff<x ∧ 1<x ∧ x<(cutoff+3)*3^(B*(2*C+1)+1) ∧
      ∀ k, 0<k → k≤B → height x<height (acceleratedOrbit k x) := by
  let q := cutoff+3
  let K := B*(2*C+1)+1
  let n := q*2^K-1
  have hq : 0<q := by dsimp [q]; omega
  have hn : cutoff<n ∧ 1<n := by
    have hp := Nat.one_le_pow K 2 (by decide)
    have hm := Nat.mul_le_mul_left q hp
    dsimp [n, q] at *
    omega
  have hrun : ∀ t, t≤B*(2*C+1) → n≤acceleratedOrbit t n := by
    intro t ht
    by_cases hz : t=0
    · subst t; exact Nat.le_refl _
    · have h := (same_residue_rising_run 1 q (B*(2*C+1)) (by decide) hq
        t (by omega) ht).1
      simpa only [Nat.one_mul] using Nat.le_of_lt h
  obtain ⟨t, ht, hfail⟩ := failure_on_odd_run height C B q hq (by
    intro t ht
    have hr := hrun t ht
    exact hheight (acceleratedOrbit t n) (by omega) (by omega))
  have hr := hrun t ht
  refine ⟨acceleratedOrbit t n, by omega, by omega, ?_, hfail⟩
  exact odd_run_upper q K t hq (by dsimp [K]; omega)

/-- Decide whether all positive steps through B increase the proposed height. -/
def failureCheck (height : Nat → Nat) (B x : Nat) : Bool :=
  (List.range B).all (fun j => decide (height x<height (acceleratedOrbit (j+1) x)))

/-- The finite Boolean test has exactly the stated obstruction semantics. -/
theorem failureCheck_iff (height : Nat → Nat) (B x : Nat) :
    failureCheck height B x=true ↔
      ∀ k, 0<k → k≤B → height x<height (acceleratedOrbit k x) := by
  simp only [failureCheck, List.all_eq_true, List.mem_range, decide_eq_true_eq]
  constructor
  · intro h k hk hb
    have ht := h (k-1) (by omega)
    have he : k-1+1=k := by omega
    simpa only [he] using ht
  · intro h j hj
    exact h (j+1) (by omega) (by omega)

/-- Search the entire finite run specified by the quantitative argument. -/
def runFailureCheck (height : Nat → Nat) (C B q : Nat) : Bool :=
  (List.range (B*(2*C+1)+1)).any (fun t =>
    failureCheck height B (acceleratedOrbit t (q*2^(B*(2*C+1)+1)-1)))

/-- A successful run search gives the exact index and its verified failure. -/
theorem runFailureCheck_iff (height : Nat → Nat) (C B q : Nat) :
    runFailureCheck height C B q=true ↔
    ∃ t, t≤B*(2*C+1) ∧ ∀ k, 0<k → k≤B →
      height (acceleratedOrbit t (q*2^(B*(2*C+1)+1)-1)) <
        height (acceleratedOrbit k (acceleratedOrbit t (q*2^(B*(2*C+1)+1)-1))) := by
  simp only [runFailureCheck, List.any_eq_true, List.mem_range, failureCheck_iff]
  constructor
  · rintro ⟨t, ht, hf⟩
    exact ⟨t, by omega, hf⟩
  · rintro ⟨t, ht, hf⟩
    exact ⟨t, by omega, hf⟩

/-- Local comparison bounds guarantee success of the executable search. -/
theorem runFailureCheck_complete (height : Nat → Nat) (C B q : Nat) (hq : 0<q)
    (hheight : ∀ t, t≤B*(2*C+1) →
      acceleratedOrbit t (q*2^(B*(2*C+1)+1)-1)+1 ≤
        height (acceleratedOrbit t (q*2^(B*(2*C+1)+1)-1)) ∧
      height (acceleratedOrbit t (q*2^(B*(2*C+1)+1)-1)) ≤
        C*(acceleratedOrbit t (q*2^(B*(2*C+1)+1)-1)+1)) :
    runFailureCheck height C B q=true :=
  (runFailureCheck_iff height C B q).mpr (failure_on_odd_run height C B q hq hheight)

/-- Kernel-reduced examples cross-check the independent integer probe. -/
theorem size_example : failureCheck (fun n => n+1) 2 383=true := by decide

theorem residue_example :
    failureCheck (fun n => (n+1)*(n%7+1)) 2 9663676415=true := by decide

theorem residue_run_example :
    runFailureCheck (fun n => (n+1)*(n%7+1)) 7 2 3=true := by decide

end Collatz.BoundedHeightWitness
