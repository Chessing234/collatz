import Collatz.Accelerated

/-!
# A deterministic comparison map with two terminal basins

This is NOT the Collatz map. It is halving with fixed points at 1 and 3.
Every target at least 2 has full dyadic intervals of predecessors; target 1
inherits intervals through 2. Nevertheless 3 never reaches 1. The model tests
the logical gap between abundant predecessors and universal convergence.
-/

namespace Collatz.DensityCountermodel

/-- A comparison map, distinct from both standard and accelerated Collatz. -/
def step (n : Nat) : Nat := if n ≤ 1 then n else if n = 3 then 3 else n/2

def orbit : Nat → Nat → Nat
  | 0, n => n
  | k+1, n => orbit k (step n)

@[simp] theorem orbit_zero (n : Nat) : orbit 0 n = n := rfl

@[simp] theorem step_one : step 1 = 1 := by decide
@[simp] theorem step_three : step 3 = 3 := by decide
@[simp] theorem step_two : step 2 = 1 := by decide

theorem orbit_succ_last (k n : Nat) : orbit (k+1) n = step (orbit k n) := by
  induction k generalizing n with
  | zero => rfl
  | succ k ih => exact ih (step n)

theorem orbit_three (k : Nat) : orbit k 3 = 3 := by
  induction k with
  | zero => rfl
  | succ k ih => simpa only [orbit, step_three] using ih

/-- A fixed positive counterexample to universal convergence for this map. -/
theorem three_never_reaches_one : ¬ ∃ k, orbit k 3 = 1 := by
  intro ⟨k, hk⟩
  rw [orbit_three] at hk
  omega

/-- The dyadic predecessor intervals halve exactly while above target 2. -/
theorem step_dyadic (a k r : Nat) (ha : 2 ≤ a) :
    step (a*2^(k+1)+r) = a*2^k+r/2 := by
  have hp : 0 < (2:Nat)^k := Nat.pow_pos (by decide)
  have hbase : 2 ≤ a*2^k := by
    have := Nat.mul_le_mul_left a hp
    omega
  rw [Nat.pow_succ]
  have he : a*(2^k*2) = 2*(a*2^k) := by
    simp [Nat.mul_comm, Nat.mul_left_comm]
  rw [he, step, if_neg (by omega), if_neg (by omega)]
  omega

/-- Every integer in [a*2^k,(a+1)*2^k) reaches a after k steps, for a≥2. -/
theorem dyadic_predecessor (a k r : Nat) (ha : 2 ≤ a) (hr : r < 2^k) :
    orbit k (a*2^k+r) = a := by
  induction k generalizing r with
  | zero =>
    have he : r = 0 := by simpa using hr
    simp [he, orbit]
  | succ k ih =>
    rw [orbit, step_dyadic a k r ha]
    apply ih
    rw [Nat.pow_succ] at hr
    omega

/-- Target 1 has a full dyadic block too, by passing through target 2. -/
theorem one_dyadic_predecessor (k r : Nat) (hr : r < 2^k) :
    orbit (k+1) (2*2^k+r) = 1 := by
  rw [orbit_succ_last, dyadic_predecessor 2 k r (by decide) hr, step_two]

/-- Unbounded, contiguous predecessor blocks coexist with a second fixed point.
This is a block statement; a lower-natural-density bound needs an additional
comparison between the block scale and an arbitrary cutoff. -/
theorem all_targets_have_blocks (a : Nat) (ha : 0 < a) (k : Nat) :
    ∃ start time : Nat, 0 < start ∧
      ∀ r, r < 2^k → orbit time (start+r) = a := by
  by_cases he : a = 1
  · subst he
    exact ⟨2*2^k, k+1, Nat.mul_pos (by decide) (Nat.pow_pos (by decide)),
      fun r hr => one_dyadic_predecessor k r hr⟩
  · exact ⟨a*2^k, k, Nat.mul_pos ha (Nat.pow_pos (by decide)),
      fun r hr => dyadic_predecessor a k r (by omega) hr⟩

/-- Count all predecessors below a cutoff, with no time bound. -/
noncomputable def predecessorCount (a N : Nat) : Nat := by
  classical
  exact ((List.range N).filter fun n => decide (∃ t, orbit t n = a)).length

/-- A certified block inside the cutoff contributes its full length to the count. -/
theorem block_count_lower (a N start len time : Nat)
    (hN : start+len ≤ N) (hblock : ∀ r, r < len → orbit time (start+r) = a) :
    len ≤ predecessorCount a N := by
  classical
  have hsub : List.range' start len ⊆
      (List.range N).filter (fun n => decide (∃ t, orbit t n = a)) := by
    intro n hn
    obtain ⟨r, hr, he⟩ := List.mem_range'.mp hn
    simp only [Nat.one_mul] at he
    subst n
    apply List.mem_filter.mpr
    refine ⟨List.mem_range.mpr (by omega), ?_⟩
    exact decide_eq_true_eq.mpr ⟨time, hblock r hr⟩
  have hc := (List.nodup_range' (s := start) (n := len)).length_le_of_subset hsub
  simpa only [List.length_range', predecessorCount] using hc

/-- Use a uniform base for the ordinary targets and the exceptional target 1. -/
theorem blocks_at_base (a k : Nat) (ha : 0 < a) :
    ∃ time, ∀ r, r < 2^k → orbit time (max a 2 * 2^k+r) = a := by
  by_cases he : a = 1
  · subst he
    exact ⟨k+1, fun r hr => one_dyadic_predecessor k r hr⟩
  · rw [Nat.max_eq_left (by omega : 2 ≤ a)]
    exact ⟨k, fun r hr => dyadic_predecessor a k r (by omega) hr⟩

/-- Every sufficiently large cutoff contains a dyadic block occupying a fixed
positive fraction of it. The time at which this block reaches a can vary. -/
theorem predecessor_count_linear (a N : Nat) (ha : 0 < a)
    (hN : max a 2 + 1 ≤ N) :
    N < (2 * (max a 2 + 1)) * predecessorCount a N := by
  let b := max a 2
  let q := N/(b+1)
  have hq : 0 < q := by
    have h : 1 ≤ N/(b+1) := (Nat.le_div_iff_mul_le (by omega)).mpr (by simpa [b] using hN)
    omega
  let k := q.log2
  have hlow : 2^k ≤ q := Nat.log2_self_le (by omega)
  have hupp : q < 2^(k+1) := Nat.lt_log2_self
  have hfit : (b+1)*2^k ≤ N := by
    have h := (Nat.le_div_iff_mul_le (by omega : 0 < b+1)).mp hlow
    simpa only [Nat.mul_comm] using h
  have hscale : N < (2*(b+1))*2^k := by
    have h := (Nat.div_lt_iff_lt_mul (by omega : 0 < b+1)).mp hupp
    simpa only [Nat.pow_succ, Nat.mul_assoc, Nat.mul_comm, Nat.mul_left_comm] using h
  obtain ⟨time, ht⟩ := blocks_at_base a k ha
  have hc : 2^k ≤ predecessorCount a N := by
    apply block_count_lower a N (b*2^k) (2^k) time
    · simpa only [Nat.add_mul, Nat.one_mul] using hfit
    · exact ht
  exact Nat.lt_of_lt_of_le hscale (Nat.mul_le_mul_left _ hc)

/-- Explicit positive lower-natural-density bounds hold for every positive
target of this map, despite the nontrivial fixed point at 3. -/
theorem all_targets_positive_lower_density :
    ∀ a, 0 < a → ∃ C N0, 0 < C ∧ ∀ N, N0 ≤ N →
      N ≤ C * predecessorCount a N := by
  intro a ha
  refine ⟨2*(max a 2+1), max a 2+1, by omega, ?_⟩
  intro N hN
  exact Nat.le_of_lt (predecessor_count_linear a N ha hN)

/-- The comparison map preserves positive integers. -/
theorem step_positive {n : Nat} (hn : 0 < n) : 0 < step n := by
  unfold step
  split
  · exact hn
  · split <;> omega

/-- Every positive orbit of the comparison map reaches 1 or 3. Thus the
failure of universal convergence here comes from a second basin, not escape. -/
theorem reaches_one_or_three (n : Nat) (hn : 0 < n) :
    ∃ k, orbit k n = 1 ∨ orbit k n = 3 := by
  induction n using Nat.strongRecOn with
  | _ n ih =>
    by_cases h1 : n = 1
    · exact ⟨0, Or.inl h1⟩
    by_cases h3 : n = 3
    · exact ⟨0, Or.inr h3⟩
    have hs : step n = n/2 := by simp only [step, if_neg (by omega : ¬ n≤1), if_neg h3]
    have hsmall : step n < n := by rw [hs]; omega
    obtain ⟨k, hk⟩ := ih (step n) hsmall (step_positive hn)
    exact ⟨k+1, hk⟩

end Collatz.DensityCountermodel
