import Collatz.Exploration.BarrierKernel

/-!
# Exact one-step capacity of a Collatz interval

For b>0, the states whose current and next values belong to [b,u] have
an explicit bijection with [0,capacity). Even states are 2q with
b ≤ q ≤ u/2. Odd states are 2q+1 with b/2 ≤ q < (u+2)/6.
Natural subtraction gives zero for empty bands, with no cap-size assumption.
This yields a smaller pigeonhole budget than the raw interval width.
No boundedness, nontrivial-cycle exclusion, or literature novelty is asserted.
-/
namespace Collatz.Exploration.IntervalCapacity

open BarrierKernel

def Viable (b u n : Nat) : Prop :=
  b ≤ n ∧ n ≤ u ∧ b ≤ step n ∧ step n ≤ u

def evenCapacity (b u : Nat) : Nat := u / 2 + 1 - b

def oddCapacity (b u : Nat) : Nat := (u + 2) / 6 - b / 2

def capacity (b u : Nat) : Nat := evenCapacity b u + oddCapacity b u

/-- Even states precede odd states in a compact indexing of the viable set. -/
def rank (b u n : Nat) : Nat :=
  if n % 2 = 0 then n / 2 - b
  else evenCapacity b u + (n / 2 - b / 2)

/-- The explicit inverse enumerates the two disjoint parity bands. -/
def unrank (b u r : Nat) : Nat :=
  if r < evenCapacity b u then 2 * (b+r)
  else 2 * (b/2 + (r-evenCapacity b u)) + 1

theorem viable_even_iff {b u n : Nat} (_hb : 0 < b) (he : n % 2 = 0) :
    Viable b u n ↔ b ≤ n/2 ∧ n/2 ≤ u/2 := by
  by_cases hn : n = 0
  · subst n
    simp [Viable, step_zero]
  · simp only [Viable, step, if_neg hn, if_pos he]
    omega

theorem viable_odd_iff {b u n : Nat} (_hb : 0 < b) (ho : n % 2 = 1) :
    Viable b u n ↔ b/2 ≤ n/2 ∧ n/2 < (u+2)/6 := by
  have hn : n ≠ 0 := by omega
  have he : ¬ n % 2 = 0 := by omega
  simp only [Viable, step, if_neg hn, if_neg he]
  omega

/-- Every viable state has a label strictly below the stated capacity. -/
theorem rank_lt {b u n : Nat} (hb : 0 < b) (h : Viable b u n) :
    rank b u n < capacity b u := by
  by_cases he : n % 2 = 0
  · have hs := (viable_even_iff hb he).mp h
    simp only [rank, if_pos he, capacity, evenCapacity, oddCapacity]
    omega
  · have ho : n % 2 = 1 := by omega
    have hs := (viable_odd_iff hb ho).mp h
    simp only [rank, if_neg he, capacity, evenCapacity, oddCapacity]
    omega

/-- Compact labels retain the complete state, not merely its residue. -/
theorem unrank_rank {b u n : Nat} (hb : 0 < b) (h : Viable b u n) :
    unrank b u (rank b u n) = n := by
  by_cases he : n % 2 = 0
  · have hs := (viable_even_iff hb he).mp h
    have hr : n/2-b < evenCapacity b u := by unfold evenCapacity; omega
    simp only [rank, if_pos he, unrank, if_pos hr]
    omega
  · have ho : n % 2 = 1 := by omega
    have hs := (viable_odd_iff hb ho).mp h
    have hr : ¬ evenCapacity b u + (n/2-b/2) < evenCapacity b u := by omega
    simp only [rank, if_neg he, unrank, if_neg hr]
    omega

theorem rank_injective {b u n m : Nat} (hb : 0 < b)
    (hn : Viable b u n) (hm : Viable b u m)
    (he : rank b u n = rank b u m) : n = m := by
  rw [← unrank_rank hb hn, ← unrank_rank hb hm, he]

/-- Every compact label produces a viable state: the capacity is exact. -/
theorem viable_unrank {b u r : Nat} (hb : 0 < b) (hr : r < capacity b u) :
    Viable b u (unrank b u r) := by
  by_cases he : r < evenCapacity b u
  · rw [unrank, if_pos he]
    apply (viable_even_iff hb (by omega)).mpr
    unfold evenCapacity at he
    omega
  · rw [unrank, if_neg he]
    apply (viable_odd_iff hb (by omega)).mpr
    unfold capacity oddCapacity at hr
    omega

theorem rank_unrank (b u r : Nat) :
    rank b u (unrank b u r) = r := by
  by_cases he : r < evenCapacity b u
  · have hp : (2*(b+r)) % 2 = 0 := by omega
    simp only [unrank, if_pos he, rank, if_pos hp]
    omega
  · have hp : ¬ (2*(b/2+(r-evenCapacity b u))+1) % 2 = 0 := by omega
    simp only [unrank, if_neg he, rank, if_neg hp]
    omega

/-- Interval survival through one extra step makes all source points viable. -/
theorem viable_of_intervalCheck {b u K n : Nat}
    (h : intervalCheck b u (K+1) n = true) {i : Nat} (hi : i ≤ K) :
    Viable b u (orbit i n) := by
  have hs := (intervalCheck_iff b u (K+1) n).mp h
  have hp := hs i (by omega)
  have ht := hs (i+1) (by omega)
  rw [orbit_succ_steps, orbit_step_commute] at ht
  exact ⟨hp.1, hp.2, ht.1, ht.2⟩

/-- Exact viable-state capacity replaces the width in finite cycle extraction.
The additional sampled endpoint validates the last source state's successor. -/
theorem cycle_of_capacity_check {b u n : Nat} (hb : 0 < b)
    (h : intervalCheck b u (capacity b u + 1) n = true) :
    ∃ i j, i < j ∧ j ≤ capacity b u ∧
      b ≤ orbit i n ∧ orbit (j-i) (orbit i n) = orbit i n := by
  have hv : ∀ i, i ≤ capacity b u → Viable b u (orbit i n) :=
    fun _ hi => viable_of_intervalCheck h hi
  obtain ⟨i,j,hij,hj,he⟩ := Pigeonhole.exists_repeat
    (f := fun i => rank b u (orbit i n))
    (B := capacity b u) (N := capacity b u)
    (fun i hi => rank_lt hb (hv i hi)) (Nat.le_refl _)
  have hi : i ≤ capacity b u := by omega
  have heq := rank_injective hb (hv i hi) (hv j hj) he
  refine ⟨i,j,hij,hj,(hv i hi).1,?_⟩
  rw [← orbit_add, Nat.sub_add_cancel (by omega : i ≤ j), ← heq]

/-- The capacity never exceeds the unfiltered inclusive interval width. -/
theorem capacity_le_width {b u : Nat} (hb : 0 < b) :
    capacity b u ≤ u-b+1 := by
  unfold capacity evenCapacity oddCapacity
  omega

/-- Above the odd-entry threshold, all floor corrections are explicit. -/
theorem capacity_remainder_identity {b u : Nat} (hb : 0 < b) (hu : 3*b+1 ≤ u) :
    6*capacity b u + 9*b + 3*(u%2) + (u+2)%6 =
      4*u + 8 + 3*(b%2) := by
  unfold capacity evenCapacity oddCapacity
  omega

theorem oddCapacity_zero_of_small_cap {b u : Nat} (hu : u ≤ 3*b) :
    oddCapacity b u = 0 := by
  unfold oddCapacity
  omega

/-- Below 3b+1 there are no viable odd sources. -/
theorem viable_even_of_small_cap {b u n : Nat} (hb : 0 < b)
    (hu : u ≤ 3*b) (h : Viable b u n) : n%2 = 0 := by
  by_cases he : n%2 = 0
  · exact he
  · have hs := (viable_odd_iff hb (by omega : n%2 = 1)).mp h
    omega

/-- No three consecutive orbit points can all lie in [b,3b].
Two viable even sources would require the first value to be at least 4b. -/
theorem small_cap_two_step_rejection {b u n : Nat} (hb : 0 < b)
    (hu : u ≤ 3*b) : intervalCheck b u 2 n = false := by
  by_cases ht : intervalCheck b u 2 n = true
  · have hv := viable_of_intervalCheck ht (i := 0) (by decide)
    have hw := viable_of_intervalCheck ht (i := 1) (by decide)
    change Viable b u n at hv
    change Viable b u (step n) at hw
    have he := viable_even_of_small_cap hb hu hv
    have hf := viable_even_of_small_cap hb hu hw
    have hn : n ≠ 0 := by have := hv.1; omega
    have hs : step n = n/2 := by simp only [step, if_neg hn, if_pos he]
    have hbnd := (viable_even_iff hb hf).mp hw
    have hupper := hv.2.1
    rw [hs] at hbnd
    omega
  · cases he : intervalCheck b u 2 n <;> simp_all

/-- At [3,10], four one-step viable states replace eight raw interval states. -/
theorem capacity_control : capacity 3 10 = 4 ∧
    unrank 3 10 0 = 6 ∧ unrank 3 10 1 = 8 ∧
    unrank 3 10 2 = 10 ∧ unrank 3 10 3 = 3 := by decide

/-- Empty and reversed intervals are handled by the same truncated formulas. -/
theorem empty_controls : capacity 2 3 = 0 ∧ capacity 7 3 = 0 := by decide

/-- Omitting the extra endpoint admits a prefix with no repeated state. -/
theorem endpoint_budget_control : capacity 1 2 = 1 ∧
    intervalCheck 1 2 1 2 = true ∧ intervalCheck 1 2 2 2 = false := by decide

/-- A representative numerical budget reduction, with no orbit assumption. -/
theorem budget_reduction_control : capacity 100 1000 + 1 = 519 ∧
    1000-100+1 = (901 : Nat) := by decide

end Collatz.Exploration.IntervalCapacity
