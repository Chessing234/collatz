import Collatz.Exploration.IntervalCapacity

/-! Exact two-step interval capacity. The three disjoint source families
are 0 modulo 4, 2 modulo 4, and odd. The latter two have the same size,
because an odd source always survives its forced halving if its expansion
remains in the interval. This refines finite certificates, not Collatz. -/
namespace Collatz.Exploration.TwoStepCapacity
open BarrierKernel IntervalCapacity

def ViableTwo (b u n : Nat) : Prop := Viable b u n ∧ Viable b u (step n)

def fourCapacity (b u : Nat) : Nat := u/4 + 1 - b

def capacityTwo (b u : Nat) : Nat := fourCapacity b u + 2*oddCapacity b u

def rankTwo (b u n : Nat) : Nat :=
  if n%4 = 0 then n/4-b
  else if n%4 = 2 then fourCapacity b u + (n/4-b/2)
  else fourCapacity b u + oddCapacity b u + (n/2-b/2)

def unrankTwo (b u r : Nat) : Nat :=
  if r < fourCapacity b u then 4*(b+r)
  else if r < fourCapacity b u + oddCapacity b u then
    4*(b/2+(r-fourCapacity b u))+2
  else 2*(b/2+(r-fourCapacity b u-oddCapacity b u))+1

theorem divisible_four_iff {b u n : Nat} (hb : 0 < b) (hn : n%4 = 0) :
    ViableTwo b u n ↔ b ≤ n/4 ∧ n/4 ≤ u/4 := by
  have he : n%2 = 0 := by omega
  have hs : step n = n/2 := by
    by_cases hz : n = 0
    · subst n; rfl
    · simp only [step, if_neg hz, if_pos he]
  have hhalf : (n/2)%2 = 0 := by omega
  unfold ViableTwo
  rw [hs, viable_even_iff hb he, viable_even_iff hb hhalf]
  omega

theorem two_mod_four_iff {b u n : Nat} (hb : 0 < b) (hn : n%4 = 2) :
    ViableTwo b u n ↔ b/2 ≤ n/4 ∧ n/4 < (u+2)/6 := by
  have he : n%2 = 0 := by omega
  have hz : n ≠ 0 := by omega
  have hs : step n = n/2 := by simp only [step, if_neg hz, if_pos he]
  have hhalf : (n/2)%2 = 1 := by omega
  unfold ViableTwo
  rw [hs, viable_even_iff hb he, viable_odd_iff hb hhalf]
  omega

/-- An odd viable source also passes its forced halving without a new condition. -/
theorem odd_iff {b u n : Nat} (hb : 0 < b) (hn : n%2 = 1) :
    ViableTwo b u n ↔ Viable b u n := by
  constructor
  · exact fun h => h.1
  · intro h
    refine ⟨h, ?_⟩
    have hz : n ≠ 0 := by omega
    have he : ¬ n%2 = 0 := by omega
    have hs : step n = 3*n+1 := by simp only [step, if_neg hz, if_neg he]
    rw [hs]
    apply (viable_even_iff hb (by omega)).mpr
    have hl := h.1
    have hu := h.2.2.2
    rw [hs] at hu
    omega

theorem rankTwo_lt {b u n : Nat} (hb : 0 < b) (h : ViableTwo b u n) :
    rankTwo b u n < capacityTwo b u := by
  by_cases h0 : n%4 = 0
  · have hs := (divisible_four_iff hb h0).mp h
    simp only [rankTwo, if_pos h0, capacityTwo, fourCapacity, oddCapacity]
    omega
  · by_cases h2 : n%4 = 2
    · have hs := (two_mod_four_iff hb h2).mp h
      simp only [rankTwo, if_neg h0, if_pos h2, capacityTwo, fourCapacity, oddCapacity]
      omega
    · have ho : n%2 = 1 := by omega
      have hs := (viable_odd_iff hb ho).mp h.1
      simp only [rankTwo, if_neg h0, if_neg h2, capacityTwo, fourCapacity, oddCapacity]
      omega

theorem unrankTwo_rankTwo {b u n : Nat} (hb : 0 < b) (h : ViableTwo b u n) :
    unrankTwo b u (rankTwo b u n) = n := by
  by_cases h0 : n%4 = 0
  · have hs := (divisible_four_iff hb h0).mp h
    have hr : n/4-b < fourCapacity b u := by unfold fourCapacity; omega
    simp only [rankTwo, if_pos h0, unrankTwo, if_pos hr]
    omega
  · by_cases h2 : n%4 = 2
    · have hs := (two_mod_four_iff hb h2).mp h
      have ha : ¬ fourCapacity b u+(n/4-b/2) < fourCapacity b u := by omega
      have hd : fourCapacity b u+(n/4-b/2) < fourCapacity b u+oddCapacity b u := by
        unfold oddCapacity; omega
      simp only [rankTwo, if_neg h0, if_pos h2, unrankTwo, if_neg ha, if_pos hd]
      omega
    · have ho : n%2 = 1 := by omega
      have hs := (viable_odd_iff hb ho).mp h.1
      have ha : ¬ fourCapacity b u+oddCapacity b u+(n/2-b/2) < fourCapacity b u := by omega
      have hd : ¬ fourCapacity b u+oddCapacity b u+(n/2-b/2) <
          fourCapacity b u+oddCapacity b u := by omega
      simp only [rankTwo, if_neg h0, if_neg h2, unrankTwo, if_neg ha, if_neg hd]
      omega

theorem viableTwo_unrankTwo {b u r : Nat} (hb : 0 < b) (hr : r < capacityTwo b u) :
    ViableTwo b u (unrankTwo b u r) := by
  by_cases ha : r < fourCapacity b u
  · rw [unrankTwo, if_pos ha]
    apply (divisible_four_iff hb (by omega)).mpr
    unfold fourCapacity at ha
    omega
  · by_cases hd : r < fourCapacity b u+oddCapacity b u
    · rw [unrankTwo, if_neg ha, if_pos hd]
      apply (two_mod_four_iff hb (by omega)).mpr
      unfold oddCapacity at hd
      omega
    · rw [unrankTwo, if_neg ha, if_neg hd]
      apply (odd_iff hb (by omega)).mpr
      apply (viable_odd_iff hb (by omega)).mpr
      unfold capacityTwo at hr
      unfold oddCapacity at *
      omega

theorem rankTwo_unrankTwo (b u r : Nat) :
    rankTwo b u (unrankTwo b u r) = r := by
  by_cases ha : r < fourCapacity b u
  · have hp : (4*(b+r))%4 = 0 := by omega
    simp only [unrankTwo, if_pos ha, rankTwo, if_pos hp]
    omega
  · by_cases hd : r < fourCapacity b u+oddCapacity b u
    · have hp : ¬ (4*(b/2+(r-fourCapacity b u))+2)%4 = 0 := by omega
      have hq : (4*(b/2+(r-fourCapacity b u))+2)%4 = 2 := by omega
      simp only [unrankTwo, if_neg ha, if_pos hd, rankTwo, if_neg hp, if_pos hq]
      omega
    · have hp : ¬ (2*(b/2+(r-fourCapacity b u-oddCapacity b u))+1)%4 = 0 := by omega
      have hq : ¬ (2*(b/2+(r-fourCapacity b u-oddCapacity b u))+1)%4 = 2 := by omega
      simp only [unrankTwo, if_neg ha, if_neg hd, rankTwo, if_neg hp, if_neg hq]
      omega

theorem capacityTwo_le_capacity {b u : Nat} : capacityTwo b u ≤ capacity b u := by
  unfold capacityTwo capacity fourCapacity evenCapacity oddCapacity
  omega

theorem cycle_of_two_capacity_check {b u n : Nat} (hb : 0 < b)
    (h : intervalCheck b u (capacityTwo b u+2) n = true) :
    ∃ i j, i < j ∧ j ≤ capacityTwo b u ∧
      b ≤ orbit i n ∧ orbit (j-i) (orbit i n) = orbit i n := by
  have hw : ∀ i, i ≤ capacityTwo b u+1 → Viable b u (orbit i n) :=
    fun _ hi => viable_of_intervalCheck h hi
  have hv : ∀ i, i ≤ capacityTwo b u → ViableTwo b u (orbit i n) := by
    intro i hi
    refine ⟨hw i (by omega), ?_⟩
    have hs := hw (i+1) (by omega)
    rw [orbit_succ_steps, orbit_step_commute] at hs
    exact hs
  obtain ⟨i,j,hij,hj,he⟩ := Pigeonhole.exists_repeat
    (f := fun i => rankTwo b u (orbit i n))
    (B := capacityTwo b u) (N := capacityTwo b u)
    (fun i hi => rankTwo_lt hb (hv i hi)) (Nat.le_refl _)
  have hi : i ≤ capacityTwo b u := by omega
  have heq : orbit i n = orbit j n := by
    rw [← unrankTwo_rankTwo hb (hv i hi), ← unrankTwo_rankTwo hb (hv j hj), he]
  refine ⟨i,j,hij,hj,(hv i hi).1.1,?_⟩
  rw [← orbit_add, Nat.sub_add_cancel (by omega : i ≤ j), ← heq]

theorem two_budget_control : capacityTwo 100 1000 + 2 = 387 := by decide

end Collatz.Exploration.TwoStepCapacity
