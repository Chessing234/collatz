import Collatz.Exploration.FloorExcursion
import Collatz.Exploration.FiveBandArithmetic

/-! A sharp constant clock for exiting an ordinary Collatz band.
All statements are finite arithmetic consequences of the actual map.
The two exit directions are kept explicit. -/
namespace Collatz.Exploration.FiveBandClock
open BarrierKernel

/-- Division-free transition equations, with the parity conditions retained. -/
theorem step_relation {n : Nat} (hn : 0 < n) :
    (2*step n = n ∧ n%2 = 0) ∨ (step n = 3*n+1 ∧ n%2 = 1) := by
  have hz : n ≠ 0 := by omega
  by_cases he : n%2 = 0
  · left
    simp only [step, if_neg hz, if_pos he]
    omega
  · right
    exact ⟨by simp [step, hz, he], by omega⟩

/-- Every ordinary orbit exits [b,5b] by time twelve when b>1. -/
theorem rejection_twelve {b n : Nat} (hb : 1 < b) :
    intervalCheck b (5*b) 12 n = false := by
  by_cases ht : intervalCheck b (5*b) 12 n = true
  · exfalso
    have hs := (intervalCheck_iff b (5*b) 12 n).mp ht
    have bounds0 := hs 0 (by decide)
    have bounds1 := hs 1 (by decide)
    have bounds2 := hs 2 (by decide)
    have bounds3 := hs 3 (by decide)
    have bounds4 := hs 4 (by decide)
    have bounds5 := hs 5 (by decide)
    have bounds6 := hs 6 (by decide)
    have bounds7 := hs 7 (by decide)
    have bounds8 := hs 8 (by decide)
    have bounds9 := hs 9 (by decide)
    have bounds10 := hs 10 (by decide)
    have bounds11 := hs 11 (by decide)
    have bounds12 := hs 12 (by decide)
    have rel (k : Nat) (hk : k ≤ 11) :
        (2*orbit (k+1) n = orbit k n ∧ (orbit k n)%2 = 0) ∨
        (orbit (k+1) n = 3*orbit k n+1 ∧ (orbit k n)%2 = 1) := by
      have hp : 0 < orbit k n := by have := hs k (by omega); omega
      have h := step_relation hp
      rw [← orbit_step_commute, ← orbit_succ_steps] at h
      exact h
    exact FiveBandArithmetic.impossible_trace b (orbit 0 n) (orbit 1 n) (orbit 2 n) (orbit 3 n) (orbit 4 n) (orbit 5 n) (orbit 6 n) (orbit 7 n) (orbit 8 n) (orbit 9 n) (orbit 10 n) (orbit 11 n) (orbit 12 n) hb
      bounds0 bounds1 bounds2 bounds3 bounds4 bounds5 bounds6 bounds7 bounds8 bounds9 bounds10 bounds11 bounds12
      ((rel 0 (by decide)).imp And.left And.left) ((rel 1 (by decide)).imp And.left And.left) ((rel 2 (by decide)).imp And.left And.left) ((rel 3 (by decide)).imp And.left And.left) ((rel 4 (by decide)).imp And.left And.left) ((rel 5 (by decide)).imp And.left And.left) ((rel 6 (by decide)).imp And.left And.left) ((rel 7 (by decide)).imp And.left And.left) ((rel 8 (by decide)).imp And.left And.left) ((rel 9 (by decide)).imp And.left And.left) ((rel 10 (by decide)).imp And.left And.left) ((rel 11 (by decide)).imp And.left And.left)
  · cases he : intervalCheck b (5*b) 12 n <;> simp_all

/-- The finite clock retains both possible exit directions. -/
theorem exit_twelve (b n : Nat) (hb : 1 < b) :
    ∃ k, k ≤ 12 ∧ (orbit k n < b ∨ 5*b < orbit k n) := by
  by_cases h : ∃ k, k ≤ 12 ∧ (orbit k n < b ∨ 5*b < orbit k n)
  · exact h
  · exfalso
    have hc : intervalCheck b (5*b) 12 n = true := by
      apply (intervalCheck_iff b (5*b) 12 n).mpr
      intro k hk
      by_cases hl : orbit k n < b
      · exact False.elim (h ⟨k,hk,Or.inl hl⟩)
      · by_cases hu : 5*b < orbit k n
        · exact False.elim (h ⟨k,hk,Or.inr hu⟩)
        · omega
    rw [rejection_twelve hb] at hc
    cases hc

/-- Twelve cannot be replaced by eleven in the arbitrary-start band theorem. -/
theorem clock_sharpness : intervalCheck 40 200 11 114 = true ∧
    orbit 12 114 = 37 ∧ intervalCheck 40 200 12 114 = false := by decide

/-- Keeping a lower barrier eliminates the downward exit alternative. -/
theorem high_within_twelve {b n : Nat} (hb : 1 < b) (h : Kernel b n) :
    ∃ k, k ≤ 12 ∧ 5*b < orbit k n := by
  obtain ⟨k,hk,hl | hu⟩ := exit_twelve b n hb
  · have := h k; omega
  · exact ⟨k,hk,hu⟩

/-- Every future 13-point window contains a high excursion. -/
theorem high_window {b n : Nat} (hb : 1 < b) (h : Kernel b n) (t : Nat) :
    ∃ s, t ≤ s ∧ s ≤ t+12 ∧ 5*b < orbit s n := by
  obtain ⟨k,hk,hv⟩ := high_within_twelve hb (kernel_forward h t)
  refine ⟨k+t,by omega,by omega,?_⟩
  rw [orbit_add]
  exact hv

/-- Explicitly distinct witnesses, one in each disjoint 13-point block.
This is a conditional lower frequency bound; it does not construct a failed orbit. -/
theorem disjoint_high_witnesses {b n : Nat} (hb : 1 < b) (h : Kernel b n) :
    ∃ f : Nat → Nat,
      (∀ q, 13*q ≤ f q ∧ f q < 13*(q+1) ∧ 5*b < orbit (f q) n) ∧
      (∀ a c, a < c → f a < f c) := by
  classical
  have hw (q : Nat) : ∃ s, 13*q ≤ s ∧ s < 13*(q+1) ∧ 5*b < orbit s n := by
    obtain ⟨s,hs,ht,hv⟩ := high_window hb h (13*q)
    exact ⟨s,hs,by omega,hv⟩
  let f (q : Nat) := Classical.choose (hw q)
  have hf (q : Nat) : 13*q ≤ f q ∧ f q < 13*(q+1) ∧ 5*b < orbit (f q) n :=
    Classical.choose_spec (hw q)
  refine ⟨f,hf,?_⟩
  intro a c hac
  have ha := hf a
  have hc := hf c
  omega

/-- For any finite block count N there are N distinct high times below 13N. -/
theorem finite_high_witnesses {b n : Nat} (hb : 1 < b) (h : Kernel b n) (N : Nat) :
    ∃ f : Fin N → Nat,
      (∀ q, f q < 13*N ∧ 5*b < orbit (f q) n) ∧
      (∀ a c, f a = f c → a = c) := by
  obtain ⟨g,hg,hstrict⟩ := disjoint_high_witnesses hb h
  refine ⟨fun q => g q.val,?_,?_⟩
  · intro q
    change g q.val < 13*N ∧ 5*b < orbit (g q.val) n
    have hq := hg q.val
    have hlt := q.isLt
    exact ⟨by omega,hq.2.2⟩
  · intro a c he
    change g a.val = g c.val at he
    have hv : a.val = c.val := by
      by_cases hac : a.val < c.val
      · have := hstrict a.val c.val hac; omega
      · by_cases hca : c.val < a.val
        · have := hstrict c.val a.val hca; omega
        · omega
    exact Fin.ext hv

/-- A finite observed lower-surviving prefix already supplies distinct witnesses;
no infinite kernel hypothesis is required for this finite conclusion. -/
theorem finite_survival_witnesses {b n : Nat} (hb : 1 < b) (N : Nat)
    (h : Survives b (13*N-1) n) :
    ∃ f : Fin N → Nat,
      (∀ q, f q < 13*N ∧ 5*b < orbit (f q) n) ∧
      (∀ a c, f a = f c → a = c) := by
  classical
  have hw (q : Fin N) :
      ∃ s, 13*q.val ≤ s ∧ s < 13*(q.val+1) ∧ 5*b < orbit s n := by
    obtain ⟨k,hk,hl | hu⟩ := exit_twelve b (orbit (13*q.val) n) hb
    · have hq := q.isLt
      have hlower := h (k+13*q.val) (by omega)
      rw [orbit_add] at hlower
      omega
    · refine ⟨k+13*q.val,by omega,by omega,?_⟩
      rw [orbit_add]
      exact hu
  let f (q : Fin N) := Classical.choose (hw q)
  have hf (q : Fin N) :
      13*q.val ≤ f q ∧ f q < 13*(q.val+1) ∧ 5*b < orbit (f q) n :=
    Classical.choose_spec (hw q)
  refine ⟨f,?_,?_⟩
  · intro q
    have hs := hf q
    have hq := q.isLt
    exact ⟨by omega,hs.2.2⟩
  · intro a c he
    have ha := hf a
    have hc := hf c
    have hv : a.val = c.val := by omega
    exact Fin.ext hv

/-- The excluded anchor 1 supports the trivial cycle indefinitely. -/
theorem anchor_one_control : intervalCheck 1 5 100 1 = true := by decide

end Collatz.Exploration.FiveBandClock
