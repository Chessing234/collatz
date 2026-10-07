import Collatz.Exploration.FiveBandClock
import Collatz.Exploration.BandClock
import Collatz.Exploration.WiderBandArithmetic

/-! A wider sharp band clock, keeping the descent/growth alternative explicit. -/
namespace Collatz.Exploration.WiderBandClock
open BarrierKernel BandClock

/-- The inclusive ratio-21/4 band cannot contain eighteen sampled states. -/
theorem no_band_seventeen {b n : Nat} (hb : 1 < b)
    (hs : ∀ k, k ≤ 17 → b ≤ orbit k n ∧ 4*orbit k n ≤ 21*b) : False := by
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
  have bounds13 := hs 13 (by decide)
  have bounds14 := hs 14 (by decide)
  have bounds15 := hs 15 (by decide)
  have bounds16 := hs 16 (by decide)
  have bounds17 := hs 17 (by decide)
  have rel (k : Nat) (hk : k ≤ 16) :
      (2*orbit (k+1) n = orbit k n ∧ (orbit k n)%2 = 0) ∨
      (orbit (k+1) n = 3*orbit k n+1 ∧ (orbit k n)%2 = 1) := by
    have hp : 0 < orbit k n := by have := hs k (by omega); omega
    have h := FiveBandClock.step_relation hp
    rw [← orbit_step_commute, ← orbit_succ_steps] at h
    exact h
  exact WiderBandArithmetic.impossible_trace b (orbit 0 n) (orbit 1 n) (orbit 2 n) (orbit 3 n) (orbit 4 n) (orbit 5 n) (orbit 6 n) (orbit 7 n) (orbit 8 n) (orbit 9 n) (orbit 10 n) (orbit 11 n) (orbit 12 n) (orbit 13 n) (orbit 14 n) (orbit 15 n) (orbit 16 n) (orbit 17 n) hb
    bounds0 bounds1 bounds2 bounds3 bounds4 bounds5 bounds6 bounds7 bounds8 bounds9 bounds10 bounds11 bounds12 bounds13 bounds14 bounds15 bounds16 bounds17
    (rel 0 (by decide)) (rel 1 (by decide)) (rel 2 (by decide)) (rel 3 (by decide)) (rel 4 (by decide)) (rel 5 (by decide)) (rel 6 (by decide)) (rel 7 (by decide)) (rel 8 (by decide)) (rel 9 (by decide)) (rel 10 (by decide)) (rel 11 (by decide)) (rel 12 (by decide)) (rel 13 (by decide)) (rel 14 (by decide)) (rel 15 (by decide)) (rel 16 (by decide))

/-- A universal exit clock for all natural starts and all integer barriers b>1. -/
theorem exit_seventeen : ExitClock 21 4 17 := by
  intro b n hb
  by_cases h : ∃ k, k ≤ 17 ∧ (orbit k n < b ∨ 21*b < 4*orbit k n)
  · exact h
  · exfalso
    apply no_band_seventeen (n := n) hb
    intro k hk
    by_cases hl : orbit k n < b
    · exact False.elim (h ⟨k,hk,Or.inl hl⟩)
    · by_cases hu : 21*b < 4*orbit k n
      · exact False.elim (h ⟨k,hk,Or.inr hu⟩)
      · omega

theorem rejection_seventeen {b n : Nat} (hb : 1 < b) :
    intervalCheck b (21*b/4) 17 n = false := by
  by_cases ht : intervalCheck b (21*b/4) 17 n = true
  · exfalso
    have hs := (intervalCheck_iff b (21*b/4) 17 n).mp ht
    apply no_band_seventeen (n := n) hb
    intro k hk
    have := hs k hk
    omega
  · cases he : intervalCheck b (21*b/4) 17 n <;> simp_all

/-- One trace witnesses sharpness both at ratio 21/4 and at ratio 51/10. -/
theorem clock_sharpness :
    intervalCheck 379 (21*379/4) 16 1010 = true ∧
    intervalCheck 379 (51*379/10) 16 1010 = true ∧ orbit 17 1010 = 361 := by decide

theorem exit_fifty_one_tenths : ExitClock 51 10 17 := by
  intro b n hb
  obtain ⟨k,hk,hl | hu⟩ := exit_seventeen b n hb
  · exact ⟨k,hk,Or.inl hl⟩
  · exact ⟨k,hk,Or.inr (by omega)⟩

theorem no_clock_sixteen : ¬ ExitClock 21 4 16 := by
  intro h
  have hc := (intervalCheck_iff 379 (21*379/4) 16 1010).mp clock_sharpness.1
  exact no_band_through (b := 379) (n := 1010) h (by decide) (fun k hk => by have := hc k hk; omega)

/-- Hypothetical lower-surviving orbits have a high visit in every 18-point window. -/
theorem high_window {b n : Nat} (hb : 1 < b) (h : Kernel b n) (t : Nat) :
    ∃ s, t ≤ s ∧ s ≤ t+17 ∧ 21*b < 4*orbit s n :=
  BandClock.high_window exit_seventeen hb h t

theorem finite_survival_witnesses {b n : Nat} (hb : 1 < b) (N : Nat)
    (h : Survives b (18*N-1) n) :
    ∃ f : Fin N → Nat,
      (∀ q, f q < 18*N ∧ 21*b < 4*orbit (f q) n) ∧
      (∀ a c, f a = f c → a = c) :=
  BandClock.finite_survival_witnesses exit_seventeen hb N h

theorem anchor_one_control : intervalCheck 1 (21/4) 100 1 = true := by decide

end Collatz.Exploration.WiderBandClock
