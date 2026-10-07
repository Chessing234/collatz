import Collatz.Exploration.FiveBandClock
import Collatz.Exploration.BandClock
import Collatz.Exploration.ElevenHalvesArithmetic

/-! A wider sharp band clock, keeping the descent/growth alternative explicit. -/
namespace Collatz.Exploration.ElevenHalvesClock
open BarrierKernel BandClock

/-- The inclusive ratio-11/2 band cannot contain thirty-one sampled states. -/
theorem no_band_thirty {b n : Nat} (hb : 1 < b)
    (hs : ∀ k, k ≤ 30 → b ≤ orbit k n ∧ 2*orbit k n ≤ 11*b) : False := by
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
  have bounds18 := hs 18 (by decide)
  have bounds19 := hs 19 (by decide)
  have bounds20 := hs 20 (by decide)
  have bounds21 := hs 21 (by decide)
  have bounds22 := hs 22 (by decide)
  have bounds23 := hs 23 (by decide)
  have bounds24 := hs 24 (by decide)
  have bounds25 := hs 25 (by decide)
  have bounds26 := hs 26 (by decide)
  have bounds27 := hs 27 (by decide)
  have bounds28 := hs 28 (by decide)
  have bounds29 := hs 29 (by decide)
  have bounds30 := hs 30 (by decide)
  have rel (k : Nat) (hk : k ≤ 29) :
      (2*orbit (k+1) n = orbit k n ∧ (orbit k n)%2 = 0) ∨
      (orbit (k+1) n = 3*orbit k n+1 ∧ (orbit k n)%2 = 1) := by
    have hp : 0 < orbit k n := by have := hs k (by omega); omega
    have h := FiveBandClock.step_relation hp
    rw [← orbit_step_commute, ← orbit_succ_steps] at h
    exact h
  exact ElevenHalvesArithmetic.impossible_trace b (orbit 0 n) (orbit 1 n) (orbit 2 n) (orbit 3 n) (orbit 4 n) (orbit 5 n) (orbit 6 n) (orbit 7 n) (orbit 8 n) (orbit 9 n) (orbit 10 n) (orbit 11 n) (orbit 12 n) (orbit 13 n) (orbit 14 n) (orbit 15 n) (orbit 16 n) (orbit 17 n) (orbit 18 n) (orbit 19 n) (orbit 20 n) (orbit 21 n) (orbit 22 n) (orbit 23 n) (orbit 24 n) (orbit 25 n) (orbit 26 n) (orbit 27 n) (orbit 28 n) (orbit 29 n) (orbit 30 n) hb
    bounds0 bounds1 bounds2 bounds3 bounds4 bounds5 bounds6 bounds7 bounds8 bounds9 bounds10 bounds11 bounds12 bounds13 bounds14 bounds15 bounds16 bounds17 bounds18 bounds19 bounds20 bounds21 bounds22 bounds23 bounds24 bounds25 bounds26 bounds27 bounds28 bounds29 bounds30
    (rel 0 (by decide)) (rel 1 (by decide)) (rel 2 (by decide)) (rel 3 (by decide)) (rel 4 (by decide)) (rel 5 (by decide)) (rel 6 (by decide)) (rel 7 (by decide)) (rel 8 (by decide)) (rel 9 (by decide)) (rel 10 (by decide)) (rel 11 (by decide)) (rel 12 (by decide)) (rel 13 (by decide)) (rel 14 (by decide)) (rel 15 (by decide)) (rel 16 (by decide)) (rel 17 (by decide)) (rel 18 (by decide)) (rel 19 (by decide)) (rel 20 (by decide)) (rel 21 (by decide)) (rel 22 (by decide)) (rel 23 (by decide)) (rel 24 (by decide)) (rel 25 (by decide)) (rel 26 (by decide)) (rel 27 (by decide)) (rel 28 (by decide)) (rel 29 (by decide))

/-- A universal exit clock for all natural starts and all integer barriers b>1. -/
theorem exit_thirty : ExitClock 11 2 30 := by
  intro b n hb
  by_cases h : ∃ k, k ≤ 30 ∧ (orbit k n < b ∨ 11*b < 2*orbit k n)
  · exact h
  · exfalso
    apply no_band_thirty (n := n) hb
    intro k hk
    by_cases hl : orbit k n < b
    · exact False.elim (h ⟨k,hk,Or.inl hl⟩)
    · by_cases hu : 11*b < 2*orbit k n
      · exact False.elim (h ⟨k,hk,Or.inr hu⟩)
      · omega

theorem rejection_thirty {b n : Nat} (hb : 1 < b) :
    intervalCheck b (11*b/2) 30 n = false := by
  by_cases ht : intervalCheck b (11*b/2) 30 n = true
  · exfalso
    have hs := (intervalCheck_iff b (11*b/2) 30 n).mp ht
    apply no_band_thirty (n := n) hb
    intro k hk
    have := hs k hk
    omega
  · cases he : intervalCheck b (11*b/2) 30 n <;> simp_all

/-- An ordinary integer trace attains the thirty-step exit bound. -/
theorem clock_sharpness :
    intervalCheck 71803 (11*71803/2) 29 201714 = true ∧ orbit 30 201714 < 71803 := by decide

theorem no_clock_twenty_nine : ¬ ExitClock 11 2 29 := by
  intro h
  have hc := (intervalCheck_iff 71803 (11*71803/2) 29 201714).mp clock_sharpness.1
  exact no_band_through (b := 71803) (n := 201714) h (by decide) (fun k hk => by have := hc k hk; omega)

/-- Hypothetical lower-surviving orbits have a high visit in every 31-point window. -/
theorem high_window {b n : Nat} (hb : 1 < b) (h : Kernel b n) (t : Nat) :
    ∃ s, t ≤ s ∧ s ≤ t+30 ∧ 11*b < 2*orbit s n :=
  BandClock.high_window exit_thirty hb h t

theorem finite_survival_witnesses {b n : Nat} (hb : 1 < b) (N : Nat)
    (h : Survives b (31*N-1) n) :
    ∃ f : Fin N → Nat,
      (∀ q, f q < 31*N ∧ 11*b < 2*orbit (f q) n) ∧
      (∀ a c, f a = f c → a = c) :=
  BandClock.finite_survival_witnesses exit_thirty hb N h

theorem anchor_one_control : intervalCheck 1 (11/2) 100 1 = true := by decide

end Collatz.Exploration.ElevenHalvesClock
