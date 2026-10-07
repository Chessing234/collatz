import Collatz.Exploration.ElevenHalvesClock

namespace Collatz.Exploration.ElevenHalvesFamily
open BarrierKernel BandClock

def source (q : Nat) := 262144*q+201714
def barrier (q : Nat) := 93312*q+71803
def peak (q : Nat) := 497664*q+382948

/-- Doubling is one ordinary even step, including the totalized zero input. -/
theorem step_double (z : Nat) : step (2*z) = z := by
  by_cases hz : z = 0
  · simp [hz]
  · have hp : 2*z ≠ 0 := by omega
    have hm : (2*z)%2 = 0 := by omega
    simp [step,hp,hm]

/-- One odd step on an affine class with fixed odd parity. -/
theorem step_odd_affine {a c : Nat} (q : Nat) (ha : a%2 = 0)
    (hc : c%2 = 1) :
    step (a*q+c) = (3*a)*q+(3*c+1) := by
  have hp : 0 < a*q+c := by omega
  have hm : (a*q+c)%2 = 1 := by simp [Nat.add_mod,Nat.mul_mod,ha,hc]
  simp only [step,Nat.ne_of_gt hp,if_false,hm,Nat.one_ne_zero,Nat.mul_add,← Nat.mul_assoc,Nat.add_assoc]

/-- Componentwise affine order uses monotonicity, with no large-coefficient elimination. -/
theorem affine_le {a c A C q : Nat} (ha : a ≤ A) (hc : c ≤ C) : a*q+c ≤ A*q+C :=
  Nat.add_le_add (Nat.mul_le_mul_right q ha) hc

/-- Exact ordinary affine trace for an infinite arithmetic progression. -/
theorem family_trace (q : Nat) :
    orbit 0 (source q) = 262144*q+201714 ∧
    orbit 1 (source q) = 131072*q+100857 ∧
    orbit 2 (source q) = 393216*q+302572 ∧
    orbit 3 (source q) = 196608*q+151286 ∧
    orbit 4 (source q) = 98304*q+75643 ∧
    orbit 5 (source q) = 294912*q+226930 ∧
    orbit 6 (source q) = 147456*q+113465 ∧
    orbit 7 (source q) = 442368*q+340396 ∧
    orbit 8 (source q) = 221184*q+170198 ∧
    orbit 9 (source q) = 110592*q+85099 ∧
    orbit 10 (source q) = 331776*q+255298 ∧
    orbit 11 (source q) = 165888*q+127649 ∧
    orbit 12 (source q) = 497664*q+382948 ∧
    orbit 13 (source q) = 248832*q+191474 ∧
    orbit 14 (source q) = 124416*q+95737 ∧
    orbit 15 (source q) = 373248*q+287212 ∧
    orbit 16 (source q) = 186624*q+143606 ∧
    orbit 17 (source q) = 93312*q+71803 ∧
    orbit 18 (source q) = 279936*q+215410 ∧
    orbit 19 (source q) = 139968*q+107705 ∧
    orbit 20 (source q) = 419904*q+323116 ∧
    orbit 21 (source q) = 209952*q+161558 ∧
    orbit 22 (source q) = 104976*q+80779 ∧
    orbit 23 (source q) = 314928*q+242338 ∧
    orbit 24 (source q) = 157464*q+121169 ∧
    orbit 25 (source q) = 472392*q+363508 ∧
    orbit 26 (source q) = 236196*q+181754 ∧
    orbit 27 (source q) = 118098*q+90877 ∧
    orbit 28 (source q) = 354294*q+272632 ∧
    orbit 29 (source q) = 177147*q+136316 := by
  have h0 : orbit 0 (source q) = 262144*q+201714 := rfl
  have h1 : orbit 1 (source q) = 131072*q+100857 := by
    rw [orbit_succ_steps,orbit_step_commute,h0]
    have he : 262144*q+201714 = 2*(131072*q+100857) := by
      simp only [Nat.mul_add,← Nat.mul_assoc,Nat.reduceMul]
    rw [he,step_double]
  have h2 : orbit 2 (source q) = 393216*q+302572 := by
    rw [orbit_succ_steps,orbit_step_commute,h1]
    simpa only [Nat.reduceMul,Nat.reduceAdd] using
      step_odd_affine (a := 131072) (c := 100857) q (by decide) (by decide)
  have h3 : orbit 3 (source q) = 196608*q+151286 := by
    rw [orbit_succ_steps,orbit_step_commute,h2]
    have he : 393216*q+302572 = 2*(196608*q+151286) := by
      simp only [Nat.mul_add,← Nat.mul_assoc,Nat.reduceMul]
    rw [he,step_double]
  have h4 : orbit 4 (source q) = 98304*q+75643 := by
    rw [orbit_succ_steps,orbit_step_commute,h3]
    have he : 196608*q+151286 = 2*(98304*q+75643) := by
      simp only [Nat.mul_add,← Nat.mul_assoc,Nat.reduceMul]
    rw [he,step_double]
  have h5 : orbit 5 (source q) = 294912*q+226930 := by
    rw [orbit_succ_steps,orbit_step_commute,h4]
    simpa only [Nat.reduceMul,Nat.reduceAdd] using
      step_odd_affine (a := 98304) (c := 75643) q (by decide) (by decide)
  have h6 : orbit 6 (source q) = 147456*q+113465 := by
    rw [orbit_succ_steps,orbit_step_commute,h5]
    have he : 294912*q+226930 = 2*(147456*q+113465) := by
      simp only [Nat.mul_add,← Nat.mul_assoc,Nat.reduceMul]
    rw [he,step_double]
  have h7 : orbit 7 (source q) = 442368*q+340396 := by
    rw [orbit_succ_steps,orbit_step_commute,h6]
    simpa only [Nat.reduceMul,Nat.reduceAdd] using
      step_odd_affine (a := 147456) (c := 113465) q (by decide) (by decide)
  have h8 : orbit 8 (source q) = 221184*q+170198 := by
    rw [orbit_succ_steps,orbit_step_commute,h7]
    have he : 442368*q+340396 = 2*(221184*q+170198) := by
      simp only [Nat.mul_add,← Nat.mul_assoc,Nat.reduceMul]
    rw [he,step_double]
  have h9 : orbit 9 (source q) = 110592*q+85099 := by
    rw [orbit_succ_steps,orbit_step_commute,h8]
    have he : 221184*q+170198 = 2*(110592*q+85099) := by
      simp only [Nat.mul_add,← Nat.mul_assoc,Nat.reduceMul]
    rw [he,step_double]
  have h10 : orbit 10 (source q) = 331776*q+255298 := by
    rw [orbit_succ_steps,orbit_step_commute,h9]
    simpa only [Nat.reduceMul,Nat.reduceAdd] using
      step_odd_affine (a := 110592) (c := 85099) q (by decide) (by decide)
  have h11 : orbit 11 (source q) = 165888*q+127649 := by
    rw [orbit_succ_steps,orbit_step_commute,h10]
    have he : 331776*q+255298 = 2*(165888*q+127649) := by
      simp only [Nat.mul_add,← Nat.mul_assoc,Nat.reduceMul]
    rw [he,step_double]
  have h12 : orbit 12 (source q) = 497664*q+382948 := by
    rw [orbit_succ_steps,orbit_step_commute,h11]
    simpa only [Nat.reduceMul,Nat.reduceAdd] using
      step_odd_affine (a := 165888) (c := 127649) q (by decide) (by decide)
  have h13 : orbit 13 (source q) = 248832*q+191474 := by
    rw [orbit_succ_steps,orbit_step_commute,h12]
    have he : 497664*q+382948 = 2*(248832*q+191474) := by
      simp only [Nat.mul_add,← Nat.mul_assoc,Nat.reduceMul]
    rw [he,step_double]
  have h14 : orbit 14 (source q) = 124416*q+95737 := by
    rw [orbit_succ_steps,orbit_step_commute,h13]
    have he : 248832*q+191474 = 2*(124416*q+95737) := by
      simp only [Nat.mul_add,← Nat.mul_assoc,Nat.reduceMul]
    rw [he,step_double]
  have h15 : orbit 15 (source q) = 373248*q+287212 := by
    rw [orbit_succ_steps,orbit_step_commute,h14]
    simpa only [Nat.reduceMul,Nat.reduceAdd] using
      step_odd_affine (a := 124416) (c := 95737) q (by decide) (by decide)
  have h16 : orbit 16 (source q) = 186624*q+143606 := by
    rw [orbit_succ_steps,orbit_step_commute,h15]
    have he : 373248*q+287212 = 2*(186624*q+143606) := by
      simp only [Nat.mul_add,← Nat.mul_assoc,Nat.reduceMul]
    rw [he,step_double]
  have h17 : orbit 17 (source q) = 93312*q+71803 := by
    rw [orbit_succ_steps,orbit_step_commute,h16]
    have he : 186624*q+143606 = 2*(93312*q+71803) := by
      simp only [Nat.mul_add,← Nat.mul_assoc,Nat.reduceMul]
    rw [he,step_double]
  have h18 : orbit 18 (source q) = 279936*q+215410 := by
    rw [orbit_succ_steps,orbit_step_commute,h17]
    simpa only [Nat.reduceMul,Nat.reduceAdd] using
      step_odd_affine (a := 93312) (c := 71803) q (by decide) (by decide)
  have h19 : orbit 19 (source q) = 139968*q+107705 := by
    rw [orbit_succ_steps,orbit_step_commute,h18]
    have he : 279936*q+215410 = 2*(139968*q+107705) := by
      simp only [Nat.mul_add,← Nat.mul_assoc,Nat.reduceMul]
    rw [he,step_double]
  have h20 : orbit 20 (source q) = 419904*q+323116 := by
    rw [orbit_succ_steps,orbit_step_commute,h19]
    simpa only [Nat.reduceMul,Nat.reduceAdd] using
      step_odd_affine (a := 139968) (c := 107705) q (by decide) (by decide)
  have h21 : orbit 21 (source q) = 209952*q+161558 := by
    rw [orbit_succ_steps,orbit_step_commute,h20]
    have he : 419904*q+323116 = 2*(209952*q+161558) := by
      simp only [Nat.mul_add,← Nat.mul_assoc,Nat.reduceMul]
    rw [he,step_double]
  have h22 : orbit 22 (source q) = 104976*q+80779 := by
    rw [orbit_succ_steps,orbit_step_commute,h21]
    have he : 209952*q+161558 = 2*(104976*q+80779) := by
      simp only [Nat.mul_add,← Nat.mul_assoc,Nat.reduceMul]
    rw [he,step_double]
  have h23 : orbit 23 (source q) = 314928*q+242338 := by
    rw [orbit_succ_steps,orbit_step_commute,h22]
    simpa only [Nat.reduceMul,Nat.reduceAdd] using
      step_odd_affine (a := 104976) (c := 80779) q (by decide) (by decide)
  have h24 : orbit 24 (source q) = 157464*q+121169 := by
    rw [orbit_succ_steps,orbit_step_commute,h23]
    have he : 314928*q+242338 = 2*(157464*q+121169) := by
      simp only [Nat.mul_add,← Nat.mul_assoc,Nat.reduceMul]
    rw [he,step_double]
  have h25 : orbit 25 (source q) = 472392*q+363508 := by
    rw [orbit_succ_steps,orbit_step_commute,h24]
    simpa only [Nat.reduceMul,Nat.reduceAdd] using
      step_odd_affine (a := 157464) (c := 121169) q (by decide) (by decide)
  have h26 : orbit 26 (source q) = 236196*q+181754 := by
    rw [orbit_succ_steps,orbit_step_commute,h25]
    have he : 472392*q+363508 = 2*(236196*q+181754) := by
      simp only [Nat.mul_add,← Nat.mul_assoc,Nat.reduceMul]
    rw [he,step_double]
  have h27 : orbit 27 (source q) = 118098*q+90877 := by
    rw [orbit_succ_steps,orbit_step_commute,h26]
    have he : 236196*q+181754 = 2*(118098*q+90877) := by
      simp only [Nat.mul_add,← Nat.mul_assoc,Nat.reduceMul]
    rw [he,step_double]
  have h28 : orbit 28 (source q) = 354294*q+272632 := by
    rw [orbit_succ_steps,orbit_step_commute,h27]
    simpa only [Nat.reduceMul,Nat.reduceAdd] using
      step_odd_affine (a := 118098) (c := 90877) q (by decide) (by decide)
  have h29 : orbit 29 (source q) = 177147*q+136316 := by
    rw [orbit_succ_steps,orbit_step_commute,h28]
    have he : 354294*q+272632 = 2*(177147*q+136316) := by
      simp only [Nat.mul_add,← Nat.mul_assoc,Nat.reduceMul]
    rw [he,step_double]
  exact ⟨h0,h1,h2,h3,h4,h5,h6,h7,h8,h9,h10,h11,h12,h13,h14,h15,h16,h17,h18,h19,h20,h21,h22,h23,h24,h25,h26,h27,h28,h29⟩

/-- Even and odd parameters leave the band in opposite directions. -/
theorem exit_directions (t : Nat) :
    orbit 30 (source (2*t)) = 177147*t+68158 ∧
    orbit 30 (source (2*t+1)) = 1062882*t+940390 ∧
    orbit 30 (source (2*t)) < barrier (2*t) ∧
    11*barrier (2*t+1) < 2*orbit 30 (source (2*t+1)) := by
  have he : orbit 29 (source (2*t)) = 354294*t+136316 := by
    have ht := (family_trace (2*t)).2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2
    omega
  have ho : orbit 29 (source (2*t+1)) = 354294*t+313463 := by
    have ht := (family_trace (2*t+1)).2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2
    omega
  have hnextE : orbit 30 (source (2*t)) = 177147*t+68158 := by
    rw [orbit_succ_steps,orbit_step_commute,he]
    have hm : (354294*t+136316)%2 = 0 := by omega
    simp [step,hm]
    omega
  have hnextO : orbit 30 (source (2*t+1)) = 1062882*t+940390 := by
    rw [orbit_succ_steps,orbit_step_commute,ho]
    have hm : (354294*t+313463)%2 = 1 := by omega
    simp [step,hm]
    omega
  refine ⟨hnextE,hnextO,?_,?_⟩ <;> simp only [hnextE,hnextO] <;> dsimp [barrier] <;> omega

/-- Both extrema are attained, and every prefix state lies between them. -/
theorem family_extrema (q : Nat) :
    orbit 17 (source q) = barrier q ∧ orbit 12 (source q) = peak q ∧
    ∀ k, k ≤ 29 → barrier q ≤ orbit k (source q) ∧ orbit k (source q) ≤ peak q := by
  obtain ⟨h0,h1,h2,h3,h4,h5,h6,h7,h8,h9,h10,h11,h12,h13,h14,h15,h16,h17,h18,h19,h20,h21,h22,h23,h24,h25,h26,h27,h28,h29⟩ := family_trace q
  refine ⟨h17,h12,?_⟩
  intro k hk
  have hc : k = 0 ∨ k = 1 ∨ k = 2 ∨ k = 3 ∨ k = 4 ∨ k = 5 ∨ k = 6 ∨ k = 7 ∨ k = 8 ∨ k = 9 ∨ k = 10 ∨ k = 11 ∨ k = 12 ∨ k = 13 ∨ k = 14 ∨ k = 15 ∨ k = 16 ∨ k = 17 ∨ k = 18 ∨ k = 19 ∨ k = 20 ∨ k = 21 ∨ k = 22 ∨ k = 23 ∨ k = 24 ∨ k = 25 ∨ k = 26 ∨ k = 27 ∨ k = 28 ∨ k = 29 := by omega
  rcases hc with h0k | h1k | h2k | h3k | h4k | h5k | h6k | h7k | h8k | h9k | h10k | h11k | h12k | h13k | h14k | h15k | h16k | h17k | h18k | h19k | h20k | h21k | h22k | h23k | h24k | h25k | h26k | h27k | h28k | h29k <;> subst k <;>
    simp only [h0,h1,h2,h3,h4,h5,h6,h7,h8,h9,h10,h11,h12,h13,h14,h15,h16,h17,h18,h19,h20,h21,h22,h23,h24,h25,h26,h27,h28,h29] <;> clear h0 h1 h2 h3 h4 h5 h6 h7 h8 h9 h10 h11 h12 h13 h14 h15 h16 h17 h18 h19 h20 h21 h22 h23 h24 h25 h26 h27 h28 h29 <;> dsimp [barrier,peak] <;> constructor <;> apply affine_le <;> decide

/-- The finite-prefix width approaches 16/3 from below, with exact defect four. -/
theorem peak_identity (q : Nat) : 3*peak q+4 = 16*barrier q := by
  simp only [peak,barrier,Nat.mul_add,← Nat.mul_assoc,Nat.add_assoc,Nat.reduceMul,Nat.reduceAdd]

/-- The whole family survives strictly inside the ratio-16/3 upper bound. -/
theorem family_bounds (q : Nat) :
    ∀ k, k ≤ 29 → barrier q ≤ orbit k (source q) ∧ 3*orbit k (source q) < 16*barrier q := by
  intro k hk
  obtain ⟨hl,hu⟩ := (family_extrema q).2.2 k hk
  refine ⟨hl,?_⟩
  rw [← peak_identity q]
  have hinc : 3*peak q < 3*peak q+4 :=
    Nat.lt_of_lt_of_le (Nat.lt_succ_self _) (Nat.add_le_add_left (by decide : 1 ≤ 4) _)
  exact Nat.lt_of_le_of_lt (Nat.mul_le_mul_left 3 hu) hinc

/-- The explicit extremal witness gives a sharp clock over a rational-width interval. -/
theorem plateau_exact {P Q : Nat} (hQ : 0 < Q)
    (hl : 382948*Q ≤ 71803*P) (hu : 2*P ≤ 11*Q) :
    ExitClock P Q 30 ∧ ¬ ExitClock P Q 29 := by
  refine ⟨narrower_ratio ElevenHalvesClock.exit_thirty hQ (by simpa only [Nat.mul_comm] using hu),?_⟩
  intro hc
  have hb : 1 < barrier 0 := by decide
  apply no_band_through (b := barrier 0) (n := source 0) hc hb
  intro k hk
  obtain ⟨hbounds,hwidth⟩ := (family_extrema 0).2.2 k hk
  have h1 := Nat.mul_le_mul_left Q hwidth
  have h2 : Q*peak 0 ≤ P*barrier 0 := by
    simpa only [peak,barrier,Nat.mul_zero,Nat.zero_add,Nat.mul_comm] using hl
  exact ⟨hbounds,Nat.le_trans h1 h2⟩

/-- In particular every rational width from 16/3 through 11/2 has clock thirty. -/
theorem plateau {P Q : Nat} (hQ : 0 < Q) (hl : 16*Q ≤ 3*P)
    (hu : 2*P ≤ 11*Q) : ExitClock P Q 30 ∧ ¬ ExitClock P Q 29 := by
  have hc : 3*(382948*Q) ≤ 3*(71803*P) := calc
    3*(382948*Q) = (3*382948)*Q := by ac_rfl
    _ ≤ (16*71803)*Q := Nat.mul_le_mul_right Q (by decide)
    _ = 71803*(16*Q) := by ac_rfl
    _ ≤ 71803*(3*P) := Nat.mul_le_mul_left 71803 hl
    _ = 3*(71803*P) := by ac_rfl
  exact plateau_exact hQ (Nat.le_of_mul_le_mul_left hc (by decide)) hu

/-- Every family member first exits the ratio-11/2 band exactly at time thirty. -/
theorem family_first_exit (q : Nat) :
    (orbit 30 (source q) < barrier q ∨ 11*barrier q < 2*orbit 30 (source q)) ∧
    ∀ k, k < 30 → barrier q ≤ orbit k (source q) ∧ 2*orbit k (source q) ≤ 11*barrier q := by
  have hb : 1 < barrier q := by dsimp [barrier]; omega
  have hp : ∀ k, k < 30 → barrier q ≤ orbit k (source q) ∧ 2*orbit k (source q) ≤ 11*barrier q := by
    intro k hk
    obtain ⟨hl,hu⟩ := (family_extrema q).2.2 k (by omega)
    have hmax : 2*peak q ≤ 11*barrier q := by
      simp only [peak,barrier,Nat.mul_add,← Nat.mul_assoc,Nat.reduceMul]
      exact affine_le (by decide) (by decide)
    exact ⟨hl,Nat.le_trans (Nat.mul_le_mul_left 2 hu) hmax⟩
  refine ⟨?_,hp⟩
  obtain ⟨k,hk,hl | hu⟩ := ElevenHalvesClock.exit_thirty (barrier q) (source q) hb
  · by_cases he : k = 30
    · subst k; exact Or.inl hl
    · have := (hp k (by omega)).1
      omega
  · by_cases he : k = 30
    · subst k; exact Or.inr hu
    · have := (hp k (by omega)).2
      omega

end Collatz.Exploration.ElevenHalvesFamily
