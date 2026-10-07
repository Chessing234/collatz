import Collatz.Exploration.BarrierKernel

/-!
# A short affine lower bound on excursions from an orbit floor

This addresses the attained minimum of an arbitrary failed positive orbit,
not just a cycle minimum. A corridor hypothesis forces four odd expansions
and three halvings before a fourth expansion reaches (81m+85)/16.
Small inputs are rejected directly. No existence of a nontrivial floor,
convergence theorem, or priority in the mathematical literature is claimed.
-/
namespace Collatz.Exploration.FloorExcursion
open BarrierKernel OrbitFloor

/-- A state below twice the anchor must be odd if its next state clears it. -/
theorem odd_of_low_state {b n : Nat} (hb : 0 < b)
    (hn : n < 2*b) (hs : b ≤ step n) : n%2 = 1 := by
  have hz : n ≠ 0 := by intro he; subst n; simp at hs; omega
  by_cases he : n%2 = 0
  · simp only [step, if_neg hz, if_pos he] at hs
    omega
  · omega

/-- An upper cap forces a sufficiently high state to be even. -/
theorem even_of_high_state {n u : Nat} (hn : u < 3*n+1)
    (hs : step n ≤ u) : n%2 = 0 := by
  by_cases hz : n = 0
  · subst n; rfl
  · by_cases he : n%2 = 0
    · exact he
    · simp only [step, if_neg hz, if_neg he] at hs
      omega

theorem odd_step {n : Nat} (hn : n%2 = 1) : step n = 3*n+1 := by
  have hz : n ≠ 0 := by omega
  simp only [step, if_neg hz, if_neg (by omega : ¬ n%2 = 0)]

theorem even_step {n : Nat} (hn : n%2 = 0) : step n = n/2 := by
  by_cases hz : n = 0
  · subst n; rfl
  · simp only [step, if_neg hz, if_pos hn]

/-- The small-input exceptions fail the floor condition within eight steps. -/
theorem small_floor_rejection {m : Nat} (hm : 1 < m) (hsmall : m < 6) :
    ¬ Survives m 8 m := by
  have he : m = 2 ∨ m = 3 ∨ m = 4 ∨ m = 5 := by omega
  intro h
  rcases he with rfl | rfl | rfl | rfl
  · have := h 1 (by decide); change 2 ≤ 1 at this; omega
  · have := h 6 (by decide); change 3 ≤ 2 at this; omega
  · have := h 1 (by decide); change 4 ≤ 2 at this; omega
  · have := h 3 (by decide); change 5 ≤ 4 at this; omega

/-- Eight-step survival forces one of two exact affine excursions. -/
theorem finite_excursion_dichotomy {m : Nat} (hm : 1 < m)
    (hfloor : Survives m 8 m) :
    4*orbit 5 m = 27*m+19 ∨ 16*orbit 8 m = 81*m+85 := by
  by_cases hsmall : m < 6
  · exact False.elim (small_floor_rejection hm hsmall hfloor)
  · have hlarge : 6 ≤ m := by omega
    have lower1 := hfloor 1 (by decide)
    have lower3 := hfloor 3 (by decide)
    have lower6 := hfloor 6 (by decide)
    have lower8 := hfloor 8 (by decide)
    have transition (j : Nat) : orbit (j+1) m = step (orbit j m) := by
      rw [orbit_succ_steps, orbit_step_commute]
    have mOdd : m%2 = 1 := odd_of_low_state (b := m)
      (by omega) (by omega) (by simpa [orbit] using lower1)
    have h0 : step m = 3*m+1 := odd_step mOdd
    have value1 : orbit 1 m = 3*m+1 := by simpa [orbit] using h0
    have h1even : (orbit 1 m)%2 = 0 := by rw [value1]; omega
    have value2 : 2*orbit 2 m = 3*m+1 := by
      rw [transition 1, even_step h1even, value1]
      omega
    have h2odd : (orbit 2 m)%2 = 1 := odd_of_low_state (b := m) (by omega)
      (by omega) (by rw [← transition 2]; exact lower3)
    have value3 : orbit 3 m = 3*orbit 2 m+1 := by rw [transition 2, odd_step h2odd]
    have h3even : (orbit 3 m)%2 = 0 := by rw [value3]; omega
    have value4 : 4*orbit 4 m = 9*m+5 := by
      rw [transition 3, even_step h3even]
      omega
    by_cases h4even : (orbit 4 m)%2 = 0
    · right
      have value5 : 8*orbit 5 m = 9*m+5 := by
        rw [transition 4, even_step h4even]
        omega
      have h5odd : (orbit 5 m)%2 = 1 := odd_of_low_state (b := m) (by omega)
        (by omega) (by rw [← transition 5]; exact lower6)
      have value6 : orbit 6 m = 3*orbit 5 m+1 := by rw [transition 5, odd_step h5odd]
      have h6even : (orbit 6 m)%2 = 0 := by rw [value6]; omega
      have value7 : 16*orbit 7 m = 27*m+23 := by
        rw [transition 6, even_step h6even]
        omega
      have h7odd : (orbit 7 m)%2 = 1 := odd_of_low_state (b := m) (by omega)
        (by omega) (by rw [← transition 7]; exact lower8)
      rw [transition 7, odd_step h7odd]
      omega
    · left
      have h4odd : (orbit 4 m)%2 = 1 := by omega
      rw [transition 4, odd_step h4odd]
      omega

/-- Some point in the first eight steps reaches the affine excursion bound.
Only the lower bounds through that same finite window are assumed. -/
theorem finite_excursion {m : Nat} (hm : 1 < m) (hfloor : Survives m 8 m) :
    ∃ k, k ≤ 8 ∧ 81*m+85 ≤ 16*orbit k m := by
  rcases finite_excursion_dichotomy hm hfloor with he | hl
  · exact ⟨5, by decide, by omega⟩
  · exact ⟨8, by decide, by omega⟩

/-- An actual orbit floor has the same short-prefix excursion. -/
theorem floor_excursion {m : Nat} (h : Floor m) :
    ∃ k, k ≤ 8 ∧ 81*m+85 ≤ 16*orbit k m :=
  finite_excursion h.1 (fun k _ => h.2 k)

/-- In particular, an orbit floor greater than one exceeds five times itself. -/
theorem floor_exceeds_five {m : Nat} (h : Floor m) :
    ∃ k, k ≤ 8 ∧ 5*m < orbit k m := by
  obtain ⟨k,hk,hv⟩ := floor_excursion h
  exact ⟨k,hk,by omega⟩

/-- The ordinary starting-point corridor [m,5m] fails within eight steps. -/
theorem five_corridor_rejection {m : Nat} (hm : 1 < m) :
    intervalCheck m (5*m) 8 m = false := by
  by_cases h : intervalCheck m (5*m) 8 m = true
  · have hw := (intervalCheck_iff m (5*m) 8 m).mp h
    obtain ⟨k,hk,hv⟩ := finite_excursion hm (fun j hj => (hw j hj).1)
    have hu := (hw k hk).2
    omega
  · cases he : intervalCheck m (5*m) 8 m <;> simp_all

/-- An infinite arithmetic family realizes the forced trace exactly. -/
theorem sharp_family_trace (q : Nat) :
    orbit 1 (32*q+27) = 96*q+82 ∧
    orbit 2 (32*q+27) = 48*q+41 ∧
    orbit 3 (32*q+27) = 144*q+124 ∧
    orbit 4 (32*q+27) = 72*q+62 ∧
    orbit 5 (32*q+27) = 36*q+31 ∧
    orbit 6 (32*q+27) = 108*q+94 ∧
    orbit 7 (32*q+27) = 54*q+47 ∧
    orbit 8 (32*q+27) = 162*q+142 := by
  have h1 : step (32*q+27) = 96*q+82 := by rw [odd_step (by omega)]; omega
  have h2 : step (96*q+82) = 48*q+41 := by rw [even_step (by omega)]; omega
  have h3 : step (48*q+41) = 144*q+124 := by rw [odd_step (by omega)]; omega
  have h4 : step (144*q+124) = 72*q+62 := by rw [even_step (by omega)]; omega
  have h5 : step (72*q+62) = 36*q+31 := by rw [even_step (by omega)]; omega
  have h6 : step (36*q+31) = 108*q+94 := by rw [odd_step (by omega)]; omega
  have h7 : step (108*q+94) = 54*q+47 := by rw [even_step (by omega)]; omega
  have h8 : step (54*q+47) = 162*q+142 := by rw [odd_step (by omega)]; omega
  simp [orbit, h1,h2,h3,h4,h5,h6,h7,h8]

/-- Sharpness concerns finite survival, not the existence of an actual floor.
Every member survives eight steps, attains equality at eight, and has no
earlier point attaining the excursion bound. -/
theorem sharp_family (q : Nat) :
    Survives (32*q+27) 8 (32*q+27) ∧
    16*orbit 8 (32*q+27) = 81*(32*q+27)+85 ∧
    ∀ k, k < 8 → 16*orbit k (32*q+27) < 81*(32*q+27)+85 := by
  obtain ⟨v1,v2,v3,v4,v5,v6,v7,v8⟩ := sharp_family_trace q
  refine ⟨?_, by rw [v8]; omega, ?_⟩
  · intro k hk
    have he : k=0 ∨ k=1 ∨ k=2 ∨ k=3 ∨ k=4 ∨ k=5 ∨ k=6 ∨ k=7 ∨ k=8 := by omega
    rcases he with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;>
      simp only [orbit_zero_steps, v1,v2,v3,v4,v5,v6,v7,v8] <;> omega
  · intro k hk
    have he : k=0 ∨ k=1 ∨ k=2 ∨ k=3 ∨ k=4 ∨ k=5 ∨ k=6 ∨ k=7 := by omega
    rcases he with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;>
      simp only [orbit_zero_steps, v1,v2,v3,v4,v5,v6,v7] <;> omega

/-- Neither increasing the additive constant nor shortening this horizon
preserves the finite-survival theorem. The witness is the ordinary start 27. -/
theorem sharpness_controls : Survives 27 8 27 ∧
    (∀ k, k≤8 → 16*orbit k 27 < 81*27+86) ∧
    (∀ k, k≤7 → 16*orbit k 27 < 81*27+85) := by
  have h := sharp_family 0
  simp only [Nat.mul_zero, Nat.zero_add] at h
  obtain ⟨hs,he,hprev⟩ := h
  refine ⟨hs, ?_, fun k hk => hprev k (by omega)⟩
  intro k hk
  by_cases h8 : k=8
  · subst k; omega
  · have hp := hprev k (by omega)
    omega

/-- Every positive failed orbit attains a floor and then makes this excursion. -/
theorem failure_excursion {n : Nat} (hp : 0 < n) (hf : ¬ Converges n) :
    ∃ j k, Floor (orbit j n) ∧ k ≤ 8 ∧
      81*orbit j n+85 ≤ 16*orbit (k+j) n := by
  obtain ⟨j,hj⟩ := floor_of_failure hp hf
  obtain ⟨k,hk,hv⟩ := floor_excursion hj
  refine ⟨j,k,hj,hk,?_⟩
  rw [orbit_add]
  exact hv

/-- No entire ordinary orbit can stay in [b,5b] above the trivial minimum.
Taking an attained minimum handles an arbitrary initial point in the band. -/
theorem no_five_band {b n : Nat} (hb : 1 < b) :
    ¬ (∀ k, b ≤ orbit k n ∧ orbit k n ≤ 5*b) := by
  intro hband
  obtain ⟨j,hmin⟩ := attained_minimum n
  have hfloor : Floor (orbit j n) :=
    ⟨by have := (hband j).1; omega, minimum_future hmin⟩
  obtain ⟨k,_,hpeak⟩ := floor_exceeds_five hfloor
  have hup := (hband (k+j)).2
  rw [orbit_add] at hup
  have hlo := (hband j).1
  omega

/-- Exiting this band means either descending below b or exceeding 5b;
the theorem deliberately retains both alternatives. -/
theorem five_band_exit (b n : Nat) (hb : 1 < b) :
    ∃ k, orbit k n < b ∨ 5*b < orbit k n := by
  by_cases he : ∃ k, orbit k n < b ∨ 5*b < orbit k n
  · exact he
  · exfalso
    apply no_five_band (n := n) hb
    intro k
    by_cases hl : orbit k n < b
    · exact False.elim (he ⟨k,Or.inl hl⟩)
    · by_cases hu : 5*b < orbit k n
      · exact False.elim (he ⟨k,Or.inr hu⟩)
      · omega

end Collatz.Exploration.FloorExcursion
