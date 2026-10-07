import Collatz.Exploration.FloorExcursion

/-! Odd-denominator rational Collatz dynamics encoded by natural numerators.
With a fixed odd denominator d, the odd update on numerators is 3n+d;
the even update halves an even numerator. All comparisons below are exact
cross-multiplied rational comparisons. This map is distinct from step. -/
namespace Collatz.Exploration.RationalBandObstruction

def denominatorStep (d n : Nat) : Nat :=
  if n % 2 = 0 then n / 2 else 3*n+d

def denominatorOrbit (d : Nat) : Nat → Nat → Nat
  | 0, n => n
  | k+1, n => denominatorStep d (denominatorOrbit d k n)

/-- Denominator one recovers the original integer map, including zero. -/
theorem denominator_one_step (n : Nat) : denominatorStep 1 n = step n := by
  by_cases hz : n = 0
  · subst n; decide
  · simp [denominatorStep, step, hz]

theorem denominator_one_orbit (k n : Nat) : denominatorOrbit 1 k n = orbit k n := by
  induction k with
  | zero => rfl
  | succ k ih =>
    simp only [denominatorOrbit, ih, denominator_one_step, orbit_succ_steps]
    exact (orbit_step_commute k n).symm

/-- The branch word OEOEEOEE has this affine identity for every fixed offset. -/
theorem word_identity (d x0 x1 x2 x3 x4 x5 x6 x7 x8 : Nat)
    (h0 : x1 = 3*x0+d) (h1 : 2*x2 = x1)
    (h2 : x3 = 3*x2+d) (h3 : 2*x4 = x3) (h4 : 2*x5 = x4)
    (h5 : x6 = 3*x5+d) (h6 : 2*x7 = x6) (h7 : 2*x8 = x7) :
    32*x8 = 27*x0+23*d := by omega

/-- Closure in this word forces the encoding denominator to be divisible by five. -/
theorem closure_denominator (d n : Nat) (h : 32*n = 27*n+23*d) : d%5 = 0 := by
  omega

/-- This word's closed encodings are exactly multiples of the primitive pair (5,23). -/
theorem closure_classification (d n : Nat) (h : 32*n = 27*n+23*d) :
    ∃ t, d = 5*t ∧ n = 23*t := by
  have hd := closure_denominator d n h
  refine ⟨d/5, ?_, ?_⟩ <;> omega

/-- The rational 23/5 cycle, uniformly encoded at every odd scale. -/
theorem scaled_transitions (t : Nat) (ht : t%2 = 1) :
    denominatorStep (5*t) (23*t) = 74*t ∧
    denominatorStep (5*t) (74*t) = 37*t ∧
    denominatorStep (5*t) (37*t) = 116*t ∧
    denominatorStep (5*t) (116*t) = 58*t ∧
    denominatorStep (5*t) (58*t) = 29*t ∧
    denominatorStep (5*t) (29*t) = 92*t ∧
    denominatorStep (5*t) (92*t) = 46*t ∧
    denominatorStep (5*t) (46*t) = 23*t := by
  simp [denominatorStep, Nat.mul_mod, ht]
  omega

/-- These eight numerator values form a closed invariant set. -/
def Member (t n : Nat) : Prop :=
  n = 23*t ∨ n = 74*t ∨ n = 37*t ∨ n = 116*t ∨
  n = 58*t ∨ n = 29*t ∨ n = 92*t ∨ n = 46*t

theorem member_forward {t n : Nat} (ht : t%2 = 1) (h : Member t n) :
    Member t (denominatorStep (5*t) n) := by
  obtain ⟨h0,h1,h2,h3,h4,h5,h6,h7⟩ := scaled_transitions t ht
  rcases h with h | h | h | h | h | h | h | h <;>
    simp_all [Member]

theorem orbit_member (t : Nat) (ht : t%2 = 1) (k : Nat) :
    Member t (denominatorOrbit (5*t) k (23*t)) := by
  induction k with
  | zero => exact Or.inl rfl
  | succ k ih => exact member_forward ht ih

theorem cycle_eight (t : Nat) (ht : t%2 = 1) :
    denominatorOrbit (5*t) 8 (23*t) = 23*t := by
  obtain ⟨h0,h1,h2,h3,h4,h5,h6,h7⟩ := scaled_transitions t ht
  simp only [denominatorOrbit, h0,h1,h2,h3,h4,h5,h6,h7]

/-- The primitive normalized cycle has least positive period eight. -/
theorem primitive_period : denominatorOrbit 5 8 23 = 23 ∧
    ∀ k : Fin 7, denominatorOrbit 5 (k.val+1) 23 ≠ 23 := by decide

/-- The numerator cycle stays in the interval [23t,116t] for all time. -/
theorem bounds_all (t : Nat) (ht : t%2 = 1) (k : Nat) :
    23*t ≤ denominatorOrbit (5*t) k (23*t) ∧
    denominatorOrbit (5*t) k (23*t) ≤ 116*t := by
  have h := orbit_member t ht k
  rcases h with h | h | h | h | h | h | h | h <;> omega

/-- Its rational minimum is greater than one, and the maximum ratio is 116/23. -/
theorem rational_floor_certificate :
    5 < 23 ∧ (∀ k, 23 ≤ denominatorOrbit 5 k 23 ∧
      denominatorOrbit 5 k 23 ≤ 116) ∧ denominatorOrbit 5 3 23 = 116 := by
  refine ⟨by decide, ?_, by decide⟩
  intro k
  simpa using bounds_all 1 (by decide) k

/-- The cycle defeats every rational-interval clock at ratio 51/10. -/
theorem band_fifty_one_tenths (k : Nat) :
    23 ≤ denominatorOrbit 5 k 23 ∧ 10*denominatorOrbit 5 k 23 ≤ 51*23 := by
  have h := bounds_all 1 (by decide) k
  simp only [Nat.mul_one] at h
  omega

/-- It still exits the narrower ratio-five band, at its largest point. -/
theorem exits_five_band : 5*23 < denominatorOrbit 5 3 23 := by decide

/-- Even the multiplicative part 81/16 of the integer-floor bound fails here. -/
theorem fails_integer_floor_excursion (k : Nat) :
    16*denominatorOrbit 5 k 23 < 81*23 := by
  have h := bounds_all 1 (by decide) k
  simp only [Nat.mul_one] at h
  omega

/-- A uniform result for arbitrary odd offsets would wrongly exclude this cycle. -/
theorem no_offset_band_exit :
    ¬ (∀ d b n : Nat, d%2 = 1 → 1 < b →
      ∃ k, denominatorOrbit d k n < b ∨
        116*b < 23*denominatorOrbit d k n) := by
  intro h
  obtain ⟨k,hl | hu⟩ := h 5 23 23 (by decide) (by decide)
  · have hb := bounds_all 1 (by decide) k
    simp only [Nat.mul_one] at hb
    omega
  · have hb := bounds_all 1 (by decide) k
    simp only [Nat.mul_one] at hb
    omega

/-- Changing the denominator changes the odd update; this is no integer cycle. -/
theorem ordinary_map_control : step 23 = 70 ∧ denominatorStep 5 23 = 74 := by decide

/-- The corresponding ordinary integer congruence class has an exact descending trace.
This class was already closed in Strategy/ExcursionMap; this records the fixed clock. -/
theorem integer_trace (q : Nat) :
    step (32*q+11) = 96*q+34 ∧ step (96*q+34) = 48*q+17 ∧
    step (48*q+17) = 144*q+52 ∧ step (144*q+52) = 72*q+26 ∧
    step (72*q+26) = 36*q+13 ∧ step (36*q+13) = 108*q+40 ∧
    step (108*q+40) = 54*q+20 ∧ step (54*q+20) = 27*q+10 := by
  have h0 : (32*q+11)%2 = 1 := by omega
  have h1 : (96*q+34)%2 = 0 := by omega
  have h2 : (48*q+17)%2 = 1 := by omega
  have h3 : (144*q+52)%2 = 0 := by omega
  have h4 : (72*q+26)%2 = 0 := by omega
  have h5 : (36*q+13)%2 = 1 := by omega
  have h6 : (108*q+40)%2 = 0 := by omega
  have h7 : (54*q+20)%2 = 0 := by omega
  simp [step, h0,h1,h2,h3,h4,h5,h6,h7]
  omega

theorem integer_eighth_value (q : Nat) : orbit 8 (32*q+11) = 27*q+10 := by
  obtain ⟨h0,h1,h2,h3,h4,h5,h6,h7⟩ := integer_trace q
  simp only [orbit, h0,h1,h2,h3,h4,h5,h6,h7]

theorem integer_strict_descent (q : Nat) : orbit 8 (32*q+11) < 32*q+11 := by
  rw [integer_eighth_value]
  omega

/-- The formal affine return identity, exposing the rational fixed point 23/5. -/
theorem integer_return_identity (q : Nat) :
    32*orbit 8 (32*q+11) = 27*(32*q+11)+23 := by
  rw [integer_eighth_value]
  omega

/-- The word's affine identity enforces the exact integer source residue. -/
theorem integer_source_residue (n r : Nat) (h : 32*r = 27*n+23) : n%32 = 11 := by
  omega

theorem integer_descent_of_residue {n : Nat} (h : n%32 = 11) : orbit 8 n < n := by
  have hn : n = 32*(n/32)+11 := by omega
  rw [hn]
  exact integer_strict_descent (n/32)

theorem no_integer_fixed_point (n : Nat) : ¬ (32*n = 27*n+23) := by omega

end Collatz.Exploration.RationalBandObstruction
