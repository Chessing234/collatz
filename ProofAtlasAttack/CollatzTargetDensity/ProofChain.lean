import CollatzTargetDensity.EnergyTargets
import CollatzTargetDensity.CounterexampleDichotomy

/-!
An explicit chain from the proved energy-dependent predecessor estimate
to the canonical Collatz proposition, conditional on one quantitative tail
gap. The tail-gap premise is NOT proved. The last equivalence makes clear
that supplying it would settle Collatz, rather than merely rename success.
-/
namespace CollatzTargetDensity.ProofChain
open Erdos1135 SyracuseEnergy Filter
open scoped Topology
noncomputable section

def avoidsBelow (B : ℕ) : Set ℕ :=
  {n | 0 < n ∧ ∀ k : ℕ, B ≤ (collatzStep^[k]) n}

def LeastBad (m : ℕ) : Prop := m ∈ rawBad ∧ ∀ n ∈ rawBad, m ≤ n

theorem step_pos {n : ℕ} (hn : 0 < n) : 0 < collatzStep n := by
  by_cases he : Even n
  · rw [collatzStep_eq_div_two_of_even he]
    have := Nat.even_iff.mp he
    omega
  · rw [collatzStep_eq_three_mul_add_one_of_not_even he]
    omega

theorem iterate_pos {n : ℕ} (hn : 0 < n) (k : ℕ) : 0 < (collatzStep^[k]) n := by
  induction k with
  | zero => exact hn
  | succ k ih =>
    rw [Function.iterate_succ_apply']
    exact step_pos ih

theorem bad_forward {n a : ℕ} (hn : n ∈ rawBad) (ha : 0 < a) (h : Reaches n a) :
    a ∈ rawBad := ⟨ha, fun ha1 => hn.2 (h.trans ha1)⟩

theorem exists_least_bad (h : rawBad.Nonempty) : ∃ m, LeastBad m := by
  classical
  let m := Nat.find h
  exact ⟨m, Nat.find_spec h, fun n hn => Nat.find_min' h hn⟩

theorem least_bad_odd {m : ℕ} (hm : LeastBad m) : Odd m := by
  apply Nat.not_even_iff_odd.mp
  intro he
  have hpos := step_pos hm.1.1
  have hb := bad_forward hm.1 hpos (reaches_step m)
  have hmin := hm.2 _ hb
  rw [collatzStep_eq_div_two_of_even he] at hmin
  have hlt := Nat.div_lt_self hm.1.1 (by decide : 1 < 2)
  omega

theorem bad_subset_avoids_of_least {m : ℕ} (hm : LeastBad m) : rawBad ⊆ avoidsBelow m := by
  intro n hn
  refine ⟨hn.1, ?_⟩
  intro k
  exact hm.2 _ (bad_forward hn (iterate_pos hn.1 k) ⟨k, rfl⟩)

theorem successor_predecessors_avoid {m : ℕ} (hm : LeastBad m) :
    rawReaches (3 * m + 1) ⊆ avoidsBelow m := by
  have hs : Reaches m (3 * m + 1) :=
    reaches_of_step_eq (collatzStep_eq_three_mul_add_one_of_odd (least_bad_odd hm))
  have hb := bad_forward hm.1 (by omega : 0 < 3 * m + 1) hs
  exact (rawReaches_subset_bad hb.2).trans (bad_subset_avoids_of_least hm)

def energyProfile (K : ℕ) (d : ℝ) (m : ℕ) : ℝ :=
  d / (16 * (m : ℝ) ^ 2 * collisionEnergy (4 * K * m))

theorem energyProfile_pos {K m : ℕ} {d : ℝ} (hd : 0 < d) (hm : 0 < m) :
    0 < energyProfile K d m := by
  have hE := collisionEnergy_pos (4 * K * m)
  have hm' : (0 : ℝ) < m := by exact_mod_cast hm
  unfold energyProfile
  positivity

theorem energyProfile_le_square (K m : ℕ) {d : ℝ} (hd : 0 ≤ d) (hm : 0 < m) :
    energyProfile K d m ≤ d / (16 * (m : ℝ) ^ 2) := by
  obtain ⟨c, hc, hfloor⟩ := exists_linear_collisionEnergy_lower
  have hE : 1 ≤ collisionEnergy (4 * K * m) := by
    have h := hfloor (4 * K * m)
    have hp : 0 ≤ c * (4 * K * m : ℕ) := by positivity
    linarith
  have hm' : (0 : ℝ) < m := by exact_mod_cast hm
  unfold energyProfile
  exact div_le_div_of_nonneg_left hd (by positivity)
    (by nlinarith [sq_nonneg (m : ℝ)])

/-- The coefficient that must be beaten is eventually smaller than every
positive inverse-integer-power-of-log bound. This does NOT say the actual
orbit tail is large; it diagnoses a mismatch between available estimates. -/
theorem energyProfile_eventually_lt_log_bound (K p : ℕ) {d C : ℝ}
    (hd : 0 ≤ d) (hC : 0 < C) :
    ∀ᶠ m : ℕ in atTop, energyProfile K d m < C / (Real.log (m : ℝ)) ^ p := by
  have hs : ∀ᶠ x : ℝ in atTop, ‖Real.log x ^ p‖ ≤ 1 * ‖x‖ :=
    Real.isLittleO_pow_log_id_atTop.bound (by norm_num)
  have hsn : ∀ᶠ m : ℕ in atTop, ‖Real.log (m : ℝ) ^ p‖ ≤ 1 * ‖(m : ℝ)‖ :=
    tendsto_natCast_atTop_atTop.eventually hs
  have hlarge : ∀ᶠ m : ℕ in atTop, d / (16 * C) < (m : ℝ) :=
    tendsto_natCast_atTop_atTop.eventually (eventually_gt_atTop (d / (16 * C)))
  filter_upwards [hsn, hlarge, eventually_ge_atTop 2] with m hs hm hm2
  have hmpos : (0 : ℝ) < m := by exact_mod_cast (show 0 < m by omega)
  have hlpos : 0 < Real.log (m : ℝ) := Real.log_pos (by exact_mod_cast (show 1 < m by omega))
  have hppos : 0 < Real.log (m : ℝ) ^ p := pow_pos hlpos p
  have hlog : Real.log (m : ℝ) ^ p ≤ (m : ℝ) := by
    simpa [Real.norm_eq_abs, abs_of_nonneg hlpos.le, abs_of_nonneg hmpos.le] using hs
  have hdlt : d < 16 * C * (m : ℝ) := by
    simpa [mul_comm] using
      (div_lt_iff₀ (show (0 : ℝ) < 16 * C by positivity)).mp hm
  calc
    energyProfile K d m ≤ d / (16 * (m : ℝ) ^ 2) := energyProfile_le_square K m hd (by omega)
    _ < C / (m : ℝ) := by
      apply (div_lt_div_iff₀ (by positivity : (0 : ℝ) < 16 * (m : ℝ) ^ 2) hmpos).2
      nlinarith [mul_lt_mul_of_pos_right hdlt hmpos]
    _ ≤ C / Real.log (m : ℝ) ^ p := div_le_div_of_nonneg_left hC.le hppos hlog

/-- Unconditional: any least counterexample would force the displayed
eventual lower bound for the count of orbits that never fall below it. -/
theorem least_bad_forces_energy_tail :
    ∃ K : ℕ, 1 ≤ K ∧ ∃ d : ℝ, 0 < d ∧
      ∀ m : ℕ, LeastBad m → ∃ X₀ : ℕ, ∀ X : ℕ, X₀ ≤ X →
        energyProfile K d m * (X : ℝ) ≤ (Terras.natCount (avoidsBelow m) X : ℝ) := by
  obtain ⟨K, hK, d, hd, hcount⟩ := energy_target_density 1 (by omega)
  refine ⟨K, hK, d, hd, ?_⟩
  intro m hm
  have hmpos : (0 : ℝ) < m := by exact_mod_cast hm.1.1
  have ha : (0 : ℝ) < 3 * m + 1 := by positivity
  have hsize : 3 * m + 1 ≤ 4 * m := by have := hm.1.1; omega
  obtain ⟨X₀, hX₀⟩ := hcount (3 * m + 1) (by omega) (by omega)
    (4 * m) (by have := hm.1.1; omega) (by simpa using hsize)
  have hcoeff : energyProfile K d m ≤
      d / (((3 * m + 1 : ℕ) : ℝ) ^ 2 * collisionEnergy (K * (4 * m))) := by
    have hE := collisionEnergy_pos (K * (4 * m))
    have hsq : ((3 * m + 1 : ℕ) : ℝ) ^ 2 ≤ (4 * (m : ℝ)) ^ 2 := by
      gcongr
      exact_mod_cast hsize
    unfold energyProfile
    rw [show 4 * K * m = K * (4 * m) by ring]
    rw [show 16 * (m : ℝ) ^ 2 = (4 * (m : ℝ)) ^ 2 by ring]
    exact div_le_div_of_nonneg_left hd.le (by positivity)
      (mul_le_mul_of_nonneg_right hsq hE.le)
  refine ⟨X₀, ?_⟩
  intro X hX
  have hmono : countBelow (3 * m + 1) X ≤ Terras.natCount (avoidsBelow m) X :=
    Terras.natCount_mono (successor_predecessors_avoid hm) X
  exact ((mul_le_mul_of_nonneg_right hcoeff (Nat.cast_nonneg X)).trans
    (hX₀ X hX)).trans (by exact_mod_cast hmono)

/-! The finite base is proved separately, without assuming convergence. -/

def hitsOneWithin : ℕ → ℕ → Bool
  | 0, n => decide (n = 1)
  | fuel + 1, n => decide (n = 1) || hitsOneWithin fuel (collatzStep n)

theorem hitsOneWithin_sound {fuel n : ℕ} (h : hitsOneWithin fuel n = true) :
    Reaches n 1 := by
  induction fuel generalizing n with
  | zero =>
    have hn : n = 1 := by simpa [hitsOneWithin] using h
    subst n
    exact reaches_refl 1
  | succ fuel ih =>
    have hh : n = 1 ∨ hitsOneWithin fuel (collatzStep n) = true := by
      simpa [hitsOneWithin, Bool.or_eq_true] using h
    rcases hh with rfl | hh
    · exact reaches_refl 1
    · exact reaches_of_reaches_step (ih hh)

def smallRangeCheck (bound fuel : ℕ) : Bool :=
  (List.range (bound + 1)).all (fun n => decide (n = 0) || hitsOneWithin fuel n)

set_option maxRecDepth 100000 in
set_option maxHeartbeats 50000000 in
theorem smallRange_1024_checked : smallRangeCheck 1024 512 = true := by decide

theorem reaches_one_up_to_1024 {n : ℕ} (hn : 0 < n) (hbound : n ≤ 1024) :
    Reaches n 1 := by
  have h := List.all_eq_true.mp smallRange_1024_checked n (List.mem_range.mpr (by omega))
  have hh : n = 0 ∨ hitsOneWithin 512 n = true := by
    simpa [smallRangeCheck, Bool.or_eq_true] using h
  rcases hh with hz | hh
  · omega
  · exact hitsOneWithin_sound hh

theorem least_bad_above_1024 {m : ℕ} (hm : LeastBad m) : 1024 < m := by
  by_contra h
  exact hm.1.2 (reaches_one_up_to_1024 hm.1.1 (by omega))

/-- UNPROVED premise: a sufficiently small upper tail along arbitrarily
large cutoffs, at every fixed threshold above the verified finite base. -/
def EnergyTailGap (K : ℕ) (d : ℝ) : Prop :=
  ∀ m : ℕ, 1024 < m → ∀ X₀ : ℕ, ∃ X : ℕ, X₀ ≤ X ∧ 0 < X ∧
    (Terras.natCount (avoidsBelow m) X : ℝ) < energyProfile K d m * (X : ℝ)

/-- The existing predecessor estimate and the tail gap would close the
least-counterexample contradiction. The tail gap is an explicit hypothesis. -/
theorem collatz_of_energy_tail_gap {K : ℕ} {d : ℝ}
    (hlower : ∀ m : ℕ, LeastBad m → ∃ X₀ : ℕ, ∀ X : ℕ, X₀ ≤ X →
      energyProfile K d m * (X : ℝ) ≤ (Terras.natCount (avoidsBelow m) X : ℝ))
    (hgap : EnergyTailGap K d) : collatzProp := by
  intro n hn
  by_contra hnot
  obtain ⟨m, hm⟩ := exists_least_bad ⟨n, hn, hnot⟩
  obtain ⟨X₀, hX₀⟩ := hlower m hm
  obtain ⟨X, hX, _, hsmall⟩ := hgap m (least_bad_above_1024 hm) X₀
  exact (not_lt_of_ge (hX₀ X hX)) hsmall

theorem energy_tail_gap_of_collatz {K : ℕ} {d : ℝ} (hd : 0 < d)
    (hall : collatzProp) : EnergyTailGap K d := by
  intro m hm X₀
  have hempty : avoidsBelow m = ∅ := by
    ext n
    constructor
    · intro hn
      obtain ⟨k, hk⟩ := hall n hn.1
      have hb := hn.2 k
      rw [hk] at hb
      omega
    · intro hn
      exact False.elim hn
  let X := max X₀ 1
  have hXpos : 0 < X := by dsimp [X]; omega
  refine ⟨X, le_max_left _ _, hXpos, ?_⟩
  have hzero : Terras.natCount (avoidsBelow m) X = 0 := by
    rw [hempty]
    simp [Terras.natCount]
  rw [hzero, Nat.cast_zero]
  exact mul_pos (energyProfile_pos hd (by omega)) (by exact_mod_cast hXpos)

/-- Fully checked lemma chain, not a proof of the remaining premise.
For constants supplied by the existing unconditional energy theorem,
the proposed tail gap is equivalent to the full canonical conjecture. -/
theorem exists_energy_tail_gap_equivalent_collatz :
    ∃ K : ℕ, 1 ≤ K ∧ ∃ d : ℝ, 0 < d ∧ (EnergyTailGap K d ↔ collatzProp) := by
  obtain ⟨K, hK, d, hd, hlower⟩ := least_bad_forces_energy_tail
  exact ⟨K, hK, d, hd, ⟨collatz_of_energy_tail_gap hlower, energy_tail_gap_of_collatz hd⟩⟩

end
end CollatzTargetDensity.ProofChain
