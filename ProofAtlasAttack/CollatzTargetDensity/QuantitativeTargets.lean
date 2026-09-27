import CollatzTargetDensity.UniformActivation
import CollatzTargetDensity.Assembly
import CollatzTargetDensity.Public
import Mathlib.Data.Nat.Sqrt

/-!
Uniform quantitative dependence on the target. For each positive integer A,
constants K,d work for every target and every t with target <= t^A.
This is weaker than a uniform c/target density estimate and is not Collatz.
-/
namespace CollatzTargetDensity
open Erdos1135 Erdos1135.ND.PositiveDensity SyracuseMinorant Filter
open scoped Topology
noncomputable section

theorem quantitative_odd_target_density (A : ℕ) (hA : 0 < A) :
    ∃ K : ℕ, 1 ≤ K ∧ ∃ d : ℝ, 0 < d ∧
      ∀ target : ℕ, Odd target → target % 3 ≠ 0 →
      ∀ t : ℕ, 1 ≤ t → target ≤ t ^ A →
      ∀ᶠ X : ℕ in atTop,
        d / ((target : ℝ) * (3 : ℝ) ^ (K * t)) * (X : ℝ) ≤
          (Terras.natCount (oddReaches target) X : ℝ) := by
  obtain ⟨C, hC, a, ha, hactivation⟩ := uniform_bounded_terminal_mark
  obtain ⟨Cmix, hCmix, hrate⟩ :=
    NDGeom2ShiftedWideSymmetricRootSideUniformFloorState.forwardCoreTerminalUnitMass_le_native_two_conductor_rate_of_nonperiodic A hA
  obtain ⟨K, hK⟩ := exists_nat_gt (max 1 (88 * (C : ℝ) * Cmix / a))
  have hKone : (1 : ℝ) ≤ K := (le_max_left _ _).trans hK.le
  have hKnat : 1 ≤ K := by exact_mod_cast hKone
  have hCpos : (0 : ℝ) < C := by exact_mod_cast (show 0 < C by omega)
  have hKpow : (K : ℝ) ≤ (K : ℝ) ^ A := le_self_pow₀ hKone (by omega)
  have hbudget : 88 * (C : ℝ) * Cmix ≤ a * (K : ℝ) ^ A := by
    have h := (div_lt_iff₀ ha).mp ((le_max_right _ _).trans_lt hK)
    nlinarith
  refine ⟨K, hKnat, a / (128 * C), by positivity, ?_⟩
  intro target hodd hthree t ht hsize
  have htpos : (0 : ℝ) < t := by exact_mod_cast (show 0 < t by omega)
  have htargetpos : (0 : ℝ) < target := by exact_mod_cast hodd.pos
  obtain ⟨M, hM, hl, hbound, hhit, hnp, hmark⟩ := hactivation target hodd hthree
  let U := ndRootCoreSingletonState (32 ^ 5) M (by norm_num) hM hl
  let cap : ℕ → ℕ := fun n => n / 100
  let m : ℕ := K * t
  have hm : 1 ≤ m := Nat.one_le_iff_ne_zero.mpr (mul_ne_zero (by omega) (by omega))
  have hmpos : (0 : ℝ) < m := by exact_mod_cast (show 0 < m by omega)
  have hPeq : U.parentSourcePotential = (M : ℝ) := by
    change ndGeom2PredictableRootSideParentSourcePotential (Finset.univ : Finset Unit)
      (fun _ => (1 : ℝ)) (fun _ => M) = M
    simp [ndGeom2PredictableRootSideParentSourcePotential]
  have hPpos : 0 < U.parentSourcePotential := by rw [hPeq]; exact_mod_cast hM.pos
  have hPC : U.parentSourcePotential ≤ (C : ℝ) * target := by rw [hPeq]; exact_mod_cast hbound
  have hPt : U.parentSourcePotential ≤ (C : ℝ) * (t : ℝ) ^ A := by
    apply hPC.trans
    exact mul_le_mul_of_nonneg_left (by exact_mod_cast hsize) hCpos.le
  have hpaid : 88 * U.parentSourcePotential * Cmix ≤ a * (m : ℝ) ^ A := by
    calc
      _ ≤ 88 * ((C : ℝ) * (t : ℝ) ^ A) * Cmix := by gcongr
      _ = (88 * (C : ℝ) * Cmix) * (t : ℝ) ^ A := by ring
      _ ≤ (a * (K : ℝ) ^ A) * (t : ℝ) ^ A :=
        mul_le_mul_of_nonneg_right hbudget (by positivity)
      _ = a * (m : ℝ) ^ A := by simp only [m, Nat.cast_mul, mul_pow]; ring
  have hcoarse : 44 * U.parentSourcePotential * (Cmix / (m : ℝ) ^ A) ≤ a / 2 := by
    rw [← mul_div_assoc]
    apply (div_le_iff₀ (by positivity : (0 : ℝ) < (m : ℝ) ^ A)).2
    nlinarith
  let eta : ℝ := a / (4 * (3 : ℝ) ^ m)
  have heta : 0 < eta := by dsimp [eta]; positivity
  have hseed : ∀ i, Nonperiodic Tao.syracuse (U.state.root i) := fun _ => hnp
  have htarget : ∀ i, ∃ k : ℕ, (Tao.syracuse^[k]) (U.state.root i) = target :=
    fun _ => ⟨1, hhit⟩
  have hspan : U.rootSpan 0 := by intro i j; change M ≤ 2 ^ 0 * M; simp
  have hcap : ∀ n, cap n ≤ 1 * (n + 1) := by intro n; dsimp [cap]; omega
  have hmass : ∀ᶠ n in atTop,
      let V := U.forwardIterate cap n
      ∀ (X : ℝ) (hX : 0 < X)
      (hi : ∀ i : V.state.Label,
        ndGeom2ShiftedWideSymmetricPhysicalIntervalMin V.floor (V.state.root i) < X ∧
        X ≤ ndGeom2ShiftedWideSymmetricPhysicalIntervalMax V.floor (V.state.root i)),
        eta ≤ U.fullTerminalMass cap n (V.fullTerminalShift X hX hi) 1 := by
    filter_upwards [hmark, eventually_ge_atTop (2 * m)] with n hn hnlarge
    intro V X hX hi
    have hf : U.floor + 2 * n ≤ V.floor := by
      rw [forward_floor_eq_coreFloor]
      exact coreFloor_linear_lower U.floor_twoHundred n
    have hmk : m ≤ V.floor / 4 := by omega
    have hT := hn X hX hi
    change a ≤ U.forwardCoreTerminalUnitMass cap ndRootCoreWidth n (cap n) (V.floor / 4) X hX hi at hT
    have hh := hrate U cap ndRootCoreWidth n (cap n) m (V.floor / 4) hm hmk
      (Nat.div_le_self _ _) hseed X hX hi (ha.trans_le hT)
    push_cast at hh
    dsimp [eta]
    apply (div_le_iff₀ (by positivity : (0 : ℝ) < 4 * 3 ^ m)).2
    change a ≤ U.fullTerminalMass cap n ((U.forwardIterate cap n).fullTerminalShift X hX hi) 1 * (4 * 3 ^ m)
    nlinarith only [ha, hT, hh, hcoarse]
  have hcount := U.targetDensity_of_eventually_pos_fullTerminalMass cap hspan hcap
    target hseed htarget hPpos heta hmass
  have hcoeff : (a / (128 * (C : ℝ))) / ((target : ℝ) * (3 : ℝ) ^ (K * t)) ≤
      eta / (32 * U.parentSourcePotential) := by
    dsimp [eta, m]
    have hp : (0 : ℝ) < 3 ^ (K * t) := by positivity
    field_simp
    nlinarith
  filter_upwards [hcount] with X hX
  exact (mul_le_mul_of_nonneg_right hcoeff (by positivity : (0 : ℝ) ≤ X)).trans hX

/-- Literal ordinary Collatz count, with constants uniform over targets.
The auxiliary t can be any positive integer with target <= t^A. -/
theorem quantitative_target_density (A : ℕ) (hA : 0 < A) :
    ∃ K : ℕ, 1 ≤ K ∧ ∃ d : ℝ, 0 < d ∧
      ∀ target : ℕ, 0 < target → target % 3 ≠ 0 →
      ∀ t : ℕ, 1 ≤ t → target ≤ t ^ A →
      ∃ X₀ : ℕ, ∀ X : ℕ, X₀ ≤ X →
        d / ((target : ℝ) * (3 : ℝ) ^ (K * t)) * (X : ℝ) ≤
          (countBelow target X : ℝ) := by
  obtain ⟨K, hK, d, hd, hcount⟩ := quantitative_odd_target_density A hA
  refine ⟨9 * K, by omega, d / 9, by positivity, ?_⟩
  intro target ht hthree t htone hsize
  obtain ⟨c, hc, hcunit, hhit, hcsize⟩ := exists_fertile_raw_child_small hthree
  have hcpos : (0 : ℝ) < c := by exact_mod_cast hc.pos
  have htpos : (0 : ℝ) < target := by exact_mod_cast ht
  have h9pow : (9 : ℕ) ≤ 9 ^ A := le_self_pow (by omega) (by omega)
  have hsize' : c ≤ (9 * t) ^ A := by
    calc
      c ≤ 9 * target := hcsize
      _ ≤ 9 * t ^ A := Nat.mul_le_mul_left _ hsize
      _ ≤ 9 ^ A * t ^ A := Nat.mul_le_mul_right _ h9pow
      _ = (9 * t) ^ A := (mul_pow _ _ _).symm
  have hcoefficient :
      (d / 9) / ((target : ℝ) * (3 : ℝ) ^ (9 * K * t)) ≤
        d / ((c : ℝ) * (3 : ℝ) ^ (K * (9 * t))) := by
    rw [show 9 * K * t = K * (9 * t) by ring]
    have hp : (0 : ℝ) < 3 ^ (K * (9 * t)) := by positivity
    calc
      (d / 9) / ((target : ℝ) * (3 : ℝ) ^ (K * (9 * t))) =
          d / ((9 * (target : ℝ)) * (3 : ℝ) ^ (K * (9 * t))) := by field_simp
      _ ≤ _ := div_le_div_of_nonneg_left hd.le (mul_pos hcpos hp)
        (mul_le_mul_of_nonneg_right (by exact_mod_cast hcsize) hp.le)
  obtain ⟨X₀, hX₀⟩ := eventually_atTop.mp (hcount c hc hcunit (9 * t) (by omega) hsize')
  refine ⟨X₀, ?_⟩
  intro X hX
  have hmono := Terras.natCount_mono (oddReaches_subset_rawReaches hhit) X
  exact ((mul_le_mul_of_nonneg_right hcoefficient (by positivity : (0 : ℝ) ≤ X)).trans
    (hX₀ X hX)).trans (by exact_mod_cast hmono)

/-- A target-only specialization; the general theorem permits every positive
integer exponent A, with constants allowed to depend on A. -/
theorem sqrt_target_density :
    ∃ K : ℕ, 1 ≤ K ∧ ∃ d : ℝ, 0 < d ∧
      ∀ target : ℕ, 0 < target → target % 3 ≠ 0 →
      ∃ X₀ : ℕ, ∀ X : ℕ, X₀ ≤ X →
        d / ((target : ℝ) * (3 : ℝ) ^ (K * (Nat.sqrt target + 1))) * (X : ℝ) ≤
          (countBelow target X : ℝ) := by
  obtain ⟨K, hK, d, hd, hcount⟩ := quantitative_target_density 2 (by norm_num)
  refine ⟨K, hK, d, hd, ?_⟩
  intro target ht hthree
  exact hcount target ht hthree (Nat.sqrt target + 1) (by omega)
    (Nat.lt_succ_sqrt' target).le

end
end CollatzTargetDensity
