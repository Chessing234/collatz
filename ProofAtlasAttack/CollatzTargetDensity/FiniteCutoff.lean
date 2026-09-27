import CollatzTargetDensity.Assembly
import CollatzTargetDensity.ProofChain
import Erdos1135.ND.PositiveDensity.Geom2ShiftedWideSymmetricExplicitCutoffCount

/-!
A finite cutoff for the arbitrary-target counting argument, conditional on
a supplied activation generation. The activation generation is not bounded
here. A separate argument locates this particular cutoff above a least bad
value, so it cannot be substituted at that value in a descent contradiction.
-/
namespace Erdos1135.ND.PositiveDensity
open scoped BigOperators
open CollatzTargetDensity
noncomputable section
namespace NDGeom2ShiftedWideSymmetricRootSideUniformFloorState

theorem targetCount_from_explicit_start
    (U : NDGeom2ShiftedWideSymmetricRootSideUniformFloorState)
    (cap : ℕ → ℕ) {e L : ℕ} (he : U.rootSpan e)
    (hcap : ∀ n, cap n ≤ L * (n + 1))
    {eta : ℝ} (target : ℕ)
    (hseed : ∀ i, Nonperiodic Tao.syracuse (U.state.root i))
    (htarget : ∀ i, ∃ k : ℕ, (Tao.syracuse^[k]) (U.state.root i) = target)
    (hP : 0 < U.parentSourcePotential)
    (N H : ℕ) (hN : 1000000000 * (e + L + 3) ≤ N)
    (hH : ∀ i : (U.iterate cap N).state.Label,
      ndGeom2ShiftedWideSymmetricPhysicalIntervalMax (U.iterate cap N).floor
        ((U.iterate cap N).state.root i) ≤ H)
    (hmass : ∀ n, N ≤ n →
      let V := U.forwardIterate cap n
      ∀ (X : ℝ) (hX : 0 < X)
        (hi : ∀ i : V.state.Label,
          ndGeom2ShiftedWideSymmetricPhysicalIntervalMin V.floor (V.state.root i) < X ∧
          X ≤ ndGeom2ShiftedWideSymmetricPhysicalIntervalMax V.floor (V.state.root i)),
        eta ≤ U.fullTerminalMass cap n (V.fullTerminalShift X hX hi) 1) :
    ∀ Y : ℕ, 32 * (H + 1) ≤ Y →
      eta / (32 * U.parentSourcePotential) * Y ≤
        (Terras.natCount (oddReaches target) Y : ℝ) := by
  classical
  intro Y hY
  have hYlarge : 32 * ((H : ℝ) + 1) ≤ Y := by exact_mod_cast hY
  let X := (Y : ℝ) / 32
  have hX : 0 < X := by dsimp [X]; have := Nat.cast_nonneg (α := ℝ) H; linarith
  have hHX : (H : ℝ) < X := by dsimp [X]; linarith
  obtain ⟨n, hn, hi⟩ := U.exists_unstopped_generation_all_intervals_contain he cap hcap
    N hN X (fun i => (hH i).trans_lt hHX)
  have hif : ∀ i : (U.forwardIterate cap n).state.Label,
      ndGeom2ShiftedWideSymmetricPhysicalIntervalMin (U.forwardIterate cap n).floor
        ((U.forwardIterate cap n).state.root i) < X ∧
      X ≤ ndGeom2ShiftedWideSymmetricPhysicalIntervalMax (U.forwardIterate cap n).floor
        ((U.forwardIterate cap n).state.root i) := by
    rw [U.forwardIterate_eq_iterate cap n]
    exact hi
  let shift := (U.forwardIterate cap n).fullTerminalShift X hX hif
  let sources := U.fullTerminalSources cap n shift 1
  have hm : eta ≤ U.fullTerminalMass cap n shift 1 := hmass n hn X hX hif
  have hwindow (z : U.FullTerminalAt cap n shift 1) :=
    (U.forwardIterate cap n).fullTerminal_source_window X hX hif z
  have hcharge := U.fullTerminal_mass_mul_lower_le_frozenPotential_mul_card_of_nonperiodic
    cap n shift 1 hseed X (fun z => (hwindow z).1)
  have hmember (source : ℕ) (hs : source ∈ sources) :
      source ∈ oddReaches target ∧ X ≤ (source : ℝ) ∧ (source : ℝ) < 32 * X := by
    obtain ⟨z, _, rfl⟩ := Finset.mem_image.mp hs
    let p := U.fullTerminalPath cap n shift 1 z
    obtain ⟨k, hk⟩ := htarget (fullTerminalAncestor z)
    refine ⟨⟨p.sourceOdd, k + p.depth, ?_⟩, hwindow z⟩
    rw [Function.iterate_add_apply, p.terminal_eq, hk]
  have hrange : sources ⊆ Finset.range Y := by
    intro source hs
    have h := (hmember source hs).2.2
    have hlt : (source : ℝ) < Y := by dsimp [X] at h; linarith
    exact Finset.mem_range.mpr (by exact_mod_cast hlt)
  have htargetS : (↑sources : Set ℕ) ⊆ oddReaches target :=
    fun source hs => (hmember source hs).1
  have hcard : sources.card ≤ Terras.natCount (oddReaches target) Y :=
    finset_card_le_natCount_of_subset_range hrange htargetS
  have hcount : X * U.fullTerminalMass cap n shift 1 ≤
      U.parentSourcePotential * (Terras.natCount (oddReaches target) Y : ℝ) :=
    hcharge.trans (mul_le_mul_of_nonneg_left (by exact_mod_cast hcard) hP.le)
  have htotal := (mul_le_mul_of_nonneg_left hm hX.le).trans hcount
  rw [div_mul_eq_mul_div]
  apply (div_le_iff₀ (by positivity : (0 : ℝ) < 32 * U.parentSourcePotential)).2
  dsimp [X] at htotal
  nlinarith only [htotal]

/-- The explicit expression is valid once the supplied generation N has the
stated terminal-mass lower bound at every later generation. -/
theorem targetCount_from_bounded_roots_and_explicit_start
    (U : NDGeom2ShiftedWideSymmetricRootSideUniformFloorState)
    (cap : ℕ → ℕ) {e L : ℕ} (he : U.rootSpan e)
    (hcap : ∀ n, cap n ≤ L * (n + 1))
    {eta Pbar : ℝ} (heta : 0 ≤ eta) (target : ℕ)
    (hseed : ∀ i, Nonperiodic Tao.syracuse (U.state.root i))
    (htarget : ∀ i, ∃ k : ℕ, (Tao.syracuse^[k]) (U.state.root i) = target)
    (hP : 0 < U.parentSourcePotential) (hPbar : U.parentSourcePotential ≤ Pbar)
    (N M : ℕ) (hN : 1000000000 * (e + L + 3) ≤ N)
    (hroot : ∀ i, U.state.root i ≤ M)
    (hmass : ∀ n, N ≤ n →
      let V := U.forwardIterate cap n
      ∀ (X : ℝ) (hX : 0 < X)
        (hi : ∀ i : V.state.Label,
          ndGeom2ShiftedWideSymmetricPhysicalIntervalMin V.floor (V.state.root i) < X ∧
          X ≤ ndGeom2ShiftedWideSymmetricPhysicalIntervalMax V.floor (V.state.root i)),
        eta ≤ U.fullTerminalMass cap n (V.fullTerminalShift X hX hi) 1) :
    ∀ Y : ℕ, ndExplicitRootPublicCutoff U.floor L M N ≤ Y →
      eta / (32 * Pbar) * Y ≤ (countBelow target Y : ℝ) := by
  intro Y hY
  have hcount := U.targetCount_from_explicit_start cap he hcap target hseed htarget hP
    N (ndExplicitRootIntervalHeight U.floor L M N) hN
    (fun i => U.iterate_physicalIntervalMax_le_explicit cap L M hcap hroot N i) hmass Y hY
  have hcoef : eta / (32 * Pbar) ≤ eta / (32 * U.parentSourcePotential) :=
    div_le_div_of_nonneg_left heta (by positivity)
      (mul_le_mul_of_nonneg_left hPbar (by norm_num))
  have hmono := Terras.natCount_mono (oddReaches_subset_rawReaches (reaches_refl target)) Y
  exact ((mul_le_mul_of_nonneg_right hcoef (Nat.cast_nonneg Y)).trans hcount).trans
    (by exact_mod_cast hmono)

end NDGeom2ShiftedWideSymmetricRootSideUniformFloorState
end
end Erdos1135.ND.PositiveDensity

namespace CollatzTargetDensity.FiniteCutoff
open Erdos1135 Erdos1135.ND.PositiveDensity ProofChain

theorem explicit_cutoff_gt_root (b L M N : ℕ) : M < ndExplicitRootPublicCutoff b L M N := by
  have hp : 1 ≤ 2 ^ ((2 * N + 4) * b * 2 ^ N + N * (L * (N + 1) + 1)) :=
    Nat.one_le_pow _ _ (by decide)
  unfold ndExplicitRootPublicCutoff ndExplicitRootIntervalHeight
  nlinarith

/-- Under the least-counterexample hypothesis, every positive seed reaching
3m+1 is at least m. This particular explicit cutoff is strictly larger still.
It therefore gives no lower bound at the smaller cutoff m. -/
theorem cutoff_above_least_bad {m M : ℕ} (hm : LeastBad m)
    (hM : 0 < M) (hreach : Reaches M (3 * m + 1)) (b L N : ℕ) :
    m < ndExplicitRootPublicCutoff b L M N := by
  have hs : Reaches m (3 * m + 1) :=
    reaches_of_step_eq (collatzStep_eq_three_mul_add_one_of_odd (least_bad_odd hm))
  have hbad := bad_forward hm.1 (by omega : 0 < 3 * m + 1) hs
  have hMbad : M ∈ rawBad := ⟨hM, fun h => hbad.2 (reaches_one_forward hreach h)⟩
  exact (hm.2 M hMbad).trans_lt (explicit_cutoff_gt_root b L M N)

/-- Once an orbit reaches one, its later values belong to this finite cycle. -/
theorem iterate_one_cycle (k : ℕ) :
    (collatzStep^[k]) 1 = 1 ∨ (collatzStep^[k]) 1 = 2 ∨ (collatzStep^[k]) 1 = 4 := by
  induction k with
  | zero => exact Or.inl rfl
  | succ k ih =>
    rw [Function.iterate_succ_apply']
    rcases ih with h | h | h <;> rw [h] <;>
      norm_num [collatzStep, CollatzConjecture.collatzStep]

theorem one_not_reaches_above_four {target : ℕ} (ht : 4 < target) :
    ¬ Reaches 1 target := by
  rintro ⟨k, hk⟩
  have h := iterate_one_cycle k
  rw [hk] at h
  omega

def avoidsAndHitsOne : ℕ → ℕ → ℕ → Bool
  | 0, target, n => decide (n = 1) && decide (n ≠ target)
  | fuel + 1, target, n => decide (n ≠ target) &&
      (decide (n = 1) || avoidsAndHitsOne fuel target (collatzStep n))

/-- The checker proves infinite-time avoidance: its successful endpoint is
one, whose entire subsequent cycle is separately known to avoid the target. -/
theorem avoidsAndHitsOne_sound {fuel target n : ℕ} (ht : 4 < target)
    (h : avoidsAndHitsOne fuel target n = true) : Reaches n 1 ∧ ¬ Reaches n target := by
  induction fuel generalizing n with
  | zero =>
    have hn : n = 1 ∧ n ≠ target := by simpa [avoidsAndHitsOne] using h
    rcases hn with ⟨rfl, _⟩
    exact ⟨reaches_refl 1, one_not_reaches_above_four ht⟩
  | succ fuel ih =>
    have hn : n ≠ target ∧ (n = 1 ∨ avoidsAndHitsOne fuel target (collatzStep n) = true) := by
      simpa [avoidsAndHitsOne, Bool.or_eq_true] using h
    rcases hn.2 with rfl | hstep
    · exact ⟨reaches_refl 1, one_not_reaches_above_four ht⟩
    · obtain ⟨h1, hnot⟩ := ih hstep
      refine ⟨reaches_of_reaches_step h1, ?_⟩
      rintro ⟨k, hk⟩
      cases k with
      | zero => exact hn.1 hk
      | succ k => exact hnot ⟨k, by simpa only [Function.iterate_succ_apply] using hk⟩

def rangeAvoidCheck (target bound fuel : ℕ) : Bool :=
  (List.range bound).all (fun n => decide (n = 0) || avoidsAndHitsOne fuel target n)

theorem rangeAvoidCheck_sound {target bound fuel : ℕ} (ht : 4 < target)
    (h : rangeAvoidCheck target bound fuel = true) {n : ℕ} (hn : 0 < n) (hb : n < bound) :
    Reaches n 1 ∧ ¬ Reaches n target := by
  have hh := List.all_eq_true.mp h n (List.mem_range.mpr hb)
  have hz : n ≠ 0 := by omega
  apply avoidsAndHitsOne_sound ht
  simpa [hz] using hh

set_option maxRecDepth 100000 in
set_option maxHeartbeats 50000000 in
theorem range_avoids_3082_checked : rangeAvoidCheck 3082 1027 512 = true := by decide

/-- A literal zero predecessor count above the previously verified base.
This is not a finite-time truncation of reachability. -/
theorem no_predecessor_3082_below_1027 : countBelow 3082 1027 = 0 := by
  classical
  unfold countBelow
  apply Nat.count_of_forall_not
  intro n hn hreach
  exact (rangeAvoidCheck_sound (by norm_num) range_avoids_3082_checked hreach.1 hn).2 hreach.2

set_option maxRecDepth 100000 in
theorem reaches_one_1027 : Reaches 1027 1 :=
  hitsOneWithin_sound (fuel := 512) (by decide)

/-- Positive eventual density is compatible with an empty initial interval,
even for the successor of an odd convergent value above 1024. -/
theorem positive_density_with_empty_initial_interval :
    Reaches 1027 1 ∧ countBelow (3 * 1027 + 1) 1027 = 0 ∧
      ∃ c : ℝ, 0 < c ∧ ∃ X₀ : ℕ, ∀ X : ℕ, X₀ ≤ X →
        c * (X : ℝ) ≤ (countBelow (3 * 1027 + 1) X : ℝ) := by
  exact ⟨reaches_one_1027, no_predecessor_3082_below_1027,
    positive_density 3082 (by norm_num) (by norm_num)⟩

/-- The unconditional shortcut "activate the positive predecessor bound by
cutoff m for every odd m above 1024" is false. This does not refute a
conditional argument that makes essential use of a least bad value. -/
theorem no_unconditional_activation_by_threshold :
    ¬ (∀ m : ℕ, 1024 < m → Odd m → ∃ c : ℝ, 0 < c ∧ ∃ X₀ : ℕ, X₀ ≤ m ∧
      ∀ X : ℕ, X₀ ≤ X → c * (X : ℝ) ≤ (countBelow (3 * m + 1) X : ℝ)) := by
  intro h
  obtain ⟨c, hc, X₀, hX₀, hcount⟩ := h 1027 (by norm_num) (by decide)
  have hb := hcount 1027 hX₀
  change c * (1027 : ℝ) ≤ (countBelow 3082 1027 : ℝ) at hb
  rw [no_predecessor_3082_below_1027, Nat.cast_zero] at hb
  nlinarith

end CollatzTargetDensity.FiniteCutoff
