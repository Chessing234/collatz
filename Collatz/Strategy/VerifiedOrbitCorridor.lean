import Collatz.Strategy.FiniteOrbitCertificates
import Collatz.Strategy.Frontier14187

/-!
# A finite corridor test from verified range and cycle length

A positive nonconvergent orbit avoids the verified initial interval and
cannot repeat in fewer steps than the proved cycle-length bound. Pigeonhole
therefore forces it to leave a corridor of that width within a fixed time.
The contrapositive is a finite convergence certificate, not universal descent.
-/
namespace Collatz.VerifiedOrbitCorridor
open Reach AccCycle VerifiedRange FiniteOrbitCertificates

/-- Any repeated pair on a nonconvergent orbit inherits a cycle-length bound. -/
theorem repeat_gap_ge {F n i j : Nat} (hn : 0<n) (hno : ¬ReachesOne n)
    (hcycle : ∀ m L, 0<m → AccIsCycleOf m L → ¬ReachesOne m → F≤L)
    (hij : i<j) (he : acceleratedOrbit i n=acceleratedOrbit j n) : F≤j-i := by
  apply hcycle (acceleratedOrbit i n) (j-i) (acceleratedOrbit_positive hn i)
  · refine ⟨by omega, ?_⟩
    rw [acceleratedOrbit_add, Nat.sub_add_cancel (by omega)]
    exact he.symm
  · exact fun h => hno (reachesOne_of_accOrbit hn h)

/-- A hypothetical nonconvergent orbit exits a corridor with F-1 available
values by time F-1. The two inputs are a verified range and a cycle bound. -/
theorem corridor_escape {V F n : Nat} (hF : 0<F) (hv : VerifiedBelow V)
    (hcycle : ∀ m L, 0<m → AccIsCycleOf m L → ¬ReachesOne m → F≤L)
    (hn : 0<n) (hno : ¬ReachesOne n) :
    ∃ t, t≤F-1 ∧ V+(F-1)≤acceleratedOrbit t n := by
  by_cases hex : ∃ t, t≤F-1 ∧ V+(F-1)≤acceleratedOrbit t n
  · exact hex
  · have hval : ∀ t, t≤F-1 → acceleratedOrbit t n-V<F-1 := by
      intro t ht
      have hlo := ge_verified_of hv hn hno ⟨t, rfl⟩
      have hhi : ¬V+(F-1)≤acceleratedOrbit t n := fun h => hex ⟨t, ht, h⟩
      omega
    obtain ⟨i, j, hij, hj, he⟩ := Pigeonhole.exists_repeat hval (Nat.le_refl _)
    have hiV := ge_verified_of hv hn hno ⟨i, rfl⟩
    have hjV := ge_verified_of hv hn hno ⟨j, rfl⟩
    have heq : acceleratedOrbit i n=acceleratedOrbit j n := by omega
    have hg := repeat_gap_ge hn hno hcycle hij heq
    omega

/-- Current verified constants: a counterexample reaches at least 4,012,906
within 14,186 accelerated steps. This does not require unboundedness. -/
theorem current_corridor_escape {n : Nat} (hn : 0<n) (hno : ¬ReachesOne n) :
    ∃ t, t≤14186 ∧ 4012906≤acceleratedOrbit t n := by
  exact corridor_escape (V := 3998720) (F := 14187) (by decide)
    Frontier14187.verified_3998720
    (fun _ _ hp hc hnr => Frontier14187.length_ge_14187 hp hc hnr) hn hno

/-- The same forced exit occurs in every fixed time window of a hypothetical
counterexample, not only at the beginning of its orbit. -/
theorem every_window_exit {n : Nat} (hn : 0<n) (hno : ¬ReachesOne n) (s : Nat) :
    ∃ t, t≤14186 ∧ 4012906≤acceleratedOrbit (t+s) n := by
  have htail : ¬ReachesOne (acceleratedOrbit s n) :=
    fun h => hno (reachesOne_of_accOrbit hn h)
  obtain ⟨t, ht, hv⟩ := current_corridor_escape (acceleratedOrbit_positive hn s) htail
  exact ⟨t, ht, by simpa only [acceleratedOrbit_add] using hv⟩

/-- An accepted positive repeat certificate has a long period and stays above
the entire kernel-verified convergence range, including its transient prefix. -/
theorem repeat_certificate_constraints {n i j : Nat} (hn : 0<n)
    (hc : repeatCheck n i j=true) :
    14187≤j-i ∧ ∀ t, 3998720≤acceleratedOrbit t n := by
  have ha := (repeatCheck_sound hc).2
  have hno : ¬ReachesOne n := fun h => ha ((NeverDrops.accReachesOne_iff hn).mp h)
  obtain ⟨hij, he, _⟩ := (repeatCheck_iff n i j).mp hc
  exact ⟨repeat_gap_ge hn hno
    (fun _ _ hp hcy hnr => Frontier14187.length_ge_14187 hp hcy hnr) hij he,
    fun t => ge_verified_of Frontier14187.verified_3998720 hn hno ⟨t, rfl⟩⟩

/-- No short repeat certificate can be accepted on a positive input. -/
theorem reject_short_repeat {n i j : Nat} (hn : 0<n) (hgap : j-i<14187) :
    repeatCheck n i j=false := by
  cases h : repeatCheck n i j with
  | false => rfl
  | true => have := (repeat_certificate_constraints hn h).1; omega

/-- Rolling finite scan: every state from time 0 through fuel is below C. -/
def staysBelow (C : Nat) : Nat → Nat → Bool
  | 0, n => decide (n<C)
  | fuel+1, n => decide (n<C) && staysBelow C fuel (acceleratedStep n)

theorem staysBelow_iff (C fuel n : Nat) : staysBelow C fuel n=true ↔
    ∀ k, k≤fuel → acceleratedOrbit k n<C := by
  induction fuel generalizing n with
  | zero => simp [staysBelow]
  | succ fuel ih =>
    simp only [staysBelow, Bool.and_eq_true, decide_eq_true_eq, ih]
    constructor
    · rintro ⟨hn, ht⟩ k hk
      cases k with
      | zero => exact hn
      | succ k => exact ht k (by omega)
    · intro h
      exact ⟨h 0 (by omega), fun k hk => h (k+1) (by omega)⟩

/-- A positive orbit staying inside this finite corridor long enough converges.
The test does not need to find a repeated state or an explicit hit on 1. -/
theorem corridor_check_sound {n : Nat} (hn : 0<n)
    (hc : staysBelow 4012906 14186 n=true) : ReachesOne n := by
  by_cases h : ReachesOne n
  · exact h
  · obtain ⟨t, ht, hv⟩ := current_corridor_escape hn h
    have hb := (staysBelow_iff 4012906 14186 n).mp hc t ht
    omega

set_option maxRecDepth 50000 in
set_option maxHeartbeats 2000000 in
/-- A concrete full-length corridor scan checked by the kernel. -/
theorem corridor_check_twenty_seven : staysBelow 4012906 14186 27=true := by decide

/-- Failure of the corridor test does not imply nonconvergence: its boundary
input is even and is already covered by the earlier verified range. -/
theorem corridor_failure_can_converge :
    staysBelow 4012906 14186 4012906=false ∧ ReachesOne 4012906 := by
  constructor
  · rfl
  · apply (reachesOne_accStep_iff (by decide : 0<4012906)).mpr
    change ReachesOne 2006453
    exact Search.reachesOne_of_lt_3998720 (by decide) (by decide)

end Collatz.VerifiedOrbitCorridor
