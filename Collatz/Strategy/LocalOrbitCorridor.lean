import Collatz.Strategy.VerifiedOrbitCorridor

/-!
# A two-step corridor criterion from local parity dynamics

The long pigeonhole corridor is numerically dominated for Collatz by its
local branches. Three consecutive orbit values cannot all lie in [V,2V): an even step exits downward, and two odd steps exit upward.
Combining this with a verified initial range gives a two-step convergence test.
-/
namespace Collatz.LocalOrbitCorridor
open Reach VerifiedRange VerifiedOrbitCorridor

/-- No three consecutive accelerated states fit in [V,2V), including V=0.
This local arithmetic fact does not use any convergence or cycle hypothesis. -/
theorem no_three_in_band {V n : Nat}
    (hlo : ∀ t, t≤2 → V≤acceleratedOrbit t n)
    (hhi : ∀ t, t≤2 → acceleratedOrbit t n<2*V) : False := by
  have h0 := hlo 0 (by decide)
  have h1 := hlo 1 (by decide)
  have h2 := hlo 2 (by decide)
  have u0 := hhi 0 (by decide)
  have u1 := hhi 1 (by decide)
  have u2 := hhi 2 (by decide)
  change V≤n at h0
  change V≤acceleratedStep n at h1
  change V≤acceleratedStep (acceleratedStep n) at h2
  change n<2*V at u0
  change acceleratedStep n<2*V at u1
  change acceleratedStep (acceleratedStep n)<2*V at u2
  by_cases he : n%2=0
  · rw [acceleratedStep, if_pos he] at h1
    omega
  · have ho : acceleratedStep n=(3*n+1)/2 := by
      rw [acceleratedStep, if_neg he]
    by_cases he1 : acceleratedStep n%2=0
    · rw [acceleratedStep, if_pos he1] at h2
      omega
    · have ho1 : acceleratedStep (acceleratedStep n)=(3*acceleratedStep n+1)/2 := by
        rw [acceleratedStep, if_neg he1]
      omega

/-- A positive nonconvergent start must reach twice the verified cutoff by
accelerated time two. -/
theorem local_escape {V n : Nat} (hv : VerifiedBelow V)
    (hn : 0<n) (hno : ¬ReachesOne n) :
    ∃ t, t≤2 ∧ 2*V≤acceleratedOrbit t n := by
  by_cases h : ∃ t, t≤2 ∧ 2*V≤acceleratedOrbit t n
  · exact h
  · apply False.elim
    apply no_three_in_band (V := V) (n := n)
    · intro t _
      exact ge_verified_of hv hn hno ⟨t, rfl⟩
    · intro t ht
      have hu : ¬2*V≤acceleratedOrbit t n := fun hh => h ⟨t, ht, hh⟩
      omega

/-- Every three-state window on a hypothetical counterexample meets [2V,∞). -/
theorem every_local_window {V n : Nat} (hv : VerifiedBelow V)
    (hn : 0<n) (hno : ¬ReachesOne n) (s : Nat) :
    ∃ t, t≤2 ∧ 2*V≤acceleratedOrbit (t+s) n := by
  obtain ⟨t, ht, hh⟩ := local_escape hv (acceleratedOrbit_positive hn s)
    (fun h => hno (reachesOne_of_accOrbit hn h))
  exact ⟨t, ht, by simpa only [acceleratedOrbit_add] using hh⟩

/-- Passing the local corridor scan actually forces entry into the verified
range during those same two steps. -/
theorem local_check_has_small_hit {V n : Nat}
    (hc : staysBelow (2*V) 2 n=true) :
    ∃ t, t≤2 ∧ acceleratedOrbit t n<V := by
  by_cases h : ∃ t, t≤2 ∧ acceleratedOrbit t n<V
  · exact h
  · apply False.elim
    apply no_three_in_band (V := V) (n := n)
    · intro t ht
      have hh : ¬acceleratedOrbit t n<V := fun hu => h ⟨t, ht, hu⟩
      omega
    · exact (staysBelow_iff (2*V) 2 n).mp hc

/-- Direct two-step entry check, avoiding the unnecessary upper-corridor
restriction when an input already reaches the verified range. -/
def twoStepVerified (V n : Nat) : Bool :=
  (List.range 3).any (fun t => decide (acceleratedOrbit t n<V))

theorem twoStepVerified_iff (V n : Nat) : twoStepVerified V n=true ↔
    ∃ t, t≤2 ∧ acceleratedOrbit t n<V := by
  simp [twoStepVerified, List.any_eq_true, Nat.lt_succ_iff]

/-- A verified-range hit transfers convergence back to the starting point. -/
theorem twoStepVerified_sound {V n : Nat} (hv : VerifiedBelow V)
    (hn : 0<n) (hc : twoStepVerified V n=true) : ReachesOne n := by
  obtain ⟨t, _, ht⟩ := (twoStepVerified_iff V n).mp hc
  exact reachesOne_of_accOrbit hn (hv _ (acceleratedOrbit_positive hn t) ht)

/-- The direct hit check accepts every successful local corridor scan. -/
theorem local_implies_hit {V n : Nat} (hc : staysBelow (2*V) 2 n=true) :
    twoStepVerified V n=true :=
  (twoStepVerified_iff V n).mpr (local_check_has_small_hit hc)

/-- A finite sufficient convergence test based only on the verified range
and the parity branches. No cycle-length theorem is needed in its proof. -/
theorem local_check_sound {V n : Nat} (hv : VerifiedBelow V)
    (hn : 0<n) (hc : staysBelow (2*V) 2 n=true) : ReachesOne n := by
  exact twoStepVerified_sound hv hn (local_implies_hit hc)

/-- Current specialization: three values below 7,997,440 suffice. -/
theorem current_local_check {n : Nat} (hn : 0<n)
    (hc : staysBelow 7997440 2 n=true) : ReachesOne n :=
  local_check_sound (V := 3998720) Frontier14187.verified_3998720 hn hc

/-- Every start accepted by the previous long corridor test is accepted by
this shorter, wider local test. -/
theorem long_check_implies_local {n : Nat}
    (hc : staysBelow 4012906 14186 n=true) : staysBelow 7997440 2 n=true := by
  apply (staysBelow_iff 7997440 2 n).mpr
  intro t ht
  have hu := (staysBelow_iff 4012906 14186 n).mp hc t (by omega)
  omega

/-- Strict improvement of the executable criterion: the old boundary fails
its original test but passes the new two-step scan. -/
theorem local_strictly_improves :
    staysBelow 4012906 14186 4012906=false ∧
    staysBelow 7997440 2 4012906=true := by decide

/-- The wider test still has false negatives: its even boundary reaches the
old verified range after another step, despite immediate rejection. -/
theorem local_failure_can_converge : staysBelow 7997440 2 7997440=false ∧
    ReachesOne 7997440 := by
  constructor
  · rfl
  · apply (reachesOne_accStep_iff (by decide : 0<7997440)).mpr
    change ReachesOne 3998720
    apply (reachesOne_accStep_iff (by decide : 0<3998720)).mpr
    change ReachesOne 1999360
    exact Search.reachesOne_of_lt_3998720 (by decide) (by decide)

/-- The direct range-hit criterion strictly improves the local corridor test. -/
theorem hit_strictly_improves : staysBelow 7997440 2 7997440=false ∧
    twoStepVerified 3998720 7997440=true := by decide

end Collatz.LocalOrbitCorridor
