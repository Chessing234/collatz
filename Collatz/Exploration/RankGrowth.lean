import Collatz.Exploration.RankReduction
import Collatz.Accelerated

/-!
# Lower growth requirements for any successful Collatz rank

Every step in either convention is at least half its input. Consequently an
orbit that reaches 1 at time k must start at or below 2^k. Combining this with
well-founded rank descent shows that a valid natural-valued standard rank
satisfies n ≤ 2^(P n). In particular, it cannot have globally bounded image.

These elementary bounds constrain candidate ranking functions. They do not
supply an upper bound on stopping time and do not establish convergence.
-/
namespace Collatz.Exploration.RankGrowth

open RankReduction OrbitFloor

/-- A standard transition never removes more than half the current value. -/
theorem input_le_twice_step (n : Nat) : n ≤ 2*step n := by
  unfold step
  by_cases hz : n = 0
  · simp [hz]
  · rw [if_neg hz]
    by_cases he : n%2 = 0
    · rw [if_pos he]
      omega
    · rw [if_neg he]
      omega

/-- The accelerated convention obeys the same one-step lower bound. -/
theorem input_le_twice_accelerated (n : Nat) : n ≤ 2*acceleratedStep n := by
  unfold acceleratedStep
  by_cases he : n%2 = 0
  · rw [if_pos he]
    omega
  · rw [if_neg he]
    omega

/-- Iterating the lower bound keeps the exact dyadic scale factor. -/
theorem input_le_scaled_orbit (k n : Nat) : n ≤ 2^k*orbit k n := by
  induction k generalizing n with
  | zero => simp
  | succ k ih =>
    calc
      n ≤ 2*step n := input_le_twice_step n
      _ ≤ 2*(2^k*orbit k (step n)) := Nat.mul_le_mul_left 2 (ih (step n))
      _ = 2^(k+1)*orbit (k+1) n := by
        rw [Nat.pow_succ, orbit_succ_steps]
        ac_rfl

/-- The analogous bound holds for accelerated iteration. -/
theorem input_le_scaled_accelerated (k n : Nat) :
    n ≤ 2^k*acceleratedOrbit k n := by
  induction k generalizing n with
  | zero => simp
  | succ k ih =>
    calc
      n ≤ 2*acceleratedStep n := input_le_twice_accelerated n
      _ ≤ 2*(2^k*acceleratedOrbit k (acceleratedStep n)) :=
        Nat.mul_le_mul_left 2 (ih (acceleratedStep n))
      _ = 2^(k+1)*acceleratedOrbit (k+1) n := by
        rw [Nat.pow_succ, acceleratedOrbit_succ]
        ac_rfl

/-- Any successful standard time is at least the dyadic size of the input. -/
theorem successful_time_lower {n k : Nat} (hk : orbit k n = 1) : n ≤ 2^k := by
  have h := input_le_scaled_orbit k n
  rw [hk, Nat.mul_one] at h
  exact h

/-- Any successful accelerated time obeys the same scale lower bound. -/
theorem successful_acc_time_lower {n k : Nat}
    (hk : acceleratedOrbit k n = 1) : n ≤ 2^k := by
  have h := input_le_scaled_accelerated k n
  rw [hk, Nat.mul_one] at h
  exact h

/-- Even the noncomputable canonical hitting time must grow with input size. -/
theorem canonical_lower {n : Nat} (hn : Converges n) : n ≤ 2^(hittingTime n) :=
  successful_time_lower (hittingTime_spec hn).1

/-- Every valid global ranking function must pay for input size. -/
theorem ranking_lower {P : Nat → Nat} (hP : Ranking P) {n : Nat}
    (hn : 0 < n) : n ≤ 2^(P n) := by
  obtain ⟨k, hk, he⟩ := reaches_within_rank hP n hn
  exact Nat.le_trans (successful_time_lower he)
    (Nat.pow_le_pow_right (by decide : 1 ≤ (2:Nat)) hk)

/-- No valid natural-valued rank has a globally bounded image. -/
theorem ranking_unbounded {P : Nat → Nat} (hP : Ranking P) (B : Nat) :
    ∃ n, 0 < n ∧ B < P n := by
  let n := 2^B+1
  have hp : 0 < n := Nat.succ_pos _
  have hlow := ranking_lower hP hp
  refine ⟨n, hp, ?_⟩
  by_cases hb : B < P n
  · exact hb
  · have hpow : 2^(P n) ≤ 2^B :=
      Nat.pow_le_pow_right (by decide) (by omega)
    have hle : n ≤ 2^B := Nat.le_trans hlow hpow
    dsimp [n] at hle
    omega

/-- A bounded rank proposal is impossible even if its monotonicity is dropped. -/
theorem no_bounded_rank {P : Nat → Nat} {B : Nat}
    (hB : ∀ n, 0 < n → P n ≤ B) : ¬ Ranking P := by
  intro hP
  obtain ⟨n, hn, hr⟩ := ranking_unbounded hP B
  have := hB n hn
  omega

/-- Any claimed universal successful horizon is ruled out by a dyadic witness. -/
theorem no_universal_hitting_horizon (B : Nat) :
    ¬ (∀ n, 0 < n → ∃ k, k ≤ B ∧ orbit k n = 1) := by
  intro h
  obtain ⟨k, hk, he⟩ := h (2^B+1) (Nat.succ_pos _)
  have hlow := successful_time_lower he
  have hpow : 2^k ≤ 2^B := Nat.pow_le_pow_right (by decide) hk
  omega

end Collatz.Exploration.RankGrowth
