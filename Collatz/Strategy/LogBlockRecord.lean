import Collatz.Accelerated

/-!
# A published record refutes logarithmic descent constants through 18

The seed and stopping time are prior art: Eliahou and Simonetto,
arXiv:2107.11160v2, Table 3, g_30 (also Roosendaal's glide-record table).
This file independently checks them in Lean's kernel. It does not prove
Collatz, establish a new record, or refute a bound with constant 19.
-/

namespace Collatz.LogBlockRecord

/-- Check every state through `fuel`, retaining a fixed lower threshold. -/
def staysAbove (threshold : Nat) : Nat → Nat → Bool
  | 0, x => threshold ≤ x
  | k + 1, x => (threshold ≤ x) && staysAbove threshold k (acceleratedStep x)

theorem staysAbove_sound {threshold fuel x : Nat}
    (h : staysAbove threshold fuel x = true) :
    ∀ j, j ≤ fuel → threshold ≤ acceleratedOrbit j x := by
  induction fuel generalizing x with
  | zero =>
    intro j hj
    have : j = 0 := by omega
    subst j
    simpa [staysAbove] using h
  | succ fuel ih =>
    have hs : threshold ≤ x ∧ staysAbove threshold fuel (acceleratedStep x) = true := by
      simpa [staysAbove, Bool.and_eq_true] using h
    intro j hj
    cases j with
    | zero => exact hs.1
    | succ j => exact ih hs.2 j (by omega)

def seed : Nat := 1008932249296231

set_option maxRecDepth 100000 in
theorem no_drop_certificate : staysAbove seed 885 seed = true := by decide

theorem no_drop : ∀ j, j ≤ 885 → seed ≤ acceleratedOrbit j seed :=
  staysAbove_sound no_drop_certificate

set_option maxRecDepth 100000 in
theorem first_drop_value : acceleratedOrbit 886 seed = 1004771328803533 := by decide

theorem first_drop : acceleratedOrbit 886 seed < seed := by
  rw [first_drop_value]
  decide

theorem exact_stopping_time :
    (∀ j, j < 886 → seed ≤ acceleratedOrbit j seed) ∧
      acceleratedOrbit 886 seed < seed :=
  ⟨fun j hj => no_drop j (by omega), first_drop⟩

theorem seed_log2 : Nat.log2 seed = 49 := by decide

/-- Written without importing the large DriftSurvivors dependency tree.
The quantified proposition is definitionally its LogBlockDescentWithin C. -/
theorem not_log_bound {C : Nat} (hC : C ≤ 18) :
    ¬ (∀ n : Nat, 1 < n →
      ∃ k, k ≤ C * Nat.log2 n ∧ acceleratedOrbit k n < n) := by
  intro h
  obtain ⟨k, hk, hd⟩ := h seed (by decide)
  rw [seed_log2] at hk
  have hk' : k ≤ 885 := by omega
  have := no_drop k hk'
  omega

/-- The proposed tail hypothesis above the existing verified range is false. -/
theorem not_tail_bound {C : Nat} (hC : C ≤ 18) :
    ¬ (∀ n : Nat, 3998720 ≤ n →
      ∃ k, k ≤ C * Nat.log2 n ∧ acceleratedOrbit k n < n) := by
  intro h
  obtain ⟨k, hk, hd⟩ := h seed (by decide)
  rw [seed_log2] at hk
  have := no_drop k (show k ≤ 885 by omega)
  omega

end Collatz.LogBlockRecord
