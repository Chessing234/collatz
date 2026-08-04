import Collatz.Basic
import Collatz.Accelerated

/-! Lean notes for Jeffrey C. Lagarias,
"The 3x+1 problem and its generalizations",
The American Mathematical Monthly 92 (1985), 3--23.

Lagarias's survey gives the standard `3x+1` map `C(n) = n/2` for even `n`
and `3n+1` for odd `n`, the accelerated map `T(n) = n/2` for even `n` and
`(3n+1)/2` for odd `n`, and the stopping-time formulation.  It records the
standard equivalences between these formulations.

This file proves the elementary one-step expansion facts and records the
main open conjectures and their equivalences as propositions.

Source: J. C. Lagarias, The 3x+1 problem and its generalizations,
Amer. Math. Monthly 92 (1985), 3--23.
-/

namespace Collatz.Papers.Lagarias1985

/-- Exact source tracked by this file. -/
def citation : String :=
  "Jeffrey C. Lagarias, The 3x+1 problem and its generalizations, Amer. Math. Monthly 92 (1985), 3--23."

/-- The standard Collatz conjecture: every positive orbit under `Collatz.step`
reaches `1`. -/
def standardCollatzConjecture : Prop :=
  ∀ n : Nat, n > 0 → ∃ k : Nat, Collatz.orbit k n = 1

/-- The accelerated Collatz conjecture: every integer `n > 1` has an
accelerated orbit that reaches `1`. -/
def acceleratedCollatzConjecture : Prop :=
  ∀ n : Nat, n > 1 → ∃ k : Nat, Collatz.acceleratedOrbit k n = 1

/-- On a positive even input, one accelerated step equals one standard step. -/
theorem acceleratedStep_even {n : Nat} (_hn : n > 0) (heven : n % 2 = 0) :
    Collatz.acceleratedStep n = Collatz.orbit 1 n := by
  have hn0 : n ≠ 0 := by omega
  have h1 : Collatz.step n = n / 2 := by
    simp [Collatz.step, heven, hn0]
  simp [Collatz.acceleratedStep, heven, Collatz.orbit, h1]

/-- On a positive odd input, one accelerated step equals two standard steps. -/
theorem acceleratedStep_odd {n : Nat} (_hn : n > 0) (hodd : n % 2 = 1) :
    Collatz.acceleratedStep n = Collatz.orbit 2 n := by
  have hn0 : n ≠ 0 := by omega
  have h1 : Collatz.step n = 3 * n + 1 := by
    simp [Collatz.step, hodd, hn0]
  have h2 : Collatz.step (3 * n + 1) = (3 * n + 1) / 2 := by
    have : (3 * n + 1) % 2 = 0 := by omega
    simp [Collatz.step, this]
  simp [Collatz.acceleratedStep, hodd, Collatz.orbit, h1, h2]

/-- Strong form of the embedding: the standard index can be taken to be at least `k`. -/
private theorem acceleratedOrbit_embeds_in_standard_aux (n : Nat) (hn : n > 0) (k : Nat) :
    ∃ M : Nat, Collatz.acceleratedOrbit k n = Collatz.orbit M n ∧ M ≥ k := by
  induction k with
  | zero =>
    refine ⟨0, ?_⟩
    simp
  | succ k ih =>
    cases ih with | intro M ih =>
    cases ih with | intro hM hMk =>
    have hpos : Collatz.orbit M n > 0 := Collatz.orbit_positive hn M
    by_cases heven : Collatz.orbit M n % 2 = 0
    · refine ⟨M + 1, ?_⟩
      constructor
      · calc
          Collatz.acceleratedOrbit (k + 1) n
              = Collatz.acceleratedStep (Collatz.acceleratedOrbit k n) := by
                rw [Collatz.acceleratedOrbit_succ_step]
          _ = Collatz.acceleratedStep (Collatz.orbit M n) := by rw [hM]
          _ = Collatz.orbit 1 (Collatz.orbit M n) := by rw [acceleratedStep_even hpos heven]
          _ = Collatz.orbit (M + 1) n := by
                rw [show M + 1 = 1 + M by omega]
                rw [Collatz.orbit_add 1 M n]
      · exact Nat.succ_le_succ hMk
    · have hodd : Collatz.orbit M n % 2 = 1 := by
        cases Nat.mod_two_eq_zero_or_one (Collatz.orbit M n) with
        | inl h =>
          exfalso
          exact heven h
        | inr h => exact h
      refine ⟨M + 2, ?_⟩
      constructor
      · calc
          Collatz.acceleratedOrbit (k + 1) n
              = Collatz.acceleratedStep (Collatz.acceleratedOrbit k n) := by
                rw [Collatz.acceleratedOrbit_succ_step]
          _ = Collatz.acceleratedStep (Collatz.orbit M n) := by rw [hM]
          _ = Collatz.orbit 2 (Collatz.orbit M n) := by rw [acceleratedStep_odd hpos hodd]
          _ = Collatz.orbit (M + 2) n := by
                rw [show M + 2 = 2 + M by omega]
                rw [Collatz.orbit_add 2 M n]
      · exact Nat.le_succ_of_le (Nat.succ_le_succ hMk)

/-- The accelerated orbit of a positive input embeds into the standard orbit:
for every `k` there is a positive `M` such that `T^k(n) = C^M(n)`. -/
theorem acceleratedOrbit_embeds_in_standard :
    ∀ n : Nat, n > 0 → ∀ k : Nat, ∃ M : Nat,
      Collatz.acceleratedOrbit k n = Collatz.orbit M n := by
  intro n hn k
  cases acceleratedOrbit_embeds_in_standard_aux n hn k with | intro M h =>
  cases h with | intro hM _ =>
  exact ⟨M, hM⟩

/-- If the accelerated orbit reaches `1`, then the standard orbit reaches `1`.
This is the easy direction of the equivalence between the two conjectures. -/
theorem accelerated_reaches_one_implies_standard :
    ∀ n : Nat, n > 0 →
      (∃ k : Nat, Collatz.acceleratedOrbit k n = 1) →
        ∃ k : Nat, Collatz.orbit k n = 1 := by
  intro n hn h
  cases h with | intro k hk =>
  cases acceleratedOrbit_embeds_in_standard n hn k with | intro M hM =>
  exact ⟨M, by rw [← hM, hk]⟩

/-- The standard orbit of `1` is trapped in `{1, 2, 4}`. -/
theorem orbit_one_cycle (d : Nat) :
    Collatz.orbit d 1 = 1 ∨ Collatz.orbit d 1 = 2 ∨ Collatz.orbit d 1 = 4 := by
  have base0 : Collatz.orbit 0 1 = 1 := by simp
  have base1 : Collatz.orbit 1 1 = 4 := by simp
  have base2 : Collatz.orbit 2 1 = 2 := by simp
  have hmod : Collatz.orbit d 1 = Collatz.orbit (d % 3) 1 := by
    have hd : d = d % 3 + 3 * (d / 3) := by
      rw [← Nat.div_add_mod d 3]
      omega
    rw [hd]
    rw [Collatz.orbit_add (d % 3) (3 * (d / 3)) 1]
    have h : Collatz.orbit (3 * (d / 3)) 1 = 1 := by
      induction d / 3 with
      | zero => simp
      | succ q ih =>
        have h1 : 3 * (q + 1) = 3 * q + 3 := by omega
        rw [h1]
        rw [Collatz.orbit_add (3 * q) 3 1]
        simp
        exact ih
    simp [h]
  have h : d % 3 = 0 ∨ d % 3 = 1 ∨ d % 3 = 2 := by omega
  cases h with
  | inl h =>
    rw [hmod, h, base0]
    simp
  | inr h =>
    cases h with
    | inl h =>
      rw [hmod, h, base1]
      simp
    | inr h =>
      rw [hmod, h, base2]
      simp

/-- The standard and accelerated Collatz conjectures are equivalent. -/
theorem collatzConjecturesEquivalent :
    standardCollatzConjecture ↔ acceleratedCollatzConjecture := by
  constructor
  · -- Standard → accelerated
    intro hstd n hn
    have hpos : n > 0 := by omega
    cases hstd n hpos with | intro M hM =>
    cases acceleratedOrbit_embeds_in_standard_aux n hpos M with | intro M' h =>
    cases h with | intro h_eq hM' =>
    have h2 : Collatz.orbit M' n = Collatz.orbit (M' - M) 1 := by
      calc
        Collatz.orbit M' n
            = Collatz.orbit ((M' - M) + M) n := by
                  rw [Nat.sub_add_cancel hM']
        _ = Collatz.orbit (M' - M) (Collatz.orbit M n) := by
                  rw [Collatz.orbit_add (M' - M) M n]
        _ = Collatz.orbit (M' - M) 1 := by
                  rw [hM]
    have h3 : Collatz.orbit (M' - M) 1 = 1 ∨
              Collatz.orbit (M' - M) 1 = 2 ∨
              Collatz.orbit (M' - M) 1 = 4 := orbit_one_cycle (M' - M)
    have h4 : Collatz.acceleratedOrbit M n = Collatz.orbit (M' - M) 1 := by
      rw [h_eq, h2]
    cases h3 with
    | inl h3 =>
      exact ⟨M, by rw [h4, h3]⟩
    | inr h3 =>
      cases h3 with
      | inl h3 =>
        have : Collatz.acceleratedOrbit (M + 1) n = 1 := by
          rw [Collatz.acceleratedOrbit_succ_step, h4, h3]
          simp
        exact ⟨M + 1, this⟩
      | inr h3 =>
        have : Collatz.acceleratedOrbit (M + 2) n = 1 := by
          rw [show M + 2 = (M + 1) + 1 by omega]
          rw [Collatz.acceleratedOrbit_succ_step, Collatz.acceleratedOrbit_succ_step, h4, h3]
          simp
        exact ⟨M + 2, this⟩
  · -- Accelerated → standard
    intro hacc n hn
    by_cases h1 : n = 1
    · subst h1
      exact ⟨0, rfl⟩
    · have hn1 : n > 1 := by omega
      cases hacc n hn1 with | intro k hk =>
      exact accelerated_reaches_one_implies_standard n (by omega) ⟨k, hk⟩

/-- Stopping-time formulation: the conjecture is equivalent to the statement
that every `n > 1` has a finite stopping time under the accelerated map.
The forward direction is proved; the converse is now also proved. -/
theorem reaches_one_of_finite_stopping_time {n : Nat} (_hn : 1 < n)
    (h : Collatz.hasFiniteStoppingTime n)
    (H : ∀ m : Nat, m < n → ∃ k : Nat, Collatz.acceleratedOrbit k m = 1) :
    ∃ k : Nat, Collatz.acceleratedOrbit k n = 1 := by
  cases h with | intro j h =>
  cases h with | intro hj1 hj =>
  have hH := H (Collatz.acceleratedOrbit j n) hj
  cases hH with | intro k hk =>
  have hjk : Collatz.acceleratedOrbit (j + k) n
      = Collatz.acceleratedOrbit k (Collatz.acceleratedOrbit j n) := by
    rw [Collatz.acceleratedOrbit_add k j n]
    rw [Nat.add_comm]
  exact ⟨j + k, by rw [hjk, hk]⟩

/-- The converse of `reaches_one_of_finite_stopping_time`: if every `n > 1`
has a finite accelerated orbit, then every `n > 1` has a finite stopping
time.  Now proved. -/
theorem finiteStoppingTimeOfReachesOne :
    ∀ n : Nat, 1 < n →
      (∃ k : Nat, Collatz.acceleratedOrbit k n = 1) →
        Collatz.hasFiniteStoppingTime n := by
  intro n hn h
  cases h with | intro k hk =>
  exact Collatz.hasFiniteStoppingTime_of_reaches_one hn ⟨k, hk⟩

end Collatz.Papers.Lagarias1985
