import Lean.Elab.Tactic.Omega

/-! Standalone ordinary Collatz definitions; no Mathlib dependency.
The equivalence does not establish its universal descent premise. -/
namespace CollatzTargetDensity.VerifiedDescent

def step (n : Nat) : Nat := if n % 2 = 0 then n / 2 else 3 * n + 1

def iter : Nat → Nat → Nat
  | 0, n => n
  | k + 1, n => step (iter k n)

def Reaches (n a : Nat) : Prop := ∃ k, iter k n = a

def UniversalDescent : Prop :=
  ∀ n : Nat, 1 < n → ∃ k : Nat, iter k n < n

theorem iter_add (k l n : Nat) : iter (k + l) n = iter l (iter k n) := by
  induction l with
  | zero => rfl
  | succ l ih =>
    change step (iter (k + l) n) = step (iter l (iter k n))
    exact congrArg step ih

theorem step_pos {n : Nat} (hn : 0 < n) : 0 < step n := by
  unfold step
  split <;> omega

theorem iterate_pos {n : Nat} (hn : 0 < n) (k : Nat) : 0 < iter k n := by
  induction k with
  | zero => exact hn
  | succ k ih => exact step_pos ih

theorem universal_descent_iff_collatz :
    UniversalDescent ↔ (∀ n : Nat, 0 < n → Reaches n 1) := by
  constructor
  · intro h n
    induction n using Nat.strongRecOn with
    | ind n ih =>
      intro hn
      by_cases h1 : n = 1
      · exact ⟨0, h1⟩
      · obtain ⟨k, hk⟩ := h n (by omega)
        obtain ⟨l, hl⟩ := ih _ hk (iterate_pos hn k)
        exact ⟨k + l, by rw [iter_add]; exact hl⟩
  · intro h n hn
    obtain ⟨k, hk⟩ := h n (by omega)
    exact ⟨k, by rw [hk]; exact hn⟩

theorem even_descent {n : Nat} (hn : 0 < n) (he : n % 2 = 0) :
    step n < n := by
  simp only [step, he, if_true]
  omega

theorem four_q_plus_one_descent {q : Nat} (hq : 0 < q) :
    iter 3 (4 * q + 1) < 4 * q + 1 := by
  have h1 : step (4 * q + 1) = 12 * q + 4 := by
    unfold step
    split <;> omega
  have h2 : step (12 * q + 4) = 6 * q + 2 := by
    unfold step
    split <;> omega
  have h3 : step (6 * q + 2) = 3 * q + 1 := by
    unfold step
    split <;> omega
  change step (step (step (4 * q + 1))) < _
  rw [h1, h2, h3]
  omega

end CollatzTargetDensity.VerifiedDescent

#print axioms CollatzTargetDensity.VerifiedDescent.universal_descent_iff_collatz
#print axioms CollatzTargetDensity.VerifiedDescent.even_descent
#print axioms CollatzTargetDensity.VerifiedDescent.four_q_plus_one_descent
