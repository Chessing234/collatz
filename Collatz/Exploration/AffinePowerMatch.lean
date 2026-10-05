import Collatz.Exploration.ThreePowerUnits

/-!
# Matching ternary affine families to large powers of two

The arithmetic family 3^a*m+B contains arbitrarily large powers of two whenever
a=0 or B is a unit modulo three. This is an exact existence theorem about a
natural arithmetic progression, obtained from unit coverage modulo 3^a.
It will be applied to endpoints of fixed Collatz parity classes.

All division and subtraction are justified by a residue equality and the size
of the chosen power. No formal quotient with negative natural subtraction is
accepted as a witness.
-/
namespace Collatz.Exploration.AffinePowerMatch

open ThreePowerUnits

/-- A larger number with the same residue is a nonnegative affine translate. -/
theorem translate_of_residue {A B x : Nat} (hB : B ≤ x) (hmod : x%A = B%A) :
    ∃ m, A*m+B = x := by
  let m := x/A-B/A
  have hq : B/A ≤ x/A := Nat.div_le_div_right hB
  have hmul : A*(B/A) ≤ A*(x/A) := Nat.mul_le_mul_left A hq
  have hdelta : A*m+A*(B/A) = A*(x/A) := by
    dsimp [m]
    rw [Nat.mul_sub, Nat.sub_add_cancel hmul]
  have hx := Nat.mod_add_div x A
  have hb := Nat.mod_add_div B A
  rw [hmod] at hx
  exact ⟨m, by omega⟩

/-- The index must exceed N when the selected affine value exceeds its Nth value. -/
theorem index_large {A B x m N : Nat} (hmatch : A*m+B = x)
    (hlarge : A*N+B < x) : N < m := by
  by_cases hN : N < m
  · exact hN
  · have hmul := Nat.mul_le_mul_left A (show m ≤ N by omega)
    omega

/-- Large powers can meet the affine residue condition, including a=0. -/
theorem large_matching_power (a B N : Nat) (hunit : a = 0 ∨ B%3 ≠ 0) :
    ∃ e, 3^a*N+B < (2:Nat)^e ∧ (2:Nat)^e%3^a = B%3^a := by
  by_cases ha : a = 0
  · subst a
    refine ⟨N+B, ?_, ?_⟩
    · simpa using (Nat.lt_two_pow_self : N+B < (2:Nat)^(N+B))
    · simp [Nat.mod_one]
  · have hb : B%3 ≠ 0 := hunit.resolve_left ha
    exact unbounded_values a B (3^a*N+B) hb

/-- Every unit affine family has arbitrarily large power-of-two values. -/
theorem power_match (a B N : Nat) (hunit : a = 0 ∨ B%3 ≠ 0) :
    ∃ m e, N < m ∧ 3^a*m+B = (2:Nat)^e := by
  obtain ⟨e, hlarge, hmod⟩ := large_matching_power a B N hunit
  have hB : B ≤ (2:Nat)^e := by omega
  obtain ⟨m, hm⟩ := translate_of_residue hB hmod
  exact ⟨m, e, index_large hm hlarge, hm⟩

/-- The same result stated with the endpoint itself beyond any prescribed bound. -/
theorem power_match_above (a B N C : Nat) (hunit : a = 0 ∨ B%3 ≠ 0) :
    ∃ m e, N < m ∧ C < (2:Nat)^e ∧ 3^a*m+B = (2:Nat)^e := by
  obtain ⟨m, e, hm, he⟩ := power_match a B (N+C) hunit
  have hpow : 1 ≤ (3:Nat)^a := by
    have := Nat.pow_pos (a := 3) (n := a) (by decide)
    omega
  have hmul := Nat.mul_le_mul_right m hpow
  simp only [Nat.one_mul] at hmul
  exact ⟨m, e, by omega, by omega, he⟩

/-- Divisible-by-three offsets cannot match a positive ternary multiplier.
This records the necessary obstruction and prevents dropping the unit premise. -/
theorem no_power_match_of_nonunit {a B m e : Nat} (ha : 0 < a)
    (hB : B%3 = 0) :
    3^a*m+B ≠ (2:Nat)^e := by
  intro he
  obtain ⟨j, hj⟩ : ∃ j, a = j+1 := ⟨a-1, by omega⟩
  have hpow : (3:Nat)^a%3 = 0 := by
    rw [hj, Nat.pow_succ, Nat.mul_mod]
    simp
  have h := congrArg (fun x => x%3) he
  simp [Nat.add_mod, Nat.mul_mod, hpow, hB] at h
  exact power_two_unit e h.symm

end Collatz.Exploration.AffinePowerMatch
