import Collatz.Strategy.LiftExponentThree

/-!
# Exact ternary lifting coefficient for powers of two

The existing lifting theorem gives divisibility of 2^(2*3^j)-1 by 3^(j+1).
For inverse-orbit constructions, divisibility alone does not ensure that the
three lifts modulo the next power are distinct. The quotient must be a unit.
Here the stronger identity has a coefficient congruent to 1 modulo 3.

This is elementary arithmetic supporting backward exploration. No Collatz
convergence assumption enters, and no claim of novelty in number theory is made.
-/
namespace Collatz.Exploration.ThreePowerLift

/-- Quotient update obtained when an identity is cubed. -/
def cubeCoefficient (t c : Nat) : Nat :=
  3*(t*t)*(c*c*c)+3*t*(c*c)+c

/-- Cubing raises the power of three by exactly one when c is a unit. -/
theorem cube_lift (t c : Nat) :
    (3*t*c+1)^3 = 9*t*cubeCoefficient t c+1 := by
  have hb : 3*t*c = 3*(t*c) := by ac_rfl
  have hp : (3*(t*c)+1)^3 =
      (3*(t*c)+1)*(3*(t*c)+1)*(3*(t*c)+1) := by
    simp [Nat.pow_succ]
  rw [hb, hp, LiftExponentThree.cube_three]
  have e2 : (t*c)*(t*c) = (t*t)*(c*c) := Nat.mul_mul_mul_comm _ _ _ _
  have e3 : (t*c)*(t*c)*(t*c) = (t*t*t)*(c*c*c) := by
    rw [Nat.mul_mul_mul_comm t c t c,
      Nat.mul_mul_mul_comm (t*t) (c*c) t c]
  have h1 : 9*t*(3*(t*t)*(c*c*c)) = 27*(t*t*t)*(c*c*c) := by
    calc
      _ = (9*3)*(t*t*t)*(c*c*c) := by ac_rfl
      _ = _ := rfl
  have h2 : 9*t*(3*t*(c*c)) = 27*(t*t)*(c*c) := by
    calc
      _ = (9*3)*(t*t)*(c*c) := by ac_rfl
      _ = _ := rfl
  unfold cubeCoefficient
  rw [e3, e2, Nat.mul_add, Nat.mul_add, h1, h2]
  simp only [Nat.mul_assoc]

/-- The update preserves the quotient's nonzero residue modulo three. -/
theorem cubeCoefficient_mod_three (t c : Nat) : cubeCoefficient t c % 3 = c%3 := by
  simp [cubeCoefficient, Nat.add_mod, Nat.mul_mod]

/-- The exact lifting identity, including its unit quotient. -/
theorem exact_lift (j : Nat) :
    ∃ c, (2:Nat)^(2*3^j) = 3^(j+1)*c+1 ∧ c%3 = 1 := by
  induction j with
  | zero => exact ⟨1, by decide, by decide⟩
  | succ j ih =>
    obtain ⟨c, hc, hmod⟩ := ih
    refine ⟨cubeCoefficient (3^j) c, ?_, ?_⟩
    · have hexp : 2*3^(j+1) = (2*3^j)*3 := by
        rw [Nat.pow_succ]
        ac_rfl
      have hbase : 3^(j+1)*c = 3*3^j*c := by
        rw [Nat.pow_succ]
        ac_rfl
      have hnext : (3:Nat)^(j+1+1) = 9*3^j := by
        rw [Nat.pow_succ, Nat.pow_succ]
        omega
      rw [hexp, Nat.pow_mul, hc, hbase, cube_lift, hnext]
    · rw [cubeCoefficient_mod_three, hmod]

/-- The quotient is positive, so the lifted power really exceeds one. -/
theorem exact_lift_positive (j : Nat) :
    ∃ c, 0 < c ∧ (2:Nat)^(2*3^j) = 3^(j+1)*c+1 ∧ c%3 = 1 := by
  obtain ⟨c, hc, hm⟩ := exact_lift j
  exact ⟨c, by omega, hc, hm⟩

/-- The power returns to 1 at the prescribed ternary modulus. -/
theorem period_mod (j : Nat) : (2:Nat)^(2*3^j) % 3^(j+1) = 1 := by
  obtain ⟨c, hc, _⟩ := exact_lift j
  have hgt : 1 < (3:Nat)^(j+1) := by
    have hp := Nat.pow_le_pow_right (by decide : 0 < (3:Nat)) (show 1 ≤ j+1 by omega)
    have he : (3:Nat)^1 = 3 := rfl
    omega
  rw [hc, Nat.add_mod, Nat.mul_mod]
  simp [Nat.mod_eq_of_lt hgt]

/-- The same power fails to return at the next ternary modulus.
The exact quotient excludes accidental extra divisibility. -/
theorem not_period_next (j : Nat) : (2:Nat)^(2*3^j) % 3^(j+2) ≠ 1 := by
  obtain ⟨c, hc, hm⟩ := exact_lift j
  have hq : 0 < (3:Nat)^(j+1) := Nat.pow_pos (by decide)
  have hnext : (3:Nat)^(j+2) = 3^(j+1)*3 := by rw [show j+2 = (j+1)+1 by omega, Nat.pow_succ]
  intro h
  let q := (2:Nat)^(2*3^j) / 3^(j+2)
  have hdiv := Nat.mod_add_div ((2:Nat)^(2*3^j)) (3^(j+2))
  change (2:Nat)^(2*3^j)%3^(j+2)+3^(j+2)*q = (2:Nat)^(2*3^j) at hdiv
  rw [h] at hdiv
  have hn : 1+3^(j+2)*q = 3^(j+1)*c+1 := hdiv.trans hc
  rw [hnext] at hn
  have hmul : 3^(j+1)*3*q = 3^(j+1)*(3*q) := by ac_rfl
  have he : 3^(j+1)*c = 3^(j+1)*(3*q) := by omega
  have hcdiv := Nat.eq_of_mul_eq_mul_left hq he
  rw [hcdiv, Nat.mul_mod] at hm
  simp at hm

end Collatz.Exploration.ThreePowerLift
