import Collatz.Exploration.ThreeUnitLift

/-!
# Powers of two cover all units modulo every power of three

The local three-lift construction and the exact period quotient combine into
an inductive proof of surjectivity: if z is not divisible by three, then for
any a there is an exponent e with 2^e = z modulo 3^a. Exponents can be chosen
arbitrarily large. This is the classical primitive-root fact in the form needed
by inverse Collatz equations; minimality of the multiplicative order is not
claimed by the surjectivity theorem.

No probability, external computation, or Collatz convergence is assumed.
-/
namespace Collatz.Exploration.ThreePowerUnits

open ThreePowerLift ThreeUnitLift

/-- Unit coverage at a modulus, with no bound asserted on the exponent. -/
def UnitCoverage (q : Nat) : Prop :=
  ∀ z, z%3 ≠ 0 → ∃ e, (2:Nat)^e%q = z%q

/-- The two nonzero residues modulo three are the first two powers of two. -/
theorem coverage_three : UnitCoverage 3 := by
  intro z hz
  have hcases : z%3 = 1 ∨ z%3 = 2 := by omega
  rcases hcases with h | h
  · exact ⟨0, by simpa using h.symm⟩
  · exact ⟨1, by simpa using h.symm⟩

/-- A period with unit quotient lifts coverage to the next ternary modulus. -/
theorem coverage_lift {q p c : Nat} (hq : q%3 = 0)
    (hc : c%3 = 1) (hperiod : (2:Nat)^p = 1+q*c)
    (hcover : UnitCoverage q) : UnitCoverage (q*3) := by
  intro z hz
  obtain ⟨e, he⟩ := hcover z hz
  have hdvd : 3 ∣ q := Nat.dvd_of_mod_eq_zero hq
  have hunit : (2:Nat)^e%3 ≠ 0 := by
    have hlow := congrArg (fun v => v%3) he
    rw [Nat.mod_mod_of_dvd _ hdvd, Nat.mod_mod_of_dvd _ hdvd] at hlow
    omega
  obtain ⟨t, _, ht⟩ := three_lifts ((2:Nat)^e) z q c hunit hq hc he
  refine ⟨e+p*t, ?_⟩
  rw [Nat.pow_add, Nat.pow_mul, hperiod]
  exact ht

/-- Coverage for every positive ternary exponent, by successive three-lifts. -/
theorem coverage_positive (j : Nat) : UnitCoverage (3^(j+1)) := by
  induction j with
  | zero => exact coverage_three
  | succ j ih =>
    obtain ⟨c, hc, hmod⟩ := exact_lift j
    have hq : (3:Nat)^(j+1)%3 = 0 := by
      rw [Nat.pow_succ, Nat.mul_mod]
      simp
    have hperiod : (2:Nat)^(2*3^j) = 1+3^(j+1)*c := by omega
    have h := coverage_lift hq hmod hperiod ih
    simpa [Nat.pow_succ] using h

/-- Every unit is represented by a power of two at every ternary modulus. -/
theorem power_representation (a z : Nat) (hz : z%3 ≠ 0) :
    ∃ e, (2:Nat)^e%3^a = z%3^a := by
  cases a with
  | zero => exact ⟨0, by simp [Nat.mod_one]⟩
  | succ j => exact coverage_positive j z hz

/-- A power of two is never divisible by three. -/
theorem power_two_unit (e : Nat) : (2:Nat)^e%3 ≠ 0 := by
  induction e with
  | zero => decide
  | succ e ih =>
    rw [Nat.pow_succ, Nat.mul_mod]
    have hcases : (2:Nat)^e%3 = 1 ∨ (2:Nat)^e%3 = 2 := by omega
    rcases hcases with h | h <;> rw [h] <;> decide

/-- Adding any multiple of a known period preserves a power's residue. -/
theorem power_period_shift (q p e d : Nat) (hq : 1 < q)
    (hp : (2:Nat)^p%q = 1) :
    (2:Nat)^(e+p*d)%q = (2:Nat)^e%q := by
  have hs : ((2:Nat)^p)^d%q = 1 := by
    rw [Nat.pow_mod (2^p) d q, hp]
    simp [Nat.mod_eq_of_lt hq]
  rw [Nat.pow_add, Nat.mul_mod, Nat.pow_mul, hs]
  simp

/-- A unit representative exists within the known period, making exhaustive
finite exponent search a complete procedure at each ternary modulus. -/
theorem bounded_exponent (j z : Nat) (hz : z%3 ≠ 0) :
    ∃ e, e < 2*3^j ∧ (2:Nat)^e%3^(j+1) = z%3^(j+1) := by
  obtain ⟨e, he⟩ := power_representation (j+1) z hz
  have hp : 0 < 2*3^j := Nat.mul_pos (by decide) (Nat.pow_pos (by decide))
  have hq : 1 < (3:Nat)^(j+1) := by
    have h := Nat.pow_le_pow_right (by decide : 0 < (3:Nat)) (show 1 ≤ j+1 by omega)
    have hval : (3:Nat)^1 = 3 := rfl
    omega
  have hr := power_period_shift (3^(j+1)) (2*3^j)
    (e%(2*3^j)) (e/(2*3^j)) hq (period_mod j)
  rw [Nat.mod_add_div] at hr
  exact ⟨e%(2*3^j), Nat.mod_lt _ hp, hr.symm.trans he⟩

/-- Unit representatives can be chosen beyond any prescribed exponent. -/
theorem unbounded_exponents (a z B : Nat) (hz : z%3 ≠ 0) :
    ∃ e, B ≤ e ∧ (2:Nat)^e%3^a = z%3^a := by
  cases a with
  | zero => exact ⟨B, Nat.le_refl _, by simp [Nat.mod_one]⟩
  | succ j =>
    obtain ⟨e, he⟩ := power_representation (j+1) z hz
    let p := 2*3^j
    have hpos : 1 ≤ p := by
      have h := Nat.pow_pos (a := 3) (n := j) (by decide)
      dsimp [p]
      omega
    have hq : 1 < (3:Nat)^(j+1) := by
      have h := Nat.pow_le_pow_right (by decide : 0 < (3:Nat)) (show 1 ≤ j+1 by omega)
      have hval : (3:Nat)^1 = 3 := rfl
      omega
    refine ⟨e+p*B, ?_, ?_⟩
    · have h := Nat.mul_le_mul_right B hpos
      simp only [Nat.one_mul] at h
      omega
    · rw [power_period_shift _ p e B hq (period_mod j), he]

/-- There are arbitrarily large actual power-of-two representatives as well. -/
theorem unbounded_values (a z B : Nat) (hz : z%3 ≠ 0) :
    ∃ e, B < (2:Nat)^e ∧ (2:Nat)^e%3^a = z%3^a := by
  obtain ⟨e, he, hmod⟩ := unbounded_exponents a z B hz
  have hlt : B < (2:Nat)^B := Nat.lt_two_pow_self
  have hpow := Nat.pow_le_pow_right (by decide : 0 < (2:Nat)) he
  exact ⟨e, Nat.lt_of_lt_of_le hlt hpow, hmod⟩

end Collatz.Exploration.ThreePowerUnits
