import Collatz.Structure.NaturalDensity

/-!
# Korec's density estimate: a rational-exponent formulation

Source: Ivan Korec, Mathematica Slovaca 44 (1994), 85–89, Theorem 1.
https://www.dml.cz/handle/10338.dmlcz/133225

The paper uses the accelerated map and proves density one for orbit values
below n^c when c>log₄3. We record its positive rational-exponent subfamily:
c=p/q, with 3^q<4^p encoding the strict threshold. Integer powers express the
orbit inequality without real exponentiation. The separate KorecCertified
module proves the complete rational-exponent statement recorded here. The
real-exponent formulation is not formalized in this interface.
-/
namespace Collatz.Papers.Korec1994
open NaturalDensity

/-- Some accelerated iterate is below the rational power n^(p/q), for q>0. -/
def OrbitBelowPower (p q n : Nat) : Prop :=
  ∃ k : Nat, (acceleratedOrbit k n)^q < n^p

/-- Rational-exponent cases of Korec's result, recorded rather than assumed. -/
def rationalExponentStatement : Prop :=
  ∀ p q : Nat, 0<q → 3^q<4^p → DensityOne (OrbitBelowPower p q)

/-- The threshold includes exponent 4/5, and it is strict. -/
theorem four_fifths_admissible : (3:Nat)^5 < 4^4 := by decide

/-- Any proof of the recorded statement would imply its 4/5 specialization. -/
theorem four_fifths_of_statement (h : rationalExponentStatement) :
    DensityOne (OrbitBelowPower 4 5) := h 4 5 (by decide) four_fifths_admissible

/-- Increasing the numerator weakens the orbit bound on positive starts. -/
theorem orbitBelowPower_mono {p p' q n : Nat} (hn : 0<n) (hpp : p≤p')
    (h : OrbitBelowPower p q n) : OrbitBelowPower p' q n := by
  obtain ⟨k, hk⟩ := h
  exact ⟨k, Nat.lt_of_lt_of_le hk (Nat.pow_le_pow_right (by omega) hpp)⟩

/-- A concrete orbit witness checks the accelerated-map and strict-power conventions. -/
theorem two_below_four_fifths : OrbitBelowPower 4 5 2 := by
  refine ⟨1, ?_⟩
  decide

/-- The strict bound excludes the fixed minimal orbit at starting value 1. -/
theorem one_not_below_power (p q : Nat) : ¬ OrbitBelowPower p q 1 := by
  intro h
  obtain ⟨k, hk⟩ := h
  have hp := acceleratedOrbit_positive (by decide : 0<(1:Nat)) k
  have hpow : 1≤(acceleratedOrbit k 1)^q := Nat.one_le_pow _ _ (by omega)
  simp only [Nat.one_pow] at hk
  omega

end Collatz.Papers.Korec1994
