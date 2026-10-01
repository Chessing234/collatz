import Collatz.Papers.KorecCertified

/-!
# Korec (1994): rational-exponent theorem

The former placeholder inequality did not mention an orbit or count any set.
The statement records the rational-exponent cases of Theorem 1. The separate
certificate development now proves this proposition, and the result is linked
below. Real-valued exponentiation is not part of this core-only interface.

Source: https://www.dml.cz/handle/10338.dmlcz/133225
-/
namespace Collatz.Papers.Journal_1994_Korec_a_density_estimate_for_the_3x

/-- Bibliographic citation. -/
def citation : String :=
  "Ivan Korec, A density estimate for the 3x+1 problem, Mathematica Slovaca 44 (1994), no. 1, 85–89."

/-- The positive rational-exponent subfamily of the published theorem. -/
def mainStatement : Prop := Korec1994.rationalExponentStatement

/-- A conditional specialization, not a proof of the recorded statement. -/
theorem four_fifths_of_mainStatement (h : mainStatement) :
    NaturalDensity.DensityOne (Korec1994.OrbitBelowPower 4 5) :=
  Korec1994.four_fifths_of_statement h

/-- The recorded rational-exponent subfamily is now a checked theorem. -/
theorem mainStatement_proved : mainStatement := Korec1994.rationalExponentStatement_proved

end Collatz.Papers.Journal_1994_Korec_a_density_estimate_for_the_3x
