import Collatz.Strategy.FirstDescentClassComplete

/-!
# Complete-class first-descent examples

These kernel-checked certificates prove exact times for unbounded families.
The representatives 2 and 5 deliberately start beyond the zero and one
exceptions. No finite collection of the families is asserted to cover all
positive inputs.
-/

namespace Collatz.FirstDescentClass

/-- Every positive even input first descends in one step. -/
theorem even_class_certificate : classCertificateB 1 2 = true := by decide

/-- Every member of the nontrivial one-modulo-four ray first descends at time two. -/
theorem one_mod_four_certificate : classCertificateB 2 5 = true := by decide

/-- The complete residue class three modulo sixteen has first descent at time four. -/
theorem three_mod_sixteen_certificate : classCertificateB 4 3 = true := by decide

/-- The first time-five class. -/
theorem eleven_mod_thirty_two_certificate : classCertificateB 5 11 = true := by decide

/-- The second time-five class. -/
theorem twenty_three_mod_thirty_two_certificate : classCertificateB 5 23 = true := by decide

/-- A time-seven class with an early long rise. -/
theorem seven_mod_128_certificate : classCertificateB 7 7 = true := by decide

/-- A second time-seven class. -/
theorem fifteen_mod_128_certificate : classCertificateB 7 15 = true := by decide

/-- A third time-seven class. -/
theorem fifty_nine_mod_128_certificate : classCertificateB 7 59 = true := by decide

/-- Exact first-descent time on the positive even ray. -/
theorem even_class_stoppingTime (m : Nat) : stoppingTime (2 * m + 2) 1 :=
  stoppingTime_of_classCertificate even_class_certificate m

/-- Exact first-descent time on the nontrivial one-modulo-four ray. -/
theorem one_mod_four_stoppingTime (m : Nat) : stoppingTime (4 * m + 5) 2 :=
  stoppingTime_of_classCertificate one_mod_four_certificate m

/-- Exact first-descent time on the complete three-modulo-sixteen class. -/
theorem three_mod_sixteen_stoppingTime (m : Nat) : stoppingTime (16 * m + 3) 4 :=
  stoppingTime_of_classCertificate three_mod_sixteen_certificate m

/-- Exact first-descent time on the complete eleven-modulo-thirty-two class. -/
theorem eleven_mod_thirty_two_stoppingTime (m : Nat) : stoppingTime (32 * m + 11) 5 :=
  stoppingTime_of_classCertificate eleven_mod_thirty_two_certificate m

/-- Exact first-descent time on the complete twenty-three-modulo-thirty-two class. -/
theorem twenty_three_mod_thirty_two_stoppingTime (m : Nat) : stoppingTime (32 * m + 23) 5 :=
  stoppingTime_of_classCertificate twenty_three_mod_thirty_two_certificate m

/-- The input one has no first-descent time, so it is excluded from that ray. -/
theorem trivial_one_not_a_class_certificate : classCertificateB 2 1 = false := by decide

/-- A later small endpoint cannot substitute for a minimal-time class certificate. -/
theorem later_time_rejected : classCertificateB 5 3 = false := by decide

end Collatz.FirstDescentClass
