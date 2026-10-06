import Collatz.Research.CoefficientDescent.Basic

namespace Collatz.Research.CoefficientDescent.Batch001

open FirstDescentClass

set_option maxRecDepth 20000
set_option maxHeartbeats 0

/-- Checked base and every prefix for input 3. -/
theorem certificate_3 : classCertificateB 4 3 = true := by
  decide

/-- The same exact first-descent time holds on an infinite dyadic ray. -/
theorem ray_3 (m : Nat) : stoppingTime (2 ^ 4 * m + 3) 4 :=
  stoppingTime_of_classCertificate certificate_3 m

/-- Checked base and every prefix for input 5. -/
theorem certificate_5 : classCertificateB 2 5 = true := by
  decide

/-- The same exact first-descent time holds on an infinite dyadic ray. -/
theorem ray_5 (m : Nat) : stoppingTime (2 ^ 2 * m + 5) 2 :=
  stoppingTime_of_classCertificate certificate_5 m

/-- Checked base and every prefix for input 7. -/
theorem certificate_7 : classCertificateB 7 7 = true := by
  decide

/-- The same exact first-descent time holds on an infinite dyadic ray. -/
theorem ray_7 (m : Nat) : stoppingTime (2 ^ 7 * m + 7) 7 :=
  stoppingTime_of_classCertificate certificate_7 m

/-- Checked base and every prefix for input 9. -/
theorem certificate_9 : classCertificateB 2 9 = true := by
  decide

/-- The same exact first-descent time holds on an infinite dyadic ray. -/
theorem ray_9 (m : Nat) : stoppingTime (2 ^ 2 * m + 9) 2 :=
  stoppingTime_of_classCertificate certificate_9 m

/-- Checked base and every prefix for input 11. -/
theorem certificate_11 : classCertificateB 5 11 = true := by
  decide

/-- The same exact first-descent time holds on an infinite dyadic ray. -/
theorem ray_11 (m : Nat) : stoppingTime (2 ^ 5 * m + 11) 5 :=
  stoppingTime_of_classCertificate certificate_11 m

/-- Checked base and every prefix for input 13. -/
theorem certificate_13 : classCertificateB 2 13 = true := by
  decide

/-- The same exact first-descent time holds on an infinite dyadic ray. -/
theorem ray_13 (m : Nat) : stoppingTime (2 ^ 2 * m + 13) 2 :=
  stoppingTime_of_classCertificate certificate_13 m

/-- Checked base and every prefix for input 15. -/
theorem certificate_15 : classCertificateB 7 15 = true := by
  decide

/-- The same exact first-descent time holds on an infinite dyadic ray. -/
theorem ray_15 (m : Nat) : stoppingTime (2 ^ 7 * m + 15) 7 :=
  stoppingTime_of_classCertificate certificate_15 m

/-- Checked base and every prefix for input 17. -/
theorem certificate_17 : classCertificateB 2 17 = true := by
  decide

/-- The same exact first-descent time holds on an infinite dyadic ray. -/
theorem ray_17 (m : Nat) : stoppingTime (2 ^ 2 * m + 17) 2 :=
  stoppingTime_of_classCertificate certificate_17 m

/-- Checked base and every prefix for input 19. -/
theorem certificate_19 : classCertificateB 4 19 = true := by
  decide

/-- The same exact first-descent time holds on an infinite dyadic ray. -/
theorem ray_19 (m : Nat) : stoppingTime (2 ^ 4 * m + 19) 4 :=
  stoppingTime_of_classCertificate certificate_19 m

/-- Checked base and every prefix for input 21. -/
theorem certificate_21 : classCertificateB 2 21 = true := by
  decide

/-- The same exact first-descent time holds on an infinite dyadic ray. -/
theorem ray_21 (m : Nat) : stoppingTime (2 ^ 2 * m + 21) 2 :=
  stoppingTime_of_classCertificate certificate_21 m

/-- Checked base and every prefix for input 23. -/
theorem certificate_23 : classCertificateB 5 23 = true := by
  decide

/-- The same exact first-descent time holds on an infinite dyadic ray. -/
theorem ray_23 (m : Nat) : stoppingTime (2 ^ 5 * m + 23) 5 :=
  stoppingTime_of_classCertificate certificate_23 m

/-- Checked base and every prefix for input 25. -/
theorem certificate_25 : classCertificateB 2 25 = true := by
  decide

/-- The same exact first-descent time holds on an infinite dyadic ray. -/
theorem ray_25 (m : Nat) : stoppingTime (2 ^ 2 * m + 25) 2 :=
  stoppingTime_of_classCertificate certificate_25 m

/-- Checked base and every prefix for input 27. -/
theorem certificate_27 : classCertificateB 59 27 = true := by
  decide

/-- The same exact first-descent time holds on an infinite dyadic ray. -/
theorem ray_27 (m : Nat) : stoppingTime (2 ^ 59 * m + 27) 59 :=
  stoppingTime_of_classCertificate certificate_27 m

/-- Checked base and every prefix for input 29. -/
theorem certificate_29 : classCertificateB 2 29 = true := by
  decide

/-- The same exact first-descent time holds on an infinite dyadic ray. -/
theorem ray_29 (m : Nat) : stoppingTime (2 ^ 2 * m + 29) 2 :=
  stoppingTime_of_classCertificate certificate_29 m

/-- Checked base and every prefix for input 31. -/
theorem certificate_31 : classCertificateB 56 31 = true := by
  decide

/-- The same exact first-descent time holds on an infinite dyadic ray. -/
theorem ray_31 (m : Nat) : stoppingTime (2 ^ 56 * m + 31) 56 :=
  stoppingTime_of_classCertificate certificate_31 m

/-- Checked base and every prefix for input 33. -/
theorem certificate_33 : classCertificateB 2 33 = true := by
  decide

/-- The same exact first-descent time holds on an infinite dyadic ray. -/
theorem ray_33 (m : Nat) : stoppingTime (2 ^ 2 * m + 33) 2 :=
  stoppingTime_of_classCertificate certificate_33 m

/-- Checked base and every prefix for input 35. -/
theorem certificate_35 : classCertificateB 4 35 = true := by
  decide

/-- The same exact first-descent time holds on an infinite dyadic ray. -/
theorem ray_35 (m : Nat) : stoppingTime (2 ^ 4 * m + 35) 4 :=
  stoppingTime_of_classCertificate certificate_35 m

/-- Checked base and every prefix for input 37. -/
theorem certificate_37 : classCertificateB 2 37 = true := by
  decide

/-- The same exact first-descent time holds on an infinite dyadic ray. -/
theorem ray_37 (m : Nat) : stoppingTime (2 ^ 2 * m + 37) 2 :=
  stoppingTime_of_classCertificate certificate_37 m

/-- Checked base and every prefix for input 39. -/
theorem certificate_39 : classCertificateB 8 39 = true := by
  decide

/-- The same exact first-descent time holds on an infinite dyadic ray. -/
theorem ray_39 (m : Nat) : stoppingTime (2 ^ 8 * m + 39) 8 :=
  stoppingTime_of_classCertificate certificate_39 m

/-- Checked base and every prefix for input 41. -/
theorem certificate_41 : classCertificateB 2 41 = true := by
  decide

/-- The same exact first-descent time holds on an infinite dyadic ray. -/
theorem ray_41 (m : Nat) : stoppingTime (2 ^ 2 * m + 41) 2 :=
  stoppingTime_of_classCertificate certificate_41 m

/-- Checked base and every prefix for input 43. -/
theorem certificate_43 : classCertificateB 5 43 = true := by
  decide

/-- The same exact first-descent time holds on an infinite dyadic ray. -/
theorem ray_43 (m : Nat) : stoppingTime (2 ^ 5 * m + 43) 5 :=
  stoppingTime_of_classCertificate certificate_43 m

/-- Checked base and every prefix for input 45. -/
theorem certificate_45 : classCertificateB 2 45 = true := by
  decide

/-- The same exact first-descent time holds on an infinite dyadic ray. -/
theorem ray_45 (m : Nat) : stoppingTime (2 ^ 2 * m + 45) 2 :=
  stoppingTime_of_classCertificate certificate_45 m

/-- Checked base and every prefix for input 47. -/
theorem certificate_47 : classCertificateB 54 47 = true := by
  decide

/-- The same exact first-descent time holds on an infinite dyadic ray. -/
theorem ray_47 (m : Nat) : stoppingTime (2 ^ 54 * m + 47) 54 :=
  stoppingTime_of_classCertificate certificate_47 m

/-- Checked base and every prefix for input 49. -/
theorem certificate_49 : classCertificateB 2 49 = true := by
  decide

/-- The same exact first-descent time holds on an infinite dyadic ray. -/
theorem ray_49 (m : Nat) : stoppingTime (2 ^ 2 * m + 49) 2 :=
  stoppingTime_of_classCertificate certificate_49 m

/-- Checked base and every prefix for input 51. -/
theorem certificate_51 : classCertificateB 4 51 = true := by
  decide

/-- The same exact first-descent time holds on an infinite dyadic ray. -/
theorem ray_51 (m : Nat) : stoppingTime (2 ^ 4 * m + 51) 4 :=
  stoppingTime_of_classCertificate certificate_51 m

/-- Checked base and every prefix for input 53. -/
theorem certificate_53 : classCertificateB 2 53 = true := by
  decide

/-- The same exact first-descent time holds on an infinite dyadic ray. -/
theorem ray_53 (m : Nat) : stoppingTime (2 ^ 2 * m + 53) 2 :=
  stoppingTime_of_classCertificate certificate_53 m

/-- Checked base and every prefix for input 55. -/
theorem certificate_55 : classCertificateB 5 55 = true := by
  decide

/-- The same exact first-descent time holds on an infinite dyadic ray. -/
theorem ray_55 (m : Nat) : stoppingTime (2 ^ 5 * m + 55) 5 :=
  stoppingTime_of_classCertificate certificate_55 m

/-- Checked base and every prefix for input 57. -/
theorem certificate_57 : classCertificateB 2 57 = true := by
  decide

/-- The same exact first-descent time holds on an infinite dyadic ray. -/
theorem ray_57 (m : Nat) : stoppingTime (2 ^ 2 * m + 57) 2 :=
  stoppingTime_of_classCertificate certificate_57 m

/-- Checked base and every prefix for input 59. -/
theorem certificate_59 : classCertificateB 7 59 = true := by
  decide

/-- The same exact first-descent time holds on an infinite dyadic ray. -/
theorem ray_59 (m : Nat) : stoppingTime (2 ^ 7 * m + 59) 7 :=
  stoppingTime_of_classCertificate certificate_59 m

/-- Checked base and every prefix for input 61. -/
theorem certificate_61 : classCertificateB 2 61 = true := by
  decide

/-- The same exact first-descent time holds on an infinite dyadic ray. -/
theorem ray_61 (m : Nat) : stoppingTime (2 ^ 2 * m + 61) 2 :=
  stoppingTime_of_classCertificate certificate_61 m

/-- Checked base and every prefix for input 63. -/
theorem certificate_63 : classCertificateB 54 63 = true := by
  decide

/-- The same exact first-descent time holds on an infinite dyadic ray. -/
theorem ray_63 (m : Nat) : stoppingTime (2 ^ 54 * m + 63) 54 :=
  stoppingTime_of_classCertificate certificate_63 m

/-- Checked base and every prefix for input 65. -/
theorem certificate_65 : classCertificateB 2 65 = true := by
  decide

/-- The same exact first-descent time holds on an infinite dyadic ray. -/
theorem ray_65 (m : Nat) : stoppingTime (2 ^ 2 * m + 65) 2 :=
  stoppingTime_of_classCertificate certificate_65 m

/-- Checked base and every prefix for input 67. -/
theorem certificate_67 : classCertificateB 4 67 = true := by
  decide

/-- The same exact first-descent time holds on an infinite dyadic ray. -/
theorem ray_67 (m : Nat) : stoppingTime (2 ^ 4 * m + 67) 4 :=
  stoppingTime_of_classCertificate certificate_67 m

/-- Exhaustive coverage of the odd inputs in this batch, with no gaps. -/
theorem coverage : CertifiedRange 3 69 := by
  intro n hlo hhi hodd
  have hn : n = 3 ∨ n = 5 ∨ n = 7 ∨ n = 9 ∨ n = 11 ∨ n = 13 ∨ n = 15 ∨ n = 17 ∨ n = 19 ∨ n = 21 ∨ n = 23 ∨ n = 25 ∨ n = 27 ∨ n = 29 ∨ n = 31 ∨ n = 33 ∨ n = 35 ∨ n = 37 ∨ n = 39 ∨ n = 41 ∨ n = 43 ∨ n = 45 ∨ n = 47 ∨ n = 49 ∨ n = 51 ∨ n = 53 ∨ n = 55 ∨ n = 57 ∨ n = 59 ∨ n = 61 ∨ n = 63 ∨ n = 65 ∨ n = 67 := by omega
  rcases hn with h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h
  · subst n
    exact ⟨4, witness_of_certificate certificate_3⟩
  · subst n
    exact ⟨2, witness_of_certificate certificate_5⟩
  · subst n
    exact ⟨7, witness_of_certificate certificate_7⟩
  · subst n
    exact ⟨2, witness_of_certificate certificate_9⟩
  · subst n
    exact ⟨5, witness_of_certificate certificate_11⟩
  · subst n
    exact ⟨2, witness_of_certificate certificate_13⟩
  · subst n
    exact ⟨7, witness_of_certificate certificate_15⟩
  · subst n
    exact ⟨2, witness_of_certificate certificate_17⟩
  · subst n
    exact ⟨4, witness_of_certificate certificate_19⟩
  · subst n
    exact ⟨2, witness_of_certificate certificate_21⟩
  · subst n
    exact ⟨5, witness_of_certificate certificate_23⟩
  · subst n
    exact ⟨2, witness_of_certificate certificate_25⟩
  · subst n
    exact ⟨59, witness_of_certificate certificate_27⟩
  · subst n
    exact ⟨2, witness_of_certificate certificate_29⟩
  · subst n
    exact ⟨56, witness_of_certificate certificate_31⟩
  · subst n
    exact ⟨2, witness_of_certificate certificate_33⟩
  · subst n
    exact ⟨4, witness_of_certificate certificate_35⟩
  · subst n
    exact ⟨2, witness_of_certificate certificate_37⟩
  · subst n
    exact ⟨8, witness_of_certificate certificate_39⟩
  · subst n
    exact ⟨2, witness_of_certificate certificate_41⟩
  · subst n
    exact ⟨5, witness_of_certificate certificate_43⟩
  · subst n
    exact ⟨2, witness_of_certificate certificate_45⟩
  · subst n
    exact ⟨54, witness_of_certificate certificate_47⟩
  · subst n
    exact ⟨2, witness_of_certificate certificate_49⟩
  · subst n
    exact ⟨4, witness_of_certificate certificate_51⟩
  · subst n
    exact ⟨2, witness_of_certificate certificate_53⟩
  · subst n
    exact ⟨5, witness_of_certificate certificate_55⟩
  · subst n
    exact ⟨2, witness_of_certificate certificate_57⟩
  · subst n
    exact ⟨7, witness_of_certificate certificate_59⟩
  · subst n
    exact ⟨2, witness_of_certificate certificate_61⟩
  · subst n
    exact ⟨54, witness_of_certificate certificate_63⟩
  · subst n
    exact ⟨2, witness_of_certificate certificate_65⟩
  · subst n
    exact ⟨4, witness_of_certificate certificate_67⟩

end Collatz.Research.CoefficientDescent.Batch001
