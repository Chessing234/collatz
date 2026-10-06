import Collatz.Research.CoefficientDescent.Basic

namespace Collatz.Research.CoefficientDescent.Batch053

open FirstDescentClass

set_option maxRecDepth 20000
set_option maxHeartbeats 0

/-- Checked base and every prefix for input 3485. -/
theorem certificate_3485 : classCertificateB 2 3485 = true := by
  decide

/-- The same exact first-descent time holds on an infinite dyadic ray. -/
theorem ray_3485 (m : Nat) : stoppingTime (2 ^ 2 * m + 3485) 2 :=
  stoppingTime_of_classCertificate certificate_3485 m

/-- Checked base and every prefix for input 3487. -/
theorem certificate_3487 : classCertificateB 16 3487 = true := by
  decide

/-- The same exact first-descent time holds on an infinite dyadic ray. -/
theorem ray_3487 (m : Nat) : stoppingTime (2 ^ 16 * m + 3487) 16 :=
  stoppingTime_of_classCertificate certificate_3487 m

/-- Checked base and every prefix for input 3489. -/
theorem certificate_3489 : classCertificateB 2 3489 = true := by
  decide

/-- The same exact first-descent time holds on an infinite dyadic ray. -/
theorem ray_3489 (m : Nat) : stoppingTime (2 ^ 2 * m + 3489) 2 :=
  stoppingTime_of_classCertificate certificate_3489 m

/-- Checked base and every prefix for input 3491. -/
theorem certificate_3491 : classCertificateB 4 3491 = true := by
  decide

/-- The same exact first-descent time holds on an infinite dyadic ray. -/
theorem ray_3491 (m : Nat) : stoppingTime (2 ^ 4 * m + 3491) 4 :=
  stoppingTime_of_classCertificate certificate_3491 m

/-- Checked base and every prefix for input 3493. -/
theorem certificate_3493 : classCertificateB 2 3493 = true := by
  decide

/-- The same exact first-descent time holds on an infinite dyadic ray. -/
theorem ray_3493 (m : Nat) : stoppingTime (2 ^ 2 * m + 3493) 2 :=
  stoppingTime_of_classCertificate certificate_3493 m

/-- Checked base and every prefix for input 3495. -/
theorem certificate_3495 : classCertificateB 10 3495 = true := by
  decide

/-- The same exact first-descent time holds on an infinite dyadic ray. -/
theorem ray_3495 (m : Nat) : stoppingTime (2 ^ 10 * m + 3495) 10 :=
  stoppingTime_of_classCertificate certificate_3495 m

/-- Checked base and every prefix for input 3497. -/
theorem certificate_3497 : classCertificateB 2 3497 = true := by
  decide

/-- The same exact first-descent time holds on an infinite dyadic ray. -/
theorem ray_3497 (m : Nat) : stoppingTime (2 ^ 2 * m + 3497) 2 :=
  stoppingTime_of_classCertificate certificate_3497 m

/-- Checked base and every prefix for input 3499. -/
theorem certificate_3499 : classCertificateB 5 3499 = true := by
  decide

/-- The same exact first-descent time holds on an infinite dyadic ray. -/
theorem ray_3499 (m : Nat) : stoppingTime (2 ^ 5 * m + 3499) 5 :=
  stoppingTime_of_classCertificate certificate_3499 m

/-- Checked base and every prefix for input 3501. -/
theorem certificate_3501 : classCertificateB 2 3501 = true := by
  decide

/-- The same exact first-descent time holds on an infinite dyadic ray. -/
theorem ray_3501 (m : Nat) : stoppingTime (2 ^ 2 * m + 3501) 2 :=
  stoppingTime_of_classCertificate certificate_3501 m

/-- Checked base and every prefix for input 3503. -/
theorem certificate_3503 : classCertificateB 8 3503 = true := by
  decide

/-- The same exact first-descent time holds on an infinite dyadic ray. -/
theorem ray_3503 (m : Nat) : stoppingTime (2 ^ 8 * m + 3503) 8 :=
  stoppingTime_of_classCertificate certificate_3503 m

/-- Checked base and every prefix for input 3505. -/
theorem certificate_3505 : classCertificateB 2 3505 = true := by
  decide

/-- The same exact first-descent time holds on an infinite dyadic ray. -/
theorem ray_3505 (m : Nat) : stoppingTime (2 ^ 2 * m + 3505) 2 :=
  stoppingTime_of_classCertificate certificate_3505 m

/-- Checked base and every prefix for input 3507. -/
theorem certificate_3507 : classCertificateB 4 3507 = true := by
  decide

/-- The same exact first-descent time holds on an infinite dyadic ray. -/
theorem ray_3507 (m : Nat) : stoppingTime (2 ^ 4 * m + 3507) 4 :=
  stoppingTime_of_classCertificate certificate_3507 m

/-- Checked base and every prefix for input 3509. -/
theorem certificate_3509 : classCertificateB 2 3509 = true := by
  decide

/-- The same exact first-descent time holds on an infinite dyadic ray. -/
theorem ray_3509 (m : Nat) : stoppingTime (2 ^ 2 * m + 3509) 2 :=
  stoppingTime_of_classCertificate certificate_3509 m

/-- Checked base and every prefix for input 3511. -/
theorem certificate_3511 : classCertificateB 5 3511 = true := by
  decide

/-- The same exact first-descent time holds on an infinite dyadic ray. -/
theorem ray_3511 (m : Nat) : stoppingTime (2 ^ 5 * m + 3511) 5 :=
  stoppingTime_of_classCertificate certificate_3511 m

/-- Checked base and every prefix for input 3513. -/
theorem certificate_3513 : classCertificateB 2 3513 = true := by
  decide

/-- The same exact first-descent time holds on an infinite dyadic ray. -/
theorem ray_3513 (m : Nat) : stoppingTime (2 ^ 2 * m + 3513) 2 :=
  stoppingTime_of_classCertificate certificate_3513 m

/-- Checked base and every prefix for input 3515. -/
theorem certificate_3515 : classCertificateB 7 3515 = true := by
  decide

/-- The same exact first-descent time holds on an infinite dyadic ray. -/
theorem ray_3515 (m : Nat) : stoppingTime (2 ^ 7 * m + 3515) 7 :=
  stoppingTime_of_classCertificate certificate_3515 m

/-- Checked base and every prefix for input 3517. -/
theorem certificate_3517 : classCertificateB 2 3517 = true := by
  decide

/-- The same exact first-descent time holds on an infinite dyadic ray. -/
theorem ray_3517 (m : Nat) : stoppingTime (2 ^ 2 * m + 3517) 2 :=
  stoppingTime_of_classCertificate certificate_3517 m

/-- Checked base and every prefix for input 3519. -/
theorem certificate_3519 : classCertificateB 24 3519 = true := by
  decide

/-- The same exact first-descent time holds on an infinite dyadic ray. -/
theorem ray_3519 (m : Nat) : stoppingTime (2 ^ 24 * m + 3519) 24 :=
  stoppingTime_of_classCertificate certificate_3519 m

/-- Checked base and every prefix for input 3521. -/
theorem certificate_3521 : classCertificateB 2 3521 = true := by
  decide

/-- The same exact first-descent time holds on an infinite dyadic ray. -/
theorem ray_3521 (m : Nat) : stoppingTime (2 ^ 2 * m + 3521) 2 :=
  stoppingTime_of_classCertificate certificate_3521 m

/-- Checked base and every prefix for input 3523. -/
theorem certificate_3523 : classCertificateB 4 3523 = true := by
  decide

/-- The same exact first-descent time holds on an infinite dyadic ray. -/
theorem ray_3523 (m : Nat) : stoppingTime (2 ^ 4 * m + 3523) 4 :=
  stoppingTime_of_classCertificate certificate_3523 m

/-- Checked base and every prefix for input 3525. -/
theorem certificate_3525 : classCertificateB 2 3525 = true := by
  decide

/-- The same exact first-descent time holds on an infinite dyadic ray. -/
theorem ray_3525 (m : Nat) : stoppingTime (2 ^ 2 * m + 3525) 2 :=
  stoppingTime_of_classCertificate certificate_3525 m

/-- Checked base and every prefix for input 3527. -/
theorem certificate_3527 : classCertificateB 8 3527 = true := by
  decide

/-- The same exact first-descent time holds on an infinite dyadic ray. -/
theorem ray_3527 (m : Nat) : stoppingTime (2 ^ 8 * m + 3527) 8 :=
  stoppingTime_of_classCertificate certificate_3527 m

/-- Checked base and every prefix for input 3529. -/
theorem certificate_3529 : classCertificateB 2 3529 = true := by
  decide

/-- The same exact first-descent time holds on an infinite dyadic ray. -/
theorem ray_3529 (m : Nat) : stoppingTime (2 ^ 2 * m + 3529) 2 :=
  stoppingTime_of_classCertificate certificate_3529 m

/-- Checked base and every prefix for input 3531. -/
theorem certificate_3531 : classCertificateB 5 3531 = true := by
  decide

/-- The same exact first-descent time holds on an infinite dyadic ray. -/
theorem ray_3531 (m : Nat) : stoppingTime (2 ^ 5 * m + 3531) 5 :=
  stoppingTime_of_classCertificate certificate_3531 m

/-- Checked base and every prefix for input 3533. -/
theorem certificate_3533 : classCertificateB 2 3533 = true := by
  decide

/-- The same exact first-descent time holds on an infinite dyadic ray. -/
theorem ray_3533 (m : Nat) : stoppingTime (2 ^ 2 * m + 3533) 2 :=
  stoppingTime_of_classCertificate certificate_3533 m

/-- Checked base and every prefix for input 3535. -/
theorem certificate_3535 : classCertificateB 16 3535 = true := by
  decide

/-- The same exact first-descent time holds on an infinite dyadic ray. -/
theorem ray_3535 (m : Nat) : stoppingTime (2 ^ 16 * m + 3535) 16 :=
  stoppingTime_of_classCertificate certificate_3535 m

/-- Checked base and every prefix for input 3537. -/
theorem certificate_3537 : classCertificateB 2 3537 = true := by
  decide

/-- The same exact first-descent time holds on an infinite dyadic ray. -/
theorem ray_3537 (m : Nat) : stoppingTime (2 ^ 2 * m + 3537) 2 :=
  stoppingTime_of_classCertificate certificate_3537 m

/-- Checked base and every prefix for input 3539. -/
theorem certificate_3539 : classCertificateB 4 3539 = true := by
  decide

/-- The same exact first-descent time holds on an infinite dyadic ray. -/
theorem ray_3539 (m : Nat) : stoppingTime (2 ^ 4 * m + 3539) 4 :=
  stoppingTime_of_classCertificate certificate_3539 m

/-- Checked base and every prefix for input 3541. -/
theorem certificate_3541 : classCertificateB 2 3541 = true := by
  decide

/-- The same exact first-descent time holds on an infinite dyadic ray. -/
theorem ray_3541 (m : Nat) : stoppingTime (2 ^ 2 * m + 3541) 2 :=
  stoppingTime_of_classCertificate certificate_3541 m

/-- Checked base and every prefix for input 3543. -/
theorem certificate_3543 : classCertificateB 5 3543 = true := by
  decide

/-- The same exact first-descent time holds on an infinite dyadic ray. -/
theorem ray_3543 (m : Nat) : stoppingTime (2 ^ 5 * m + 3543) 5 :=
  stoppingTime_of_classCertificate certificate_3543 m

/-- Checked base and every prefix for input 3545. -/
theorem certificate_3545 : classCertificateB 2 3545 = true := by
  decide

/-- The same exact first-descent time holds on an infinite dyadic ray. -/
theorem ray_3545 (m : Nat) : stoppingTime (2 ^ 2 * m + 3545) 2 :=
  stoppingTime_of_classCertificate certificate_3545 m

/-- Checked base and every prefix for input 3547. -/
theorem certificate_3547 : classCertificateB 8 3547 = true := by
  decide

/-- The same exact first-descent time holds on an infinite dyadic ray. -/
theorem ray_3547 (m : Nat) : stoppingTime (2 ^ 8 * m + 3547) 8 :=
  stoppingTime_of_classCertificate certificate_3547 m

/-- Checked base and every prefix for input 3549. -/
theorem certificate_3549 : classCertificateB 2 3549 = true := by
  decide

/-- The same exact first-descent time holds on an infinite dyadic ray. -/
theorem ray_3549 (m : Nat) : stoppingTime (2 ^ 2 * m + 3549) 2 :=
  stoppingTime_of_classCertificate certificate_3549 m

/-- Exhaustive coverage of the odd inputs in this batch, with no gaps. -/
theorem coverage : CertifiedRange 3485 3551 := by
  intro n hlo hhi hodd
  have hn : n = 3485 ∨ n = 3487 ∨ n = 3489 ∨ n = 3491 ∨ n = 3493 ∨ n = 3495 ∨ n = 3497 ∨ n = 3499 ∨ n = 3501 ∨ n = 3503 ∨ n = 3505 ∨ n = 3507 ∨ n = 3509 ∨ n = 3511 ∨ n = 3513 ∨ n = 3515 ∨ n = 3517 ∨ n = 3519 ∨ n = 3521 ∨ n = 3523 ∨ n = 3525 ∨ n = 3527 ∨ n = 3529 ∨ n = 3531 ∨ n = 3533 ∨ n = 3535 ∨ n = 3537 ∨ n = 3539 ∨ n = 3541 ∨ n = 3543 ∨ n = 3545 ∨ n = 3547 ∨ n = 3549 := by omega
  rcases hn with h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h
  · subst n
    exact ⟨2, witness_of_certificate certificate_3485⟩
  · subst n
    exact ⟨16, witness_of_certificate certificate_3487⟩
  · subst n
    exact ⟨2, witness_of_certificate certificate_3489⟩
  · subst n
    exact ⟨4, witness_of_certificate certificate_3491⟩
  · subst n
    exact ⟨2, witness_of_certificate certificate_3493⟩
  · subst n
    exact ⟨10, witness_of_certificate certificate_3495⟩
  · subst n
    exact ⟨2, witness_of_certificate certificate_3497⟩
  · subst n
    exact ⟨5, witness_of_certificate certificate_3499⟩
  · subst n
    exact ⟨2, witness_of_certificate certificate_3501⟩
  · subst n
    exact ⟨8, witness_of_certificate certificate_3503⟩
  · subst n
    exact ⟨2, witness_of_certificate certificate_3505⟩
  · subst n
    exact ⟨4, witness_of_certificate certificate_3507⟩
  · subst n
    exact ⟨2, witness_of_certificate certificate_3509⟩
  · subst n
    exact ⟨5, witness_of_certificate certificate_3511⟩
  · subst n
    exact ⟨2, witness_of_certificate certificate_3513⟩
  · subst n
    exact ⟨7, witness_of_certificate certificate_3515⟩
  · subst n
    exact ⟨2, witness_of_certificate certificate_3517⟩
  · subst n
    exact ⟨24, witness_of_certificate certificate_3519⟩
  · subst n
    exact ⟨2, witness_of_certificate certificate_3521⟩
  · subst n
    exact ⟨4, witness_of_certificate certificate_3523⟩
  · subst n
    exact ⟨2, witness_of_certificate certificate_3525⟩
  · subst n
    exact ⟨8, witness_of_certificate certificate_3527⟩
  · subst n
    exact ⟨2, witness_of_certificate certificate_3529⟩
  · subst n
    exact ⟨5, witness_of_certificate certificate_3531⟩
  · subst n
    exact ⟨2, witness_of_certificate certificate_3533⟩
  · subst n
    exact ⟨16, witness_of_certificate certificate_3535⟩
  · subst n
    exact ⟨2, witness_of_certificate certificate_3537⟩
  · subst n
    exact ⟨4, witness_of_certificate certificate_3539⟩
  · subst n
    exact ⟨2, witness_of_certificate certificate_3541⟩
  · subst n
    exact ⟨5, witness_of_certificate certificate_3543⟩
  · subst n
    exact ⟨2, witness_of_certificate certificate_3545⟩
  · subst n
    exact ⟨8, witness_of_certificate certificate_3547⟩
  · subst n
    exact ⟨2, witness_of_certificate certificate_3549⟩

end Collatz.Research.CoefficientDescent.Batch053
