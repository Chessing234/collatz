import Collatz.Research.CoefficientDescent.Basic

namespace Collatz.Research.CoefficientDescent.Batch098

open FirstDescentClass

set_option maxRecDepth 20000
set_option maxHeartbeats 0

/-- Checked base and every prefix for input 6499. -/
theorem certificate_6499 : classCertificateB 4 6499 = true := by
  decide

/-- The same exact first-descent time holds on an infinite dyadic ray. -/
theorem ray_6499 (m : Nat) : stoppingTime (2 ^ 4 * m + 6499) 4 :=
  stoppingTime_of_classCertificate certificate_6499 m

/-- Checked base and every prefix for input 6501. -/
theorem certificate_6501 : classCertificateB 2 6501 = true := by
  decide

/-- The same exact first-descent time holds on an infinite dyadic ray. -/
theorem ray_6501 (m : Nat) : stoppingTime (2 ^ 2 * m + 6501) 2 :=
  stoppingTime_of_classCertificate certificate_6501 m

/-- Checked base and every prefix for input 6503. -/
theorem certificate_6503 : classCertificateB 15 6503 = true := by
  decide

/-- The same exact first-descent time holds on an infinite dyadic ray. -/
theorem ray_6503 (m : Nat) : stoppingTime (2 ^ 15 * m + 6503) 15 :=
  stoppingTime_of_classCertificate certificate_6503 m

/-- Checked base and every prefix for input 6505. -/
theorem certificate_6505 : classCertificateB 2 6505 = true := by
  decide

/-- The same exact first-descent time holds on an infinite dyadic ray. -/
theorem ray_6505 (m : Nat) : stoppingTime (2 ^ 2 * m + 6505) 2 :=
  stoppingTime_of_classCertificate certificate_6505 m

/-- Checked base and every prefix for input 6507. -/
theorem certificate_6507 : classCertificateB 5 6507 = true := by
  decide

/-- The same exact first-descent time holds on an infinite dyadic ray. -/
theorem ray_6507 (m : Nat) : stoppingTime (2 ^ 5 * m + 6507) 5 :=
  stoppingTime_of_classCertificate certificate_6507 m

/-- Checked base and every prefix for input 6509. -/
theorem certificate_6509 : classCertificateB 2 6509 = true := by
  decide

/-- The same exact first-descent time holds on an infinite dyadic ray. -/
theorem ray_6509 (m : Nat) : stoppingTime (2 ^ 2 * m + 6509) 2 :=
  stoppingTime_of_classCertificate certificate_6509 m

/-- Checked base and every prefix for input 6511. -/
theorem certificate_6511 : classCertificateB 10 6511 = true := by
  decide

/-- The same exact first-descent time holds on an infinite dyadic ray. -/
theorem ray_6511 (m : Nat) : stoppingTime (2 ^ 10 * m + 6511) 10 :=
  stoppingTime_of_classCertificate certificate_6511 m

/-- Checked base and every prefix for input 6513. -/
theorem certificate_6513 : classCertificateB 2 6513 = true := by
  decide

/-- The same exact first-descent time holds on an infinite dyadic ray. -/
theorem ray_6513 (m : Nat) : stoppingTime (2 ^ 2 * m + 6513) 2 :=
  stoppingTime_of_classCertificate certificate_6513 m

/-- Checked base and every prefix for input 6515. -/
theorem certificate_6515 : classCertificateB 4 6515 = true := by
  decide

/-- The same exact first-descent time holds on an infinite dyadic ray. -/
theorem ray_6515 (m : Nat) : stoppingTime (2 ^ 4 * m + 6515) 4 :=
  stoppingTime_of_classCertificate certificate_6515 m

/-- Checked base and every prefix for input 6517. -/
theorem certificate_6517 : classCertificateB 2 6517 = true := by
  decide

/-- The same exact first-descent time holds on an infinite dyadic ray. -/
theorem ray_6517 (m : Nat) : stoppingTime (2 ^ 2 * m + 6517) 2 :=
  stoppingTime_of_classCertificate certificate_6517 m

/-- Checked base and every prefix for input 6519. -/
theorem certificate_6519 : classCertificateB 5 6519 = true := by
  decide

/-- The same exact first-descent time holds on an infinite dyadic ray. -/
theorem ray_6519 (m : Nat) : stoppingTime (2 ^ 5 * m + 6519) 5 :=
  stoppingTime_of_classCertificate certificate_6519 m

/-- Checked base and every prefix for input 6521. -/
theorem certificate_6521 : classCertificateB 2 6521 = true := by
  decide

/-- The same exact first-descent time holds on an infinite dyadic ray. -/
theorem ray_6521 (m : Nat) : stoppingTime (2 ^ 2 * m + 6521) 2 :=
  stoppingTime_of_classCertificate certificate_6521 m

/-- Checked base and every prefix for input 6523. -/
theorem certificate_6523 : classCertificateB 8 6523 = true := by
  decide

/-- The same exact first-descent time holds on an infinite dyadic ray. -/
theorem ray_6523 (m : Nat) : stoppingTime (2 ^ 8 * m + 6523) 8 :=
  stoppingTime_of_classCertificate certificate_6523 m

/-- Checked base and every prefix for input 6525. -/
theorem certificate_6525 : classCertificateB 2 6525 = true := by
  decide

/-- The same exact first-descent time holds on an infinite dyadic ray. -/
theorem ray_6525 (m : Nat) : stoppingTime (2 ^ 2 * m + 6525) 2 :=
  stoppingTime_of_classCertificate certificate_6525 m

/-- Checked base and every prefix for input 6527. -/
theorem certificate_6527 : classCertificateB 18 6527 = true := by
  decide

/-- The same exact first-descent time holds on an infinite dyadic ray. -/
theorem ray_6527 (m : Nat) : stoppingTime (2 ^ 18 * m + 6527) 18 :=
  stoppingTime_of_classCertificate certificate_6527 m

/-- Checked base and every prefix for input 6529. -/
theorem certificate_6529 : classCertificateB 2 6529 = true := by
  decide

/-- The same exact first-descent time holds on an infinite dyadic ray. -/
theorem ray_6529 (m : Nat) : stoppingTime (2 ^ 2 * m + 6529) 2 :=
  stoppingTime_of_classCertificate certificate_6529 m

/-- Checked base and every prefix for input 6531. -/
theorem certificate_6531 : classCertificateB 4 6531 = true := by
  decide

/-- The same exact first-descent time holds on an infinite dyadic ray. -/
theorem ray_6531 (m : Nat) : stoppingTime (2 ^ 4 * m + 6531) 4 :=
  stoppingTime_of_classCertificate certificate_6531 m

/-- Checked base and every prefix for input 6533. -/
theorem certificate_6533 : classCertificateB 2 6533 = true := by
  decide

/-- The same exact first-descent time holds on an infinite dyadic ray. -/
theorem ray_6533 (m : Nat) : stoppingTime (2 ^ 2 * m + 6533) 2 :=
  stoppingTime_of_classCertificate certificate_6533 m

/-- Checked base and every prefix for input 6535. -/
theorem certificate_6535 : classCertificateB 7 6535 = true := by
  decide

/-- The same exact first-descent time holds on an infinite dyadic ray. -/
theorem ray_6535 (m : Nat) : stoppingTime (2 ^ 7 * m + 6535) 7 :=
  stoppingTime_of_classCertificate certificate_6535 m

/-- Checked base and every prefix for input 6537. -/
theorem certificate_6537 : classCertificateB 2 6537 = true := by
  decide

/-- The same exact first-descent time holds on an infinite dyadic ray. -/
theorem ray_6537 (m : Nat) : stoppingTime (2 ^ 2 * m + 6537) 2 :=
  stoppingTime_of_classCertificate certificate_6537 m

/-- Checked base and every prefix for input 6539. -/
theorem certificate_6539 : classCertificateB 5 6539 = true := by
  decide

/-- The same exact first-descent time holds on an infinite dyadic ray. -/
theorem ray_6539 (m : Nat) : stoppingTime (2 ^ 5 * m + 6539) 5 :=
  stoppingTime_of_classCertificate certificate_6539 m

/-- Checked base and every prefix for input 6541. -/
theorem certificate_6541 : classCertificateB 2 6541 = true := by
  decide

/-- The same exact first-descent time holds on an infinite dyadic ray. -/
theorem ray_6541 (m : Nat) : stoppingTime (2 ^ 2 * m + 6541) 2 :=
  stoppingTime_of_classCertificate certificate_6541 m

/-- Checked base and every prefix for input 6543. -/
theorem certificate_6543 : classCertificateB 7 6543 = true := by
  decide

/-- The same exact first-descent time holds on an infinite dyadic ray. -/
theorem ray_6543 (m : Nat) : stoppingTime (2 ^ 7 * m + 6543) 7 :=
  stoppingTime_of_classCertificate certificate_6543 m

/-- Checked base and every prefix for input 6545. -/
theorem certificate_6545 : classCertificateB 2 6545 = true := by
  decide

/-- The same exact first-descent time holds on an infinite dyadic ray. -/
theorem ray_6545 (m : Nat) : stoppingTime (2 ^ 2 * m + 6545) 2 :=
  stoppingTime_of_classCertificate certificate_6545 m

/-- Checked base and every prefix for input 6547. -/
theorem certificate_6547 : classCertificateB 4 6547 = true := by
  decide

/-- The same exact first-descent time holds on an infinite dyadic ray. -/
theorem ray_6547 (m : Nat) : stoppingTime (2 ^ 4 * m + 6547) 4 :=
  stoppingTime_of_classCertificate certificate_6547 m

/-- Checked base and every prefix for input 6549. -/
theorem certificate_6549 : classCertificateB 2 6549 = true := by
  decide

/-- The same exact first-descent time holds on an infinite dyadic ray. -/
theorem ray_6549 (m : Nat) : stoppingTime (2 ^ 2 * m + 6549) 2 :=
  stoppingTime_of_classCertificate certificate_6549 m

/-- Checked base and every prefix for input 6551. -/
theorem certificate_6551 : classCertificateB 5 6551 = true := by
  decide

/-- The same exact first-descent time holds on an infinite dyadic ray. -/
theorem ray_6551 (m : Nat) : stoppingTime (2 ^ 5 * m + 6551) 5 :=
  stoppingTime_of_classCertificate certificate_6551 m

/-- Checked base and every prefix for input 6553. -/
theorem certificate_6553 : classCertificateB 2 6553 = true := by
  decide

/-- The same exact first-descent time holds on an infinite dyadic ray. -/
theorem ray_6553 (m : Nat) : stoppingTime (2 ^ 2 * m + 6553) 2 :=
  stoppingTime_of_classCertificate certificate_6553 m

/-- Checked base and every prefix for input 6555. -/
theorem certificate_6555 : classCertificateB 16 6555 = true := by
  decide

/-- The same exact first-descent time holds on an infinite dyadic ray. -/
theorem ray_6555 (m : Nat) : stoppingTime (2 ^ 16 * m + 6555) 16 :=
  stoppingTime_of_classCertificate certificate_6555 m

/-- Checked base and every prefix for input 6557. -/
theorem certificate_6557 : classCertificateB 2 6557 = true := by
  decide

/-- The same exact first-descent time holds on an infinite dyadic ray. -/
theorem ray_6557 (m : Nat) : stoppingTime (2 ^ 2 * m + 6557) 2 :=
  stoppingTime_of_classCertificate certificate_6557 m

/-- Checked base and every prefix for input 6559. -/
theorem certificate_6559 : classCertificateB 13 6559 = true := by
  decide

/-- The same exact first-descent time holds on an infinite dyadic ray. -/
theorem ray_6559 (m : Nat) : stoppingTime (2 ^ 13 * m + 6559) 13 :=
  stoppingTime_of_classCertificate certificate_6559 m

/-- Checked base and every prefix for input 6561. -/
theorem certificate_6561 : classCertificateB 2 6561 = true := by
  decide

/-- The same exact first-descent time holds on an infinite dyadic ray. -/
theorem ray_6561 (m : Nat) : stoppingTime (2 ^ 2 * m + 6561) 2 :=
  stoppingTime_of_classCertificate certificate_6561 m

/-- Checked base and every prefix for input 6563. -/
theorem certificate_6563 : classCertificateB 4 6563 = true := by
  decide

/-- The same exact first-descent time holds on an infinite dyadic ray. -/
theorem ray_6563 (m : Nat) : stoppingTime (2 ^ 4 * m + 6563) 4 :=
  stoppingTime_of_classCertificate certificate_6563 m

/-- Checked base and every prefix for input 6565. -/
theorem certificate_6565 : classCertificateB 2 6565 = true := by
  decide

/-- The same exact first-descent time holds on an infinite dyadic ray. -/
theorem ray_6565 (m : Nat) : stoppingTime (2 ^ 2 * m + 6565) 2 :=
  stoppingTime_of_classCertificate certificate_6565 m

/-- Exhaustive coverage of the odd inputs in this batch, with no gaps. -/
theorem coverage : CertifiedRange 6499 6567 := by
  intro n hlo hhi hodd
  have hn : n = 6499 ∨ n = 6501 ∨ n = 6503 ∨ n = 6505 ∨ n = 6507 ∨ n = 6509 ∨ n = 6511 ∨ n = 6513 ∨ n = 6515 ∨ n = 6517 ∨ n = 6519 ∨ n = 6521 ∨ n = 6523 ∨ n = 6525 ∨ n = 6527 ∨ n = 6529 ∨ n = 6531 ∨ n = 6533 ∨ n = 6535 ∨ n = 6537 ∨ n = 6539 ∨ n = 6541 ∨ n = 6543 ∨ n = 6545 ∨ n = 6547 ∨ n = 6549 ∨ n = 6551 ∨ n = 6553 ∨ n = 6555 ∨ n = 6557 ∨ n = 6559 ∨ n = 6561 ∨ n = 6563 ∨ n = 6565 := by omega
  rcases hn with h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h
  · subst n
    exact ⟨4, witness_of_certificate certificate_6499⟩
  · subst n
    exact ⟨2, witness_of_certificate certificate_6501⟩
  · subst n
    exact ⟨15, witness_of_certificate certificate_6503⟩
  · subst n
    exact ⟨2, witness_of_certificate certificate_6505⟩
  · subst n
    exact ⟨5, witness_of_certificate certificate_6507⟩
  · subst n
    exact ⟨2, witness_of_certificate certificate_6509⟩
  · subst n
    exact ⟨10, witness_of_certificate certificate_6511⟩
  · subst n
    exact ⟨2, witness_of_certificate certificate_6513⟩
  · subst n
    exact ⟨4, witness_of_certificate certificate_6515⟩
  · subst n
    exact ⟨2, witness_of_certificate certificate_6517⟩
  · subst n
    exact ⟨5, witness_of_certificate certificate_6519⟩
  · subst n
    exact ⟨2, witness_of_certificate certificate_6521⟩
  · subst n
    exact ⟨8, witness_of_certificate certificate_6523⟩
  · subst n
    exact ⟨2, witness_of_certificate certificate_6525⟩
  · subst n
    exact ⟨18, witness_of_certificate certificate_6527⟩
  · subst n
    exact ⟨2, witness_of_certificate certificate_6529⟩
  · subst n
    exact ⟨4, witness_of_certificate certificate_6531⟩
  · subst n
    exact ⟨2, witness_of_certificate certificate_6533⟩
  · subst n
    exact ⟨7, witness_of_certificate certificate_6535⟩
  · subst n
    exact ⟨2, witness_of_certificate certificate_6537⟩
  · subst n
    exact ⟨5, witness_of_certificate certificate_6539⟩
  · subst n
    exact ⟨2, witness_of_certificate certificate_6541⟩
  · subst n
    exact ⟨7, witness_of_certificate certificate_6543⟩
  · subst n
    exact ⟨2, witness_of_certificate certificate_6545⟩
  · subst n
    exact ⟨4, witness_of_certificate certificate_6547⟩
  · subst n
    exact ⟨2, witness_of_certificate certificate_6549⟩
  · subst n
    exact ⟨5, witness_of_certificate certificate_6551⟩
  · subst n
    exact ⟨2, witness_of_certificate certificate_6553⟩
  · subst n
    exact ⟨16, witness_of_certificate certificate_6555⟩
  · subst n
    exact ⟨2, witness_of_certificate certificate_6557⟩
  · subst n
    exact ⟨13, witness_of_certificate certificate_6559⟩
  · subst n
    exact ⟨2, witness_of_certificate certificate_6561⟩
  · subst n
    exact ⟨4, witness_of_certificate certificate_6563⟩
  · subst n
    exact ⟨2, witness_of_certificate certificate_6565⟩

end Collatz.Research.CoefficientDescent.Batch098
