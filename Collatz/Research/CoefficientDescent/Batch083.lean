import Collatz.Research.CoefficientDescent.Basic

namespace Collatz.Research.CoefficientDescent.Batch083

open FirstDescentClass

set_option maxRecDepth 20000
set_option maxHeartbeats 0

/-- Checked base and every prefix for input 5495. -/
theorem certificate_5495 : classCertificateB 5 5495 = true := by
  decide

/-- The same exact first-descent time holds on an infinite dyadic ray. -/
theorem ray_5495 (m : Nat) : stoppingTime (2 ^ 5 * m + 5495) 5 :=
  stoppingTime_of_classCertificate certificate_5495 m

/-- Checked base and every prefix for input 5497. -/
theorem certificate_5497 : classCertificateB 2 5497 = true := by
  decide

/-- The same exact first-descent time holds on an infinite dyadic ray. -/
theorem ray_5497 (m : Nat) : stoppingTime (2 ^ 2 * m + 5497) 2 :=
  stoppingTime_of_classCertificate certificate_5497 m

/-- Checked base and every prefix for input 5499. -/
theorem certificate_5499 : classCertificateB 8 5499 = true := by
  decide

/-- The same exact first-descent time holds on an infinite dyadic ray. -/
theorem ray_5499 (m : Nat) : stoppingTime (2 ^ 8 * m + 5499) 8 :=
  stoppingTime_of_classCertificate certificate_5499 m

/-- Checked base and every prefix for input 5501. -/
theorem certificate_5501 : classCertificateB 2 5501 = true := by
  decide

/-- The same exact first-descent time holds on an infinite dyadic ray. -/
theorem ray_5501 (m : Nat) : stoppingTime (2 ^ 2 * m + 5501) 2 :=
  stoppingTime_of_classCertificate certificate_5501 m

/-- Checked base and every prefix for input 5503. -/
theorem certificate_5503 : classCertificateB 43 5503 = true := by
  decide

/-- The same exact first-descent time holds on an infinite dyadic ray. -/
theorem ray_5503 (m : Nat) : stoppingTime (2 ^ 43 * m + 5503) 43 :=
  stoppingTime_of_classCertificate certificate_5503 m

/-- Checked base and every prefix for input 5505. -/
theorem certificate_5505 : classCertificateB 2 5505 = true := by
  decide

/-- The same exact first-descent time holds on an infinite dyadic ray. -/
theorem ray_5505 (m : Nat) : stoppingTime (2 ^ 2 * m + 5505) 2 :=
  stoppingTime_of_classCertificate certificate_5505 m

/-- Checked base and every prefix for input 5507. -/
theorem certificate_5507 : classCertificateB 4 5507 = true := by
  decide

/-- The same exact first-descent time holds on an infinite dyadic ray. -/
theorem ray_5507 (m : Nat) : stoppingTime (2 ^ 4 * m + 5507) 4 :=
  stoppingTime_of_classCertificate certificate_5507 m

/-- Checked base and every prefix for input 5509. -/
theorem certificate_5509 : classCertificateB 2 5509 = true := by
  decide

/-- The same exact first-descent time holds on an infinite dyadic ray. -/
theorem ray_5509 (m : Nat) : stoppingTime (2 ^ 2 * m + 5509) 2 :=
  stoppingTime_of_classCertificate certificate_5509 m

/-- Checked base and every prefix for input 5511. -/
theorem certificate_5511 : classCertificateB 7 5511 = true := by
  decide

/-- The same exact first-descent time holds on an infinite dyadic ray. -/
theorem ray_5511 (m : Nat) : stoppingTime (2 ^ 7 * m + 5511) 7 :=
  stoppingTime_of_classCertificate certificate_5511 m

/-- Checked base and every prefix for input 5513. -/
theorem certificate_5513 : classCertificateB 2 5513 = true := by
  decide

/-- The same exact first-descent time holds on an infinite dyadic ray. -/
theorem ray_5513 (m : Nat) : stoppingTime (2 ^ 2 * m + 5513) 2 :=
  stoppingTime_of_classCertificate certificate_5513 m

/-- Checked base and every prefix for input 5515. -/
theorem certificate_5515 : classCertificateB 5 5515 = true := by
  decide

/-- The same exact first-descent time holds on an infinite dyadic ray. -/
theorem ray_5515 (m : Nat) : stoppingTime (2 ^ 5 * m + 5515) 5 :=
  stoppingTime_of_classCertificate certificate_5515 m

/-- Checked base and every prefix for input 5517. -/
theorem certificate_5517 : classCertificateB 2 5517 = true := by
  decide

/-- The same exact first-descent time holds on an infinite dyadic ray. -/
theorem ray_5517 (m : Nat) : stoppingTime (2 ^ 2 * m + 5517) 2 :=
  stoppingTime_of_classCertificate certificate_5517 m

/-- Checked base and every prefix for input 5519. -/
theorem certificate_5519 : classCertificateB 7 5519 = true := by
  decide

/-- The same exact first-descent time holds on an infinite dyadic ray. -/
theorem ray_5519 (m : Nat) : stoppingTime (2 ^ 7 * m + 5519) 7 :=
  stoppingTime_of_classCertificate certificate_5519 m

/-- Checked base and every prefix for input 5521. -/
theorem certificate_5521 : classCertificateB 2 5521 = true := by
  decide

/-- The same exact first-descent time holds on an infinite dyadic ray. -/
theorem ray_5521 (m : Nat) : stoppingTime (2 ^ 2 * m + 5521) 2 :=
  stoppingTime_of_classCertificate certificate_5521 m

/-- Checked base and every prefix for input 5523. -/
theorem certificate_5523 : classCertificateB 4 5523 = true := by
  decide

/-- The same exact first-descent time holds on an infinite dyadic ray. -/
theorem ray_5523 (m : Nat) : stoppingTime (2 ^ 4 * m + 5523) 4 :=
  stoppingTime_of_classCertificate certificate_5523 m

/-- Checked base and every prefix for input 5525. -/
theorem certificate_5525 : classCertificateB 2 5525 = true := by
  decide

/-- The same exact first-descent time holds on an infinite dyadic ray. -/
theorem ray_5525 (m : Nat) : stoppingTime (2 ^ 2 * m + 5525) 2 :=
  stoppingTime_of_classCertificate certificate_5525 m

/-- Checked base and every prefix for input 5527. -/
theorem certificate_5527 : classCertificateB 5 5527 = true := by
  decide

/-- The same exact first-descent time holds on an infinite dyadic ray. -/
theorem ray_5527 (m : Nat) : stoppingTime (2 ^ 5 * m + 5527) 5 :=
  stoppingTime_of_classCertificate certificate_5527 m

/-- Checked base and every prefix for input 5529. -/
theorem certificate_5529 : classCertificateB 2 5529 = true := by
  decide

/-- The same exact first-descent time holds on an infinite dyadic ray. -/
theorem ray_5529 (m : Nat) : stoppingTime (2 ^ 2 * m + 5529) 2 :=
  stoppingTime_of_classCertificate certificate_5529 m

/-- Checked base and every prefix for input 5531. -/
theorem certificate_5531 : classCertificateB 12 5531 = true := by
  decide

/-- The same exact first-descent time holds on an infinite dyadic ray. -/
theorem ray_5531 (m : Nat) : stoppingTime (2 ^ 12 * m + 5531) 12 :=
  stoppingTime_of_classCertificate certificate_5531 m

/-- Checked base and every prefix for input 5533. -/
theorem certificate_5533 : classCertificateB 2 5533 = true := by
  decide

/-- The same exact first-descent time holds on an infinite dyadic ray. -/
theorem ray_5533 (m : Nat) : stoppingTime (2 ^ 2 * m + 5533) 2 :=
  stoppingTime_of_classCertificate certificate_5533 m

/-- Checked base and every prefix for input 5535. -/
theorem certificate_5535 : classCertificateB 27 5535 = true := by
  decide

/-- The same exact first-descent time holds on an infinite dyadic ray. -/
theorem ray_5535 (m : Nat) : stoppingTime (2 ^ 27 * m + 5535) 27 :=
  stoppingTime_of_classCertificate certificate_5535 m

/-- Checked base and every prefix for input 5537. -/
theorem certificate_5537 : classCertificateB 2 5537 = true := by
  decide

/-- The same exact first-descent time holds on an infinite dyadic ray. -/
theorem ray_5537 (m : Nat) : stoppingTime (2 ^ 2 * m + 5537) 2 :=
  stoppingTime_of_classCertificate certificate_5537 m

/-- Checked base and every prefix for input 5539. -/
theorem certificate_5539 : classCertificateB 4 5539 = true := by
  decide

/-- The same exact first-descent time holds on an infinite dyadic ray. -/
theorem ray_5539 (m : Nat) : stoppingTime (2 ^ 4 * m + 5539) 4 :=
  stoppingTime_of_classCertificate certificate_5539 m

/-- Checked base and every prefix for input 5541. -/
theorem certificate_5541 : classCertificateB 2 5541 = true := by
  decide

/-- The same exact first-descent time holds on an infinite dyadic ray. -/
theorem ray_5541 (m : Nat) : stoppingTime (2 ^ 2 * m + 5541) 2 :=
  stoppingTime_of_classCertificate certificate_5541 m

/-- Checked base and every prefix for input 5543. -/
theorem certificate_5543 : classCertificateB 10 5543 = true := by
  decide

/-- The same exact first-descent time holds on an infinite dyadic ray. -/
theorem ray_5543 (m : Nat) : stoppingTime (2 ^ 10 * m + 5543) 10 :=
  stoppingTime_of_classCertificate certificate_5543 m

/-- Checked base and every prefix for input 5545. -/
theorem certificate_5545 : classCertificateB 2 5545 = true := by
  decide

/-- The same exact first-descent time holds on an infinite dyadic ray. -/
theorem ray_5545 (m : Nat) : stoppingTime (2 ^ 2 * m + 5545) 2 :=
  stoppingTime_of_classCertificate certificate_5545 m

/-- Checked base and every prefix for input 5547. -/
theorem certificate_5547 : classCertificateB 5 5547 = true := by
  decide

/-- The same exact first-descent time holds on an infinite dyadic ray. -/
theorem ray_5547 (m : Nat) : stoppingTime (2 ^ 5 * m + 5547) 5 :=
  stoppingTime_of_classCertificate certificate_5547 m

/-- Checked base and every prefix for input 5549. -/
theorem certificate_5549 : classCertificateB 2 5549 = true := by
  decide

/-- The same exact first-descent time holds on an infinite dyadic ray. -/
theorem ray_5549 (m : Nat) : stoppingTime (2 ^ 2 * m + 5549) 2 :=
  stoppingTime_of_classCertificate certificate_5549 m

/-- Checked base and every prefix for input 5551. -/
theorem certificate_5551 : classCertificateB 8 5551 = true := by
  decide

/-- The same exact first-descent time holds on an infinite dyadic ray. -/
theorem ray_5551 (m : Nat) : stoppingTime (2 ^ 8 * m + 5551) 8 :=
  stoppingTime_of_classCertificate certificate_5551 m

/-- Checked base and every prefix for input 5553. -/
theorem certificate_5553 : classCertificateB 2 5553 = true := by
  decide

/-- The same exact first-descent time holds on an infinite dyadic ray. -/
theorem ray_5553 (m : Nat) : stoppingTime (2 ^ 2 * m + 5553) 2 :=
  stoppingTime_of_classCertificate certificate_5553 m

/-- Checked base and every prefix for input 5555. -/
theorem certificate_5555 : classCertificateB 4 5555 = true := by
  decide

/-- The same exact first-descent time holds on an infinite dyadic ray. -/
theorem ray_5555 (m : Nat) : stoppingTime (2 ^ 4 * m + 5555) 4 :=
  stoppingTime_of_classCertificate certificate_5555 m

/-- Checked base and every prefix for input 5557. -/
theorem certificate_5557 : classCertificateB 2 5557 = true := by
  decide

/-- The same exact first-descent time holds on an infinite dyadic ray. -/
theorem ray_5557 (m : Nat) : stoppingTime (2 ^ 2 * m + 5557) 2 :=
  stoppingTime_of_classCertificate certificate_5557 m

/-- Checked base and every prefix for input 5559. -/
theorem certificate_5559 : classCertificateB 5 5559 = true := by
  decide

/-- The same exact first-descent time holds on an infinite dyadic ray. -/
theorem ray_5559 (m : Nat) : stoppingTime (2 ^ 5 * m + 5559) 5 :=
  stoppingTime_of_classCertificate certificate_5559 m

/-- Exhaustive coverage of the odd inputs in this batch, with no gaps. -/
theorem coverage : CertifiedRange 5495 5561 := by
  intro n hlo hhi hodd
  have hn : n = 5495 ∨ n = 5497 ∨ n = 5499 ∨ n = 5501 ∨ n = 5503 ∨ n = 5505 ∨ n = 5507 ∨ n = 5509 ∨ n = 5511 ∨ n = 5513 ∨ n = 5515 ∨ n = 5517 ∨ n = 5519 ∨ n = 5521 ∨ n = 5523 ∨ n = 5525 ∨ n = 5527 ∨ n = 5529 ∨ n = 5531 ∨ n = 5533 ∨ n = 5535 ∨ n = 5537 ∨ n = 5539 ∨ n = 5541 ∨ n = 5543 ∨ n = 5545 ∨ n = 5547 ∨ n = 5549 ∨ n = 5551 ∨ n = 5553 ∨ n = 5555 ∨ n = 5557 ∨ n = 5559 := by omega
  rcases hn with h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h
  · subst n
    exact ⟨5, witness_of_certificate certificate_5495⟩
  · subst n
    exact ⟨2, witness_of_certificate certificate_5497⟩
  · subst n
    exact ⟨8, witness_of_certificate certificate_5499⟩
  · subst n
    exact ⟨2, witness_of_certificate certificate_5501⟩
  · subst n
    exact ⟨43, witness_of_certificate certificate_5503⟩
  · subst n
    exact ⟨2, witness_of_certificate certificate_5505⟩
  · subst n
    exact ⟨4, witness_of_certificate certificate_5507⟩
  · subst n
    exact ⟨2, witness_of_certificate certificate_5509⟩
  · subst n
    exact ⟨7, witness_of_certificate certificate_5511⟩
  · subst n
    exact ⟨2, witness_of_certificate certificate_5513⟩
  · subst n
    exact ⟨5, witness_of_certificate certificate_5515⟩
  · subst n
    exact ⟨2, witness_of_certificate certificate_5517⟩
  · subst n
    exact ⟨7, witness_of_certificate certificate_5519⟩
  · subst n
    exact ⟨2, witness_of_certificate certificate_5521⟩
  · subst n
    exact ⟨4, witness_of_certificate certificate_5523⟩
  · subst n
    exact ⟨2, witness_of_certificate certificate_5525⟩
  · subst n
    exact ⟨5, witness_of_certificate certificate_5527⟩
  · subst n
    exact ⟨2, witness_of_certificate certificate_5529⟩
  · subst n
    exact ⟨12, witness_of_certificate certificate_5531⟩
  · subst n
    exact ⟨2, witness_of_certificate certificate_5533⟩
  · subst n
    exact ⟨27, witness_of_certificate certificate_5535⟩
  · subst n
    exact ⟨2, witness_of_certificate certificate_5537⟩
  · subst n
    exact ⟨4, witness_of_certificate certificate_5539⟩
  · subst n
    exact ⟨2, witness_of_certificate certificate_5541⟩
  · subst n
    exact ⟨10, witness_of_certificate certificate_5543⟩
  · subst n
    exact ⟨2, witness_of_certificate certificate_5545⟩
  · subst n
    exact ⟨5, witness_of_certificate certificate_5547⟩
  · subst n
    exact ⟨2, witness_of_certificate certificate_5549⟩
  · subst n
    exact ⟨8, witness_of_certificate certificate_5551⟩
  · subst n
    exact ⟨2, witness_of_certificate certificate_5553⟩
  · subst n
    exact ⟨4, witness_of_certificate certificate_5555⟩
  · subst n
    exact ⟨2, witness_of_certificate certificate_5557⟩
  · subst n
    exact ⟨5, witness_of_certificate certificate_5559⟩

end Collatz.Research.CoefficientDescent.Batch083
