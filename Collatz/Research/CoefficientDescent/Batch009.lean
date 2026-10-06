import Collatz.Research.CoefficientDescent.Basic

namespace Collatz.Research.CoefficientDescent.Batch009

open FirstDescentClass

set_option maxRecDepth 20000
set_option maxHeartbeats 0

/-- Checked base and every prefix for input 537. -/
theorem certificate_537 : classCertificateB 2 537 = true := by
  decide

/-- The same exact first-descent time holds on an infinite dyadic ray. -/
theorem ray_537 (m : Nat) : stoppingTime (2 ^ 2 * m + 537) 2 :=
  stoppingTime_of_classCertificate certificate_537 m

/-- Checked base and every prefix for input 539. -/
theorem certificate_539 : classCertificateB 13 539 = true := by
  decide

/-- The same exact first-descent time holds on an infinite dyadic ray. -/
theorem ray_539 (m : Nat) : stoppingTime (2 ^ 13 * m + 539) 13 :=
  stoppingTime_of_classCertificate certificate_539 m

/-- Checked base and every prefix for input 541. -/
theorem certificate_541 : classCertificateB 2 541 = true := by
  decide

/-- The same exact first-descent time holds on an infinite dyadic ray. -/
theorem ray_541 (m : Nat) : stoppingTime (2 ^ 2 * m + 541) 2 :=
  stoppingTime_of_classCertificate certificate_541 m

/-- Checked base and every prefix for input 543. -/
theorem certificate_543 : classCertificateB 13 543 = true := by
  decide

/-- The same exact first-descent time holds on an infinite dyadic ray. -/
theorem ray_543 (m : Nat) : stoppingTime (2 ^ 13 * m + 543) 13 :=
  stoppingTime_of_classCertificate certificate_543 m

/-- Checked base and every prefix for input 545. -/
theorem certificate_545 : classCertificateB 2 545 = true := by
  decide

/-- The same exact first-descent time holds on an infinite dyadic ray. -/
theorem ray_545 (m : Nat) : stoppingTime (2 ^ 2 * m + 545) 2 :=
  stoppingTime_of_classCertificate certificate_545 m

/-- Checked base and every prefix for input 547. -/
theorem certificate_547 : classCertificateB 4 547 = true := by
  decide

/-- The same exact first-descent time holds on an infinite dyadic ray. -/
theorem ray_547 (m : Nat) : stoppingTime (2 ^ 4 * m + 547) 4 :=
  stoppingTime_of_classCertificate certificate_547 m

/-- Checked base and every prefix for input 549. -/
theorem certificate_549 : classCertificateB 2 549 = true := by
  decide

/-- The same exact first-descent time holds on an infinite dyadic ray. -/
theorem ray_549 (m : Nat) : stoppingTime (2 ^ 2 * m + 549) 2 :=
  stoppingTime_of_classCertificate certificate_549 m

/-- Checked base and every prefix for input 551. -/
theorem certificate_551 : classCertificateB 8 551 = true := by
  decide

/-- The same exact first-descent time holds on an infinite dyadic ray. -/
theorem ray_551 (m : Nat) : stoppingTime (2 ^ 8 * m + 551) 8 :=
  stoppingTime_of_classCertificate certificate_551 m

/-- Checked base and every prefix for input 553. -/
theorem certificate_553 : classCertificateB 2 553 = true := by
  decide

/-- The same exact first-descent time holds on an infinite dyadic ray. -/
theorem ray_553 (m : Nat) : stoppingTime (2 ^ 2 * m + 553) 2 :=
  stoppingTime_of_classCertificate certificate_553 m

/-- Checked base and every prefix for input 555. -/
theorem certificate_555 : classCertificateB 5 555 = true := by
  decide

/-- The same exact first-descent time holds on an infinite dyadic ray. -/
theorem ray_555 (m : Nat) : stoppingTime (2 ^ 5 * m + 555) 5 :=
  stoppingTime_of_classCertificate certificate_555 m

/-- Checked base and every prefix for input 557. -/
theorem certificate_557 : classCertificateB 2 557 = true := by
  decide

/-- The same exact first-descent time holds on an infinite dyadic ray. -/
theorem ray_557 (m : Nat) : stoppingTime (2 ^ 2 * m + 557) 2 :=
  stoppingTime_of_classCertificate certificate_557 m

/-- Checked base and every prefix for input 559. -/
theorem certificate_559 : classCertificateB 16 559 = true := by
  decide

/-- The same exact first-descent time holds on an infinite dyadic ray. -/
theorem ray_559 (m : Nat) : stoppingTime (2 ^ 16 * m + 559) 16 :=
  stoppingTime_of_classCertificate certificate_559 m

/-- Checked base and every prefix for input 561. -/
theorem certificate_561 : classCertificateB 2 561 = true := by
  decide

/-- The same exact first-descent time holds on an infinite dyadic ray. -/
theorem ray_561 (m : Nat) : stoppingTime (2 ^ 2 * m + 561) 2 :=
  stoppingTime_of_classCertificate certificate_561 m

/-- Checked base and every prefix for input 563. -/
theorem certificate_563 : classCertificateB 4 563 = true := by
  decide

/-- The same exact first-descent time holds on an infinite dyadic ray. -/
theorem ray_563 (m : Nat) : stoppingTime (2 ^ 4 * m + 563) 4 :=
  stoppingTime_of_classCertificate certificate_563 m

/-- Checked base and every prefix for input 565. -/
theorem certificate_565 : classCertificateB 2 565 = true := by
  decide

/-- The same exact first-descent time holds on an infinite dyadic ray. -/
theorem ray_565 (m : Nat) : stoppingTime (2 ^ 2 * m + 565) 2 :=
  stoppingTime_of_classCertificate certificate_565 m

/-- Checked base and every prefix for input 567. -/
theorem certificate_567 : classCertificateB 5 567 = true := by
  decide

/-- The same exact first-descent time holds on an infinite dyadic ray. -/
theorem ray_567 (m : Nat) : stoppingTime (2 ^ 5 * m + 567) 5 :=
  stoppingTime_of_classCertificate certificate_567 m

/-- Checked base and every prefix for input 569. -/
theorem certificate_569 : classCertificateB 2 569 = true := by
  decide

/-- The same exact first-descent time holds on an infinite dyadic ray. -/
theorem ray_569 (m : Nat) : stoppingTime (2 ^ 2 * m + 569) 2 :=
  stoppingTime_of_classCertificate certificate_569 m

/-- Checked base and every prefix for input 571. -/
theorem certificate_571 : classCertificateB 7 571 = true := by
  decide

/-- The same exact first-descent time holds on an infinite dyadic ray. -/
theorem ray_571 (m : Nat) : stoppingTime (2 ^ 7 * m + 571) 7 :=
  stoppingTime_of_classCertificate certificate_571 m

/-- Checked base and every prefix for input 573. -/
theorem certificate_573 : classCertificateB 2 573 = true := by
  decide

/-- The same exact first-descent time holds on an infinite dyadic ray. -/
theorem ray_573 (m : Nat) : stoppingTime (2 ^ 2 * m + 573) 2 :=
  stoppingTime_of_classCertificate certificate_573 m

/-- Checked base and every prefix for input 575. -/
theorem certificate_575 : classCertificateB 10 575 = true := by
  decide

/-- The same exact first-descent time holds on an infinite dyadic ray. -/
theorem ray_575 (m : Nat) : stoppingTime (2 ^ 10 * m + 575) 10 :=
  stoppingTime_of_classCertificate certificate_575 m

/-- Checked base and every prefix for input 577. -/
theorem certificate_577 : classCertificateB 2 577 = true := by
  decide

/-- The same exact first-descent time holds on an infinite dyadic ray. -/
theorem ray_577 (m : Nat) : stoppingTime (2 ^ 2 * m + 577) 2 :=
  stoppingTime_of_classCertificate certificate_577 m

/-- Checked base and every prefix for input 579. -/
theorem certificate_579 : classCertificateB 4 579 = true := by
  decide

/-- The same exact first-descent time holds on an infinite dyadic ray. -/
theorem ray_579 (m : Nat) : stoppingTime (2 ^ 4 * m + 579) 4 :=
  stoppingTime_of_classCertificate certificate_579 m

/-- Checked base and every prefix for input 581. -/
theorem certificate_581 : classCertificateB 2 581 = true := by
  decide

/-- The same exact first-descent time holds on an infinite dyadic ray. -/
theorem ray_581 (m : Nat) : stoppingTime (2 ^ 2 * m + 581) 2 :=
  stoppingTime_of_classCertificate certificate_581 m

/-- Checked base and every prefix for input 583. -/
theorem certificate_583 : classCertificateB 10 583 = true := by
  decide

/-- The same exact first-descent time holds on an infinite dyadic ray. -/
theorem ray_583 (m : Nat) : stoppingTime (2 ^ 10 * m + 583) 10 :=
  stoppingTime_of_classCertificate certificate_583 m

/-- Checked base and every prefix for input 585. -/
theorem certificate_585 : classCertificateB 2 585 = true := by
  decide

/-- The same exact first-descent time holds on an infinite dyadic ray. -/
theorem ray_585 (m : Nat) : stoppingTime (2 ^ 2 * m + 585) 2 :=
  stoppingTime_of_classCertificate certificate_585 m

/-- Checked base and every prefix for input 587. -/
theorem certificate_587 : classCertificateB 5 587 = true := by
  decide

/-- The same exact first-descent time holds on an infinite dyadic ray. -/
theorem ray_587 (m : Nat) : stoppingTime (2 ^ 5 * m + 587) 5 :=
  stoppingTime_of_classCertificate certificate_587 m

/-- Checked base and every prefix for input 589. -/
theorem certificate_589 : classCertificateB 2 589 = true := by
  decide

/-- The same exact first-descent time holds on an infinite dyadic ray. -/
theorem ray_589 (m : Nat) : stoppingTime (2 ^ 2 * m + 589) 2 :=
  stoppingTime_of_classCertificate certificate_589 m

/-- Checked base and every prefix for input 591. -/
theorem certificate_591 : classCertificateB 8 591 = true := by
  decide

/-- The same exact first-descent time holds on an infinite dyadic ray. -/
theorem ray_591 (m : Nat) : stoppingTime (2 ^ 8 * m + 591) 8 :=
  stoppingTime_of_classCertificate certificate_591 m

/-- Checked base and every prefix for input 593. -/
theorem certificate_593 : classCertificateB 2 593 = true := by
  decide

/-- The same exact first-descent time holds on an infinite dyadic ray. -/
theorem ray_593 (m : Nat) : stoppingTime (2 ^ 2 * m + 593) 2 :=
  stoppingTime_of_classCertificate certificate_593 m

/-- Checked base and every prefix for input 595. -/
theorem certificate_595 : classCertificateB 4 595 = true := by
  decide

/-- The same exact first-descent time holds on an infinite dyadic ray. -/
theorem ray_595 (m : Nat) : stoppingTime (2 ^ 4 * m + 595) 4 :=
  stoppingTime_of_classCertificate certificate_595 m

/-- Checked base and every prefix for input 597. -/
theorem certificate_597 : classCertificateB 2 597 = true := by
  decide

/-- The same exact first-descent time holds on an infinite dyadic ray. -/
theorem ray_597 (m : Nat) : stoppingTime (2 ^ 2 * m + 597) 2 :=
  stoppingTime_of_classCertificate certificate_597 m

/-- Checked base and every prefix for input 599. -/
theorem certificate_599 : classCertificateB 5 599 = true := by
  decide

/-- The same exact first-descent time holds on an infinite dyadic ray. -/
theorem ray_599 (m : Nat) : stoppingTime (2 ^ 5 * m + 599) 5 :=
  stoppingTime_of_classCertificate certificate_599 m

/-- Checked base and every prefix for input 601. -/
theorem certificate_601 : classCertificateB 2 601 = true := by
  decide

/-- The same exact first-descent time holds on an infinite dyadic ray. -/
theorem ray_601 (m : Nat) : stoppingTime (2 ^ 2 * m + 601) 2 :=
  stoppingTime_of_classCertificate certificate_601 m

/-- Checked base and every prefix for input 603. -/
theorem certificate_603 : classCertificateB 16 603 = true := by
  decide

/-- The same exact first-descent time holds on an infinite dyadic ray. -/
theorem ray_603 (m : Nat) : stoppingTime (2 ^ 16 * m + 603) 16 :=
  stoppingTime_of_classCertificate certificate_603 m

/-- Exhaustive coverage of the odd inputs in this batch, with no gaps. -/
theorem coverage : CertifiedRange 537 605 := by
  intro n hlo hhi hodd
  have hn : n = 537 ∨ n = 539 ∨ n = 541 ∨ n = 543 ∨ n = 545 ∨ n = 547 ∨ n = 549 ∨ n = 551 ∨ n = 553 ∨ n = 555 ∨ n = 557 ∨ n = 559 ∨ n = 561 ∨ n = 563 ∨ n = 565 ∨ n = 567 ∨ n = 569 ∨ n = 571 ∨ n = 573 ∨ n = 575 ∨ n = 577 ∨ n = 579 ∨ n = 581 ∨ n = 583 ∨ n = 585 ∨ n = 587 ∨ n = 589 ∨ n = 591 ∨ n = 593 ∨ n = 595 ∨ n = 597 ∨ n = 599 ∨ n = 601 ∨ n = 603 := by omega
  rcases hn with h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h
  · subst n
    exact ⟨2, witness_of_certificate certificate_537⟩
  · subst n
    exact ⟨13, witness_of_certificate certificate_539⟩
  · subst n
    exact ⟨2, witness_of_certificate certificate_541⟩
  · subst n
    exact ⟨13, witness_of_certificate certificate_543⟩
  · subst n
    exact ⟨2, witness_of_certificate certificate_545⟩
  · subst n
    exact ⟨4, witness_of_certificate certificate_547⟩
  · subst n
    exact ⟨2, witness_of_certificate certificate_549⟩
  · subst n
    exact ⟨8, witness_of_certificate certificate_551⟩
  · subst n
    exact ⟨2, witness_of_certificate certificate_553⟩
  · subst n
    exact ⟨5, witness_of_certificate certificate_555⟩
  · subst n
    exact ⟨2, witness_of_certificate certificate_557⟩
  · subst n
    exact ⟨16, witness_of_certificate certificate_559⟩
  · subst n
    exact ⟨2, witness_of_certificate certificate_561⟩
  · subst n
    exact ⟨4, witness_of_certificate certificate_563⟩
  · subst n
    exact ⟨2, witness_of_certificate certificate_565⟩
  · subst n
    exact ⟨5, witness_of_certificate certificate_567⟩
  · subst n
    exact ⟨2, witness_of_certificate certificate_569⟩
  · subst n
    exact ⟨7, witness_of_certificate certificate_571⟩
  · subst n
    exact ⟨2, witness_of_certificate certificate_573⟩
  · subst n
    exact ⟨10, witness_of_certificate certificate_575⟩
  · subst n
    exact ⟨2, witness_of_certificate certificate_577⟩
  · subst n
    exact ⟨4, witness_of_certificate certificate_579⟩
  · subst n
    exact ⟨2, witness_of_certificate certificate_581⟩
  · subst n
    exact ⟨10, witness_of_certificate certificate_583⟩
  · subst n
    exact ⟨2, witness_of_certificate certificate_585⟩
  · subst n
    exact ⟨5, witness_of_certificate certificate_587⟩
  · subst n
    exact ⟨2, witness_of_certificate certificate_589⟩
  · subst n
    exact ⟨8, witness_of_certificate certificate_591⟩
  · subst n
    exact ⟨2, witness_of_certificate certificate_593⟩
  · subst n
    exact ⟨4, witness_of_certificate certificate_595⟩
  · subst n
    exact ⟨2, witness_of_certificate certificate_597⟩
  · subst n
    exact ⟨5, witness_of_certificate certificate_599⟩
  · subst n
    exact ⟨2, witness_of_certificate certificate_601⟩
  · subst n
    exact ⟨16, witness_of_certificate certificate_603⟩

end Collatz.Research.CoefficientDescent.Batch009
