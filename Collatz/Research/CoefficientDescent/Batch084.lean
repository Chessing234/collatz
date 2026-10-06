import Collatz.Research.CoefficientDescent.Basic

namespace Collatz.Research.CoefficientDescent.Batch084

open FirstDescentClass

set_option maxRecDepth 20000
set_option maxHeartbeats 0

/-- Checked base and every prefix for input 5561. -/
theorem certificate_5561 : classCertificateB 2 5561 = true := by
  decide

/-- The same exact first-descent time holds on an infinite dyadic ray. -/
theorem ray_5561 (m : Nat) : stoppingTime (2 ^ 2 * m + 5561) 2 :=
  stoppingTime_of_classCertificate certificate_5561 m

/-- Checked base and every prefix for input 5563. -/
theorem certificate_5563 : classCertificateB 7 5563 = true := by
  decide

/-- The same exact first-descent time holds on an infinite dyadic ray. -/
theorem ray_5563 (m : Nat) : stoppingTime (2 ^ 7 * m + 5563) 7 :=
  stoppingTime_of_classCertificate certificate_5563 m

/-- Checked base and every prefix for input 5565. -/
theorem certificate_5565 : classCertificateB 2 5565 = true := by
  decide

/-- The same exact first-descent time holds on an infinite dyadic ray. -/
theorem ray_5565 (m : Nat) : stoppingTime (2 ^ 2 * m + 5565) 2 :=
  stoppingTime_of_classCertificate certificate_5565 m

/-- Checked base and every prefix for input 5567. -/
theorem certificate_5567 : classCertificateB 35 5567 = true := by
  decide

/-- The same exact first-descent time holds on an infinite dyadic ray. -/
theorem ray_5567 (m : Nat) : stoppingTime (2 ^ 35 * m + 5567) 35 :=
  stoppingTime_of_classCertificate certificate_5567 m

/-- Checked base and every prefix for input 5569. -/
theorem certificate_5569 : classCertificateB 2 5569 = true := by
  decide

/-- The same exact first-descent time holds on an infinite dyadic ray. -/
theorem ray_5569 (m : Nat) : stoppingTime (2 ^ 2 * m + 5569) 2 :=
  stoppingTime_of_classCertificate certificate_5569 m

/-- Checked base and every prefix for input 5571. -/
theorem certificate_5571 : classCertificateB 4 5571 = true := by
  decide

/-- The same exact first-descent time holds on an infinite dyadic ray. -/
theorem ray_5571 (m : Nat) : stoppingTime (2 ^ 4 * m + 5571) 4 :=
  stoppingTime_of_classCertificate certificate_5571 m

/-- Checked base and every prefix for input 5573. -/
theorem certificate_5573 : classCertificateB 2 5573 = true := by
  decide

/-- The same exact first-descent time holds on an infinite dyadic ray. -/
theorem ray_5573 (m : Nat) : stoppingTime (2 ^ 2 * m + 5573) 2 :=
  stoppingTime_of_classCertificate certificate_5573 m

/-- Checked base and every prefix for input 5575. -/
theorem certificate_5575 : classCertificateB 8 5575 = true := by
  decide

/-- The same exact first-descent time holds on an infinite dyadic ray. -/
theorem ray_5575 (m : Nat) : stoppingTime (2 ^ 8 * m + 5575) 8 :=
  stoppingTime_of_classCertificate certificate_5575 m

/-- Checked base and every prefix for input 5577. -/
theorem certificate_5577 : classCertificateB 2 5577 = true := by
  decide

/-- The same exact first-descent time holds on an infinite dyadic ray. -/
theorem ray_5577 (m : Nat) : stoppingTime (2 ^ 2 * m + 5577) 2 :=
  stoppingTime_of_classCertificate certificate_5577 m

/-- Checked base and every prefix for input 5579. -/
theorem certificate_5579 : classCertificateB 5 5579 = true := by
  decide

/-- The same exact first-descent time holds on an infinite dyadic ray. -/
theorem ray_5579 (m : Nat) : stoppingTime (2 ^ 5 * m + 5579) 5 :=
  stoppingTime_of_classCertificate certificate_5579 m

/-- Checked base and every prefix for input 5581. -/
theorem certificate_5581 : classCertificateB 2 5581 = true := by
  decide

/-- The same exact first-descent time holds on an infinite dyadic ray. -/
theorem ray_5581 (m : Nat) : stoppingTime (2 ^ 2 * m + 5581) 2 :=
  stoppingTime_of_classCertificate certificate_5581 m

/-- Checked base and every prefix for input 5583. -/
theorem certificate_5583 : classCertificateB 16 5583 = true := by
  decide

/-- The same exact first-descent time holds on an infinite dyadic ray. -/
theorem ray_5583 (m : Nat) : stoppingTime (2 ^ 16 * m + 5583) 16 :=
  stoppingTime_of_classCertificate certificate_5583 m

/-- Checked base and every prefix for input 5585. -/
theorem certificate_5585 : classCertificateB 2 5585 = true := by
  decide

/-- The same exact first-descent time holds on an infinite dyadic ray. -/
theorem ray_5585 (m : Nat) : stoppingTime (2 ^ 2 * m + 5585) 2 :=
  stoppingTime_of_classCertificate certificate_5585 m

/-- Checked base and every prefix for input 5587. -/
theorem certificate_5587 : classCertificateB 4 5587 = true := by
  decide

/-- The same exact first-descent time holds on an infinite dyadic ray. -/
theorem ray_5587 (m : Nat) : stoppingTime (2 ^ 4 * m + 5587) 4 :=
  stoppingTime_of_classCertificate certificate_5587 m

/-- Checked base and every prefix for input 5589. -/
theorem certificate_5589 : classCertificateB 2 5589 = true := by
  decide

/-- The same exact first-descent time holds on an infinite dyadic ray. -/
theorem ray_5589 (m : Nat) : stoppingTime (2 ^ 2 * m + 5589) 2 :=
  stoppingTime_of_classCertificate certificate_5589 m

/-- Checked base and every prefix for input 5591. -/
theorem certificate_5591 : classCertificateB 5 5591 = true := by
  decide

/-- The same exact first-descent time holds on an infinite dyadic ray. -/
theorem ray_5591 (m : Nat) : stoppingTime (2 ^ 5 * m + 5591) 5 :=
  stoppingTime_of_classCertificate certificate_5591 m

/-- Checked base and every prefix for input 5593. -/
theorem certificate_5593 : classCertificateB 2 5593 = true := by
  decide

/-- The same exact first-descent time holds on an infinite dyadic ray. -/
theorem ray_5593 (m : Nat) : stoppingTime (2 ^ 2 * m + 5593) 2 :=
  stoppingTime_of_classCertificate certificate_5593 m

/-- Checked base and every prefix for input 5595. -/
theorem certificate_5595 : classCertificateB 8 5595 = true := by
  decide

/-- The same exact first-descent time holds on an infinite dyadic ray. -/
theorem ray_5595 (m : Nat) : stoppingTime (2 ^ 8 * m + 5595) 8 :=
  stoppingTime_of_classCertificate certificate_5595 m

/-- Checked base and every prefix for input 5597. -/
theorem certificate_5597 : classCertificateB 2 5597 = true := by
  decide

/-- The same exact first-descent time holds on an infinite dyadic ray. -/
theorem ray_5597 (m : Nat) : stoppingTime (2 ^ 2 * m + 5597) 2 :=
  stoppingTime_of_classCertificate certificate_5597 m

/-- Checked base and every prefix for input 5599. -/
theorem certificate_5599 : classCertificateB 15 5599 = true := by
  decide

/-- The same exact first-descent time holds on an infinite dyadic ray. -/
theorem ray_5599 (m : Nat) : stoppingTime (2 ^ 15 * m + 5599) 15 :=
  stoppingTime_of_classCertificate certificate_5599 m

/-- Checked base and every prefix for input 5601. -/
theorem certificate_5601 : classCertificateB 2 5601 = true := by
  decide

/-- The same exact first-descent time holds on an infinite dyadic ray. -/
theorem ray_5601 (m : Nat) : stoppingTime (2 ^ 2 * m + 5601) 2 :=
  stoppingTime_of_classCertificate certificate_5601 m

/-- Checked base and every prefix for input 5603. -/
theorem certificate_5603 : classCertificateB 4 5603 = true := by
  decide

/-- The same exact first-descent time holds on an infinite dyadic ray. -/
theorem ray_5603 (m : Nat) : stoppingTime (2 ^ 4 * m + 5603) 4 :=
  stoppingTime_of_classCertificate certificate_5603 m

/-- Checked base and every prefix for input 5605. -/
theorem certificate_5605 : classCertificateB 2 5605 = true := by
  decide

/-- The same exact first-descent time holds on an infinite dyadic ray. -/
theorem ray_5605 (m : Nat) : stoppingTime (2 ^ 2 * m + 5605) 2 :=
  stoppingTime_of_classCertificate certificate_5605 m

/-- Checked base and every prefix for input 5607. -/
theorem certificate_5607 : classCertificateB 13 5607 = true := by
  decide

/-- The same exact first-descent time holds on an infinite dyadic ray. -/
theorem ray_5607 (m : Nat) : stoppingTime (2 ^ 13 * m + 5607) 13 :=
  stoppingTime_of_classCertificate certificate_5607 m

/-- Checked base and every prefix for input 5609. -/
theorem certificate_5609 : classCertificateB 2 5609 = true := by
  decide

/-- The same exact first-descent time holds on an infinite dyadic ray. -/
theorem ray_5609 (m : Nat) : stoppingTime (2 ^ 2 * m + 5609) 2 :=
  stoppingTime_of_classCertificate certificate_5609 m

/-- Checked base and every prefix for input 5611. -/
theorem certificate_5611 : classCertificateB 5 5611 = true := by
  decide

/-- The same exact first-descent time holds on an infinite dyadic ray. -/
theorem ray_5611 (m : Nat) : stoppingTime (2 ^ 5 * m + 5611) 5 :=
  stoppingTime_of_classCertificate certificate_5611 m

/-- Checked base and every prefix for input 5613. -/
theorem certificate_5613 : classCertificateB 2 5613 = true := by
  decide

/-- The same exact first-descent time holds on an infinite dyadic ray. -/
theorem ray_5613 (m : Nat) : stoppingTime (2 ^ 2 * m + 5613) 2 :=
  stoppingTime_of_classCertificate certificate_5613 m

/-- Checked base and every prefix for input 5615. -/
theorem certificate_5615 : classCertificateB 13 5615 = true := by
  decide

/-- The same exact first-descent time holds on an infinite dyadic ray. -/
theorem ray_5615 (m : Nat) : stoppingTime (2 ^ 13 * m + 5615) 13 :=
  stoppingTime_of_classCertificate certificate_5615 m

/-- Checked base and every prefix for input 5617. -/
theorem certificate_5617 : classCertificateB 2 5617 = true := by
  decide

/-- The same exact first-descent time holds on an infinite dyadic ray. -/
theorem ray_5617 (m : Nat) : stoppingTime (2 ^ 2 * m + 5617) 2 :=
  stoppingTime_of_classCertificate certificate_5617 m

/-- Checked base and every prefix for input 5619. -/
theorem certificate_5619 : classCertificateB 4 5619 = true := by
  decide

/-- The same exact first-descent time holds on an infinite dyadic ray. -/
theorem ray_5619 (m : Nat) : stoppingTime (2 ^ 4 * m + 5619) 4 :=
  stoppingTime_of_classCertificate certificate_5619 m

/-- Checked base and every prefix for input 5621. -/
theorem certificate_5621 : classCertificateB 2 5621 = true := by
  decide

/-- The same exact first-descent time holds on an infinite dyadic ray. -/
theorem ray_5621 (m : Nat) : stoppingTime (2 ^ 2 * m + 5621) 2 :=
  stoppingTime_of_classCertificate certificate_5621 m

/-- Checked base and every prefix for input 5623. -/
theorem certificate_5623 : classCertificateB 5 5623 = true := by
  decide

/-- The same exact first-descent time holds on an infinite dyadic ray. -/
theorem ray_5623 (m : Nat) : stoppingTime (2 ^ 5 * m + 5623) 5 :=
  stoppingTime_of_classCertificate certificate_5623 m

/-- Checked base and every prefix for input 5625. -/
theorem certificate_5625 : classCertificateB 2 5625 = true := by
  decide

/-- The same exact first-descent time holds on an infinite dyadic ray. -/
theorem ray_5625 (m : Nat) : stoppingTime (2 ^ 2 * m + 5625) 2 :=
  stoppingTime_of_classCertificate certificate_5625 m

/-- Checked base and every prefix for input 5627. -/
theorem certificate_5627 : classCertificateB 10 5627 = true := by
  decide

/-- The same exact first-descent time holds on an infinite dyadic ray. -/
theorem ray_5627 (m : Nat) : stoppingTime (2 ^ 10 * m + 5627) 10 :=
  stoppingTime_of_classCertificate certificate_5627 m

/-- Exhaustive coverage of the odd inputs in this batch, with no gaps. -/
theorem coverage : CertifiedRange 5561 5629 := by
  intro n hlo hhi hodd
  have hn : n = 5561 ∨ n = 5563 ∨ n = 5565 ∨ n = 5567 ∨ n = 5569 ∨ n = 5571 ∨ n = 5573 ∨ n = 5575 ∨ n = 5577 ∨ n = 5579 ∨ n = 5581 ∨ n = 5583 ∨ n = 5585 ∨ n = 5587 ∨ n = 5589 ∨ n = 5591 ∨ n = 5593 ∨ n = 5595 ∨ n = 5597 ∨ n = 5599 ∨ n = 5601 ∨ n = 5603 ∨ n = 5605 ∨ n = 5607 ∨ n = 5609 ∨ n = 5611 ∨ n = 5613 ∨ n = 5615 ∨ n = 5617 ∨ n = 5619 ∨ n = 5621 ∨ n = 5623 ∨ n = 5625 ∨ n = 5627 := by omega
  rcases hn with h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h
  · subst n
    exact ⟨2, witness_of_certificate certificate_5561⟩
  · subst n
    exact ⟨7, witness_of_certificate certificate_5563⟩
  · subst n
    exact ⟨2, witness_of_certificate certificate_5565⟩
  · subst n
    exact ⟨35, witness_of_certificate certificate_5567⟩
  · subst n
    exact ⟨2, witness_of_certificate certificate_5569⟩
  · subst n
    exact ⟨4, witness_of_certificate certificate_5571⟩
  · subst n
    exact ⟨2, witness_of_certificate certificate_5573⟩
  · subst n
    exact ⟨8, witness_of_certificate certificate_5575⟩
  · subst n
    exact ⟨2, witness_of_certificate certificate_5577⟩
  · subst n
    exact ⟨5, witness_of_certificate certificate_5579⟩
  · subst n
    exact ⟨2, witness_of_certificate certificate_5581⟩
  · subst n
    exact ⟨16, witness_of_certificate certificate_5583⟩
  · subst n
    exact ⟨2, witness_of_certificate certificate_5585⟩
  · subst n
    exact ⟨4, witness_of_certificate certificate_5587⟩
  · subst n
    exact ⟨2, witness_of_certificate certificate_5589⟩
  · subst n
    exact ⟨5, witness_of_certificate certificate_5591⟩
  · subst n
    exact ⟨2, witness_of_certificate certificate_5593⟩
  · subst n
    exact ⟨8, witness_of_certificate certificate_5595⟩
  · subst n
    exact ⟨2, witness_of_certificate certificate_5597⟩
  · subst n
    exact ⟨15, witness_of_certificate certificate_5599⟩
  · subst n
    exact ⟨2, witness_of_certificate certificate_5601⟩
  · subst n
    exact ⟨4, witness_of_certificate certificate_5603⟩
  · subst n
    exact ⟨2, witness_of_certificate certificate_5605⟩
  · subst n
    exact ⟨13, witness_of_certificate certificate_5607⟩
  · subst n
    exact ⟨2, witness_of_certificate certificate_5609⟩
  · subst n
    exact ⟨5, witness_of_certificate certificate_5611⟩
  · subst n
    exact ⟨2, witness_of_certificate certificate_5613⟩
  · subst n
    exact ⟨13, witness_of_certificate certificate_5615⟩
  · subst n
    exact ⟨2, witness_of_certificate certificate_5617⟩
  · subst n
    exact ⟨4, witness_of_certificate certificate_5619⟩
  · subst n
    exact ⟨2, witness_of_certificate certificate_5621⟩
  · subst n
    exact ⟨5, witness_of_certificate certificate_5623⟩
  · subst n
    exact ⟨2, witness_of_certificate certificate_5625⟩
  · subst n
    exact ⟨10, witness_of_certificate certificate_5627⟩

end Collatz.Research.CoefficientDescent.Batch084
