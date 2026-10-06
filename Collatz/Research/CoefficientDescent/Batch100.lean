import Collatz.Research.CoefficientDescent.Basic

namespace Collatz.Research.CoefficientDescent.Batch100

open FirstDescentClass

set_option maxRecDepth 20000
set_option maxHeartbeats 0

/-- Checked base and every prefix for input 6633. -/
theorem certificate_6633 : classCertificateB 2 6633 = true := by
  decide

/-- The same exact first-descent time holds on an infinite dyadic ray. -/
theorem ray_6633 (m : Nat) : stoppingTime (2 ^ 2 * m + 6633) 2 :=
  stoppingTime_of_classCertificate certificate_6633 m

/-- Checked base and every prefix for input 6635. -/
theorem certificate_6635 : classCertificateB 5 6635 = true := by
  decide

/-- The same exact first-descent time holds on an infinite dyadic ray. -/
theorem ray_6635 (m : Nat) : stoppingTime (2 ^ 5 * m + 6635) 5 :=
  stoppingTime_of_classCertificate certificate_6635 m

/-- Checked base and every prefix for input 6637. -/
theorem certificate_6637 : classCertificateB 2 6637 = true := by
  decide

/-- The same exact first-descent time holds on an infinite dyadic ray. -/
theorem ray_6637 (m : Nat) : stoppingTime (2 ^ 2 * m + 6637) 2 :=
  stoppingTime_of_classCertificate certificate_6637 m

/-- Checked base and every prefix for input 6639. -/
theorem certificate_6639 : classCertificateB 16 6639 = true := by
  decide

/-- The same exact first-descent time holds on an infinite dyadic ray. -/
theorem ray_6639 (m : Nat) : stoppingTime (2 ^ 16 * m + 6639) 16 :=
  stoppingTime_of_classCertificate certificate_6639 m

/-- Checked base and every prefix for input 6641. -/
theorem certificate_6641 : classCertificateB 2 6641 = true := by
  decide

/-- The same exact first-descent time holds on an infinite dyadic ray. -/
theorem ray_6641 (m : Nat) : stoppingTime (2 ^ 2 * m + 6641) 2 :=
  stoppingTime_of_classCertificate certificate_6641 m

/-- Checked base and every prefix for input 6643. -/
theorem certificate_6643 : classCertificateB 4 6643 = true := by
  decide

/-- The same exact first-descent time holds on an infinite dyadic ray. -/
theorem ray_6643 (m : Nat) : stoppingTime (2 ^ 4 * m + 6643) 4 :=
  stoppingTime_of_classCertificate certificate_6643 m

/-- Checked base and every prefix for input 6645. -/
theorem certificate_6645 : classCertificateB 2 6645 = true := by
  decide

/-- The same exact first-descent time holds on an infinite dyadic ray. -/
theorem ray_6645 (m : Nat) : stoppingTime (2 ^ 2 * m + 6645) 2 :=
  stoppingTime_of_classCertificate certificate_6645 m

/-- Checked base and every prefix for input 6647. -/
theorem certificate_6647 : classCertificateB 5 6647 = true := by
  decide

/-- The same exact first-descent time holds on an infinite dyadic ray. -/
theorem ray_6647 (m : Nat) : stoppingTime (2 ^ 5 * m + 6647) 5 :=
  stoppingTime_of_classCertificate certificate_6647 m

/-- Checked base and every prefix for input 6649. -/
theorem certificate_6649 : classCertificateB 2 6649 = true := by
  decide

/-- The same exact first-descent time holds on an infinite dyadic ray. -/
theorem ray_6649 (m : Nat) : stoppingTime (2 ^ 2 * m + 6649) 2 :=
  stoppingTime_of_classCertificate certificate_6649 m

/-- Checked base and every prefix for input 6651. -/
theorem certificate_6651 : classCertificateB 10 6651 = true := by
  decide

/-- The same exact first-descent time holds on an infinite dyadic ray. -/
theorem ray_6651 (m : Nat) : stoppingTime (2 ^ 10 * m + 6651) 10 :=
  stoppingTime_of_classCertificate certificate_6651 m

/-- Checked base and every prefix for input 6653. -/
theorem certificate_6653 : classCertificateB 2 6653 = true := by
  decide

/-- The same exact first-descent time holds on an infinite dyadic ray. -/
theorem ray_6653 (m : Nat) : stoppingTime (2 ^ 2 * m + 6653) 2 :=
  stoppingTime_of_classCertificate certificate_6653 m

/-- Checked base and every prefix for input 6655. -/
theorem certificate_6655 : classCertificateB 35 6655 = true := by
  decide

/-- The same exact first-descent time holds on an infinite dyadic ray. -/
theorem ray_6655 (m : Nat) : stoppingTime (2 ^ 35 * m + 6655) 35 :=
  stoppingTime_of_classCertificate certificate_6655 m

/-- Checked base and every prefix for input 6657. -/
theorem certificate_6657 : classCertificateB 2 6657 = true := by
  decide

/-- The same exact first-descent time holds on an infinite dyadic ray. -/
theorem ray_6657 (m : Nat) : stoppingTime (2 ^ 2 * m + 6657) 2 :=
  stoppingTime_of_classCertificate certificate_6657 m

/-- Checked base and every prefix for input 6659. -/
theorem certificate_6659 : classCertificateB 4 6659 = true := by
  decide

/-- The same exact first-descent time holds on an infinite dyadic ray. -/
theorem ray_6659 (m : Nat) : stoppingTime (2 ^ 4 * m + 6659) 4 :=
  stoppingTime_of_classCertificate certificate_6659 m

/-- Checked base and every prefix for input 6661. -/
theorem certificate_6661 : classCertificateB 2 6661 = true := by
  decide

/-- The same exact first-descent time holds on an infinite dyadic ray. -/
theorem ray_6661 (m : Nat) : stoppingTime (2 ^ 2 * m + 6661) 2 :=
  stoppingTime_of_classCertificate certificate_6661 m

/-- Checked base and every prefix for input 6663. -/
theorem certificate_6663 : classCertificateB 7 6663 = true := by
  decide

/-- The same exact first-descent time holds on an infinite dyadic ray. -/
theorem ray_6663 (m : Nat) : stoppingTime (2 ^ 7 * m + 6663) 7 :=
  stoppingTime_of_classCertificate certificate_6663 m

/-- Checked base and every prefix for input 6665. -/
theorem certificate_6665 : classCertificateB 2 6665 = true := by
  decide

/-- The same exact first-descent time holds on an infinite dyadic ray. -/
theorem ray_6665 (m : Nat) : stoppingTime (2 ^ 2 * m + 6665) 2 :=
  stoppingTime_of_classCertificate certificate_6665 m

/-- Checked base and every prefix for input 6667. -/
theorem certificate_6667 : classCertificateB 5 6667 = true := by
  decide

/-- The same exact first-descent time holds on an infinite dyadic ray. -/
theorem ray_6667 (m : Nat) : stoppingTime (2 ^ 5 * m + 6667) 5 :=
  stoppingTime_of_classCertificate certificate_6667 m

/-- Checked base and every prefix for input 6669. -/
theorem certificate_6669 : classCertificateB 2 6669 = true := by
  decide

/-- The same exact first-descent time holds on an infinite dyadic ray. -/
theorem ray_6669 (m : Nat) : stoppingTime (2 ^ 2 * m + 6669) 2 :=
  stoppingTime_of_classCertificate certificate_6669 m

/-- Checked base and every prefix for input 6671. -/
theorem certificate_6671 : classCertificateB 7 6671 = true := by
  decide

/-- The same exact first-descent time holds on an infinite dyadic ray. -/
theorem ray_6671 (m : Nat) : stoppingTime (2 ^ 7 * m + 6671) 7 :=
  stoppingTime_of_classCertificate certificate_6671 m

/-- Checked base and every prefix for input 6673. -/
theorem certificate_6673 : classCertificateB 2 6673 = true := by
  decide

/-- The same exact first-descent time holds on an infinite dyadic ray. -/
theorem ray_6673 (m : Nat) : stoppingTime (2 ^ 2 * m + 6673) 2 :=
  stoppingTime_of_classCertificate certificate_6673 m

/-- Checked base and every prefix for input 6675. -/
theorem certificate_6675 : classCertificateB 4 6675 = true := by
  decide

/-- The same exact first-descent time holds on an infinite dyadic ray. -/
theorem ray_6675 (m : Nat) : stoppingTime (2 ^ 4 * m + 6675) 4 :=
  stoppingTime_of_classCertificate certificate_6675 m

/-- Checked base and every prefix for input 6677. -/
theorem certificate_6677 : classCertificateB 2 6677 = true := by
  decide

/-- The same exact first-descent time holds on an infinite dyadic ray. -/
theorem ray_6677 (m : Nat) : stoppingTime (2 ^ 2 * m + 6677) 2 :=
  stoppingTime_of_classCertificate certificate_6677 m

/-- Checked base and every prefix for input 6679. -/
theorem certificate_6679 : classCertificateB 5 6679 = true := by
  decide

/-- The same exact first-descent time holds on an infinite dyadic ray. -/
theorem ray_6679 (m : Nat) : stoppingTime (2 ^ 5 * m + 6679) 5 :=
  stoppingTime_of_classCertificate certificate_6679 m

/-- Checked base and every prefix for input 6681. -/
theorem certificate_6681 : classCertificateB 2 6681 = true := by
  decide

/-- The same exact first-descent time holds on an infinite dyadic ray. -/
theorem ray_6681 (m : Nat) : stoppingTime (2 ^ 2 * m + 6681) 2 :=
  stoppingTime_of_classCertificate certificate_6681 m

/-- Checked base and every prefix for input 6683. -/
theorem certificate_6683 : classCertificateB 12 6683 = true := by
  decide

/-- The same exact first-descent time holds on an infinite dyadic ray. -/
theorem ray_6683 (m : Nat) : stoppingTime (2 ^ 12 * m + 6683) 12 :=
  stoppingTime_of_classCertificate certificate_6683 m

/-- Checked base and every prefix for input 6685. -/
theorem certificate_6685 : classCertificateB 2 6685 = true := by
  decide

/-- The same exact first-descent time holds on an infinite dyadic ray. -/
theorem ray_6685 (m : Nat) : stoppingTime (2 ^ 2 * m + 6685) 2 :=
  stoppingTime_of_classCertificate certificate_6685 m

/-- Checked base and every prefix for input 6687. -/
theorem certificate_6687 : classCertificateB 12 6687 = true := by
  decide

/-- The same exact first-descent time holds on an infinite dyadic ray. -/
theorem ray_6687 (m : Nat) : stoppingTime (2 ^ 12 * m + 6687) 12 :=
  stoppingTime_of_classCertificate certificate_6687 m

/-- Checked base and every prefix for input 6689. -/
theorem certificate_6689 : classCertificateB 2 6689 = true := by
  decide

/-- The same exact first-descent time holds on an infinite dyadic ray. -/
theorem ray_6689 (m : Nat) : stoppingTime (2 ^ 2 * m + 6689) 2 :=
  stoppingTime_of_classCertificate certificate_6689 m

/-- Checked base and every prefix for input 6691. -/
theorem certificate_6691 : classCertificateB 4 6691 = true := by
  decide

/-- The same exact first-descent time holds on an infinite dyadic ray. -/
theorem ray_6691 (m : Nat) : stoppingTime (2 ^ 4 * m + 6691) 4 :=
  stoppingTime_of_classCertificate certificate_6691 m

/-- Checked base and every prefix for input 6693. -/
theorem certificate_6693 : classCertificateB 2 6693 = true := by
  decide

/-- The same exact first-descent time holds on an infinite dyadic ray. -/
theorem ray_6693 (m : Nat) : stoppingTime (2 ^ 2 * m + 6693) 2 :=
  stoppingTime_of_classCertificate certificate_6693 m

/-- Checked base and every prefix for input 6695. -/
theorem certificate_6695 : classCertificateB 8 6695 = true := by
  decide

/-- The same exact first-descent time holds on an infinite dyadic ray. -/
theorem ray_6695 (m : Nat) : stoppingTime (2 ^ 8 * m + 6695) 8 :=
  stoppingTime_of_classCertificate certificate_6695 m

/-- Checked base and every prefix for input 6697. -/
theorem certificate_6697 : classCertificateB 2 6697 = true := by
  decide

/-- The same exact first-descent time holds on an infinite dyadic ray. -/
theorem ray_6697 (m : Nat) : stoppingTime (2 ^ 2 * m + 6697) 2 :=
  stoppingTime_of_classCertificate certificate_6697 m

/-- Checked base and every prefix for input 6699. -/
theorem certificate_6699 : classCertificateB 5 6699 = true := by
  decide

/-- The same exact first-descent time holds on an infinite dyadic ray. -/
theorem ray_6699 (m : Nat) : stoppingTime (2 ^ 5 * m + 6699) 5 :=
  stoppingTime_of_classCertificate certificate_6699 m

/-- Exhaustive coverage of the odd inputs in this batch, with no gaps. -/
theorem coverage : CertifiedRange 6633 6701 := by
  intro n hlo hhi hodd
  have hn : n = 6633 ∨ n = 6635 ∨ n = 6637 ∨ n = 6639 ∨ n = 6641 ∨ n = 6643 ∨ n = 6645 ∨ n = 6647 ∨ n = 6649 ∨ n = 6651 ∨ n = 6653 ∨ n = 6655 ∨ n = 6657 ∨ n = 6659 ∨ n = 6661 ∨ n = 6663 ∨ n = 6665 ∨ n = 6667 ∨ n = 6669 ∨ n = 6671 ∨ n = 6673 ∨ n = 6675 ∨ n = 6677 ∨ n = 6679 ∨ n = 6681 ∨ n = 6683 ∨ n = 6685 ∨ n = 6687 ∨ n = 6689 ∨ n = 6691 ∨ n = 6693 ∨ n = 6695 ∨ n = 6697 ∨ n = 6699 := by omega
  rcases hn with h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h
  · subst n
    exact ⟨2, witness_of_certificate certificate_6633⟩
  · subst n
    exact ⟨5, witness_of_certificate certificate_6635⟩
  · subst n
    exact ⟨2, witness_of_certificate certificate_6637⟩
  · subst n
    exact ⟨16, witness_of_certificate certificate_6639⟩
  · subst n
    exact ⟨2, witness_of_certificate certificate_6641⟩
  · subst n
    exact ⟨4, witness_of_certificate certificate_6643⟩
  · subst n
    exact ⟨2, witness_of_certificate certificate_6645⟩
  · subst n
    exact ⟨5, witness_of_certificate certificate_6647⟩
  · subst n
    exact ⟨2, witness_of_certificate certificate_6649⟩
  · subst n
    exact ⟨10, witness_of_certificate certificate_6651⟩
  · subst n
    exact ⟨2, witness_of_certificate certificate_6653⟩
  · subst n
    exact ⟨35, witness_of_certificate certificate_6655⟩
  · subst n
    exact ⟨2, witness_of_certificate certificate_6657⟩
  · subst n
    exact ⟨4, witness_of_certificate certificate_6659⟩
  · subst n
    exact ⟨2, witness_of_certificate certificate_6661⟩
  · subst n
    exact ⟨7, witness_of_certificate certificate_6663⟩
  · subst n
    exact ⟨2, witness_of_certificate certificate_6665⟩
  · subst n
    exact ⟨5, witness_of_certificate certificate_6667⟩
  · subst n
    exact ⟨2, witness_of_certificate certificate_6669⟩
  · subst n
    exact ⟨7, witness_of_certificate certificate_6671⟩
  · subst n
    exact ⟨2, witness_of_certificate certificate_6673⟩
  · subst n
    exact ⟨4, witness_of_certificate certificate_6675⟩
  · subst n
    exact ⟨2, witness_of_certificate certificate_6677⟩
  · subst n
    exact ⟨5, witness_of_certificate certificate_6679⟩
  · subst n
    exact ⟨2, witness_of_certificate certificate_6681⟩
  · subst n
    exact ⟨12, witness_of_certificate certificate_6683⟩
  · subst n
    exact ⟨2, witness_of_certificate certificate_6685⟩
  · subst n
    exact ⟨12, witness_of_certificate certificate_6687⟩
  · subst n
    exact ⟨2, witness_of_certificate certificate_6689⟩
  · subst n
    exact ⟨4, witness_of_certificate certificate_6691⟩
  · subst n
    exact ⟨2, witness_of_certificate certificate_6693⟩
  · subst n
    exact ⟨8, witness_of_certificate certificate_6695⟩
  · subst n
    exact ⟨2, witness_of_certificate certificate_6697⟩
  · subst n
    exact ⟨5, witness_of_certificate certificate_6699⟩

end Collatz.Research.CoefficientDescent.Batch100
