import Collatz.Research.CoefficientDescent.Basic

namespace Collatz.Research.CoefficientDescent.Batch085

open FirstDescentClass

set_option maxRecDepth 20000
set_option maxHeartbeats 0

/-- Checked base and every prefix for input 5629. -/
theorem certificate_5629 : classCertificateB 2 5629 = true := by
  decide

/-- The same exact first-descent time holds on an infinite dyadic ray. -/
theorem ray_5629 (m : Nat) : stoppingTime (2 ^ 2 * m + 5629) 2 :=
  stoppingTime_of_classCertificate certificate_5629 m

/-- Checked base and every prefix for input 5631. -/
theorem certificate_5631 : classCertificateB 15 5631 = true := by
  decide

/-- The same exact first-descent time holds on an infinite dyadic ray. -/
theorem ray_5631 (m : Nat) : stoppingTime (2 ^ 15 * m + 5631) 15 :=
  stoppingTime_of_classCertificate certificate_5631 m

/-- Checked base and every prefix for input 5633. -/
theorem certificate_5633 : classCertificateB 2 5633 = true := by
  decide

/-- The same exact first-descent time holds on an infinite dyadic ray. -/
theorem ray_5633 (m : Nat) : stoppingTime (2 ^ 2 * m + 5633) 2 :=
  stoppingTime_of_classCertificate certificate_5633 m

/-- Checked base and every prefix for input 5635. -/
theorem certificate_5635 : classCertificateB 4 5635 = true := by
  decide

/-- The same exact first-descent time holds on an infinite dyadic ray. -/
theorem ray_5635 (m : Nat) : stoppingTime (2 ^ 4 * m + 5635) 4 :=
  stoppingTime_of_classCertificate certificate_5635 m

/-- Checked base and every prefix for input 5637. -/
theorem certificate_5637 : classCertificateB 2 5637 = true := by
  decide

/-- The same exact first-descent time holds on an infinite dyadic ray. -/
theorem ray_5637 (m : Nat) : stoppingTime (2 ^ 2 * m + 5637) 2 :=
  stoppingTime_of_classCertificate certificate_5637 m

/-- Checked base and every prefix for input 5639. -/
theorem certificate_5639 : classCertificateB 7 5639 = true := by
  decide

/-- The same exact first-descent time holds on an infinite dyadic ray. -/
theorem ray_5639 (m : Nat) : stoppingTime (2 ^ 7 * m + 5639) 7 :=
  stoppingTime_of_classCertificate certificate_5639 m

/-- Checked base and every prefix for input 5641. -/
theorem certificate_5641 : classCertificateB 2 5641 = true := by
  decide

/-- The same exact first-descent time holds on an infinite dyadic ray. -/
theorem ray_5641 (m : Nat) : stoppingTime (2 ^ 2 * m + 5641) 2 :=
  stoppingTime_of_classCertificate certificate_5641 m

/-- Checked base and every prefix for input 5643. -/
theorem certificate_5643 : classCertificateB 5 5643 = true := by
  decide

/-- The same exact first-descent time holds on an infinite dyadic ray. -/
theorem ray_5643 (m : Nat) : stoppingTime (2 ^ 5 * m + 5643) 5 :=
  stoppingTime_of_classCertificate certificate_5643 m

/-- Checked base and every prefix for input 5645. -/
theorem certificate_5645 : classCertificateB 2 5645 = true := by
  decide

/-- The same exact first-descent time holds on an infinite dyadic ray. -/
theorem ray_5645 (m : Nat) : stoppingTime (2 ^ 2 * m + 5645) 2 :=
  stoppingTime_of_classCertificate certificate_5645 m

/-- Checked base and every prefix for input 5647. -/
theorem certificate_5647 : classCertificateB 7 5647 = true := by
  decide

/-- The same exact first-descent time holds on an infinite dyadic ray. -/
theorem ray_5647 (m : Nat) : stoppingTime (2 ^ 7 * m + 5647) 7 :=
  stoppingTime_of_classCertificate certificate_5647 m

/-- Checked base and every prefix for input 5649. -/
theorem certificate_5649 : classCertificateB 2 5649 = true := by
  decide

/-- The same exact first-descent time holds on an infinite dyadic ray. -/
theorem ray_5649 (m : Nat) : stoppingTime (2 ^ 2 * m + 5649) 2 :=
  stoppingTime_of_classCertificate certificate_5649 m

/-- Checked base and every prefix for input 5651. -/
theorem certificate_5651 : classCertificateB 4 5651 = true := by
  decide

/-- The same exact first-descent time holds on an infinite dyadic ray. -/
theorem ray_5651 (m : Nat) : stoppingTime (2 ^ 4 * m + 5651) 4 :=
  stoppingTime_of_classCertificate certificate_5651 m

/-- Checked base and every prefix for input 5653. -/
theorem certificate_5653 : classCertificateB 2 5653 = true := by
  decide

/-- The same exact first-descent time holds on an infinite dyadic ray. -/
theorem ray_5653 (m : Nat) : stoppingTime (2 ^ 2 * m + 5653) 2 :=
  stoppingTime_of_classCertificate certificate_5653 m

/-- Checked base and every prefix for input 5655. -/
theorem certificate_5655 : classCertificateB 5 5655 = true := by
  decide

/-- The same exact first-descent time holds on an infinite dyadic ray. -/
theorem ray_5655 (m : Nat) : stoppingTime (2 ^ 5 * m + 5655) 5 :=
  stoppingTime_of_classCertificate certificate_5655 m

/-- Checked base and every prefix for input 5657. -/
theorem certificate_5657 : classCertificateB 2 5657 = true := by
  decide

/-- The same exact first-descent time holds on an infinite dyadic ray. -/
theorem ray_5657 (m : Nat) : stoppingTime (2 ^ 2 * m + 5657) 2 :=
  stoppingTime_of_classCertificate certificate_5657 m

/-- Checked base and every prefix for input 5659. -/
theorem certificate_5659 : classCertificateB 21 5659 = true := by
  decide

/-- The same exact first-descent time holds on an infinite dyadic ray. -/
theorem ray_5659 (m : Nat) : stoppingTime (2 ^ 21 * m + 5659) 21 :=
  stoppingTime_of_classCertificate certificate_5659 m

/-- Checked base and every prefix for input 5661. -/
theorem certificate_5661 : classCertificateB 2 5661 = true := by
  decide

/-- The same exact first-descent time holds on an infinite dyadic ray. -/
theorem ray_5661 (m : Nat) : stoppingTime (2 ^ 2 * m + 5661) 2 :=
  stoppingTime_of_classCertificate certificate_5661 m

/-- Checked base and every prefix for input 5663. -/
theorem certificate_5663 : classCertificateB 16 5663 = true := by
  decide

/-- The same exact first-descent time holds on an infinite dyadic ray. -/
theorem ray_5663 (m : Nat) : stoppingTime (2 ^ 16 * m + 5663) 16 :=
  stoppingTime_of_classCertificate certificate_5663 m

/-- Checked base and every prefix for input 5665. -/
theorem certificate_5665 : classCertificateB 2 5665 = true := by
  decide

/-- The same exact first-descent time holds on an infinite dyadic ray. -/
theorem ray_5665 (m : Nat) : stoppingTime (2 ^ 2 * m + 5665) 2 :=
  stoppingTime_of_classCertificate certificate_5665 m

/-- Checked base and every prefix for input 5667. -/
theorem certificate_5667 : classCertificateB 4 5667 = true := by
  decide

/-- The same exact first-descent time holds on an infinite dyadic ray. -/
theorem ray_5667 (m : Nat) : stoppingTime (2 ^ 4 * m + 5667) 4 :=
  stoppingTime_of_classCertificate certificate_5667 m

/-- Checked base and every prefix for input 5669. -/
theorem certificate_5669 : classCertificateB 2 5669 = true := by
  decide

/-- The same exact first-descent time holds on an infinite dyadic ray. -/
theorem ray_5669 (m : Nat) : stoppingTime (2 ^ 2 * m + 5669) 2 :=
  stoppingTime_of_classCertificate certificate_5669 m

/-- Checked base and every prefix for input 5671. -/
theorem certificate_5671 : classCertificateB 8 5671 = true := by
  decide

/-- The same exact first-descent time holds on an infinite dyadic ray. -/
theorem ray_5671 (m : Nat) : stoppingTime (2 ^ 8 * m + 5671) 8 :=
  stoppingTime_of_classCertificate certificate_5671 m

/-- Checked base and every prefix for input 5673. -/
theorem certificate_5673 : classCertificateB 2 5673 = true := by
  decide

/-- The same exact first-descent time holds on an infinite dyadic ray. -/
theorem ray_5673 (m : Nat) : stoppingTime (2 ^ 2 * m + 5673) 2 :=
  stoppingTime_of_classCertificate certificate_5673 m

/-- Checked base and every prefix for input 5675. -/
theorem certificate_5675 : classCertificateB 5 5675 = true := by
  decide

/-- The same exact first-descent time holds on an infinite dyadic ray. -/
theorem ray_5675 (m : Nat) : stoppingTime (2 ^ 5 * m + 5675) 5 :=
  stoppingTime_of_classCertificate certificate_5675 m

/-- Checked base and every prefix for input 5677. -/
theorem certificate_5677 : classCertificateB 2 5677 = true := by
  decide

/-- The same exact first-descent time holds on an infinite dyadic ray. -/
theorem ray_5677 (m : Nat) : stoppingTime (2 ^ 2 * m + 5677) 2 :=
  stoppingTime_of_classCertificate certificate_5677 m

/-- Checked base and every prefix for input 5679. -/
theorem certificate_5679 : classCertificateB 20 5679 = true := by
  decide

/-- The same exact first-descent time holds on an infinite dyadic ray. -/
theorem ray_5679 (m : Nat) : stoppingTime (2 ^ 20 * m + 5679) 20 :=
  stoppingTime_of_classCertificate certificate_5679 m

/-- Checked base and every prefix for input 5681. -/
theorem certificate_5681 : classCertificateB 2 5681 = true := by
  decide

/-- The same exact first-descent time holds on an infinite dyadic ray. -/
theorem ray_5681 (m : Nat) : stoppingTime (2 ^ 2 * m + 5681) 2 :=
  stoppingTime_of_classCertificate certificate_5681 m

/-- Checked base and every prefix for input 5683. -/
theorem certificate_5683 : classCertificateB 4 5683 = true := by
  decide

/-- The same exact first-descent time holds on an infinite dyadic ray. -/
theorem ray_5683 (m : Nat) : stoppingTime (2 ^ 4 * m + 5683) 4 :=
  stoppingTime_of_classCertificate certificate_5683 m

/-- Checked base and every prefix for input 5685. -/
theorem certificate_5685 : classCertificateB 2 5685 = true := by
  decide

/-- The same exact first-descent time holds on an infinite dyadic ray. -/
theorem ray_5685 (m : Nat) : stoppingTime (2 ^ 2 * m + 5685) 2 :=
  stoppingTime_of_classCertificate certificate_5685 m

/-- Checked base and every prefix for input 5687. -/
theorem certificate_5687 : classCertificateB 5 5687 = true := by
  decide

/-- The same exact first-descent time holds on an infinite dyadic ray. -/
theorem ray_5687 (m : Nat) : stoppingTime (2 ^ 5 * m + 5687) 5 :=
  stoppingTime_of_classCertificate certificate_5687 m

/-- Checked base and every prefix for input 5689. -/
theorem certificate_5689 : classCertificateB 2 5689 = true := by
  decide

/-- The same exact first-descent time holds on an infinite dyadic ray. -/
theorem ray_5689 (m : Nat) : stoppingTime (2 ^ 2 * m + 5689) 2 :=
  stoppingTime_of_classCertificate certificate_5689 m

/-- Checked base and every prefix for input 5691. -/
theorem certificate_5691 : classCertificateB 7 5691 = true := by
  decide

/-- The same exact first-descent time holds on an infinite dyadic ray. -/
theorem ray_5691 (m : Nat) : stoppingTime (2 ^ 7 * m + 5691) 7 :=
  stoppingTime_of_classCertificate certificate_5691 m

/-- Checked base and every prefix for input 5693. -/
theorem certificate_5693 : classCertificateB 2 5693 = true := by
  decide

/-- The same exact first-descent time holds on an infinite dyadic ray. -/
theorem ray_5693 (m : Nat) : stoppingTime (2 ^ 2 * m + 5693) 2 :=
  stoppingTime_of_classCertificate certificate_5693 m

/-- Exhaustive coverage of the odd inputs in this batch, with no gaps. -/
theorem coverage : CertifiedRange 5629 5695 := by
  intro n hlo hhi hodd
  have hn : n = 5629 ∨ n = 5631 ∨ n = 5633 ∨ n = 5635 ∨ n = 5637 ∨ n = 5639 ∨ n = 5641 ∨ n = 5643 ∨ n = 5645 ∨ n = 5647 ∨ n = 5649 ∨ n = 5651 ∨ n = 5653 ∨ n = 5655 ∨ n = 5657 ∨ n = 5659 ∨ n = 5661 ∨ n = 5663 ∨ n = 5665 ∨ n = 5667 ∨ n = 5669 ∨ n = 5671 ∨ n = 5673 ∨ n = 5675 ∨ n = 5677 ∨ n = 5679 ∨ n = 5681 ∨ n = 5683 ∨ n = 5685 ∨ n = 5687 ∨ n = 5689 ∨ n = 5691 ∨ n = 5693 := by omega
  rcases hn with h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h
  · subst n
    exact ⟨2, witness_of_certificate certificate_5629⟩
  · subst n
    exact ⟨15, witness_of_certificate certificate_5631⟩
  · subst n
    exact ⟨2, witness_of_certificate certificate_5633⟩
  · subst n
    exact ⟨4, witness_of_certificate certificate_5635⟩
  · subst n
    exact ⟨2, witness_of_certificate certificate_5637⟩
  · subst n
    exact ⟨7, witness_of_certificate certificate_5639⟩
  · subst n
    exact ⟨2, witness_of_certificate certificate_5641⟩
  · subst n
    exact ⟨5, witness_of_certificate certificate_5643⟩
  · subst n
    exact ⟨2, witness_of_certificate certificate_5645⟩
  · subst n
    exact ⟨7, witness_of_certificate certificate_5647⟩
  · subst n
    exact ⟨2, witness_of_certificate certificate_5649⟩
  · subst n
    exact ⟨4, witness_of_certificate certificate_5651⟩
  · subst n
    exact ⟨2, witness_of_certificate certificate_5653⟩
  · subst n
    exact ⟨5, witness_of_certificate certificate_5655⟩
  · subst n
    exact ⟨2, witness_of_certificate certificate_5657⟩
  · subst n
    exact ⟨21, witness_of_certificate certificate_5659⟩
  · subst n
    exact ⟨2, witness_of_certificate certificate_5661⟩
  · subst n
    exact ⟨16, witness_of_certificate certificate_5663⟩
  · subst n
    exact ⟨2, witness_of_certificate certificate_5665⟩
  · subst n
    exact ⟨4, witness_of_certificate certificate_5667⟩
  · subst n
    exact ⟨2, witness_of_certificate certificate_5669⟩
  · subst n
    exact ⟨8, witness_of_certificate certificate_5671⟩
  · subst n
    exact ⟨2, witness_of_certificate certificate_5673⟩
  · subst n
    exact ⟨5, witness_of_certificate certificate_5675⟩
  · subst n
    exact ⟨2, witness_of_certificate certificate_5677⟩
  · subst n
    exact ⟨20, witness_of_certificate certificate_5679⟩
  · subst n
    exact ⟨2, witness_of_certificate certificate_5681⟩
  · subst n
    exact ⟨4, witness_of_certificate certificate_5683⟩
  · subst n
    exact ⟨2, witness_of_certificate certificate_5685⟩
  · subst n
    exact ⟨5, witness_of_certificate certificate_5687⟩
  · subst n
    exact ⟨2, witness_of_certificate certificate_5689⟩
  · subst n
    exact ⟨7, witness_of_certificate certificate_5691⟩
  · subst n
    exact ⟨2, witness_of_certificate certificate_5693⟩

end Collatz.Research.CoefficientDescent.Batch085
