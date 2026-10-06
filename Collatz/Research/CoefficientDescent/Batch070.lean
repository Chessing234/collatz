import Collatz.Research.CoefficientDescent.Basic

namespace Collatz.Research.CoefficientDescent.Batch070

open FirstDescentClass

set_option maxRecDepth 20000
set_option maxHeartbeats 0

/-- Checked base and every prefix for input 4623. -/
theorem certificate_4623 : classCertificateB 7 4623 = true := by
  decide

/-- The same exact first-descent time holds on an infinite dyadic ray. -/
theorem ray_4623 (m : Nat) : stoppingTime (2 ^ 7 * m + 4623) 7 :=
  stoppingTime_of_classCertificate certificate_4623 m

/-- Checked base and every prefix for input 4625. -/
theorem certificate_4625 : classCertificateB 2 4625 = true := by
  decide

/-- The same exact first-descent time holds on an infinite dyadic ray. -/
theorem ray_4625 (m : Nat) : stoppingTime (2 ^ 2 * m + 4625) 2 :=
  stoppingTime_of_classCertificate certificate_4625 m

/-- Checked base and every prefix for input 4627. -/
theorem certificate_4627 : classCertificateB 4 4627 = true := by
  decide

/-- The same exact first-descent time holds on an infinite dyadic ray. -/
theorem ray_4627 (m : Nat) : stoppingTime (2 ^ 4 * m + 4627) 4 :=
  stoppingTime_of_classCertificate certificate_4627 m

/-- Checked base and every prefix for input 4629. -/
theorem certificate_4629 : classCertificateB 2 4629 = true := by
  decide

/-- The same exact first-descent time holds on an infinite dyadic ray. -/
theorem ray_4629 (m : Nat) : stoppingTime (2 ^ 2 * m + 4629) 2 :=
  stoppingTime_of_classCertificate certificate_4629 m

/-- Checked base and every prefix for input 4631. -/
theorem certificate_4631 : classCertificateB 5 4631 = true := by
  decide

/-- The same exact first-descent time holds on an infinite dyadic ray. -/
theorem ray_4631 (m : Nat) : stoppingTime (2 ^ 5 * m + 4631) 5 :=
  stoppingTime_of_classCertificate certificate_4631 m

/-- Checked base and every prefix for input 4633. -/
theorem certificate_4633 : classCertificateB 2 4633 = true := by
  decide

/-- The same exact first-descent time holds on an infinite dyadic ray. -/
theorem ray_4633 (m : Nat) : stoppingTime (2 ^ 2 * m + 4633) 2 :=
  stoppingTime_of_classCertificate certificate_4633 m

/-- Checked base and every prefix for input 4635. -/
theorem certificate_4635 : classCertificateB 16 4635 = true := by
  decide

/-- The same exact first-descent time holds on an infinite dyadic ray. -/
theorem ray_4635 (m : Nat) : stoppingTime (2 ^ 16 * m + 4635) 16 :=
  stoppingTime_of_classCertificate certificate_4635 m

/-- Checked base and every prefix for input 4637. -/
theorem certificate_4637 : classCertificateB 2 4637 = true := by
  decide

/-- The same exact first-descent time holds on an infinite dyadic ray. -/
theorem ray_4637 (m : Nat) : stoppingTime (2 ^ 2 * m + 4637) 2 :=
  stoppingTime_of_classCertificate certificate_4637 m

/-- Checked base and every prefix for input 4639. -/
theorem certificate_4639 : classCertificateB 24 4639 = true := by
  decide

/-- The same exact first-descent time holds on an infinite dyadic ray. -/
theorem ray_4639 (m : Nat) : stoppingTime (2 ^ 24 * m + 4639) 24 :=
  stoppingTime_of_classCertificate certificate_4639 m

/-- Checked base and every prefix for input 4641. -/
theorem certificate_4641 : classCertificateB 2 4641 = true := by
  decide

/-- The same exact first-descent time holds on an infinite dyadic ray. -/
theorem ray_4641 (m : Nat) : stoppingTime (2 ^ 2 * m + 4641) 2 :=
  stoppingTime_of_classCertificate certificate_4641 m

/-- Checked base and every prefix for input 4643. -/
theorem certificate_4643 : classCertificateB 4 4643 = true := by
  decide

/-- The same exact first-descent time holds on an infinite dyadic ray. -/
theorem ray_4643 (m : Nat) : stoppingTime (2 ^ 4 * m + 4643) 4 :=
  stoppingTime_of_classCertificate certificate_4643 m

/-- Checked base and every prefix for input 4645. -/
theorem certificate_4645 : classCertificateB 2 4645 = true := by
  decide

/-- The same exact first-descent time holds on an infinite dyadic ray. -/
theorem ray_4645 (m : Nat) : stoppingTime (2 ^ 2 * m + 4645) 2 :=
  stoppingTime_of_classCertificate certificate_4645 m

/-- Checked base and every prefix for input 4647. -/
theorem certificate_4647 : classCertificateB 8 4647 = true := by
  decide

/-- The same exact first-descent time holds on an infinite dyadic ray. -/
theorem ray_4647 (m : Nat) : stoppingTime (2 ^ 8 * m + 4647) 8 :=
  stoppingTime_of_classCertificate certificate_4647 m

/-- Checked base and every prefix for input 4649. -/
theorem certificate_4649 : classCertificateB 2 4649 = true := by
  decide

/-- The same exact first-descent time holds on an infinite dyadic ray. -/
theorem ray_4649 (m : Nat) : stoppingTime (2 ^ 2 * m + 4649) 2 :=
  stoppingTime_of_classCertificate certificate_4649 m

/-- Checked base and every prefix for input 4651. -/
theorem certificate_4651 : classCertificateB 5 4651 = true := by
  decide

/-- The same exact first-descent time holds on an infinite dyadic ray. -/
theorem ray_4651 (m : Nat) : stoppingTime (2 ^ 5 * m + 4651) 5 :=
  stoppingTime_of_classCertificate certificate_4651 m

/-- Checked base and every prefix for input 4653. -/
theorem certificate_4653 : classCertificateB 2 4653 = true := by
  decide

/-- The same exact first-descent time holds on an infinite dyadic ray. -/
theorem ray_4653 (m : Nat) : stoppingTime (2 ^ 2 * m + 4653) 2 :=
  stoppingTime_of_classCertificate certificate_4653 m

/-- Checked base and every prefix for input 4655. -/
theorem certificate_4655 : classCertificateB 15 4655 = true := by
  decide

/-- The same exact first-descent time holds on an infinite dyadic ray. -/
theorem ray_4655 (m : Nat) : stoppingTime (2 ^ 15 * m + 4655) 15 :=
  stoppingTime_of_classCertificate certificate_4655 m

/-- Checked base and every prefix for input 4657. -/
theorem certificate_4657 : classCertificateB 2 4657 = true := by
  decide

/-- The same exact first-descent time holds on an infinite dyadic ray. -/
theorem ray_4657 (m : Nat) : stoppingTime (2 ^ 2 * m + 4657) 2 :=
  stoppingTime_of_classCertificate certificate_4657 m

/-- Checked base and every prefix for input 4659. -/
theorem certificate_4659 : classCertificateB 4 4659 = true := by
  decide

/-- The same exact first-descent time holds on an infinite dyadic ray. -/
theorem ray_4659 (m : Nat) : stoppingTime (2 ^ 4 * m + 4659) 4 :=
  stoppingTime_of_classCertificate certificate_4659 m

/-- Checked base and every prefix for input 4661. -/
theorem certificate_4661 : classCertificateB 2 4661 = true := by
  decide

/-- The same exact first-descent time holds on an infinite dyadic ray. -/
theorem ray_4661 (m : Nat) : stoppingTime (2 ^ 2 * m + 4661) 2 :=
  stoppingTime_of_classCertificate certificate_4661 m

/-- Checked base and every prefix for input 4663. -/
theorem certificate_4663 : classCertificateB 5 4663 = true := by
  decide

/-- The same exact first-descent time holds on an infinite dyadic ray. -/
theorem ray_4663 (m : Nat) : stoppingTime (2 ^ 5 * m + 4663) 5 :=
  stoppingTime_of_classCertificate certificate_4663 m

/-- Checked base and every prefix for input 4665. -/
theorem certificate_4665 : classCertificateB 2 4665 = true := by
  decide

/-- The same exact first-descent time holds on an infinite dyadic ray. -/
theorem ray_4665 (m : Nat) : stoppingTime (2 ^ 2 * m + 4665) 2 :=
  stoppingTime_of_classCertificate certificate_4665 m

/-- Checked base and every prefix for input 4667. -/
theorem certificate_4667 : classCertificateB 7 4667 = true := by
  decide

/-- The same exact first-descent time holds on an infinite dyadic ray. -/
theorem ray_4667 (m : Nat) : stoppingTime (2 ^ 7 * m + 4667) 7 :=
  stoppingTime_of_classCertificate certificate_4667 m

/-- Checked base and every prefix for input 4669. -/
theorem certificate_4669 : classCertificateB 2 4669 = true := by
  decide

/-- The same exact first-descent time holds on an infinite dyadic ray. -/
theorem ray_4669 (m : Nat) : stoppingTime (2 ^ 2 * m + 4669) 2 :=
  stoppingTime_of_classCertificate certificate_4669 m

/-- Checked base and every prefix for input 4671. -/
theorem certificate_4671 : classCertificateB 10 4671 = true := by
  decide

/-- The same exact first-descent time holds on an infinite dyadic ray. -/
theorem ray_4671 (m : Nat) : stoppingTime (2 ^ 10 * m + 4671) 10 :=
  stoppingTime_of_classCertificate certificate_4671 m

/-- Checked base and every prefix for input 4673. -/
theorem certificate_4673 : classCertificateB 2 4673 = true := by
  decide

/-- The same exact first-descent time holds on an infinite dyadic ray. -/
theorem ray_4673 (m : Nat) : stoppingTime (2 ^ 2 * m + 4673) 2 :=
  stoppingTime_of_classCertificate certificate_4673 m

/-- Checked base and every prefix for input 4675. -/
theorem certificate_4675 : classCertificateB 4 4675 = true := by
  decide

/-- The same exact first-descent time holds on an infinite dyadic ray. -/
theorem ray_4675 (m : Nat) : stoppingTime (2 ^ 4 * m + 4675) 4 :=
  stoppingTime_of_classCertificate certificate_4675 m

/-- Checked base and every prefix for input 4677. -/
theorem certificate_4677 : classCertificateB 2 4677 = true := by
  decide

/-- The same exact first-descent time holds on an infinite dyadic ray. -/
theorem ray_4677 (m : Nat) : stoppingTime (2 ^ 2 * m + 4677) 2 :=
  stoppingTime_of_classCertificate certificate_4677 m

/-- Checked base and every prefix for input 4679. -/
theorem certificate_4679 : classCertificateB 10 4679 = true := by
  decide

/-- The same exact first-descent time holds on an infinite dyadic ray. -/
theorem ray_4679 (m : Nat) : stoppingTime (2 ^ 10 * m + 4679) 10 :=
  stoppingTime_of_classCertificate certificate_4679 m

/-- Checked base and every prefix for input 4681. -/
theorem certificate_4681 : classCertificateB 2 4681 = true := by
  decide

/-- The same exact first-descent time holds on an infinite dyadic ray. -/
theorem ray_4681 (m : Nat) : stoppingTime (2 ^ 2 * m + 4681) 2 :=
  stoppingTime_of_classCertificate certificate_4681 m

/-- Checked base and every prefix for input 4683. -/
theorem certificate_4683 : classCertificateB 5 4683 = true := by
  decide

/-- The same exact first-descent time holds on an infinite dyadic ray. -/
theorem ray_4683 (m : Nat) : stoppingTime (2 ^ 5 * m + 4683) 5 :=
  stoppingTime_of_classCertificate certificate_4683 m

/-- Checked base and every prefix for input 4685. -/
theorem certificate_4685 : classCertificateB 2 4685 = true := by
  decide

/-- The same exact first-descent time holds on an infinite dyadic ray. -/
theorem ray_4685 (m : Nat) : stoppingTime (2 ^ 2 * m + 4685) 2 :=
  stoppingTime_of_classCertificate certificate_4685 m

/-- Checked base and every prefix for input 4687. -/
theorem certificate_4687 : classCertificateB 8 4687 = true := by
  decide

/-- The same exact first-descent time holds on an infinite dyadic ray. -/
theorem ray_4687 (m : Nat) : stoppingTime (2 ^ 8 * m + 4687) 8 :=
  stoppingTime_of_classCertificate certificate_4687 m

/-- Checked base and every prefix for input 4689. -/
theorem certificate_4689 : classCertificateB 2 4689 = true := by
  decide

/-- The same exact first-descent time holds on an infinite dyadic ray. -/
theorem ray_4689 (m : Nat) : stoppingTime (2 ^ 2 * m + 4689) 2 :=
  stoppingTime_of_classCertificate certificate_4689 m

/-- Exhaustive coverage of the odd inputs in this batch, with no gaps. -/
theorem coverage : CertifiedRange 4623 4691 := by
  intro n hlo hhi hodd
  have hn : n = 4623 ∨ n = 4625 ∨ n = 4627 ∨ n = 4629 ∨ n = 4631 ∨ n = 4633 ∨ n = 4635 ∨ n = 4637 ∨ n = 4639 ∨ n = 4641 ∨ n = 4643 ∨ n = 4645 ∨ n = 4647 ∨ n = 4649 ∨ n = 4651 ∨ n = 4653 ∨ n = 4655 ∨ n = 4657 ∨ n = 4659 ∨ n = 4661 ∨ n = 4663 ∨ n = 4665 ∨ n = 4667 ∨ n = 4669 ∨ n = 4671 ∨ n = 4673 ∨ n = 4675 ∨ n = 4677 ∨ n = 4679 ∨ n = 4681 ∨ n = 4683 ∨ n = 4685 ∨ n = 4687 ∨ n = 4689 := by omega
  rcases hn with h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h
  · subst n
    exact ⟨7, witness_of_certificate certificate_4623⟩
  · subst n
    exact ⟨2, witness_of_certificate certificate_4625⟩
  · subst n
    exact ⟨4, witness_of_certificate certificate_4627⟩
  · subst n
    exact ⟨2, witness_of_certificate certificate_4629⟩
  · subst n
    exact ⟨5, witness_of_certificate certificate_4631⟩
  · subst n
    exact ⟨2, witness_of_certificate certificate_4633⟩
  · subst n
    exact ⟨16, witness_of_certificate certificate_4635⟩
  · subst n
    exact ⟨2, witness_of_certificate certificate_4637⟩
  · subst n
    exact ⟨24, witness_of_certificate certificate_4639⟩
  · subst n
    exact ⟨2, witness_of_certificate certificate_4641⟩
  · subst n
    exact ⟨4, witness_of_certificate certificate_4643⟩
  · subst n
    exact ⟨2, witness_of_certificate certificate_4645⟩
  · subst n
    exact ⟨8, witness_of_certificate certificate_4647⟩
  · subst n
    exact ⟨2, witness_of_certificate certificate_4649⟩
  · subst n
    exact ⟨5, witness_of_certificate certificate_4651⟩
  · subst n
    exact ⟨2, witness_of_certificate certificate_4653⟩
  · subst n
    exact ⟨15, witness_of_certificate certificate_4655⟩
  · subst n
    exact ⟨2, witness_of_certificate certificate_4657⟩
  · subst n
    exact ⟨4, witness_of_certificate certificate_4659⟩
  · subst n
    exact ⟨2, witness_of_certificate certificate_4661⟩
  · subst n
    exact ⟨5, witness_of_certificate certificate_4663⟩
  · subst n
    exact ⟨2, witness_of_certificate certificate_4665⟩
  · subst n
    exact ⟨7, witness_of_certificate certificate_4667⟩
  · subst n
    exact ⟨2, witness_of_certificate certificate_4669⟩
  · subst n
    exact ⟨10, witness_of_certificate certificate_4671⟩
  · subst n
    exact ⟨2, witness_of_certificate certificate_4673⟩
  · subst n
    exact ⟨4, witness_of_certificate certificate_4675⟩
  · subst n
    exact ⟨2, witness_of_certificate certificate_4677⟩
  · subst n
    exact ⟨10, witness_of_certificate certificate_4679⟩
  · subst n
    exact ⟨2, witness_of_certificate certificate_4681⟩
  · subst n
    exact ⟨5, witness_of_certificate certificate_4683⟩
  · subst n
    exact ⟨2, witness_of_certificate certificate_4685⟩
  · subst n
    exact ⟨8, witness_of_certificate certificate_4687⟩
  · subst n
    exact ⟨2, witness_of_certificate certificate_4689⟩

end Collatz.Research.CoefficientDescent.Batch070
