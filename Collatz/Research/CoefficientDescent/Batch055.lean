import Collatz.Research.CoefficientDescent.Basic

namespace Collatz.Research.CoefficientDescent.Batch055

open FirstDescentClass

set_option maxRecDepth 20000
set_option maxHeartbeats 0

/-- Checked base and every prefix for input 3619. -/
theorem certificate_3619 : classCertificateB 4 3619 = true := by
  decide

/-- The same exact first-descent time holds on an infinite dyadic ray. -/
theorem ray_3619 (m : Nat) : stoppingTime (2 ^ 4 * m + 3619) 4 :=
  stoppingTime_of_classCertificate certificate_3619 m

/-- Checked base and every prefix for input 3621. -/
theorem certificate_3621 : classCertificateB 2 3621 = true := by
  decide

/-- The same exact first-descent time holds on an infinite dyadic ray. -/
theorem ray_3621 (m : Nat) : stoppingTime (2 ^ 2 * m + 3621) 2 :=
  stoppingTime_of_classCertificate certificate_3621 m

/-- Checked base and every prefix for input 3623. -/
theorem certificate_3623 : classCertificateB 8 3623 = true := by
  decide

/-- The same exact first-descent time holds on an infinite dyadic ray. -/
theorem ray_3623 (m : Nat) : stoppingTime (2 ^ 8 * m + 3623) 8 :=
  stoppingTime_of_classCertificate certificate_3623 m

/-- Checked base and every prefix for input 3625. -/
theorem certificate_3625 : classCertificateB 2 3625 = true := by
  decide

/-- The same exact first-descent time holds on an infinite dyadic ray. -/
theorem ray_3625 (m : Nat) : stoppingTime (2 ^ 2 * m + 3625) 2 :=
  stoppingTime_of_classCertificate certificate_3625 m

/-- Checked base and every prefix for input 3627. -/
theorem certificate_3627 : classCertificateB 5 3627 = true := by
  decide

/-- The same exact first-descent time holds on an infinite dyadic ray. -/
theorem ray_3627 (m : Nat) : stoppingTime (2 ^ 5 * m + 3627) 5 :=
  stoppingTime_of_classCertificate certificate_3627 m

/-- Checked base and every prefix for input 3629. -/
theorem certificate_3629 : classCertificateB 2 3629 = true := by
  decide

/-- The same exact first-descent time holds on an infinite dyadic ray. -/
theorem ray_3629 (m : Nat) : stoppingTime (2 ^ 2 * m + 3629) 2 :=
  stoppingTime_of_classCertificate certificate_3629 m

/-- Checked base and every prefix for input 3631. -/
theorem certificate_3631 : classCertificateB 37 3631 = true := by
  decide

/-- The same exact first-descent time holds on an infinite dyadic ray. -/
theorem ray_3631 (m : Nat) : stoppingTime (2 ^ 37 * m + 3631) 37 :=
  stoppingTime_of_classCertificate certificate_3631 m

/-- Checked base and every prefix for input 3633. -/
theorem certificate_3633 : classCertificateB 2 3633 = true := by
  decide

/-- The same exact first-descent time holds on an infinite dyadic ray. -/
theorem ray_3633 (m : Nat) : stoppingTime (2 ^ 2 * m + 3633) 2 :=
  stoppingTime_of_classCertificate certificate_3633 m

/-- Checked base and every prefix for input 3635. -/
theorem certificate_3635 : classCertificateB 4 3635 = true := by
  decide

/-- The same exact first-descent time holds on an infinite dyadic ray. -/
theorem ray_3635 (m : Nat) : stoppingTime (2 ^ 4 * m + 3635) 4 :=
  stoppingTime_of_classCertificate certificate_3635 m

/-- Checked base and every prefix for input 3637. -/
theorem certificate_3637 : classCertificateB 2 3637 = true := by
  decide

/-- The same exact first-descent time holds on an infinite dyadic ray. -/
theorem ray_3637 (m : Nat) : stoppingTime (2 ^ 2 * m + 3637) 2 :=
  stoppingTime_of_classCertificate certificate_3637 m

/-- Checked base and every prefix for input 3639. -/
theorem certificate_3639 : classCertificateB 5 3639 = true := by
  decide

/-- The same exact first-descent time holds on an infinite dyadic ray. -/
theorem ray_3639 (m : Nat) : stoppingTime (2 ^ 5 * m + 3639) 5 :=
  stoppingTime_of_classCertificate certificate_3639 m

/-- Checked base and every prefix for input 3641. -/
theorem certificate_3641 : classCertificateB 2 3641 = true := by
  decide

/-- The same exact first-descent time holds on an infinite dyadic ray. -/
theorem ray_3641 (m : Nat) : stoppingTime (2 ^ 2 * m + 3641) 2 :=
  stoppingTime_of_classCertificate certificate_3641 m

/-- Checked base and every prefix for input 3643. -/
theorem certificate_3643 : classCertificateB 7 3643 = true := by
  decide

/-- The same exact first-descent time holds on an infinite dyadic ray. -/
theorem ray_3643 (m : Nat) : stoppingTime (2 ^ 7 * m + 3643) 7 :=
  stoppingTime_of_classCertificate certificate_3643 m

/-- Checked base and every prefix for input 3645. -/
theorem certificate_3645 : classCertificateB 2 3645 = true := by
  decide

/-- The same exact first-descent time holds on an infinite dyadic ray. -/
theorem ray_3645 (m : Nat) : stoppingTime (2 ^ 2 * m + 3645) 2 :=
  stoppingTime_of_classCertificate certificate_3645 m

/-- Checked base and every prefix for input 3647. -/
theorem certificate_3647 : classCertificateB 10 3647 = true := by
  decide

/-- The same exact first-descent time holds on an infinite dyadic ray. -/
theorem ray_3647 (m : Nat) : stoppingTime (2 ^ 10 * m + 3647) 10 :=
  stoppingTime_of_classCertificate certificate_3647 m

/-- Checked base and every prefix for input 3649. -/
theorem certificate_3649 : classCertificateB 2 3649 = true := by
  decide

/-- The same exact first-descent time holds on an infinite dyadic ray. -/
theorem ray_3649 (m : Nat) : stoppingTime (2 ^ 2 * m + 3649) 2 :=
  stoppingTime_of_classCertificate certificate_3649 m

/-- Checked base and every prefix for input 3651. -/
theorem certificate_3651 : classCertificateB 4 3651 = true := by
  decide

/-- The same exact first-descent time holds on an infinite dyadic ray. -/
theorem ray_3651 (m : Nat) : stoppingTime (2 ^ 4 * m + 3651) 4 :=
  stoppingTime_of_classCertificate certificate_3651 m

/-- Checked base and every prefix for input 3653. -/
theorem certificate_3653 : classCertificateB 2 3653 = true := by
  decide

/-- The same exact first-descent time holds on an infinite dyadic ray. -/
theorem ray_3653 (m : Nat) : stoppingTime (2 ^ 2 * m + 3653) 2 :=
  stoppingTime_of_classCertificate certificate_3653 m

/-- Checked base and every prefix for input 3655. -/
theorem certificate_3655 : classCertificateB 10 3655 = true := by
  decide

/-- The same exact first-descent time holds on an infinite dyadic ray. -/
theorem ray_3655 (m : Nat) : stoppingTime (2 ^ 10 * m + 3655) 10 :=
  stoppingTime_of_classCertificate certificate_3655 m

/-- Checked base and every prefix for input 3657. -/
theorem certificate_3657 : classCertificateB 2 3657 = true := by
  decide

/-- The same exact first-descent time holds on an infinite dyadic ray. -/
theorem ray_3657 (m : Nat) : stoppingTime (2 ^ 2 * m + 3657) 2 :=
  stoppingTime_of_classCertificate certificate_3657 m

/-- Checked base and every prefix for input 3659. -/
theorem certificate_3659 : classCertificateB 5 3659 = true := by
  decide

/-- The same exact first-descent time holds on an infinite dyadic ray. -/
theorem ray_3659 (m : Nat) : stoppingTime (2 ^ 5 * m + 3659) 5 :=
  stoppingTime_of_classCertificate certificate_3659 m

/-- Checked base and every prefix for input 3661. -/
theorem certificate_3661 : classCertificateB 2 3661 = true := by
  decide

/-- The same exact first-descent time holds on an infinite dyadic ray. -/
theorem ray_3661 (m : Nat) : stoppingTime (2 ^ 2 * m + 3661) 2 :=
  stoppingTime_of_classCertificate certificate_3661 m

/-- Checked base and every prefix for input 3663. -/
theorem certificate_3663 : classCertificateB 8 3663 = true := by
  decide

/-- The same exact first-descent time holds on an infinite dyadic ray. -/
theorem ray_3663 (m : Nat) : stoppingTime (2 ^ 8 * m + 3663) 8 :=
  stoppingTime_of_classCertificate certificate_3663 m

/-- Checked base and every prefix for input 3665. -/
theorem certificate_3665 : classCertificateB 2 3665 = true := by
  decide

/-- The same exact first-descent time holds on an infinite dyadic ray. -/
theorem ray_3665 (m : Nat) : stoppingTime (2 ^ 2 * m + 3665) 2 :=
  stoppingTime_of_classCertificate certificate_3665 m

/-- Checked base and every prefix for input 3667. -/
theorem certificate_3667 : classCertificateB 4 3667 = true := by
  decide

/-- The same exact first-descent time holds on an infinite dyadic ray. -/
theorem ray_3667 (m : Nat) : stoppingTime (2 ^ 4 * m + 3667) 4 :=
  stoppingTime_of_classCertificate certificate_3667 m

/-- Checked base and every prefix for input 3669. -/
theorem certificate_3669 : classCertificateB 2 3669 = true := by
  decide

/-- The same exact first-descent time holds on an infinite dyadic ray. -/
theorem ray_3669 (m : Nat) : stoppingTime (2 ^ 2 * m + 3669) 2 :=
  stoppingTime_of_classCertificate certificate_3669 m

/-- Checked base and every prefix for input 3671. -/
theorem certificate_3671 : classCertificateB 5 3671 = true := by
  decide

/-- The same exact first-descent time holds on an infinite dyadic ray. -/
theorem ray_3671 (m : Nat) : stoppingTime (2 ^ 5 * m + 3671) 5 :=
  stoppingTime_of_classCertificate certificate_3671 m

/-- Checked base and every prefix for input 3673. -/
theorem certificate_3673 : classCertificateB 2 3673 = true := by
  decide

/-- The same exact first-descent time holds on an infinite dyadic ray. -/
theorem ray_3673 (m : Nat) : stoppingTime (2 ^ 2 * m + 3673) 2 :=
  stoppingTime_of_classCertificate certificate_3673 m

/-- Checked base and every prefix for input 3675. -/
theorem certificate_3675 : classCertificateB 12 3675 = true := by
  decide

/-- The same exact first-descent time holds on an infinite dyadic ray. -/
theorem ray_3675 (m : Nat) : stoppingTime (2 ^ 12 * m + 3675) 12 :=
  stoppingTime_of_classCertificate certificate_3675 m

/-- Checked base and every prefix for input 3677. -/
theorem certificate_3677 : classCertificateB 2 3677 = true := by
  decide

/-- The same exact first-descent time holds on an infinite dyadic ray. -/
theorem ray_3677 (m : Nat) : stoppingTime (2 ^ 2 * m + 3677) 2 :=
  stoppingTime_of_classCertificate certificate_3677 m

/-- Checked base and every prefix for input 3679. -/
theorem certificate_3679 : classCertificateB 8 3679 = true := by
  decide

/-- The same exact first-descent time holds on an infinite dyadic ray. -/
theorem ray_3679 (m : Nat) : stoppingTime (2 ^ 8 * m + 3679) 8 :=
  stoppingTime_of_classCertificate certificate_3679 m

/-- Checked base and every prefix for input 3681. -/
theorem certificate_3681 : classCertificateB 2 3681 = true := by
  decide

/-- The same exact first-descent time holds on an infinite dyadic ray. -/
theorem ray_3681 (m : Nat) : stoppingTime (2 ^ 2 * m + 3681) 2 :=
  stoppingTime_of_classCertificate certificate_3681 m

/-- Checked base and every prefix for input 3683. -/
theorem certificate_3683 : classCertificateB 4 3683 = true := by
  decide

/-- The same exact first-descent time holds on an infinite dyadic ray. -/
theorem ray_3683 (m : Nat) : stoppingTime (2 ^ 4 * m + 3683) 4 :=
  stoppingTime_of_classCertificate certificate_3683 m

/-- Exhaustive coverage of the odd inputs in this batch, with no gaps. -/
theorem coverage : CertifiedRange 3619 3685 := by
  intro n hlo hhi hodd
  have hn : n = 3619 ∨ n = 3621 ∨ n = 3623 ∨ n = 3625 ∨ n = 3627 ∨ n = 3629 ∨ n = 3631 ∨ n = 3633 ∨ n = 3635 ∨ n = 3637 ∨ n = 3639 ∨ n = 3641 ∨ n = 3643 ∨ n = 3645 ∨ n = 3647 ∨ n = 3649 ∨ n = 3651 ∨ n = 3653 ∨ n = 3655 ∨ n = 3657 ∨ n = 3659 ∨ n = 3661 ∨ n = 3663 ∨ n = 3665 ∨ n = 3667 ∨ n = 3669 ∨ n = 3671 ∨ n = 3673 ∨ n = 3675 ∨ n = 3677 ∨ n = 3679 ∨ n = 3681 ∨ n = 3683 := by omega
  rcases hn with h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h
  · subst n
    exact ⟨4, witness_of_certificate certificate_3619⟩
  · subst n
    exact ⟨2, witness_of_certificate certificate_3621⟩
  · subst n
    exact ⟨8, witness_of_certificate certificate_3623⟩
  · subst n
    exact ⟨2, witness_of_certificate certificate_3625⟩
  · subst n
    exact ⟨5, witness_of_certificate certificate_3627⟩
  · subst n
    exact ⟨2, witness_of_certificate certificate_3629⟩
  · subst n
    exact ⟨37, witness_of_certificate certificate_3631⟩
  · subst n
    exact ⟨2, witness_of_certificate certificate_3633⟩
  · subst n
    exact ⟨4, witness_of_certificate certificate_3635⟩
  · subst n
    exact ⟨2, witness_of_certificate certificate_3637⟩
  · subst n
    exact ⟨5, witness_of_certificate certificate_3639⟩
  · subst n
    exact ⟨2, witness_of_certificate certificate_3641⟩
  · subst n
    exact ⟨7, witness_of_certificate certificate_3643⟩
  · subst n
    exact ⟨2, witness_of_certificate certificate_3645⟩
  · subst n
    exact ⟨10, witness_of_certificate certificate_3647⟩
  · subst n
    exact ⟨2, witness_of_certificate certificate_3649⟩
  · subst n
    exact ⟨4, witness_of_certificate certificate_3651⟩
  · subst n
    exact ⟨2, witness_of_certificate certificate_3653⟩
  · subst n
    exact ⟨10, witness_of_certificate certificate_3655⟩
  · subst n
    exact ⟨2, witness_of_certificate certificate_3657⟩
  · subst n
    exact ⟨5, witness_of_certificate certificate_3659⟩
  · subst n
    exact ⟨2, witness_of_certificate certificate_3661⟩
  · subst n
    exact ⟨8, witness_of_certificate certificate_3663⟩
  · subst n
    exact ⟨2, witness_of_certificate certificate_3665⟩
  · subst n
    exact ⟨4, witness_of_certificate certificate_3667⟩
  · subst n
    exact ⟨2, witness_of_certificate certificate_3669⟩
  · subst n
    exact ⟨5, witness_of_certificate certificate_3671⟩
  · subst n
    exact ⟨2, witness_of_certificate certificate_3673⟩
  · subst n
    exact ⟨12, witness_of_certificate certificate_3675⟩
  · subst n
    exact ⟨2, witness_of_certificate certificate_3677⟩
  · subst n
    exact ⟨8, witness_of_certificate certificate_3679⟩
  · subst n
    exact ⟨2, witness_of_certificate certificate_3681⟩
  · subst n
    exact ⟨4, witness_of_certificate certificate_3683⟩

end Collatz.Research.CoefficientDescent.Batch055
