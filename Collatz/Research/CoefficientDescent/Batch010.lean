import Collatz.Research.CoefficientDescent.Basic

namespace Collatz.Research.CoefficientDescent.Batch010

open FirstDescentClass

set_option maxRecDepth 20000
set_option maxHeartbeats 0

/-- Checked base and every prefix for input 605. -/
theorem certificate_605 : classCertificateB 2 605 = true := by
  decide

/-- The same exact first-descent time holds on an infinite dyadic ray. -/
theorem ray_605 (m : Nat) : stoppingTime (2 ^ 2 * m + 605) 2 :=
  stoppingTime_of_classCertificate certificate_605 m

/-- Checked base and every prefix for input 607. -/
theorem certificate_607 : classCertificateB 8 607 = true := by
  decide

/-- The same exact first-descent time holds on an infinite dyadic ray. -/
theorem ray_607 (m : Nat) : stoppingTime (2 ^ 8 * m + 607) 8 :=
  stoppingTime_of_classCertificate certificate_607 m

/-- Checked base and every prefix for input 609. -/
theorem certificate_609 : classCertificateB 2 609 = true := by
  decide

/-- The same exact first-descent time holds on an infinite dyadic ray. -/
theorem ray_609 (m : Nat) : stoppingTime (2 ^ 2 * m + 609) 2 :=
  stoppingTime_of_classCertificate certificate_609 m

/-- Checked base and every prefix for input 611. -/
theorem certificate_611 : classCertificateB 4 611 = true := by
  decide

/-- The same exact first-descent time holds on an infinite dyadic ray. -/
theorem ray_611 (m : Nat) : stoppingTime (2 ^ 4 * m + 611) 4 :=
  stoppingTime_of_classCertificate certificate_611 m

/-- Checked base and every prefix for input 613. -/
theorem certificate_613 : classCertificateB 2 613 = true := by
  decide

/-- The same exact first-descent time holds on an infinite dyadic ray. -/
theorem ray_613 (m : Nat) : stoppingTime (2 ^ 2 * m + 613) 2 :=
  stoppingTime_of_classCertificate certificate_613 m

/-- Checked base and every prefix for input 615. -/
theorem certificate_615 : classCertificateB 12 615 = true := by
  decide

/-- The same exact first-descent time holds on an infinite dyadic ray. -/
theorem ray_615 (m : Nat) : stoppingTime (2 ^ 12 * m + 615) 12 :=
  stoppingTime_of_classCertificate certificate_615 m

/-- Checked base and every prefix for input 617. -/
theorem certificate_617 : classCertificateB 2 617 = true := by
  decide

/-- The same exact first-descent time holds on an infinite dyadic ray. -/
theorem ray_617 (m : Nat) : stoppingTime (2 ^ 2 * m + 617) 2 :=
  stoppingTime_of_classCertificate certificate_617 m

/-- Checked base and every prefix for input 619. -/
theorem certificate_619 : classCertificateB 5 619 = true := by
  decide

/-- The same exact first-descent time holds on an infinite dyadic ray. -/
theorem ray_619 (m : Nat) : stoppingTime (2 ^ 5 * m + 619) 5 :=
  stoppingTime_of_classCertificate certificate_619 m

/-- Checked base and every prefix for input 621. -/
theorem certificate_621 : classCertificateB 2 621 = true := by
  decide

/-- The same exact first-descent time holds on an infinite dyadic ray. -/
theorem ray_621 (m : Nat) : stoppingTime (2 ^ 2 * m + 621) 2 :=
  stoppingTime_of_classCertificate certificate_621 m

/-- Checked base and every prefix for input 623. -/
theorem certificate_623 : classCertificateB 13 623 = true := by
  decide

/-- The same exact first-descent time holds on an infinite dyadic ray. -/
theorem ray_623 (m : Nat) : stoppingTime (2 ^ 13 * m + 623) 13 :=
  stoppingTime_of_classCertificate certificate_623 m

/-- Checked base and every prefix for input 625. -/
theorem certificate_625 : classCertificateB 2 625 = true := by
  decide

/-- The same exact first-descent time holds on an infinite dyadic ray. -/
theorem ray_625 (m : Nat) : stoppingTime (2 ^ 2 * m + 625) 2 :=
  stoppingTime_of_classCertificate certificate_625 m

/-- Checked base and every prefix for input 627. -/
theorem certificate_627 : classCertificateB 4 627 = true := by
  decide

/-- The same exact first-descent time holds on an infinite dyadic ray. -/
theorem ray_627 (m : Nat) : stoppingTime (2 ^ 4 * m + 627) 4 :=
  stoppingTime_of_classCertificate certificate_627 m

/-- Checked base and every prefix for input 629. -/
theorem certificate_629 : classCertificateB 2 629 = true := by
  decide

/-- The same exact first-descent time holds on an infinite dyadic ray. -/
theorem ray_629 (m : Nat) : stoppingTime (2 ^ 2 * m + 629) 2 :=
  stoppingTime_of_classCertificate certificate_629 m

/-- Checked base and every prefix for input 631. -/
theorem certificate_631 : classCertificateB 5 631 = true := by
  decide

/-- The same exact first-descent time holds on an infinite dyadic ray. -/
theorem ray_631 (m : Nat) : stoppingTime (2 ^ 5 * m + 631) 5 :=
  stoppingTime_of_classCertificate certificate_631 m

/-- Checked base and every prefix for input 633. -/
theorem certificate_633 : classCertificateB 2 633 = true := by
  decide

/-- The same exact first-descent time holds on an infinite dyadic ray. -/
theorem ray_633 (m : Nat) : stoppingTime (2 ^ 2 * m + 633) 2 :=
  stoppingTime_of_classCertificate certificate_633 m

/-- Checked base and every prefix for input 635. -/
theorem certificate_635 : classCertificateB 8 635 = true := by
  decide

/-- The same exact first-descent time holds on an infinite dyadic ray. -/
theorem ray_635 (m : Nat) : stoppingTime (2 ^ 8 * m + 635) 8 :=
  stoppingTime_of_classCertificate certificate_635 m

/-- Checked base and every prefix for input 637. -/
theorem certificate_637 : classCertificateB 2 637 = true := by
  decide

/-- The same exact first-descent time holds on an infinite dyadic ray. -/
theorem ray_637 (m : Nat) : stoppingTime (2 ^ 2 * m + 637) 2 :=
  stoppingTime_of_classCertificate certificate_637 m

/-- Checked base and every prefix for input 639. -/
theorem certificate_639 : classCertificateB 23 639 = true := by
  decide

/-- The same exact first-descent time holds on an infinite dyadic ray. -/
theorem ray_639 (m : Nat) : stoppingTime (2 ^ 23 * m + 639) 23 :=
  stoppingTime_of_classCertificate certificate_639 m

/-- Checked base and every prefix for input 641. -/
theorem certificate_641 : classCertificateB 2 641 = true := by
  decide

/-- The same exact first-descent time holds on an infinite dyadic ray. -/
theorem ray_641 (m : Nat) : stoppingTime (2 ^ 2 * m + 641) 2 :=
  stoppingTime_of_classCertificate certificate_641 m

/-- Checked base and every prefix for input 643. -/
theorem certificate_643 : classCertificateB 4 643 = true := by
  decide

/-- The same exact first-descent time holds on an infinite dyadic ray. -/
theorem ray_643 (m : Nat) : stoppingTime (2 ^ 4 * m + 643) 4 :=
  stoppingTime_of_classCertificate certificate_643 m

/-- Checked base and every prefix for input 645. -/
theorem certificate_645 : classCertificateB 2 645 = true := by
  decide

/-- The same exact first-descent time holds on an infinite dyadic ray. -/
theorem ray_645 (m : Nat) : stoppingTime (2 ^ 2 * m + 645) 2 :=
  stoppingTime_of_classCertificate certificate_645 m

/-- Checked base and every prefix for input 647. -/
theorem certificate_647 : classCertificateB 7 647 = true := by
  decide

/-- The same exact first-descent time holds on an infinite dyadic ray. -/
theorem ray_647 (m : Nat) : stoppingTime (2 ^ 7 * m + 647) 7 :=
  stoppingTime_of_classCertificate certificate_647 m

/-- Checked base and every prefix for input 649. -/
theorem certificate_649 : classCertificateB 2 649 = true := by
  decide

/-- The same exact first-descent time holds on an infinite dyadic ray. -/
theorem ray_649 (m : Nat) : stoppingTime (2 ^ 2 * m + 649) 2 :=
  stoppingTime_of_classCertificate certificate_649 m

/-- Checked base and every prefix for input 651. -/
theorem certificate_651 : classCertificateB 5 651 = true := by
  decide

/-- The same exact first-descent time holds on an infinite dyadic ray. -/
theorem ray_651 (m : Nat) : stoppingTime (2 ^ 5 * m + 651) 5 :=
  stoppingTime_of_classCertificate certificate_651 m

/-- Checked base and every prefix for input 653. -/
theorem certificate_653 : classCertificateB 2 653 = true := by
  decide

/-- The same exact first-descent time holds on an infinite dyadic ray. -/
theorem ray_653 (m : Nat) : stoppingTime (2 ^ 2 * m + 653) 2 :=
  stoppingTime_of_classCertificate certificate_653 m

/-- Checked base and every prefix for input 655. -/
theorem certificate_655 : classCertificateB 7 655 = true := by
  decide

/-- The same exact first-descent time holds on an infinite dyadic ray. -/
theorem ray_655 (m : Nat) : stoppingTime (2 ^ 7 * m + 655) 7 :=
  stoppingTime_of_classCertificate certificate_655 m

/-- Checked base and every prefix for input 657. -/
theorem certificate_657 : classCertificateB 2 657 = true := by
  decide

/-- The same exact first-descent time holds on an infinite dyadic ray. -/
theorem ray_657 (m : Nat) : stoppingTime (2 ^ 2 * m + 657) 2 :=
  stoppingTime_of_classCertificate certificate_657 m

/-- Checked base and every prefix for input 659. -/
theorem certificate_659 : classCertificateB 4 659 = true := by
  decide

/-- The same exact first-descent time holds on an infinite dyadic ray. -/
theorem ray_659 (m : Nat) : stoppingTime (2 ^ 4 * m + 659) 4 :=
  stoppingTime_of_classCertificate certificate_659 m

/-- Checked base and every prefix for input 661. -/
theorem certificate_661 : classCertificateB 2 661 = true := by
  decide

/-- The same exact first-descent time holds on an infinite dyadic ray. -/
theorem ray_661 (m : Nat) : stoppingTime (2 ^ 2 * m + 661) 2 :=
  stoppingTime_of_classCertificate certificate_661 m

/-- Checked base and every prefix for input 663. -/
theorem certificate_663 : classCertificateB 5 663 = true := by
  decide

/-- The same exact first-descent time holds on an infinite dyadic ray. -/
theorem ray_663 (m : Nat) : stoppingTime (2 ^ 5 * m + 663) 5 :=
  stoppingTime_of_classCertificate certificate_663 m

/-- Checked base and every prefix for input 665. -/
theorem certificate_665 : classCertificateB 2 665 = true := by
  decide

/-- The same exact first-descent time holds on an infinite dyadic ray. -/
theorem ray_665 (m : Nat) : stoppingTime (2 ^ 2 * m + 665) 2 :=
  stoppingTime_of_classCertificate certificate_665 m

/-- Checked base and every prefix for input 667. -/
theorem certificate_667 : classCertificateB 24 667 = true := by
  decide

/-- The same exact first-descent time holds on an infinite dyadic ray. -/
theorem ray_667 (m : Nat) : stoppingTime (2 ^ 24 * m + 667) 24 :=
  stoppingTime_of_classCertificate certificate_667 m

/-- Checked base and every prefix for input 669. -/
theorem certificate_669 : classCertificateB 2 669 = true := by
  decide

/-- The same exact first-descent time holds on an infinite dyadic ray. -/
theorem ray_669 (m : Nat) : stoppingTime (2 ^ 2 * m + 669) 2 :=
  stoppingTime_of_classCertificate certificate_669 m

/-- Exhaustive coverage of the odd inputs in this batch, with no gaps. -/
theorem coverage : CertifiedRange 605 671 := by
  intro n hlo hhi hodd
  have hn : n = 605 ∨ n = 607 ∨ n = 609 ∨ n = 611 ∨ n = 613 ∨ n = 615 ∨ n = 617 ∨ n = 619 ∨ n = 621 ∨ n = 623 ∨ n = 625 ∨ n = 627 ∨ n = 629 ∨ n = 631 ∨ n = 633 ∨ n = 635 ∨ n = 637 ∨ n = 639 ∨ n = 641 ∨ n = 643 ∨ n = 645 ∨ n = 647 ∨ n = 649 ∨ n = 651 ∨ n = 653 ∨ n = 655 ∨ n = 657 ∨ n = 659 ∨ n = 661 ∨ n = 663 ∨ n = 665 ∨ n = 667 ∨ n = 669 := by omega
  rcases hn with h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h
  · subst n
    exact ⟨2, witness_of_certificate certificate_605⟩
  · subst n
    exact ⟨8, witness_of_certificate certificate_607⟩
  · subst n
    exact ⟨2, witness_of_certificate certificate_609⟩
  · subst n
    exact ⟨4, witness_of_certificate certificate_611⟩
  · subst n
    exact ⟨2, witness_of_certificate certificate_613⟩
  · subst n
    exact ⟨12, witness_of_certificate certificate_615⟩
  · subst n
    exact ⟨2, witness_of_certificate certificate_617⟩
  · subst n
    exact ⟨5, witness_of_certificate certificate_619⟩
  · subst n
    exact ⟨2, witness_of_certificate certificate_621⟩
  · subst n
    exact ⟨13, witness_of_certificate certificate_623⟩
  · subst n
    exact ⟨2, witness_of_certificate certificate_625⟩
  · subst n
    exact ⟨4, witness_of_certificate certificate_627⟩
  · subst n
    exact ⟨2, witness_of_certificate certificate_629⟩
  · subst n
    exact ⟨5, witness_of_certificate certificate_631⟩
  · subst n
    exact ⟨2, witness_of_certificate certificate_633⟩
  · subst n
    exact ⟨8, witness_of_certificate certificate_635⟩
  · subst n
    exact ⟨2, witness_of_certificate certificate_637⟩
  · subst n
    exact ⟨23, witness_of_certificate certificate_639⟩
  · subst n
    exact ⟨2, witness_of_certificate certificate_641⟩
  · subst n
    exact ⟨4, witness_of_certificate certificate_643⟩
  · subst n
    exact ⟨2, witness_of_certificate certificate_645⟩
  · subst n
    exact ⟨7, witness_of_certificate certificate_647⟩
  · subst n
    exact ⟨2, witness_of_certificate certificate_649⟩
  · subst n
    exact ⟨5, witness_of_certificate certificate_651⟩
  · subst n
    exact ⟨2, witness_of_certificate certificate_653⟩
  · subst n
    exact ⟨7, witness_of_certificate certificate_655⟩
  · subst n
    exact ⟨2, witness_of_certificate certificate_657⟩
  · subst n
    exact ⟨4, witness_of_certificate certificate_659⟩
  · subst n
    exact ⟨2, witness_of_certificate certificate_661⟩
  · subst n
    exact ⟨5, witness_of_certificate certificate_663⟩
  · subst n
    exact ⟨2, witness_of_certificate certificate_665⟩
  · subst n
    exact ⟨24, witness_of_certificate certificate_667⟩
  · subst n
    exact ⟨2, witness_of_certificate certificate_669⟩

end Collatz.Research.CoefficientDescent.Batch010
