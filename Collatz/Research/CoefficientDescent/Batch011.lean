import Collatz.Research.CoefficientDescent.Basic

namespace Collatz.Research.CoefficientDescent.Batch011

open FirstDescentClass

set_option maxRecDepth 20000
set_option maxHeartbeats 0

/-- Checked base and every prefix for input 671. -/
theorem certificate_671 : classCertificateB 39 671 = true := by
  decide

/-- The same exact first-descent time holds on an infinite dyadic ray. -/
theorem ray_671 (m : Nat) : stoppingTime (2 ^ 39 * m + 671) 39 :=
  stoppingTime_of_classCertificate certificate_671 m

/-- Checked base and every prefix for input 673. -/
theorem certificate_673 : classCertificateB 2 673 = true := by
  decide

/-- The same exact first-descent time holds on an infinite dyadic ray. -/
theorem ray_673 (m : Nat) : stoppingTime (2 ^ 2 * m + 673) 2 :=
  stoppingTime_of_classCertificate certificate_673 m

/-- Checked base and every prefix for input 675. -/
theorem certificate_675 : classCertificateB 4 675 = true := by
  decide

/-- The same exact first-descent time holds on an infinite dyadic ray. -/
theorem ray_675 (m : Nat) : stoppingTime (2 ^ 4 * m + 675) 4 :=
  stoppingTime_of_classCertificate certificate_675 m

/-- Checked base and every prefix for input 677. -/
theorem certificate_677 : classCertificateB 2 677 = true := by
  decide

/-- The same exact first-descent time holds on an infinite dyadic ray. -/
theorem ray_677 (m : Nat) : stoppingTime (2 ^ 2 * m + 677) 2 :=
  stoppingTime_of_classCertificate certificate_677 m

/-- Checked base and every prefix for input 679. -/
theorem certificate_679 : classCertificateB 13 679 = true := by
  decide

/-- The same exact first-descent time holds on an infinite dyadic ray. -/
theorem ray_679 (m : Nat) : stoppingTime (2 ^ 13 * m + 679) 13 :=
  stoppingTime_of_classCertificate certificate_679 m

/-- Checked base and every prefix for input 681. -/
theorem certificate_681 : classCertificateB 2 681 = true := by
  decide

/-- The same exact first-descent time holds on an infinite dyadic ray. -/
theorem ray_681 (m : Nat) : stoppingTime (2 ^ 2 * m + 681) 2 :=
  stoppingTime_of_classCertificate certificate_681 m

/-- Checked base and every prefix for input 683. -/
theorem certificate_683 : classCertificateB 5 683 = true := by
  decide

/-- The same exact first-descent time holds on an infinite dyadic ray. -/
theorem ray_683 (m : Nat) : stoppingTime (2 ^ 5 * m + 683) 5 :=
  stoppingTime_of_classCertificate certificate_683 m

/-- Checked base and every prefix for input 685. -/
theorem certificate_685 : classCertificateB 2 685 = true := by
  decide

/-- The same exact first-descent time holds on an infinite dyadic ray. -/
theorem ray_685 (m : Nat) : stoppingTime (2 ^ 2 * m + 685) 2 :=
  stoppingTime_of_classCertificate certificate_685 m

/-- Checked base and every prefix for input 687. -/
theorem certificate_687 : classCertificateB 8 687 = true := by
  decide

/-- The same exact first-descent time holds on an infinite dyadic ray. -/
theorem ray_687 (m : Nat) : stoppingTime (2 ^ 8 * m + 687) 8 :=
  stoppingTime_of_classCertificate certificate_687 m

/-- Checked base and every prefix for input 689. -/
theorem certificate_689 : classCertificateB 2 689 = true := by
  decide

/-- The same exact first-descent time holds on an infinite dyadic ray. -/
theorem ray_689 (m : Nat) : stoppingTime (2 ^ 2 * m + 689) 2 :=
  stoppingTime_of_classCertificate certificate_689 m

/-- Checked base and every prefix for input 691. -/
theorem certificate_691 : classCertificateB 4 691 = true := by
  decide

/-- The same exact first-descent time holds on an infinite dyadic ray. -/
theorem ray_691 (m : Nat) : stoppingTime (2 ^ 4 * m + 691) 4 :=
  stoppingTime_of_classCertificate certificate_691 m

/-- Checked base and every prefix for input 693. -/
theorem certificate_693 : classCertificateB 2 693 = true := by
  decide

/-- The same exact first-descent time holds on an infinite dyadic ray. -/
theorem ray_693 (m : Nat) : stoppingTime (2 ^ 2 * m + 693) 2 :=
  stoppingTime_of_classCertificate certificate_693 m

/-- Checked base and every prefix for input 695. -/
theorem certificate_695 : classCertificateB 5 695 = true := by
  decide

/-- The same exact first-descent time holds on an infinite dyadic ray. -/
theorem ray_695 (m : Nat) : stoppingTime (2 ^ 5 * m + 695) 5 :=
  stoppingTime_of_classCertificate certificate_695 m

/-- Checked base and every prefix for input 697. -/
theorem certificate_697 : classCertificateB 2 697 = true := by
  decide

/-- The same exact first-descent time holds on an infinite dyadic ray. -/
theorem ray_697 (m : Nat) : stoppingTime (2 ^ 2 * m + 697) 2 :=
  stoppingTime_of_classCertificate certificate_697 m

/-- Checked base and every prefix for input 699. -/
theorem certificate_699 : classCertificateB 7 699 = true := by
  decide

/-- The same exact first-descent time holds on an infinite dyadic ray. -/
theorem ray_699 (m : Nat) : stoppingTime (2 ^ 7 * m + 699) 7 :=
  stoppingTime_of_classCertificate certificate_699 m

/-- Checked base and every prefix for input 701. -/
theorem certificate_701 : classCertificateB 2 701 = true := by
  decide

/-- The same exact first-descent time holds on an infinite dyadic ray. -/
theorem ray_701 (m : Nat) : stoppingTime (2 ^ 2 * m + 701) 2 :=
  stoppingTime_of_classCertificate certificate_701 m

/-- Checked base and every prefix for input 703. -/
theorem certificate_703 : classCertificateB 81 703 = true := by
  decide

/-- The same exact first-descent time holds on an infinite dyadic ray. -/
theorem ray_703 (m : Nat) : stoppingTime (2 ^ 81 * m + 703) 81 :=
  stoppingTime_of_classCertificate certificate_703 m

/-- Checked base and every prefix for input 705. -/
theorem certificate_705 : classCertificateB 2 705 = true := by
  decide

/-- The same exact first-descent time holds on an infinite dyadic ray. -/
theorem ray_705 (m : Nat) : stoppingTime (2 ^ 2 * m + 705) 2 :=
  stoppingTime_of_classCertificate certificate_705 m

/-- Checked base and every prefix for input 707. -/
theorem certificate_707 : classCertificateB 4 707 = true := by
  decide

/-- The same exact first-descent time holds on an infinite dyadic ray. -/
theorem ray_707 (m : Nat) : stoppingTime (2 ^ 4 * m + 707) 4 :=
  stoppingTime_of_classCertificate certificate_707 m

/-- Checked base and every prefix for input 709. -/
theorem certificate_709 : classCertificateB 2 709 = true := by
  decide

/-- The same exact first-descent time holds on an infinite dyadic ray. -/
theorem ray_709 (m : Nat) : stoppingTime (2 ^ 2 * m + 709) 2 :=
  stoppingTime_of_classCertificate certificate_709 m

/-- Checked base and every prefix for input 711. -/
theorem certificate_711 : classCertificateB 8 711 = true := by
  decide

/-- The same exact first-descent time holds on an infinite dyadic ray. -/
theorem ray_711 (m : Nat) : stoppingTime (2 ^ 8 * m + 711) 8 :=
  stoppingTime_of_classCertificate certificate_711 m

/-- Checked base and every prefix for input 713. -/
theorem certificate_713 : classCertificateB 2 713 = true := by
  decide

/-- The same exact first-descent time holds on an infinite dyadic ray. -/
theorem ray_713 (m : Nat) : stoppingTime (2 ^ 2 * m + 713) 2 :=
  stoppingTime_of_classCertificate certificate_713 m

/-- Checked base and every prefix for input 715. -/
theorem certificate_715 : classCertificateB 5 715 = true := by
  decide

/-- The same exact first-descent time holds on an infinite dyadic ray. -/
theorem ray_715 (m : Nat) : stoppingTime (2 ^ 5 * m + 715) 5 :=
  stoppingTime_of_classCertificate certificate_715 m

/-- Checked base and every prefix for input 717. -/
theorem certificate_717 : classCertificateB 2 717 = true := by
  decide

/-- The same exact first-descent time holds on an infinite dyadic ray. -/
theorem ray_717 (m : Nat) : stoppingTime (2 ^ 2 * m + 717) 2 :=
  stoppingTime_of_classCertificate certificate_717 m

/-- Checked base and every prefix for input 719. -/
theorem certificate_719 : classCertificateB 13 719 = true := by
  decide

/-- The same exact first-descent time holds on an infinite dyadic ray. -/
theorem ray_719 (m : Nat) : stoppingTime (2 ^ 13 * m + 719) 13 :=
  stoppingTime_of_classCertificate certificate_719 m

/-- Checked base and every prefix for input 721. -/
theorem certificate_721 : classCertificateB 2 721 = true := by
  decide

/-- The same exact first-descent time holds on an infinite dyadic ray. -/
theorem ray_721 (m : Nat) : stoppingTime (2 ^ 2 * m + 721) 2 :=
  stoppingTime_of_classCertificate certificate_721 m

/-- Checked base and every prefix for input 723. -/
theorem certificate_723 : classCertificateB 4 723 = true := by
  decide

/-- The same exact first-descent time holds on an infinite dyadic ray. -/
theorem ray_723 (m : Nat) : stoppingTime (2 ^ 4 * m + 723) 4 :=
  stoppingTime_of_classCertificate certificate_723 m

/-- Checked base and every prefix for input 725. -/
theorem certificate_725 : classCertificateB 2 725 = true := by
  decide

/-- The same exact first-descent time holds on an infinite dyadic ray. -/
theorem ray_725 (m : Nat) : stoppingTime (2 ^ 2 * m + 725) 2 :=
  stoppingTime_of_classCertificate certificate_725 m

/-- Checked base and every prefix for input 727. -/
theorem certificate_727 : classCertificateB 5 727 = true := by
  decide

/-- The same exact first-descent time holds on an infinite dyadic ray. -/
theorem ray_727 (m : Nat) : stoppingTime (2 ^ 5 * m + 727) 5 :=
  stoppingTime_of_classCertificate certificate_727 m

/-- Checked base and every prefix for input 729. -/
theorem certificate_729 : classCertificateB 2 729 = true := by
  decide

/-- The same exact first-descent time holds on an infinite dyadic ray. -/
theorem ray_729 (m : Nat) : stoppingTime (2 ^ 2 * m + 729) 2 :=
  stoppingTime_of_classCertificate certificate_729 m

/-- Checked base and every prefix for input 731. -/
theorem certificate_731 : classCertificateB 8 731 = true := by
  decide

/-- The same exact first-descent time holds on an infinite dyadic ray. -/
theorem ray_731 (m : Nat) : stoppingTime (2 ^ 8 * m + 731) 8 :=
  stoppingTime_of_classCertificate certificate_731 m

/-- Checked base and every prefix for input 733. -/
theorem certificate_733 : classCertificateB 2 733 = true := by
  decide

/-- The same exact first-descent time holds on an infinite dyadic ray. -/
theorem ray_733 (m : Nat) : stoppingTime (2 ^ 2 * m + 733) 2 :=
  stoppingTime_of_classCertificate certificate_733 m

/-- Checked base and every prefix for input 735. -/
theorem certificate_735 : classCertificateB 10 735 = true := by
  decide

/-- The same exact first-descent time holds on an infinite dyadic ray. -/
theorem ray_735 (m : Nat) : stoppingTime (2 ^ 10 * m + 735) 10 :=
  stoppingTime_of_classCertificate certificate_735 m

/-- Checked base and every prefix for input 737. -/
theorem certificate_737 : classCertificateB 2 737 = true := by
  decide

/-- The same exact first-descent time holds on an infinite dyadic ray. -/
theorem ray_737 (m : Nat) : stoppingTime (2 ^ 2 * m + 737) 2 :=
  stoppingTime_of_classCertificate certificate_737 m

/-- Exhaustive coverage of the odd inputs in this batch, with no gaps. -/
theorem coverage : CertifiedRange 671 739 := by
  intro n hlo hhi hodd
  have hn : n = 671 ∨ n = 673 ∨ n = 675 ∨ n = 677 ∨ n = 679 ∨ n = 681 ∨ n = 683 ∨ n = 685 ∨ n = 687 ∨ n = 689 ∨ n = 691 ∨ n = 693 ∨ n = 695 ∨ n = 697 ∨ n = 699 ∨ n = 701 ∨ n = 703 ∨ n = 705 ∨ n = 707 ∨ n = 709 ∨ n = 711 ∨ n = 713 ∨ n = 715 ∨ n = 717 ∨ n = 719 ∨ n = 721 ∨ n = 723 ∨ n = 725 ∨ n = 727 ∨ n = 729 ∨ n = 731 ∨ n = 733 ∨ n = 735 ∨ n = 737 := by omega
  rcases hn with h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h
  · subst n
    exact ⟨39, witness_of_certificate certificate_671⟩
  · subst n
    exact ⟨2, witness_of_certificate certificate_673⟩
  · subst n
    exact ⟨4, witness_of_certificate certificate_675⟩
  · subst n
    exact ⟨2, witness_of_certificate certificate_677⟩
  · subst n
    exact ⟨13, witness_of_certificate certificate_679⟩
  · subst n
    exact ⟨2, witness_of_certificate certificate_681⟩
  · subst n
    exact ⟨5, witness_of_certificate certificate_683⟩
  · subst n
    exact ⟨2, witness_of_certificate certificate_685⟩
  · subst n
    exact ⟨8, witness_of_certificate certificate_687⟩
  · subst n
    exact ⟨2, witness_of_certificate certificate_689⟩
  · subst n
    exact ⟨4, witness_of_certificate certificate_691⟩
  · subst n
    exact ⟨2, witness_of_certificate certificate_693⟩
  · subst n
    exact ⟨5, witness_of_certificate certificate_695⟩
  · subst n
    exact ⟨2, witness_of_certificate certificate_697⟩
  · subst n
    exact ⟨7, witness_of_certificate certificate_699⟩
  · subst n
    exact ⟨2, witness_of_certificate certificate_701⟩
  · subst n
    exact ⟨81, witness_of_certificate certificate_703⟩
  · subst n
    exact ⟨2, witness_of_certificate certificate_705⟩
  · subst n
    exact ⟨4, witness_of_certificate certificate_707⟩
  · subst n
    exact ⟨2, witness_of_certificate certificate_709⟩
  · subst n
    exact ⟨8, witness_of_certificate certificate_711⟩
  · subst n
    exact ⟨2, witness_of_certificate certificate_713⟩
  · subst n
    exact ⟨5, witness_of_certificate certificate_715⟩
  · subst n
    exact ⟨2, witness_of_certificate certificate_717⟩
  · subst n
    exact ⟨13, witness_of_certificate certificate_719⟩
  · subst n
    exact ⟨2, witness_of_certificate certificate_721⟩
  · subst n
    exact ⟨4, witness_of_certificate certificate_723⟩
  · subst n
    exact ⟨2, witness_of_certificate certificate_725⟩
  · subst n
    exact ⟨5, witness_of_certificate certificate_727⟩
  · subst n
    exact ⟨2, witness_of_certificate certificate_729⟩
  · subst n
    exact ⟨8, witness_of_certificate certificate_731⟩
  · subst n
    exact ⟨2, witness_of_certificate certificate_733⟩
  · subst n
    exact ⟨10, witness_of_certificate certificate_735⟩
  · subst n
    exact ⟨2, witness_of_certificate certificate_737⟩

end Collatz.Research.CoefficientDescent.Batch011
