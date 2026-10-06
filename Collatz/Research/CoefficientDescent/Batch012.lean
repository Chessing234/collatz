import Collatz.Research.CoefficientDescent.Basic

namespace Collatz.Research.CoefficientDescent.Batch012

open FirstDescentClass

set_option maxRecDepth 20000
set_option maxHeartbeats 0

/-- Checked base and every prefix for input 739. -/
theorem certificate_739 : classCertificateB 4 739 = true := by
  decide

/-- The same exact first-descent time holds on an infinite dyadic ray. -/
theorem ray_739 (m : Nat) : stoppingTime (2 ^ 4 * m + 739) 4 :=
  stoppingTime_of_classCertificate certificate_739 m

/-- Checked base and every prefix for input 741. -/
theorem certificate_741 : classCertificateB 2 741 = true := by
  decide

/-- The same exact first-descent time holds on an infinite dyadic ray. -/
theorem ray_741 (m : Nat) : stoppingTime (2 ^ 2 * m + 741) 2 :=
  stoppingTime_of_classCertificate certificate_741 m

/-- Checked base and every prefix for input 743. -/
theorem certificate_743 : classCertificateB 24 743 = true := by
  decide

/-- The same exact first-descent time holds on an infinite dyadic ray. -/
theorem ray_743 (m : Nat) : stoppingTime (2 ^ 24 * m + 743) 24 :=
  stoppingTime_of_classCertificate certificate_743 m

/-- Checked base and every prefix for input 745. -/
theorem certificate_745 : classCertificateB 2 745 = true := by
  decide

/-- The same exact first-descent time holds on an infinite dyadic ray. -/
theorem ray_745 (m : Nat) : stoppingTime (2 ^ 2 * m + 745) 2 :=
  stoppingTime_of_classCertificate certificate_745 m

/-- Checked base and every prefix for input 747. -/
theorem certificate_747 : classCertificateB 5 747 = true := by
  decide

/-- The same exact first-descent time holds on an infinite dyadic ray. -/
theorem ray_747 (m : Nat) : stoppingTime (2 ^ 5 * m + 747) 5 :=
  stoppingTime_of_classCertificate certificate_747 m

/-- Checked base and every prefix for input 749. -/
theorem certificate_749 : classCertificateB 2 749 = true := by
  decide

/-- The same exact first-descent time holds on an infinite dyadic ray. -/
theorem ray_749 (m : Nat) : stoppingTime (2 ^ 2 * m + 749) 2 :=
  stoppingTime_of_classCertificate certificate_749 m

/-- Checked base and every prefix for input 751. -/
theorem certificate_751 : classCertificateB 21 751 = true := by
  decide

/-- The same exact first-descent time holds on an infinite dyadic ray. -/
theorem ray_751 (m : Nat) : stoppingTime (2 ^ 21 * m + 751) 21 :=
  stoppingTime_of_classCertificate certificate_751 m

/-- Checked base and every prefix for input 753. -/
theorem certificate_753 : classCertificateB 2 753 = true := by
  decide

/-- The same exact first-descent time holds on an infinite dyadic ray. -/
theorem ray_753 (m : Nat) : stoppingTime (2 ^ 2 * m + 753) 2 :=
  stoppingTime_of_classCertificate certificate_753 m

/-- Checked base and every prefix for input 755. -/
theorem certificate_755 : classCertificateB 4 755 = true := by
  decide

/-- The same exact first-descent time holds on an infinite dyadic ray. -/
theorem ray_755 (m : Nat) : stoppingTime (2 ^ 4 * m + 755) 4 :=
  stoppingTime_of_classCertificate certificate_755 m

/-- Checked base and every prefix for input 757. -/
theorem certificate_757 : classCertificateB 2 757 = true := by
  decide

/-- The same exact first-descent time holds on an infinite dyadic ray. -/
theorem ray_757 (m : Nat) : stoppingTime (2 ^ 2 * m + 757) 2 :=
  stoppingTime_of_classCertificate certificate_757 m

/-- Checked base and every prefix for input 759. -/
theorem certificate_759 : classCertificateB 5 759 = true := by
  decide

/-- The same exact first-descent time holds on an infinite dyadic ray. -/
theorem ray_759 (m : Nat) : stoppingTime (2 ^ 5 * m + 759) 5 :=
  stoppingTime_of_classCertificate certificate_759 m

/-- Checked base and every prefix for input 761. -/
theorem certificate_761 : classCertificateB 2 761 = true := by
  decide

/-- The same exact first-descent time holds on an infinite dyadic ray. -/
theorem ray_761 (m : Nat) : stoppingTime (2 ^ 2 * m + 761) 2 :=
  stoppingTime_of_classCertificate certificate_761 m

/-- Checked base and every prefix for input 763. -/
theorem certificate_763 : classCertificateB 20 763 = true := by
  decide

/-- The same exact first-descent time holds on an infinite dyadic ray. -/
theorem ray_763 (m : Nat) : stoppingTime (2 ^ 20 * m + 763) 20 :=
  stoppingTime_of_classCertificate certificate_763 m

/-- Checked base and every prefix for input 765. -/
theorem certificate_765 : classCertificateB 2 765 = true := by
  decide

/-- The same exact first-descent time holds on an infinite dyadic ray. -/
theorem ray_765 (m : Nat) : stoppingTime (2 ^ 2 * m + 765) 2 :=
  stoppingTime_of_classCertificate certificate_765 m

/-- Checked base and every prefix for input 767. -/
theorem certificate_767 : classCertificateB 16 767 = true := by
  decide

/-- The same exact first-descent time holds on an infinite dyadic ray. -/
theorem ray_767 (m : Nat) : stoppingTime (2 ^ 16 * m + 767) 16 :=
  stoppingTime_of_classCertificate certificate_767 m

/-- Checked base and every prefix for input 769. -/
theorem certificate_769 : classCertificateB 2 769 = true := by
  decide

/-- The same exact first-descent time holds on an infinite dyadic ray. -/
theorem ray_769 (m : Nat) : stoppingTime (2 ^ 2 * m + 769) 2 :=
  stoppingTime_of_classCertificate certificate_769 m

/-- Checked base and every prefix for input 771. -/
theorem certificate_771 : classCertificateB 4 771 = true := by
  decide

/-- The same exact first-descent time holds on an infinite dyadic ray. -/
theorem ray_771 (m : Nat) : stoppingTime (2 ^ 4 * m + 771) 4 :=
  stoppingTime_of_classCertificate certificate_771 m

/-- Checked base and every prefix for input 773. -/
theorem certificate_773 : classCertificateB 2 773 = true := by
  decide

/-- The same exact first-descent time holds on an infinite dyadic ray. -/
theorem ray_773 (m : Nat) : stoppingTime (2 ^ 2 * m + 773) 2 :=
  stoppingTime_of_classCertificate certificate_773 m

/-- Checked base and every prefix for input 775. -/
theorem certificate_775 : classCertificateB 7 775 = true := by
  decide

/-- The same exact first-descent time holds on an infinite dyadic ray. -/
theorem ray_775 (m : Nat) : stoppingTime (2 ^ 7 * m + 775) 7 :=
  stoppingTime_of_classCertificate certificate_775 m

/-- Checked base and every prefix for input 777. -/
theorem certificate_777 : classCertificateB 2 777 = true := by
  decide

/-- The same exact first-descent time holds on an infinite dyadic ray. -/
theorem ray_777 (m : Nat) : stoppingTime (2 ^ 2 * m + 777) 2 :=
  stoppingTime_of_classCertificate certificate_777 m

/-- Checked base and every prefix for input 779. -/
theorem certificate_779 : classCertificateB 5 779 = true := by
  decide

/-- The same exact first-descent time holds on an infinite dyadic ray. -/
theorem ray_779 (m : Nat) : stoppingTime (2 ^ 5 * m + 779) 5 :=
  stoppingTime_of_classCertificate certificate_779 m

/-- Checked base and every prefix for input 781. -/
theorem certificate_781 : classCertificateB 2 781 = true := by
  decide

/-- The same exact first-descent time holds on an infinite dyadic ray. -/
theorem ray_781 (m : Nat) : stoppingTime (2 ^ 2 * m + 781) 2 :=
  stoppingTime_of_classCertificate certificate_781 m

/-- Checked base and every prefix for input 783. -/
theorem certificate_783 : classCertificateB 7 783 = true := by
  decide

/-- The same exact first-descent time holds on an infinite dyadic ray. -/
theorem ray_783 (m : Nat) : stoppingTime (2 ^ 7 * m + 783) 7 :=
  stoppingTime_of_classCertificate certificate_783 m

/-- Checked base and every prefix for input 785. -/
theorem certificate_785 : classCertificateB 2 785 = true := by
  decide

/-- The same exact first-descent time holds on an infinite dyadic ray. -/
theorem ray_785 (m : Nat) : stoppingTime (2 ^ 2 * m + 785) 2 :=
  stoppingTime_of_classCertificate certificate_785 m

/-- Checked base and every prefix for input 787. -/
theorem certificate_787 : classCertificateB 4 787 = true := by
  decide

/-- The same exact first-descent time holds on an infinite dyadic ray. -/
theorem ray_787 (m : Nat) : stoppingTime (2 ^ 4 * m + 787) 4 :=
  stoppingTime_of_classCertificate certificate_787 m

/-- Checked base and every prefix for input 789. -/
theorem certificate_789 : classCertificateB 2 789 = true := by
  decide

/-- The same exact first-descent time holds on an infinite dyadic ray. -/
theorem ray_789 (m : Nat) : stoppingTime (2 ^ 2 * m + 789) 2 :=
  stoppingTime_of_classCertificate certificate_789 m

/-- Checked base and every prefix for input 791. -/
theorem certificate_791 : classCertificateB 5 791 = true := by
  decide

/-- The same exact first-descent time holds on an infinite dyadic ray. -/
theorem ray_791 (m : Nat) : stoppingTime (2 ^ 5 * m + 791) 5 :=
  stoppingTime_of_classCertificate certificate_791 m

/-- Checked base and every prefix for input 793. -/
theorem certificate_793 : classCertificateB 2 793 = true := by
  decide

/-- The same exact first-descent time holds on an infinite dyadic ray. -/
theorem ray_793 (m : Nat) : stoppingTime (2 ^ 2 * m + 793) 2 :=
  stoppingTime_of_classCertificate certificate_793 m

/-- Checked base and every prefix for input 795. -/
theorem certificate_795 : classCertificateB 27 795 = true := by
  decide

/-- The same exact first-descent time holds on an infinite dyadic ray. -/
theorem ray_795 (m : Nat) : stoppingTime (2 ^ 27 * m + 795) 27 :=
  stoppingTime_of_classCertificate certificate_795 m

/-- Checked base and every prefix for input 797. -/
theorem certificate_797 : classCertificateB 2 797 = true := by
  decide

/-- The same exact first-descent time holds on an infinite dyadic ray. -/
theorem ray_797 (m : Nat) : stoppingTime (2 ^ 2 * m + 797) 2 :=
  stoppingTime_of_classCertificate certificate_797 m

/-- Checked base and every prefix for input 799. -/
theorem certificate_799 : classCertificateB 13 799 = true := by
  decide

/-- The same exact first-descent time holds on an infinite dyadic ray. -/
theorem ray_799 (m : Nat) : stoppingTime (2 ^ 13 * m + 799) 13 :=
  stoppingTime_of_classCertificate certificate_799 m

/-- Checked base and every prefix for input 801. -/
theorem certificate_801 : classCertificateB 2 801 = true := by
  decide

/-- The same exact first-descent time holds on an infinite dyadic ray. -/
theorem ray_801 (m : Nat) : stoppingTime (2 ^ 2 * m + 801) 2 :=
  stoppingTime_of_classCertificate certificate_801 m

/-- Checked base and every prefix for input 803. -/
theorem certificate_803 : classCertificateB 4 803 = true := by
  decide

/-- The same exact first-descent time holds on an infinite dyadic ray. -/
theorem ray_803 (m : Nat) : stoppingTime (2 ^ 4 * m + 803) 4 :=
  stoppingTime_of_classCertificate certificate_803 m

/-- Exhaustive coverage of the odd inputs in this batch, with no gaps. -/
theorem coverage : CertifiedRange 739 805 := by
  intro n hlo hhi hodd
  have hn : n = 739 ∨ n = 741 ∨ n = 743 ∨ n = 745 ∨ n = 747 ∨ n = 749 ∨ n = 751 ∨ n = 753 ∨ n = 755 ∨ n = 757 ∨ n = 759 ∨ n = 761 ∨ n = 763 ∨ n = 765 ∨ n = 767 ∨ n = 769 ∨ n = 771 ∨ n = 773 ∨ n = 775 ∨ n = 777 ∨ n = 779 ∨ n = 781 ∨ n = 783 ∨ n = 785 ∨ n = 787 ∨ n = 789 ∨ n = 791 ∨ n = 793 ∨ n = 795 ∨ n = 797 ∨ n = 799 ∨ n = 801 ∨ n = 803 := by omega
  rcases hn with h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h
  · subst n
    exact ⟨4, witness_of_certificate certificate_739⟩
  · subst n
    exact ⟨2, witness_of_certificate certificate_741⟩
  · subst n
    exact ⟨24, witness_of_certificate certificate_743⟩
  · subst n
    exact ⟨2, witness_of_certificate certificate_745⟩
  · subst n
    exact ⟨5, witness_of_certificate certificate_747⟩
  · subst n
    exact ⟨2, witness_of_certificate certificate_749⟩
  · subst n
    exact ⟨21, witness_of_certificate certificate_751⟩
  · subst n
    exact ⟨2, witness_of_certificate certificate_753⟩
  · subst n
    exact ⟨4, witness_of_certificate certificate_755⟩
  · subst n
    exact ⟨2, witness_of_certificate certificate_757⟩
  · subst n
    exact ⟨5, witness_of_certificate certificate_759⟩
  · subst n
    exact ⟨2, witness_of_certificate certificate_761⟩
  · subst n
    exact ⟨20, witness_of_certificate certificate_763⟩
  · subst n
    exact ⟨2, witness_of_certificate certificate_765⟩
  · subst n
    exact ⟨16, witness_of_certificate certificate_767⟩
  · subst n
    exact ⟨2, witness_of_certificate certificate_769⟩
  · subst n
    exact ⟨4, witness_of_certificate certificate_771⟩
  · subst n
    exact ⟨2, witness_of_certificate certificate_773⟩
  · subst n
    exact ⟨7, witness_of_certificate certificate_775⟩
  · subst n
    exact ⟨2, witness_of_certificate certificate_777⟩
  · subst n
    exact ⟨5, witness_of_certificate certificate_779⟩
  · subst n
    exact ⟨2, witness_of_certificate certificate_781⟩
  · subst n
    exact ⟨7, witness_of_certificate certificate_783⟩
  · subst n
    exact ⟨2, witness_of_certificate certificate_785⟩
  · subst n
    exact ⟨4, witness_of_certificate certificate_787⟩
  · subst n
    exact ⟨2, witness_of_certificate certificate_789⟩
  · subst n
    exact ⟨5, witness_of_certificate certificate_791⟩
  · subst n
    exact ⟨2, witness_of_certificate certificate_793⟩
  · subst n
    exact ⟨27, witness_of_certificate certificate_795⟩
  · subst n
    exact ⟨2, witness_of_certificate certificate_797⟩
  · subst n
    exact ⟨13, witness_of_certificate certificate_799⟩
  · subst n
    exact ⟨2, witness_of_certificate certificate_801⟩
  · subst n
    exact ⟨4, witness_of_certificate certificate_803⟩

end Collatz.Research.CoefficientDescent.Batch012
