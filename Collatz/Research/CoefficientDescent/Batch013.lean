import Collatz.Research.CoefficientDescent.Basic

namespace Collatz.Research.CoefficientDescent.Batch013

open FirstDescentClass

set_option maxRecDepth 20000
set_option maxHeartbeats 0

/-- Checked base and every prefix for input 805. -/
theorem certificate_805 : classCertificateB 2 805 = true := by
  decide

/-- The same exact first-descent time holds on an infinite dyadic ray. -/
theorem ray_805 (m : Nat) : stoppingTime (2 ^ 2 * m + 805) 2 :=
  stoppingTime_of_classCertificate certificate_805 m

/-- Checked base and every prefix for input 807. -/
theorem certificate_807 : classCertificateB 8 807 = true := by
  decide

/-- The same exact first-descent time holds on an infinite dyadic ray. -/
theorem ray_807 (m : Nat) : stoppingTime (2 ^ 8 * m + 807) 8 :=
  stoppingTime_of_classCertificate certificate_807 m

/-- Checked base and every prefix for input 809. -/
theorem certificate_809 : classCertificateB 2 809 = true := by
  decide

/-- The same exact first-descent time holds on an infinite dyadic ray. -/
theorem ray_809 (m : Nat) : stoppingTime (2 ^ 2 * m + 809) 2 :=
  stoppingTime_of_classCertificate certificate_809 m

/-- Checked base and every prefix for input 811. -/
theorem certificate_811 : classCertificateB 5 811 = true := by
  decide

/-- The same exact first-descent time holds on an infinite dyadic ray. -/
theorem ray_811 (m : Nat) : stoppingTime (2 ^ 5 * m + 811) 5 :=
  stoppingTime_of_classCertificate certificate_811 m

/-- Checked base and every prefix for input 813. -/
theorem certificate_813 : classCertificateB 2 813 = true := by
  decide

/-- The same exact first-descent time holds on an infinite dyadic ray. -/
theorem ray_813 (m : Nat) : stoppingTime (2 ^ 2 * m + 813) 2 :=
  stoppingTime_of_classCertificate certificate_813 m

/-- Checked base and every prefix for input 815. -/
theorem certificate_815 : classCertificateB 10 815 = true := by
  decide

/-- The same exact first-descent time holds on an infinite dyadic ray. -/
theorem ray_815 (m : Nat) : stoppingTime (2 ^ 10 * m + 815) 10 :=
  stoppingTime_of_classCertificate certificate_815 m

/-- Checked base and every prefix for input 817. -/
theorem certificate_817 : classCertificateB 2 817 = true := by
  decide

/-- The same exact first-descent time holds on an infinite dyadic ray. -/
theorem ray_817 (m : Nat) : stoppingTime (2 ^ 2 * m + 817) 2 :=
  stoppingTime_of_classCertificate certificate_817 m

/-- Checked base and every prefix for input 819. -/
theorem certificate_819 : classCertificateB 4 819 = true := by
  decide

/-- The same exact first-descent time holds on an infinite dyadic ray. -/
theorem ray_819 (m : Nat) : stoppingTime (2 ^ 4 * m + 819) 4 :=
  stoppingTime_of_classCertificate certificate_819 m

/-- Checked base and every prefix for input 821. -/
theorem certificate_821 : classCertificateB 2 821 = true := by
  decide

/-- The same exact first-descent time holds on an infinite dyadic ray. -/
theorem ray_821 (m : Nat) : stoppingTime (2 ^ 2 * m + 821) 2 :=
  stoppingTime_of_classCertificate certificate_821 m

/-- Checked base and every prefix for input 823. -/
theorem certificate_823 : classCertificateB 5 823 = true := by
  decide

/-- The same exact first-descent time holds on an infinite dyadic ray. -/
theorem ray_823 (m : Nat) : stoppingTime (2 ^ 5 * m + 823) 5 :=
  stoppingTime_of_classCertificate certificate_823 m

/-- Checked base and every prefix for input 825. -/
theorem certificate_825 : classCertificateB 2 825 = true := by
  decide

/-- The same exact first-descent time holds on an infinite dyadic ray. -/
theorem ray_825 (m : Nat) : stoppingTime (2 ^ 2 * m + 825) 2 :=
  stoppingTime_of_classCertificate certificate_825 m

/-- Checked base and every prefix for input 827. -/
theorem certificate_827 : classCertificateB 7 827 = true := by
  decide

/-- The same exact first-descent time holds on an infinite dyadic ray. -/
theorem ray_827 (m : Nat) : stoppingTime (2 ^ 7 * m + 827) 7 :=
  stoppingTime_of_classCertificate certificate_827 m

/-- Checked base and every prefix for input 829. -/
theorem certificate_829 : classCertificateB 2 829 = true := by
  decide

/-- The same exact first-descent time holds on an infinite dyadic ray. -/
theorem ray_829 (m : Nat) : stoppingTime (2 ^ 2 * m + 829) 2 :=
  stoppingTime_of_classCertificate certificate_829 m

/-- Checked base and every prefix for input 831. -/
theorem certificate_831 : classCertificateB 15 831 = true := by
  decide

/-- The same exact first-descent time holds on an infinite dyadic ray. -/
theorem ray_831 (m : Nat) : stoppingTime (2 ^ 15 * m + 831) 15 :=
  stoppingTime_of_classCertificate certificate_831 m

/-- Checked base and every prefix for input 833. -/
theorem certificate_833 : classCertificateB 2 833 = true := by
  decide

/-- The same exact first-descent time holds on an infinite dyadic ray. -/
theorem ray_833 (m : Nat) : stoppingTime (2 ^ 2 * m + 833) 2 :=
  stoppingTime_of_classCertificate certificate_833 m

/-- Checked base and every prefix for input 835. -/
theorem certificate_835 : classCertificateB 4 835 = true := by
  decide

/-- The same exact first-descent time holds on an infinite dyadic ray. -/
theorem ray_835 (m : Nat) : stoppingTime (2 ^ 4 * m + 835) 4 :=
  stoppingTime_of_classCertificate certificate_835 m

/-- Checked base and every prefix for input 837. -/
theorem certificate_837 : classCertificateB 2 837 = true := by
  decide

/-- The same exact first-descent time holds on an infinite dyadic ray. -/
theorem ray_837 (m : Nat) : stoppingTime (2 ^ 2 * m + 837) 2 :=
  stoppingTime_of_classCertificate certificate_837 m

/-- Checked base and every prefix for input 839. -/
theorem certificate_839 : classCertificateB 15 839 = true := by
  decide

/-- The same exact first-descent time holds on an infinite dyadic ray. -/
theorem ray_839 (m : Nat) : stoppingTime (2 ^ 15 * m + 839) 15 :=
  stoppingTime_of_classCertificate certificate_839 m

/-- Checked base and every prefix for input 841. -/
theorem certificate_841 : classCertificateB 2 841 = true := by
  decide

/-- The same exact first-descent time holds on an infinite dyadic ray. -/
theorem ray_841 (m : Nat) : stoppingTime (2 ^ 2 * m + 841) 2 :=
  stoppingTime_of_classCertificate certificate_841 m

/-- Checked base and every prefix for input 843. -/
theorem certificate_843 : classCertificateB 5 843 = true := by
  decide

/-- The same exact first-descent time holds on an infinite dyadic ray. -/
theorem ray_843 (m : Nat) : stoppingTime (2 ^ 5 * m + 843) 5 :=
  stoppingTime_of_classCertificate certificate_843 m

/-- Checked base and every prefix for input 845. -/
theorem certificate_845 : classCertificateB 2 845 = true := by
  decide

/-- The same exact first-descent time holds on an infinite dyadic ray. -/
theorem ray_845 (m : Nat) : stoppingTime (2 ^ 2 * m + 845) 2 :=
  stoppingTime_of_classCertificate certificate_845 m

/-- Checked base and every prefix for input 847. -/
theorem certificate_847 : classCertificateB 8 847 = true := by
  decide

/-- The same exact first-descent time holds on an infinite dyadic ray. -/
theorem ray_847 (m : Nat) : stoppingTime (2 ^ 8 * m + 847) 8 :=
  stoppingTime_of_classCertificate certificate_847 m

/-- Checked base and every prefix for input 849. -/
theorem certificate_849 : classCertificateB 2 849 = true := by
  decide

/-- The same exact first-descent time holds on an infinite dyadic ray. -/
theorem ray_849 (m : Nat) : stoppingTime (2 ^ 2 * m + 849) 2 :=
  stoppingTime_of_classCertificate certificate_849 m

/-- Checked base and every prefix for input 851. -/
theorem certificate_851 : classCertificateB 4 851 = true := by
  decide

/-- The same exact first-descent time holds on an infinite dyadic ray. -/
theorem ray_851 (m : Nat) : stoppingTime (2 ^ 4 * m + 851) 4 :=
  stoppingTime_of_classCertificate certificate_851 m

/-- Checked base and every prefix for input 853. -/
theorem certificate_853 : classCertificateB 2 853 = true := by
  decide

/-- The same exact first-descent time holds on an infinite dyadic ray. -/
theorem ray_853 (m : Nat) : stoppingTime (2 ^ 2 * m + 853) 2 :=
  stoppingTime_of_classCertificate certificate_853 m

/-- Checked base and every prefix for input 855. -/
theorem certificate_855 : classCertificateB 5 855 = true := by
  decide

/-- The same exact first-descent time holds on an infinite dyadic ray. -/
theorem ray_855 (m : Nat) : stoppingTime (2 ^ 5 * m + 855) 5 :=
  stoppingTime_of_classCertificate certificate_855 m

/-- Checked base and every prefix for input 857. -/
theorem certificate_857 : classCertificateB 2 857 = true := by
  decide

/-- The same exact first-descent time holds on an infinite dyadic ray. -/
theorem ray_857 (m : Nat) : stoppingTime (2 ^ 2 * m + 857) 2 :=
  stoppingTime_of_classCertificate certificate_857 m

/-- Checked base and every prefix for input 859. -/
theorem certificate_859 : classCertificateB 16 859 = true := by
  decide

/-- The same exact first-descent time holds on an infinite dyadic ray. -/
theorem ray_859 (m : Nat) : stoppingTime (2 ^ 16 * m + 859) 16 :=
  stoppingTime_of_classCertificate certificate_859 m

/-- Checked base and every prefix for input 861. -/
theorem certificate_861 : classCertificateB 2 861 = true := by
  decide

/-- The same exact first-descent time holds on an infinite dyadic ray. -/
theorem ray_861 (m : Nat) : stoppingTime (2 ^ 2 * m + 861) 2 :=
  stoppingTime_of_classCertificate certificate_861 m

/-- Checked base and every prefix for input 863. -/
theorem certificate_863 : classCertificateB 8 863 = true := by
  decide

/-- The same exact first-descent time holds on an infinite dyadic ray. -/
theorem ray_863 (m : Nat) : stoppingTime (2 ^ 8 * m + 863) 8 :=
  stoppingTime_of_classCertificate certificate_863 m

/-- Checked base and every prefix for input 865. -/
theorem certificate_865 : classCertificateB 2 865 = true := by
  decide

/-- The same exact first-descent time holds on an infinite dyadic ray. -/
theorem ray_865 (m : Nat) : stoppingTime (2 ^ 2 * m + 865) 2 :=
  stoppingTime_of_classCertificate certificate_865 m

/-- Checked base and every prefix for input 867. -/
theorem certificate_867 : classCertificateB 4 867 = true := by
  decide

/-- The same exact first-descent time holds on an infinite dyadic ray. -/
theorem ray_867 (m : Nat) : stoppingTime (2 ^ 4 * m + 867) 4 :=
  stoppingTime_of_classCertificate certificate_867 m

/-- Checked base and every prefix for input 869. -/
theorem certificate_869 : classCertificateB 2 869 = true := by
  decide

/-- The same exact first-descent time holds on an infinite dyadic ray. -/
theorem ray_869 (m : Nat) : stoppingTime (2 ^ 2 * m + 869) 2 :=
  stoppingTime_of_classCertificate certificate_869 m

/-- Checked base and every prefix for input 871. -/
theorem certificate_871 : classCertificateB 35 871 = true := by
  decide

/-- The same exact first-descent time holds on an infinite dyadic ray. -/
theorem ray_871 (m : Nat) : stoppingTime (2 ^ 35 * m + 871) 35 :=
  stoppingTime_of_classCertificate certificate_871 m

/-- Exhaustive coverage of the odd inputs in this batch, with no gaps. -/
theorem coverage : CertifiedRange 805 873 := by
  intro n hlo hhi hodd
  have hn : n = 805 ∨ n = 807 ∨ n = 809 ∨ n = 811 ∨ n = 813 ∨ n = 815 ∨ n = 817 ∨ n = 819 ∨ n = 821 ∨ n = 823 ∨ n = 825 ∨ n = 827 ∨ n = 829 ∨ n = 831 ∨ n = 833 ∨ n = 835 ∨ n = 837 ∨ n = 839 ∨ n = 841 ∨ n = 843 ∨ n = 845 ∨ n = 847 ∨ n = 849 ∨ n = 851 ∨ n = 853 ∨ n = 855 ∨ n = 857 ∨ n = 859 ∨ n = 861 ∨ n = 863 ∨ n = 865 ∨ n = 867 ∨ n = 869 ∨ n = 871 := by omega
  rcases hn with h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h
  · subst n
    exact ⟨2, witness_of_certificate certificate_805⟩
  · subst n
    exact ⟨8, witness_of_certificate certificate_807⟩
  · subst n
    exact ⟨2, witness_of_certificate certificate_809⟩
  · subst n
    exact ⟨5, witness_of_certificate certificate_811⟩
  · subst n
    exact ⟨2, witness_of_certificate certificate_813⟩
  · subst n
    exact ⟨10, witness_of_certificate certificate_815⟩
  · subst n
    exact ⟨2, witness_of_certificate certificate_817⟩
  · subst n
    exact ⟨4, witness_of_certificate certificate_819⟩
  · subst n
    exact ⟨2, witness_of_certificate certificate_821⟩
  · subst n
    exact ⟨5, witness_of_certificate certificate_823⟩
  · subst n
    exact ⟨2, witness_of_certificate certificate_825⟩
  · subst n
    exact ⟨7, witness_of_certificate certificate_827⟩
  · subst n
    exact ⟨2, witness_of_certificate certificate_829⟩
  · subst n
    exact ⟨15, witness_of_certificate certificate_831⟩
  · subst n
    exact ⟨2, witness_of_certificate certificate_833⟩
  · subst n
    exact ⟨4, witness_of_certificate certificate_835⟩
  · subst n
    exact ⟨2, witness_of_certificate certificate_837⟩
  · subst n
    exact ⟨15, witness_of_certificate certificate_839⟩
  · subst n
    exact ⟨2, witness_of_certificate certificate_841⟩
  · subst n
    exact ⟨5, witness_of_certificate certificate_843⟩
  · subst n
    exact ⟨2, witness_of_certificate certificate_845⟩
  · subst n
    exact ⟨8, witness_of_certificate certificate_847⟩
  · subst n
    exact ⟨2, witness_of_certificate certificate_849⟩
  · subst n
    exact ⟨4, witness_of_certificate certificate_851⟩
  · subst n
    exact ⟨2, witness_of_certificate certificate_853⟩
  · subst n
    exact ⟨5, witness_of_certificate certificate_855⟩
  · subst n
    exact ⟨2, witness_of_certificate certificate_857⟩
  · subst n
    exact ⟨16, witness_of_certificate certificate_859⟩
  · subst n
    exact ⟨2, witness_of_certificate certificate_861⟩
  · subst n
    exact ⟨8, witness_of_certificate certificate_863⟩
  · subst n
    exact ⟨2, witness_of_certificate certificate_865⟩
  · subst n
    exact ⟨4, witness_of_certificate certificate_867⟩
  · subst n
    exact ⟨2, witness_of_certificate certificate_869⟩
  · subst n
    exact ⟨35, witness_of_certificate certificate_871⟩

end Collatz.Research.CoefficientDescent.Batch013
