import Collatz.Research.CoefficientDescent.Basic

namespace Collatz.Research.CoefficientDescent.Batch073

open FirstDescentClass

set_option maxRecDepth 20000
set_option maxHeartbeats 0

/-- Checked base and every prefix for input 4825. -/
theorem certificate_4825 : classCertificateB 2 4825 = true := by
  decide

/-- The same exact first-descent time holds on an infinite dyadic ray. -/
theorem ray_4825 (m : Nat) : stoppingTime (2 ^ 2 * m + 4825) 2 :=
  stoppingTime_of_classCertificate certificate_4825 m

/-- Checked base and every prefix for input 4827. -/
theorem certificate_4827 : classCertificateB 8 4827 = true := by
  decide

/-- The same exact first-descent time holds on an infinite dyadic ray. -/
theorem ray_4827 (m : Nat) : stoppingTime (2 ^ 8 * m + 4827) 8 :=
  stoppingTime_of_classCertificate certificate_4827 m

/-- Checked base and every prefix for input 4829. -/
theorem certificate_4829 : classCertificateB 2 4829 = true := by
  decide

/-- The same exact first-descent time holds on an infinite dyadic ray. -/
theorem ray_4829 (m : Nat) : stoppingTime (2 ^ 2 * m + 4829) 2 :=
  stoppingTime_of_classCertificate certificate_4829 m

/-- Checked base and every prefix for input 4831. -/
theorem certificate_4831 : classCertificateB 10 4831 = true := by
  decide

/-- The same exact first-descent time holds on an infinite dyadic ray. -/
theorem ray_4831 (m : Nat) : stoppingTime (2 ^ 10 * m + 4831) 10 :=
  stoppingTime_of_classCertificate certificate_4831 m

/-- Checked base and every prefix for input 4833. -/
theorem certificate_4833 : classCertificateB 2 4833 = true := by
  decide

/-- The same exact first-descent time holds on an infinite dyadic ray. -/
theorem ray_4833 (m : Nat) : stoppingTime (2 ^ 2 * m + 4833) 2 :=
  stoppingTime_of_classCertificate certificate_4833 m

/-- Checked base and every prefix for input 4835. -/
theorem certificate_4835 : classCertificateB 4 4835 = true := by
  decide

/-- The same exact first-descent time holds on an infinite dyadic ray. -/
theorem ray_4835 (m : Nat) : stoppingTime (2 ^ 4 * m + 4835) 4 :=
  stoppingTime_of_classCertificate certificate_4835 m

/-- Checked base and every prefix for input 4837. -/
theorem certificate_4837 : classCertificateB 2 4837 = true := by
  decide

/-- The same exact first-descent time holds on an infinite dyadic ray. -/
theorem ray_4837 (m : Nat) : stoppingTime (2 ^ 2 * m + 4837) 2 :=
  stoppingTime_of_classCertificate certificate_4837 m

/-- Checked base and every prefix for input 4839. -/
theorem certificate_4839 : classCertificateB 24 4839 = true := by
  decide

/-- The same exact first-descent time holds on an infinite dyadic ray. -/
theorem ray_4839 (m : Nat) : stoppingTime (2 ^ 24 * m + 4839) 24 :=
  stoppingTime_of_classCertificate certificate_4839 m

/-- Checked base and every prefix for input 4841. -/
theorem certificate_4841 : classCertificateB 2 4841 = true := by
  decide

/-- The same exact first-descent time holds on an infinite dyadic ray. -/
theorem ray_4841 (m : Nat) : stoppingTime (2 ^ 2 * m + 4841) 2 :=
  stoppingTime_of_classCertificate certificate_4841 m

/-- Checked base and every prefix for input 4843. -/
theorem certificate_4843 : classCertificateB 5 4843 = true := by
  decide

/-- The same exact first-descent time holds on an infinite dyadic ray. -/
theorem ray_4843 (m : Nat) : stoppingTime (2 ^ 5 * m + 4843) 5 :=
  stoppingTime_of_classCertificate certificate_4843 m

/-- Checked base and every prefix for input 4845. -/
theorem certificate_4845 : classCertificateB 2 4845 = true := by
  decide

/-- The same exact first-descent time holds on an infinite dyadic ray. -/
theorem ray_4845 (m : Nat) : stoppingTime (2 ^ 2 * m + 4845) 2 :=
  stoppingTime_of_classCertificate certificate_4845 m

/-- Checked base and every prefix for input 4847. -/
theorem certificate_4847 : classCertificateB 21 4847 = true := by
  decide

/-- The same exact first-descent time holds on an infinite dyadic ray. -/
theorem ray_4847 (m : Nat) : stoppingTime (2 ^ 21 * m + 4847) 21 :=
  stoppingTime_of_classCertificate certificate_4847 m

/-- Checked base and every prefix for input 4849. -/
theorem certificate_4849 : classCertificateB 2 4849 = true := by
  decide

/-- The same exact first-descent time holds on an infinite dyadic ray. -/
theorem ray_4849 (m : Nat) : stoppingTime (2 ^ 2 * m + 4849) 2 :=
  stoppingTime_of_classCertificate certificate_4849 m

/-- Checked base and every prefix for input 4851. -/
theorem certificate_4851 : classCertificateB 4 4851 = true := by
  decide

/-- The same exact first-descent time holds on an infinite dyadic ray. -/
theorem ray_4851 (m : Nat) : stoppingTime (2 ^ 4 * m + 4851) 4 :=
  stoppingTime_of_classCertificate certificate_4851 m

/-- Checked base and every prefix for input 4853. -/
theorem certificate_4853 : classCertificateB 2 4853 = true := by
  decide

/-- The same exact first-descent time holds on an infinite dyadic ray. -/
theorem ray_4853 (m : Nat) : stoppingTime (2 ^ 2 * m + 4853) 2 :=
  stoppingTime_of_classCertificate certificate_4853 m

/-- Checked base and every prefix for input 4855. -/
theorem certificate_4855 : classCertificateB 5 4855 = true := by
  decide

/-- The same exact first-descent time holds on an infinite dyadic ray. -/
theorem ray_4855 (m : Nat) : stoppingTime (2 ^ 5 * m + 4855) 5 :=
  stoppingTime_of_classCertificate certificate_4855 m

/-- Checked base and every prefix for input 4857. -/
theorem certificate_4857 : classCertificateB 2 4857 = true := by
  decide

/-- The same exact first-descent time holds on an infinite dyadic ray. -/
theorem ray_4857 (m : Nat) : stoppingTime (2 ^ 2 * m + 4857) 2 :=
  stoppingTime_of_classCertificate certificate_4857 m

/-- Checked base and every prefix for input 4859. -/
theorem certificate_4859 : classCertificateB 13 4859 = true := by
  decide

/-- The same exact first-descent time holds on an infinite dyadic ray. -/
theorem ray_4859 (m : Nat) : stoppingTime (2 ^ 13 * m + 4859) 13 :=
  stoppingTime_of_classCertificate certificate_4859 m

/-- Checked base and every prefix for input 4861. -/
theorem certificate_4861 : classCertificateB 2 4861 = true := by
  decide

/-- The same exact first-descent time holds on an infinite dyadic ray. -/
theorem ray_4861 (m : Nat) : stoppingTime (2 ^ 2 * m + 4861) 2 :=
  stoppingTime_of_classCertificate certificate_4861 m

/-- Checked base and every prefix for input 4863. -/
theorem certificate_4863 : classCertificateB 32 4863 = true := by
  decide

/-- The same exact first-descent time holds on an infinite dyadic ray. -/
theorem ray_4863 (m : Nat) : stoppingTime (2 ^ 32 * m + 4863) 32 :=
  stoppingTime_of_classCertificate certificate_4863 m

/-- Checked base and every prefix for input 4865. -/
theorem certificate_4865 : classCertificateB 2 4865 = true := by
  decide

/-- The same exact first-descent time holds on an infinite dyadic ray. -/
theorem ray_4865 (m : Nat) : stoppingTime (2 ^ 2 * m + 4865) 2 :=
  stoppingTime_of_classCertificate certificate_4865 m

/-- Checked base and every prefix for input 4867. -/
theorem certificate_4867 : classCertificateB 4 4867 = true := by
  decide

/-- The same exact first-descent time holds on an infinite dyadic ray. -/
theorem ray_4867 (m : Nat) : stoppingTime (2 ^ 4 * m + 4867) 4 :=
  stoppingTime_of_classCertificate certificate_4867 m

/-- Checked base and every prefix for input 4869. -/
theorem certificate_4869 : classCertificateB 2 4869 = true := by
  decide

/-- The same exact first-descent time holds on an infinite dyadic ray. -/
theorem ray_4869 (m : Nat) : stoppingTime (2 ^ 2 * m + 4869) 2 :=
  stoppingTime_of_classCertificate certificate_4869 m

/-- Checked base and every prefix for input 4871. -/
theorem certificate_4871 : classCertificateB 7 4871 = true := by
  decide

/-- The same exact first-descent time holds on an infinite dyadic ray. -/
theorem ray_4871 (m : Nat) : stoppingTime (2 ^ 7 * m + 4871) 7 :=
  stoppingTime_of_classCertificate certificate_4871 m

/-- Checked base and every prefix for input 4873. -/
theorem certificate_4873 : classCertificateB 2 4873 = true := by
  decide

/-- The same exact first-descent time holds on an infinite dyadic ray. -/
theorem ray_4873 (m : Nat) : stoppingTime (2 ^ 2 * m + 4873) 2 :=
  stoppingTime_of_classCertificate certificate_4873 m

/-- Checked base and every prefix for input 4875. -/
theorem certificate_4875 : classCertificateB 5 4875 = true := by
  decide

/-- The same exact first-descent time holds on an infinite dyadic ray. -/
theorem ray_4875 (m : Nat) : stoppingTime (2 ^ 5 * m + 4875) 5 :=
  stoppingTime_of_classCertificate certificate_4875 m

/-- Checked base and every prefix for input 4877. -/
theorem certificate_4877 : classCertificateB 2 4877 = true := by
  decide

/-- The same exact first-descent time holds on an infinite dyadic ray. -/
theorem ray_4877 (m : Nat) : stoppingTime (2 ^ 2 * m + 4877) 2 :=
  stoppingTime_of_classCertificate certificate_4877 m

/-- Checked base and every prefix for input 4879. -/
theorem certificate_4879 : classCertificateB 7 4879 = true := by
  decide

/-- The same exact first-descent time holds on an infinite dyadic ray. -/
theorem ray_4879 (m : Nat) : stoppingTime (2 ^ 7 * m + 4879) 7 :=
  stoppingTime_of_classCertificate certificate_4879 m

/-- Checked base and every prefix for input 4881. -/
theorem certificate_4881 : classCertificateB 2 4881 = true := by
  decide

/-- The same exact first-descent time holds on an infinite dyadic ray. -/
theorem ray_4881 (m : Nat) : stoppingTime (2 ^ 2 * m + 4881) 2 :=
  stoppingTime_of_classCertificate certificate_4881 m

/-- Checked base and every prefix for input 4883. -/
theorem certificate_4883 : classCertificateB 4 4883 = true := by
  decide

/-- The same exact first-descent time holds on an infinite dyadic ray. -/
theorem ray_4883 (m : Nat) : stoppingTime (2 ^ 4 * m + 4883) 4 :=
  stoppingTime_of_classCertificate certificate_4883 m

/-- Checked base and every prefix for input 4885. -/
theorem certificate_4885 : classCertificateB 2 4885 = true := by
  decide

/-- The same exact first-descent time holds on an infinite dyadic ray. -/
theorem ray_4885 (m : Nat) : stoppingTime (2 ^ 2 * m + 4885) 2 :=
  stoppingTime_of_classCertificate certificate_4885 m

/-- Checked base and every prefix for input 4887. -/
theorem certificate_4887 : classCertificateB 5 4887 = true := by
  decide

/-- The same exact first-descent time holds on an infinite dyadic ray. -/
theorem ray_4887 (m : Nat) : stoppingTime (2 ^ 5 * m + 4887) 5 :=
  stoppingTime_of_classCertificate certificate_4887 m

/-- Checked base and every prefix for input 4889. -/
theorem certificate_4889 : classCertificateB 2 4889 = true := by
  decide

/-- The same exact first-descent time holds on an infinite dyadic ray. -/
theorem ray_4889 (m : Nat) : stoppingTime (2 ^ 2 * m + 4889) 2 :=
  stoppingTime_of_classCertificate certificate_4889 m

/-- Exhaustive coverage of the odd inputs in this batch, with no gaps. -/
theorem coverage : CertifiedRange 4825 4891 := by
  intro n hlo hhi hodd
  have hn : n = 4825 ∨ n = 4827 ∨ n = 4829 ∨ n = 4831 ∨ n = 4833 ∨ n = 4835 ∨ n = 4837 ∨ n = 4839 ∨ n = 4841 ∨ n = 4843 ∨ n = 4845 ∨ n = 4847 ∨ n = 4849 ∨ n = 4851 ∨ n = 4853 ∨ n = 4855 ∨ n = 4857 ∨ n = 4859 ∨ n = 4861 ∨ n = 4863 ∨ n = 4865 ∨ n = 4867 ∨ n = 4869 ∨ n = 4871 ∨ n = 4873 ∨ n = 4875 ∨ n = 4877 ∨ n = 4879 ∨ n = 4881 ∨ n = 4883 ∨ n = 4885 ∨ n = 4887 ∨ n = 4889 := by omega
  rcases hn with h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h
  · subst n
    exact ⟨2, witness_of_certificate certificate_4825⟩
  · subst n
    exact ⟨8, witness_of_certificate certificate_4827⟩
  · subst n
    exact ⟨2, witness_of_certificate certificate_4829⟩
  · subst n
    exact ⟨10, witness_of_certificate certificate_4831⟩
  · subst n
    exact ⟨2, witness_of_certificate certificate_4833⟩
  · subst n
    exact ⟨4, witness_of_certificate certificate_4835⟩
  · subst n
    exact ⟨2, witness_of_certificate certificate_4837⟩
  · subst n
    exact ⟨24, witness_of_certificate certificate_4839⟩
  · subst n
    exact ⟨2, witness_of_certificate certificate_4841⟩
  · subst n
    exact ⟨5, witness_of_certificate certificate_4843⟩
  · subst n
    exact ⟨2, witness_of_certificate certificate_4845⟩
  · subst n
    exact ⟨21, witness_of_certificate certificate_4847⟩
  · subst n
    exact ⟨2, witness_of_certificate certificate_4849⟩
  · subst n
    exact ⟨4, witness_of_certificate certificate_4851⟩
  · subst n
    exact ⟨2, witness_of_certificate certificate_4853⟩
  · subst n
    exact ⟨5, witness_of_certificate certificate_4855⟩
  · subst n
    exact ⟨2, witness_of_certificate certificate_4857⟩
  · subst n
    exact ⟨13, witness_of_certificate certificate_4859⟩
  · subst n
    exact ⟨2, witness_of_certificate certificate_4861⟩
  · subst n
    exact ⟨32, witness_of_certificate certificate_4863⟩
  · subst n
    exact ⟨2, witness_of_certificate certificate_4865⟩
  · subst n
    exact ⟨4, witness_of_certificate certificate_4867⟩
  · subst n
    exact ⟨2, witness_of_certificate certificate_4869⟩
  · subst n
    exact ⟨7, witness_of_certificate certificate_4871⟩
  · subst n
    exact ⟨2, witness_of_certificate certificate_4873⟩
  · subst n
    exact ⟨5, witness_of_certificate certificate_4875⟩
  · subst n
    exact ⟨2, witness_of_certificate certificate_4877⟩
  · subst n
    exact ⟨7, witness_of_certificate certificate_4879⟩
  · subst n
    exact ⟨2, witness_of_certificate certificate_4881⟩
  · subst n
    exact ⟨4, witness_of_certificate certificate_4883⟩
  · subst n
    exact ⟨2, witness_of_certificate certificate_4885⟩
  · subst n
    exact ⟨5, witness_of_certificate certificate_4887⟩
  · subst n
    exact ⟨2, witness_of_certificate certificate_4889⟩

end Collatz.Research.CoefficientDescent.Batch073
