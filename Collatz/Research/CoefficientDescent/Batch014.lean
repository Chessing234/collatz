import Collatz.Research.CoefficientDescent.Basic

namespace Collatz.Research.CoefficientDescent.Batch014

open FirstDescentClass

set_option maxRecDepth 20000
set_option maxHeartbeats 0

/-- Checked base and every prefix for input 873. -/
theorem certificate_873 : classCertificateB 2 873 = true := by
  decide

/-- The same exact first-descent time holds on an infinite dyadic ray. -/
theorem ray_873 (m : Nat) : stoppingTime (2 ^ 2 * m + 873) 2 :=
  stoppingTime_of_classCertificate certificate_873 m

/-- Checked base and every prefix for input 875. -/
theorem certificate_875 : classCertificateB 5 875 = true := by
  decide

/-- The same exact first-descent time holds on an infinite dyadic ray. -/
theorem ray_875 (m : Nat) : stoppingTime (2 ^ 5 * m + 875) 5 :=
  stoppingTime_of_classCertificate certificate_875 m

/-- Checked base and every prefix for input 877. -/
theorem certificate_877 : classCertificateB 2 877 = true := by
  decide

/-- The same exact first-descent time holds on an infinite dyadic ray. -/
theorem ray_877 (m : Nat) : stoppingTime (2 ^ 2 * m + 877) 2 :=
  stoppingTime_of_classCertificate certificate_877 m

/-- Checked base and every prefix for input 879. -/
theorem certificate_879 : classCertificateB 12 879 = true := by
  decide

/-- The same exact first-descent time holds on an infinite dyadic ray. -/
theorem ray_879 (m : Nat) : stoppingTime (2 ^ 12 * m + 879) 12 :=
  stoppingTime_of_classCertificate certificate_879 m

/-- Checked base and every prefix for input 881. -/
theorem certificate_881 : classCertificateB 2 881 = true := by
  decide

/-- The same exact first-descent time holds on an infinite dyadic ray. -/
theorem ray_881 (m : Nat) : stoppingTime (2 ^ 2 * m + 881) 2 :=
  stoppingTime_of_classCertificate certificate_881 m

/-- Checked base and every prefix for input 883. -/
theorem certificate_883 : classCertificateB 4 883 = true := by
  decide

/-- The same exact first-descent time holds on an infinite dyadic ray. -/
theorem ray_883 (m : Nat) : stoppingTime (2 ^ 4 * m + 883) 4 :=
  stoppingTime_of_classCertificate certificate_883 m

/-- Checked base and every prefix for input 885. -/
theorem certificate_885 : classCertificateB 2 885 = true := by
  decide

/-- The same exact first-descent time holds on an infinite dyadic ray. -/
theorem ray_885 (m : Nat) : stoppingTime (2 ^ 2 * m + 885) 2 :=
  stoppingTime_of_classCertificate certificate_885 m

/-- Checked base and every prefix for input 887. -/
theorem certificate_887 : classCertificateB 5 887 = true := by
  decide

/-- The same exact first-descent time holds on an infinite dyadic ray. -/
theorem ray_887 (m : Nat) : stoppingTime (2 ^ 5 * m + 887) 5 :=
  stoppingTime_of_classCertificate certificate_887 m

/-- Checked base and every prefix for input 889. -/
theorem certificate_889 : classCertificateB 2 889 = true := by
  decide

/-- The same exact first-descent time holds on an infinite dyadic ray. -/
theorem ray_889 (m : Nat) : stoppingTime (2 ^ 2 * m + 889) 2 :=
  stoppingTime_of_classCertificate certificate_889 m

/-- Checked base and every prefix for input 891. -/
theorem certificate_891 : classCertificateB 8 891 = true := by
  decide

/-- The same exact first-descent time holds on an infinite dyadic ray. -/
theorem ray_891 (m : Nat) : stoppingTime (2 ^ 8 * m + 891) 8 :=
  stoppingTime_of_classCertificate certificate_891 m

/-- Checked base and every prefix for input 893. -/
theorem certificate_893 : classCertificateB 2 893 = true := by
  decide

/-- The same exact first-descent time holds on an infinite dyadic ray. -/
theorem ray_893 (m : Nat) : stoppingTime (2 ^ 2 * m + 893) 2 :=
  stoppingTime_of_classCertificate certificate_893 m

/-- Checked base and every prefix for input 895. -/
theorem certificate_895 : classCertificateB 24 895 = true := by
  decide

/-- The same exact first-descent time holds on an infinite dyadic ray. -/
theorem ray_895 (m : Nat) : stoppingTime (2 ^ 24 * m + 895) 24 :=
  stoppingTime_of_classCertificate certificate_895 m

/-- Checked base and every prefix for input 897. -/
theorem certificate_897 : classCertificateB 2 897 = true := by
  decide

/-- The same exact first-descent time holds on an infinite dyadic ray. -/
theorem ray_897 (m : Nat) : stoppingTime (2 ^ 2 * m + 897) 2 :=
  stoppingTime_of_classCertificate certificate_897 m

/-- Checked base and every prefix for input 899. -/
theorem certificate_899 : classCertificateB 4 899 = true := by
  decide

/-- The same exact first-descent time holds on an infinite dyadic ray. -/
theorem ray_899 (m : Nat) : stoppingTime (2 ^ 4 * m + 899) 4 :=
  stoppingTime_of_classCertificate certificate_899 m

/-- Checked base and every prefix for input 901. -/
theorem certificate_901 : classCertificateB 2 901 = true := by
  decide

/-- The same exact first-descent time holds on an infinite dyadic ray. -/
theorem ray_901 (m : Nat) : stoppingTime (2 ^ 2 * m + 901) 2 :=
  stoppingTime_of_classCertificate certificate_901 m

/-- Checked base and every prefix for input 903. -/
theorem certificate_903 : classCertificateB 7 903 = true := by
  decide

/-- The same exact first-descent time holds on an infinite dyadic ray. -/
theorem ray_903 (m : Nat) : stoppingTime (2 ^ 7 * m + 903) 7 :=
  stoppingTime_of_classCertificate certificate_903 m

/-- Checked base and every prefix for input 905. -/
theorem certificate_905 : classCertificateB 2 905 = true := by
  decide

/-- The same exact first-descent time holds on an infinite dyadic ray. -/
theorem ray_905 (m : Nat) : stoppingTime (2 ^ 2 * m + 905) 2 :=
  stoppingTime_of_classCertificate certificate_905 m

/-- Checked base and every prefix for input 907. -/
theorem certificate_907 : classCertificateB 5 907 = true := by
  decide

/-- The same exact first-descent time holds on an infinite dyadic ray. -/
theorem ray_907 (m : Nat) : stoppingTime (2 ^ 5 * m + 907) 5 :=
  stoppingTime_of_classCertificate certificate_907 m

/-- Checked base and every prefix for input 909. -/
theorem certificate_909 : classCertificateB 2 909 = true := by
  decide

/-- The same exact first-descent time holds on an infinite dyadic ray. -/
theorem ray_909 (m : Nat) : stoppingTime (2 ^ 2 * m + 909) 2 :=
  stoppingTime_of_classCertificate certificate_909 m

/-- Checked base and every prefix for input 911. -/
theorem certificate_911 : classCertificateB 7 911 = true := by
  decide

/-- The same exact first-descent time holds on an infinite dyadic ray. -/
theorem ray_911 (m : Nat) : stoppingTime (2 ^ 7 * m + 911) 7 :=
  stoppingTime_of_classCertificate certificate_911 m

/-- Checked base and every prefix for input 913. -/
theorem certificate_913 : classCertificateB 2 913 = true := by
  decide

/-- The same exact first-descent time holds on an infinite dyadic ray. -/
theorem ray_913 (m : Nat) : stoppingTime (2 ^ 2 * m + 913) 2 :=
  stoppingTime_of_classCertificate certificate_913 m

/-- Checked base and every prefix for input 915. -/
theorem certificate_915 : classCertificateB 4 915 = true := by
  decide

/-- The same exact first-descent time holds on an infinite dyadic ray. -/
theorem ray_915 (m : Nat) : stoppingTime (2 ^ 4 * m + 915) 4 :=
  stoppingTime_of_classCertificate certificate_915 m

/-- Checked base and every prefix for input 917. -/
theorem certificate_917 : classCertificateB 2 917 = true := by
  decide

/-- The same exact first-descent time holds on an infinite dyadic ray. -/
theorem ray_917 (m : Nat) : stoppingTime (2 ^ 2 * m + 917) 2 :=
  stoppingTime_of_classCertificate certificate_917 m

/-- Checked base and every prefix for input 919. -/
theorem certificate_919 : classCertificateB 5 919 = true := by
  decide

/-- The same exact first-descent time holds on an infinite dyadic ray. -/
theorem ray_919 (m : Nat) : stoppingTime (2 ^ 5 * m + 919) 5 :=
  stoppingTime_of_classCertificate certificate_919 m

/-- Checked base and every prefix for input 921. -/
theorem certificate_921 : classCertificateB 2 921 = true := by
  decide

/-- The same exact first-descent time holds on an infinite dyadic ray. -/
theorem ray_921 (m : Nat) : stoppingTime (2 ^ 2 * m + 921) 2 :=
  stoppingTime_of_classCertificate certificate_921 m

/-- Checked base and every prefix for input 923. -/
theorem certificate_923 : classCertificateB 10 923 = true := by
  decide

/-- The same exact first-descent time holds on an infinite dyadic ray. -/
theorem ray_923 (m : Nat) : stoppingTime (2 ^ 10 * m + 923) 10 :=
  stoppingTime_of_classCertificate certificate_923 m

/-- Checked base and every prefix for input 925. -/
theorem certificate_925 : classCertificateB 2 925 = true := by
  decide

/-- The same exact first-descent time holds on an infinite dyadic ray. -/
theorem ray_925 (m : Nat) : stoppingTime (2 ^ 2 * m + 925) 2 :=
  stoppingTime_of_classCertificate certificate_925 m

/-- Checked base and every prefix for input 927. -/
theorem certificate_927 : classCertificateB 37 927 = true := by
  decide

/-- The same exact first-descent time holds on an infinite dyadic ray. -/
theorem ray_927 (m : Nat) : stoppingTime (2 ^ 37 * m + 927) 37 :=
  stoppingTime_of_classCertificate certificate_927 m

/-- Checked base and every prefix for input 929. -/
theorem certificate_929 : classCertificateB 2 929 = true := by
  decide

/-- The same exact first-descent time holds on an infinite dyadic ray. -/
theorem ray_929 (m : Nat) : stoppingTime (2 ^ 2 * m + 929) 2 :=
  stoppingTime_of_classCertificate certificate_929 m

/-- Checked base and every prefix for input 931. -/
theorem certificate_931 : classCertificateB 4 931 = true := by
  decide

/-- The same exact first-descent time holds on an infinite dyadic ray. -/
theorem ray_931 (m : Nat) : stoppingTime (2 ^ 4 * m + 931) 4 :=
  stoppingTime_of_classCertificate certificate_931 m

/-- Checked base and every prefix for input 933. -/
theorem certificate_933 : classCertificateB 2 933 = true := by
  decide

/-- The same exact first-descent time holds on an infinite dyadic ray. -/
theorem ray_933 (m : Nat) : stoppingTime (2 ^ 2 * m + 933) 2 :=
  stoppingTime_of_classCertificate certificate_933 m

/-- Checked base and every prefix for input 935. -/
theorem certificate_935 : classCertificateB 12 935 = true := by
  decide

/-- The same exact first-descent time holds on an infinite dyadic ray. -/
theorem ray_935 (m : Nat) : stoppingTime (2 ^ 12 * m + 935) 12 :=
  stoppingTime_of_classCertificate certificate_935 m

/-- Checked base and every prefix for input 937. -/
theorem certificate_937 : classCertificateB 2 937 = true := by
  decide

/-- The same exact first-descent time holds on an infinite dyadic ray. -/
theorem ray_937 (m : Nat) : stoppingTime (2 ^ 2 * m + 937) 2 :=
  stoppingTime_of_classCertificate certificate_937 m

/-- Exhaustive coverage of the odd inputs in this batch, with no gaps. -/
theorem coverage : CertifiedRange 873 939 := by
  intro n hlo hhi hodd
  have hn : n = 873 ∨ n = 875 ∨ n = 877 ∨ n = 879 ∨ n = 881 ∨ n = 883 ∨ n = 885 ∨ n = 887 ∨ n = 889 ∨ n = 891 ∨ n = 893 ∨ n = 895 ∨ n = 897 ∨ n = 899 ∨ n = 901 ∨ n = 903 ∨ n = 905 ∨ n = 907 ∨ n = 909 ∨ n = 911 ∨ n = 913 ∨ n = 915 ∨ n = 917 ∨ n = 919 ∨ n = 921 ∨ n = 923 ∨ n = 925 ∨ n = 927 ∨ n = 929 ∨ n = 931 ∨ n = 933 ∨ n = 935 ∨ n = 937 := by omega
  rcases hn with h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h
  · subst n
    exact ⟨2, witness_of_certificate certificate_873⟩
  · subst n
    exact ⟨5, witness_of_certificate certificate_875⟩
  · subst n
    exact ⟨2, witness_of_certificate certificate_877⟩
  · subst n
    exact ⟨12, witness_of_certificate certificate_879⟩
  · subst n
    exact ⟨2, witness_of_certificate certificate_881⟩
  · subst n
    exact ⟨4, witness_of_certificate certificate_883⟩
  · subst n
    exact ⟨2, witness_of_certificate certificate_885⟩
  · subst n
    exact ⟨5, witness_of_certificate certificate_887⟩
  · subst n
    exact ⟨2, witness_of_certificate certificate_889⟩
  · subst n
    exact ⟨8, witness_of_certificate certificate_891⟩
  · subst n
    exact ⟨2, witness_of_certificate certificate_893⟩
  · subst n
    exact ⟨24, witness_of_certificate certificate_895⟩
  · subst n
    exact ⟨2, witness_of_certificate certificate_897⟩
  · subst n
    exact ⟨4, witness_of_certificate certificate_899⟩
  · subst n
    exact ⟨2, witness_of_certificate certificate_901⟩
  · subst n
    exact ⟨7, witness_of_certificate certificate_903⟩
  · subst n
    exact ⟨2, witness_of_certificate certificate_905⟩
  · subst n
    exact ⟨5, witness_of_certificate certificate_907⟩
  · subst n
    exact ⟨2, witness_of_certificate certificate_909⟩
  · subst n
    exact ⟨7, witness_of_certificate certificate_911⟩
  · subst n
    exact ⟨2, witness_of_certificate certificate_913⟩
  · subst n
    exact ⟨4, witness_of_certificate certificate_915⟩
  · subst n
    exact ⟨2, witness_of_certificate certificate_917⟩
  · subst n
    exact ⟨5, witness_of_certificate certificate_919⟩
  · subst n
    exact ⟨2, witness_of_certificate certificate_921⟩
  · subst n
    exact ⟨10, witness_of_certificate certificate_923⟩
  · subst n
    exact ⟨2, witness_of_certificate certificate_925⟩
  · subst n
    exact ⟨37, witness_of_certificate certificate_927⟩
  · subst n
    exact ⟨2, witness_of_certificate certificate_929⟩
  · subst n
    exact ⟨4, witness_of_certificate certificate_931⟩
  · subst n
    exact ⟨2, witness_of_certificate certificate_933⟩
  · subst n
    exact ⟨12, witness_of_certificate certificate_935⟩
  · subst n
    exact ⟨2, witness_of_certificate certificate_937⟩

end Collatz.Research.CoefficientDescent.Batch014
