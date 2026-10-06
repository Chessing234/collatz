import Collatz.Research.CoefficientDescent.Basic

namespace Collatz.Research.CoefficientDescent.Batch059

open FirstDescentClass

set_option maxRecDepth 20000
set_option maxHeartbeats 0

/-- Checked base and every prefix for input 3887. -/
theorem certificate_3887 : classCertificateB 10 3887 = true := by
  decide

/-- The same exact first-descent time holds on an infinite dyadic ray. -/
theorem ray_3887 (m : Nat) : stoppingTime (2 ^ 10 * m + 3887) 10 :=
  stoppingTime_of_classCertificate certificate_3887 m

/-- Checked base and every prefix for input 3889. -/
theorem certificate_3889 : classCertificateB 2 3889 = true := by
  decide

/-- The same exact first-descent time holds on an infinite dyadic ray. -/
theorem ray_3889 (m : Nat) : stoppingTime (2 ^ 2 * m + 3889) 2 :=
  stoppingTime_of_classCertificate certificate_3889 m

/-- Checked base and every prefix for input 3891. -/
theorem certificate_3891 : classCertificateB 4 3891 = true := by
  decide

/-- The same exact first-descent time holds on an infinite dyadic ray. -/
theorem ray_3891 (m : Nat) : stoppingTime (2 ^ 4 * m + 3891) 4 :=
  stoppingTime_of_classCertificate certificate_3891 m

/-- Checked base and every prefix for input 3893. -/
theorem certificate_3893 : classCertificateB 2 3893 = true := by
  decide

/-- The same exact first-descent time holds on an infinite dyadic ray. -/
theorem ray_3893 (m : Nat) : stoppingTime (2 ^ 2 * m + 3893) 2 :=
  stoppingTime_of_classCertificate certificate_3893 m

/-- Checked base and every prefix for input 3895. -/
theorem certificate_3895 : classCertificateB 5 3895 = true := by
  decide

/-- The same exact first-descent time holds on an infinite dyadic ray. -/
theorem ray_3895 (m : Nat) : stoppingTime (2 ^ 5 * m + 3895) 5 :=
  stoppingTime_of_classCertificate certificate_3895 m

/-- Checked base and every prefix for input 3897. -/
theorem certificate_3897 : classCertificateB 2 3897 = true := by
  decide

/-- The same exact first-descent time holds on an infinite dyadic ray. -/
theorem ray_3897 (m : Nat) : stoppingTime (2 ^ 2 * m + 3897) 2 :=
  stoppingTime_of_classCertificate certificate_3897 m

/-- Checked base and every prefix for input 3899. -/
theorem certificate_3899 : classCertificateB 7 3899 = true := by
  decide

/-- The same exact first-descent time holds on an infinite dyadic ray. -/
theorem ray_3899 (m : Nat) : stoppingTime (2 ^ 7 * m + 3899) 7 :=
  stoppingTime_of_classCertificate certificate_3899 m

/-- Checked base and every prefix for input 3901. -/
theorem certificate_3901 : classCertificateB 2 3901 = true := by
  decide

/-- The same exact first-descent time holds on an infinite dyadic ray. -/
theorem ray_3901 (m : Nat) : stoppingTime (2 ^ 2 * m + 3901) 2 :=
  stoppingTime_of_classCertificate certificate_3901 m

/-- Checked base and every prefix for input 3903. -/
theorem certificate_3903 : classCertificateB 13 3903 = true := by
  decide

/-- The same exact first-descent time holds on an infinite dyadic ray. -/
theorem ray_3903 (m : Nat) : stoppingTime (2 ^ 13 * m + 3903) 13 :=
  stoppingTime_of_classCertificate certificate_3903 m

/-- Checked base and every prefix for input 3905. -/
theorem certificate_3905 : classCertificateB 2 3905 = true := by
  decide

/-- The same exact first-descent time holds on an infinite dyadic ray. -/
theorem ray_3905 (m : Nat) : stoppingTime (2 ^ 2 * m + 3905) 2 :=
  stoppingTime_of_classCertificate certificate_3905 m

/-- Checked base and every prefix for input 3907. -/
theorem certificate_3907 : classCertificateB 4 3907 = true := by
  decide

/-- The same exact first-descent time holds on an infinite dyadic ray. -/
theorem ray_3907 (m : Nat) : stoppingTime (2 ^ 4 * m + 3907) 4 :=
  stoppingTime_of_classCertificate certificate_3907 m

/-- Checked base and every prefix for input 3909. -/
theorem certificate_3909 : classCertificateB 2 3909 = true := by
  decide

/-- The same exact first-descent time holds on an infinite dyadic ray. -/
theorem ray_3909 (m : Nat) : stoppingTime (2 ^ 2 * m + 3909) 2 :=
  stoppingTime_of_classCertificate certificate_3909 m

/-- Checked base and every prefix for input 3911. -/
theorem certificate_3911 : classCertificateB 12 3911 = true := by
  decide

/-- The same exact first-descent time holds on an infinite dyadic ray. -/
theorem ray_3911 (m : Nat) : stoppingTime (2 ^ 12 * m + 3911) 12 :=
  stoppingTime_of_classCertificate certificate_3911 m

/-- Checked base and every prefix for input 3913. -/
theorem certificate_3913 : classCertificateB 2 3913 = true := by
  decide

/-- The same exact first-descent time holds on an infinite dyadic ray. -/
theorem ray_3913 (m : Nat) : stoppingTime (2 ^ 2 * m + 3913) 2 :=
  stoppingTime_of_classCertificate certificate_3913 m

/-- Checked base and every prefix for input 3915. -/
theorem certificate_3915 : classCertificateB 5 3915 = true := by
  decide

/-- The same exact first-descent time holds on an infinite dyadic ray. -/
theorem ray_3915 (m : Nat) : stoppingTime (2 ^ 5 * m + 3915) 5 :=
  stoppingTime_of_classCertificate certificate_3915 m

/-- Checked base and every prefix for input 3917. -/
theorem certificate_3917 : classCertificateB 2 3917 = true := by
  decide

/-- The same exact first-descent time holds on an infinite dyadic ray. -/
theorem ray_3917 (m : Nat) : stoppingTime (2 ^ 2 * m + 3917) 2 :=
  stoppingTime_of_classCertificate certificate_3917 m

/-- Checked base and every prefix for input 3919. -/
theorem certificate_3919 : classCertificateB 8 3919 = true := by
  decide

/-- The same exact first-descent time holds on an infinite dyadic ray. -/
theorem ray_3919 (m : Nat) : stoppingTime (2 ^ 8 * m + 3919) 8 :=
  stoppingTime_of_classCertificate certificate_3919 m

/-- Checked base and every prefix for input 3921. -/
theorem certificate_3921 : classCertificateB 2 3921 = true := by
  decide

/-- The same exact first-descent time holds on an infinite dyadic ray. -/
theorem ray_3921 (m : Nat) : stoppingTime (2 ^ 2 * m + 3921) 2 :=
  stoppingTime_of_classCertificate certificate_3921 m

/-- Checked base and every prefix for input 3923. -/
theorem certificate_3923 : classCertificateB 4 3923 = true := by
  decide

/-- The same exact first-descent time holds on an infinite dyadic ray. -/
theorem ray_3923 (m : Nat) : stoppingTime (2 ^ 4 * m + 3923) 4 :=
  stoppingTime_of_classCertificate certificate_3923 m

/-- Checked base and every prefix for input 3925. -/
theorem certificate_3925 : classCertificateB 2 3925 = true := by
  decide

/-- The same exact first-descent time holds on an infinite dyadic ray. -/
theorem ray_3925 (m : Nat) : stoppingTime (2 ^ 2 * m + 3925) 2 :=
  stoppingTime_of_classCertificate certificate_3925 m

/-- Checked base and every prefix for input 3927. -/
theorem certificate_3927 : classCertificateB 5 3927 = true := by
  decide

/-- The same exact first-descent time holds on an infinite dyadic ray. -/
theorem ray_3927 (m : Nat) : stoppingTime (2 ^ 5 * m + 3927) 5 :=
  stoppingTime_of_classCertificate certificate_3927 m

/-- Checked base and every prefix for input 3929. -/
theorem certificate_3929 : classCertificateB 2 3929 = true := by
  decide

/-- The same exact first-descent time holds on an infinite dyadic ray. -/
theorem ray_3929 (m : Nat) : stoppingTime (2 ^ 2 * m + 3929) 2 :=
  stoppingTime_of_classCertificate certificate_3929 m

/-- Checked base and every prefix for input 3931. -/
theorem certificate_3931 : classCertificateB 24 3931 = true := by
  decide

/-- The same exact first-descent time holds on an infinite dyadic ray. -/
theorem ray_3931 (m : Nat) : stoppingTime (2 ^ 24 * m + 3931) 24 :=
  stoppingTime_of_classCertificate certificate_3931 m

/-- Checked base and every prefix for input 3933. -/
theorem certificate_3933 : classCertificateB 2 3933 = true := by
  decide

/-- The same exact first-descent time holds on an infinite dyadic ray. -/
theorem ray_3933 (m : Nat) : stoppingTime (2 ^ 2 * m + 3933) 2 :=
  stoppingTime_of_classCertificate certificate_3933 m

/-- Checked base and every prefix for input 3935. -/
theorem certificate_3935 : classCertificateB 8 3935 = true := by
  decide

/-- The same exact first-descent time holds on an infinite dyadic ray. -/
theorem ray_3935 (m : Nat) : stoppingTime (2 ^ 8 * m + 3935) 8 :=
  stoppingTime_of_classCertificate certificate_3935 m

/-- Checked base and every prefix for input 3937. -/
theorem certificate_3937 : classCertificateB 2 3937 = true := by
  decide

/-- The same exact first-descent time holds on an infinite dyadic ray. -/
theorem ray_3937 (m : Nat) : stoppingTime (2 ^ 2 * m + 3937) 2 :=
  stoppingTime_of_classCertificate certificate_3937 m

/-- Checked base and every prefix for input 3939. -/
theorem certificate_3939 : classCertificateB 4 3939 = true := by
  decide

/-- The same exact first-descent time holds on an infinite dyadic ray. -/
theorem ray_3939 (m : Nat) : stoppingTime (2 ^ 4 * m + 3939) 4 :=
  stoppingTime_of_classCertificate certificate_3939 m

/-- Checked base and every prefix for input 3941. -/
theorem certificate_3941 : classCertificateB 2 3941 = true := by
  decide

/-- The same exact first-descent time holds on an infinite dyadic ray. -/
theorem ray_3941 (m : Nat) : stoppingTime (2 ^ 2 * m + 3941) 2 :=
  stoppingTime_of_classCertificate certificate_3941 m

/-- Checked base and every prefix for input 3943. -/
theorem certificate_3943 : classCertificateB 40 3943 = true := by
  decide

/-- The same exact first-descent time holds on an infinite dyadic ray. -/
theorem ray_3943 (m : Nat) : stoppingTime (2 ^ 40 * m + 3943) 40 :=
  stoppingTime_of_classCertificate certificate_3943 m

/-- Checked base and every prefix for input 3945. -/
theorem certificate_3945 : classCertificateB 2 3945 = true := by
  decide

/-- The same exact first-descent time holds on an infinite dyadic ray. -/
theorem ray_3945 (m : Nat) : stoppingTime (2 ^ 2 * m + 3945) 2 :=
  stoppingTime_of_classCertificate certificate_3945 m

/-- Checked base and every prefix for input 3947. -/
theorem certificate_3947 : classCertificateB 5 3947 = true := by
  decide

/-- The same exact first-descent time holds on an infinite dyadic ray. -/
theorem ray_3947 (m : Nat) : stoppingTime (2 ^ 5 * m + 3947) 5 :=
  stoppingTime_of_classCertificate certificate_3947 m

/-- Checked base and every prefix for input 3949. -/
theorem certificate_3949 : classCertificateB 2 3949 = true := by
  decide

/-- The same exact first-descent time holds on an infinite dyadic ray. -/
theorem ray_3949 (m : Nat) : stoppingTime (2 ^ 2 * m + 3949) 2 :=
  stoppingTime_of_classCertificate certificate_3949 m

/-- Checked base and every prefix for input 3951. -/
theorem certificate_3951 : classCertificateB 34 3951 = true := by
  decide

/-- The same exact first-descent time holds on an infinite dyadic ray. -/
theorem ray_3951 (m : Nat) : stoppingTime (2 ^ 34 * m + 3951) 34 :=
  stoppingTime_of_classCertificate certificate_3951 m

/-- Exhaustive coverage of the odd inputs in this batch, with no gaps. -/
theorem coverage : CertifiedRange 3887 3953 := by
  intro n hlo hhi hodd
  have hn : n = 3887 ∨ n = 3889 ∨ n = 3891 ∨ n = 3893 ∨ n = 3895 ∨ n = 3897 ∨ n = 3899 ∨ n = 3901 ∨ n = 3903 ∨ n = 3905 ∨ n = 3907 ∨ n = 3909 ∨ n = 3911 ∨ n = 3913 ∨ n = 3915 ∨ n = 3917 ∨ n = 3919 ∨ n = 3921 ∨ n = 3923 ∨ n = 3925 ∨ n = 3927 ∨ n = 3929 ∨ n = 3931 ∨ n = 3933 ∨ n = 3935 ∨ n = 3937 ∨ n = 3939 ∨ n = 3941 ∨ n = 3943 ∨ n = 3945 ∨ n = 3947 ∨ n = 3949 ∨ n = 3951 := by omega
  rcases hn with h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h
  · subst n
    exact ⟨10, witness_of_certificate certificate_3887⟩
  · subst n
    exact ⟨2, witness_of_certificate certificate_3889⟩
  · subst n
    exact ⟨4, witness_of_certificate certificate_3891⟩
  · subst n
    exact ⟨2, witness_of_certificate certificate_3893⟩
  · subst n
    exact ⟨5, witness_of_certificate certificate_3895⟩
  · subst n
    exact ⟨2, witness_of_certificate certificate_3897⟩
  · subst n
    exact ⟨7, witness_of_certificate certificate_3899⟩
  · subst n
    exact ⟨2, witness_of_certificate certificate_3901⟩
  · subst n
    exact ⟨13, witness_of_certificate certificate_3903⟩
  · subst n
    exact ⟨2, witness_of_certificate certificate_3905⟩
  · subst n
    exact ⟨4, witness_of_certificate certificate_3907⟩
  · subst n
    exact ⟨2, witness_of_certificate certificate_3909⟩
  · subst n
    exact ⟨12, witness_of_certificate certificate_3911⟩
  · subst n
    exact ⟨2, witness_of_certificate certificate_3913⟩
  · subst n
    exact ⟨5, witness_of_certificate certificate_3915⟩
  · subst n
    exact ⟨2, witness_of_certificate certificate_3917⟩
  · subst n
    exact ⟨8, witness_of_certificate certificate_3919⟩
  · subst n
    exact ⟨2, witness_of_certificate certificate_3921⟩
  · subst n
    exact ⟨4, witness_of_certificate certificate_3923⟩
  · subst n
    exact ⟨2, witness_of_certificate certificate_3925⟩
  · subst n
    exact ⟨5, witness_of_certificate certificate_3927⟩
  · subst n
    exact ⟨2, witness_of_certificate certificate_3929⟩
  · subst n
    exact ⟨24, witness_of_certificate certificate_3931⟩
  · subst n
    exact ⟨2, witness_of_certificate certificate_3933⟩
  · subst n
    exact ⟨8, witness_of_certificate certificate_3935⟩
  · subst n
    exact ⟨2, witness_of_certificate certificate_3937⟩
  · subst n
    exact ⟨4, witness_of_certificate certificate_3939⟩
  · subst n
    exact ⟨2, witness_of_certificate certificate_3941⟩
  · subst n
    exact ⟨40, witness_of_certificate certificate_3943⟩
  · subst n
    exact ⟨2, witness_of_certificate certificate_3945⟩
  · subst n
    exact ⟨5, witness_of_certificate certificate_3947⟩
  · subst n
    exact ⟨2, witness_of_certificate certificate_3949⟩
  · subst n
    exact ⟨34, witness_of_certificate certificate_3951⟩

end Collatz.Research.CoefficientDescent.Batch059
