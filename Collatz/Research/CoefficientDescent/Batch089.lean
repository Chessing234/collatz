import Collatz.Research.CoefficientDescent.Basic

namespace Collatz.Research.CoefficientDescent.Batch089

open FirstDescentClass

set_option maxRecDepth 20000
set_option maxHeartbeats 0

/-- Checked base and every prefix for input 5897. -/
theorem certificate_5897 : classCertificateB 2 5897 = true := by
  decide

/-- The same exact first-descent time holds on an infinite dyadic ray. -/
theorem ray_5897 (m : Nat) : stoppingTime (2 ^ 2 * m + 5897) 2 :=
  stoppingTime_of_classCertificate certificate_5897 m

/-- Checked base and every prefix for input 5899. -/
theorem certificate_5899 : classCertificateB 5 5899 = true := by
  decide

/-- The same exact first-descent time holds on an infinite dyadic ray. -/
theorem ray_5899 (m : Nat) : stoppingTime (2 ^ 5 * m + 5899) 5 :=
  stoppingTime_of_classCertificate certificate_5899 m

/-- Checked base and every prefix for input 5901. -/
theorem certificate_5901 : classCertificateB 2 5901 = true := by
  decide

/-- The same exact first-descent time holds on an infinite dyadic ray. -/
theorem ray_5901 (m : Nat) : stoppingTime (2 ^ 2 * m + 5901) 2 :=
  stoppingTime_of_classCertificate certificate_5901 m

/-- Checked base and every prefix for input 5903. -/
theorem certificate_5903 : classCertificateB 7 5903 = true := by
  decide

/-- The same exact first-descent time holds on an infinite dyadic ray. -/
theorem ray_5903 (m : Nat) : stoppingTime (2 ^ 7 * m + 5903) 7 :=
  stoppingTime_of_classCertificate certificate_5903 m

/-- Checked base and every prefix for input 5905. -/
theorem certificate_5905 : classCertificateB 2 5905 = true := by
  decide

/-- The same exact first-descent time holds on an infinite dyadic ray. -/
theorem ray_5905 (m : Nat) : stoppingTime (2 ^ 2 * m + 5905) 2 :=
  stoppingTime_of_classCertificate certificate_5905 m

/-- Checked base and every prefix for input 5907. -/
theorem certificate_5907 : classCertificateB 4 5907 = true := by
  decide

/-- The same exact first-descent time holds on an infinite dyadic ray. -/
theorem ray_5907 (m : Nat) : stoppingTime (2 ^ 4 * m + 5907) 4 :=
  stoppingTime_of_classCertificate certificate_5907 m

/-- Checked base and every prefix for input 5909. -/
theorem certificate_5909 : classCertificateB 2 5909 = true := by
  decide

/-- The same exact first-descent time holds on an infinite dyadic ray. -/
theorem ray_5909 (m : Nat) : stoppingTime (2 ^ 2 * m + 5909) 2 :=
  stoppingTime_of_classCertificate certificate_5909 m

/-- Checked base and every prefix for input 5911. -/
theorem certificate_5911 : classCertificateB 5 5911 = true := by
  decide

/-- The same exact first-descent time holds on an infinite dyadic ray. -/
theorem ray_5911 (m : Nat) : stoppingTime (2 ^ 5 * m + 5911) 5 :=
  stoppingTime_of_classCertificate certificate_5911 m

/-- Checked base and every prefix for input 5913. -/
theorem certificate_5913 : classCertificateB 2 5913 = true := by
  decide

/-- The same exact first-descent time holds on an infinite dyadic ray. -/
theorem ray_5913 (m : Nat) : stoppingTime (2 ^ 2 * m + 5913) 2 :=
  stoppingTime_of_classCertificate certificate_5913 m

/-- Checked base and every prefix for input 5915. -/
theorem certificate_5915 : classCertificateB 39 5915 = true := by
  decide

/-- The same exact first-descent time holds on an infinite dyadic ray. -/
theorem ray_5915 (m : Nat) : stoppingTime (2 ^ 39 * m + 5915) 39 :=
  stoppingTime_of_classCertificate certificate_5915 m

/-- Checked base and every prefix for input 5917. -/
theorem certificate_5917 : classCertificateB 2 5917 = true := by
  decide

/-- The same exact first-descent time holds on an infinite dyadic ray. -/
theorem ray_5917 (m : Nat) : stoppingTime (2 ^ 2 * m + 5917) 2 :=
  stoppingTime_of_classCertificate certificate_5917 m

/-- Checked base and every prefix for input 5919. -/
theorem certificate_5919 : classCertificateB 12 5919 = true := by
  decide

/-- The same exact first-descent time holds on an infinite dyadic ray. -/
theorem ray_5919 (m : Nat) : stoppingTime (2 ^ 12 * m + 5919) 12 :=
  stoppingTime_of_classCertificate certificate_5919 m

/-- Checked base and every prefix for input 5921. -/
theorem certificate_5921 : classCertificateB 2 5921 = true := by
  decide

/-- The same exact first-descent time holds on an infinite dyadic ray. -/
theorem ray_5921 (m : Nat) : stoppingTime (2 ^ 2 * m + 5921) 2 :=
  stoppingTime_of_classCertificate certificate_5921 m

/-- Checked base and every prefix for input 5923. -/
theorem certificate_5923 : classCertificateB 4 5923 = true := by
  decide

/-- The same exact first-descent time holds on an infinite dyadic ray. -/
theorem ray_5923 (m : Nat) : stoppingTime (2 ^ 4 * m + 5923) 4 :=
  stoppingTime_of_classCertificate certificate_5923 m

/-- Checked base and every prefix for input 5925. -/
theorem certificate_5925 : classCertificateB 2 5925 = true := by
  decide

/-- The same exact first-descent time holds on an infinite dyadic ray. -/
theorem ray_5925 (m : Nat) : stoppingTime (2 ^ 2 * m + 5925) 2 :=
  stoppingTime_of_classCertificate certificate_5925 m

/-- Checked base and every prefix for input 5927. -/
theorem certificate_5927 : classCertificateB 8 5927 = true := by
  decide

/-- The same exact first-descent time holds on an infinite dyadic ray. -/
theorem ray_5927 (m : Nat) : stoppingTime (2 ^ 8 * m + 5927) 8 :=
  stoppingTime_of_classCertificate certificate_5927 m

/-- Checked base and every prefix for input 5929. -/
theorem certificate_5929 : classCertificateB 2 5929 = true := by
  decide

/-- The same exact first-descent time holds on an infinite dyadic ray. -/
theorem ray_5929 (m : Nat) : stoppingTime (2 ^ 2 * m + 5929) 2 :=
  stoppingTime_of_classCertificate certificate_5929 m

/-- Checked base and every prefix for input 5931. -/
theorem certificate_5931 : classCertificateB 5 5931 = true := by
  decide

/-- The same exact first-descent time holds on an infinite dyadic ray. -/
theorem ray_5931 (m : Nat) : stoppingTime (2 ^ 5 * m + 5931) 5 :=
  stoppingTime_of_classCertificate certificate_5931 m

/-- Checked base and every prefix for input 5933. -/
theorem certificate_5933 : classCertificateB 2 5933 = true := by
  decide

/-- The same exact first-descent time holds on an infinite dyadic ray. -/
theorem ray_5933 (m : Nat) : stoppingTime (2 ^ 2 * m + 5933) 2 :=
  stoppingTime_of_classCertificate certificate_5933 m

/-- Checked base and every prefix for input 5935. -/
theorem certificate_5935 : classCertificateB 10 5935 = true := by
  decide

/-- The same exact first-descent time holds on an infinite dyadic ray. -/
theorem ray_5935 (m : Nat) : stoppingTime (2 ^ 10 * m + 5935) 10 :=
  stoppingTime_of_classCertificate certificate_5935 m

/-- Checked base and every prefix for input 5937. -/
theorem certificate_5937 : classCertificateB 2 5937 = true := by
  decide

/-- The same exact first-descent time holds on an infinite dyadic ray. -/
theorem ray_5937 (m : Nat) : stoppingTime (2 ^ 2 * m + 5937) 2 :=
  stoppingTime_of_classCertificate certificate_5937 m

/-- Checked base and every prefix for input 5939. -/
theorem certificate_5939 : classCertificateB 4 5939 = true := by
  decide

/-- The same exact first-descent time holds on an infinite dyadic ray. -/
theorem ray_5939 (m : Nat) : stoppingTime (2 ^ 4 * m + 5939) 4 :=
  stoppingTime_of_classCertificate certificate_5939 m

/-- Checked base and every prefix for input 5941. -/
theorem certificate_5941 : classCertificateB 2 5941 = true := by
  decide

/-- The same exact first-descent time holds on an infinite dyadic ray. -/
theorem ray_5941 (m : Nat) : stoppingTime (2 ^ 2 * m + 5941) 2 :=
  stoppingTime_of_classCertificate certificate_5941 m

/-- Checked base and every prefix for input 5943. -/
theorem certificate_5943 : classCertificateB 5 5943 = true := by
  decide

/-- The same exact first-descent time holds on an infinite dyadic ray. -/
theorem ray_5943 (m : Nat) : stoppingTime (2 ^ 5 * m + 5943) 5 :=
  stoppingTime_of_classCertificate certificate_5943 m

/-- Checked base and every prefix for input 5945. -/
theorem certificate_5945 : classCertificateB 2 5945 = true := by
  decide

/-- The same exact first-descent time holds on an infinite dyadic ray. -/
theorem ray_5945 (m : Nat) : stoppingTime (2 ^ 2 * m + 5945) 2 :=
  stoppingTime_of_classCertificate certificate_5945 m

/-- Checked base and every prefix for input 5947. -/
theorem certificate_5947 : classCertificateB 7 5947 = true := by
  decide

/-- The same exact first-descent time holds on an infinite dyadic ray. -/
theorem ray_5947 (m : Nat) : stoppingTime (2 ^ 7 * m + 5947) 7 :=
  stoppingTime_of_classCertificate certificate_5947 m

/-- Checked base and every prefix for input 5949. -/
theorem certificate_5949 : classCertificateB 2 5949 = true := by
  decide

/-- The same exact first-descent time holds on an infinite dyadic ray. -/
theorem ray_5949 (m : Nat) : stoppingTime (2 ^ 2 * m + 5949) 2 :=
  stoppingTime_of_classCertificate certificate_5949 m

/-- Checked base and every prefix for input 5951. -/
theorem certificate_5951 : classCertificateB 12 5951 = true := by
  decide

/-- The same exact first-descent time holds on an infinite dyadic ray. -/
theorem ray_5951 (m : Nat) : stoppingTime (2 ^ 12 * m + 5951) 12 :=
  stoppingTime_of_classCertificate certificate_5951 m

/-- Checked base and every prefix for input 5953. -/
theorem certificate_5953 : classCertificateB 2 5953 = true := by
  decide

/-- The same exact first-descent time holds on an infinite dyadic ray. -/
theorem ray_5953 (m : Nat) : stoppingTime (2 ^ 2 * m + 5953) 2 :=
  stoppingTime_of_classCertificate certificate_5953 m

/-- Checked base and every prefix for input 5955. -/
theorem certificate_5955 : classCertificateB 4 5955 = true := by
  decide

/-- The same exact first-descent time holds on an infinite dyadic ray. -/
theorem ray_5955 (m : Nat) : stoppingTime (2 ^ 4 * m + 5955) 4 :=
  stoppingTime_of_classCertificate certificate_5955 m

/-- Checked base and every prefix for input 5957. -/
theorem certificate_5957 : classCertificateB 2 5957 = true := by
  decide

/-- The same exact first-descent time holds on an infinite dyadic ray. -/
theorem ray_5957 (m : Nat) : stoppingTime (2 ^ 2 * m + 5957) 2 :=
  stoppingTime_of_classCertificate certificate_5957 m

/-- Checked base and every prefix for input 5959. -/
theorem certificate_5959 : classCertificateB 13 5959 = true := by
  decide

/-- The same exact first-descent time holds on an infinite dyadic ray. -/
theorem ray_5959 (m : Nat) : stoppingTime (2 ^ 13 * m + 5959) 13 :=
  stoppingTime_of_classCertificate certificate_5959 m

/-- Checked base and every prefix for input 5961. -/
theorem certificate_5961 : classCertificateB 2 5961 = true := by
  decide

/-- The same exact first-descent time holds on an infinite dyadic ray. -/
theorem ray_5961 (m : Nat) : stoppingTime (2 ^ 2 * m + 5961) 2 :=
  stoppingTime_of_classCertificate certificate_5961 m

/-- Exhaustive coverage of the odd inputs in this batch, with no gaps. -/
theorem coverage : CertifiedRange 5897 5963 := by
  intro n hlo hhi hodd
  have hn : n = 5897 ∨ n = 5899 ∨ n = 5901 ∨ n = 5903 ∨ n = 5905 ∨ n = 5907 ∨ n = 5909 ∨ n = 5911 ∨ n = 5913 ∨ n = 5915 ∨ n = 5917 ∨ n = 5919 ∨ n = 5921 ∨ n = 5923 ∨ n = 5925 ∨ n = 5927 ∨ n = 5929 ∨ n = 5931 ∨ n = 5933 ∨ n = 5935 ∨ n = 5937 ∨ n = 5939 ∨ n = 5941 ∨ n = 5943 ∨ n = 5945 ∨ n = 5947 ∨ n = 5949 ∨ n = 5951 ∨ n = 5953 ∨ n = 5955 ∨ n = 5957 ∨ n = 5959 ∨ n = 5961 := by omega
  rcases hn with h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h
  · subst n
    exact ⟨2, witness_of_certificate certificate_5897⟩
  · subst n
    exact ⟨5, witness_of_certificate certificate_5899⟩
  · subst n
    exact ⟨2, witness_of_certificate certificate_5901⟩
  · subst n
    exact ⟨7, witness_of_certificate certificate_5903⟩
  · subst n
    exact ⟨2, witness_of_certificate certificate_5905⟩
  · subst n
    exact ⟨4, witness_of_certificate certificate_5907⟩
  · subst n
    exact ⟨2, witness_of_certificate certificate_5909⟩
  · subst n
    exact ⟨5, witness_of_certificate certificate_5911⟩
  · subst n
    exact ⟨2, witness_of_certificate certificate_5913⟩
  · subst n
    exact ⟨39, witness_of_certificate certificate_5915⟩
  · subst n
    exact ⟨2, witness_of_certificate certificate_5917⟩
  · subst n
    exact ⟨12, witness_of_certificate certificate_5919⟩
  · subst n
    exact ⟨2, witness_of_certificate certificate_5921⟩
  · subst n
    exact ⟨4, witness_of_certificate certificate_5923⟩
  · subst n
    exact ⟨2, witness_of_certificate certificate_5925⟩
  · subst n
    exact ⟨8, witness_of_certificate certificate_5927⟩
  · subst n
    exact ⟨2, witness_of_certificate certificate_5929⟩
  · subst n
    exact ⟨5, witness_of_certificate certificate_5931⟩
  · subst n
    exact ⟨2, witness_of_certificate certificate_5933⟩
  · subst n
    exact ⟨10, witness_of_certificate certificate_5935⟩
  · subst n
    exact ⟨2, witness_of_certificate certificate_5937⟩
  · subst n
    exact ⟨4, witness_of_certificate certificate_5939⟩
  · subst n
    exact ⟨2, witness_of_certificate certificate_5941⟩
  · subst n
    exact ⟨5, witness_of_certificate certificate_5943⟩
  · subst n
    exact ⟨2, witness_of_certificate certificate_5945⟩
  · subst n
    exact ⟨7, witness_of_certificate certificate_5947⟩
  · subst n
    exact ⟨2, witness_of_certificate certificate_5949⟩
  · subst n
    exact ⟨12, witness_of_certificate certificate_5951⟩
  · subst n
    exact ⟨2, witness_of_certificate certificate_5953⟩
  · subst n
    exact ⟨4, witness_of_certificate certificate_5955⟩
  · subst n
    exact ⟨2, witness_of_certificate certificate_5957⟩
  · subst n
    exact ⟨13, witness_of_certificate certificate_5959⟩
  · subst n
    exact ⟨2, witness_of_certificate certificate_5961⟩

end Collatz.Research.CoefficientDescent.Batch089
