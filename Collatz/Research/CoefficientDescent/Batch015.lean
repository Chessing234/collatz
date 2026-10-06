import Collatz.Research.CoefficientDescent.Basic

namespace Collatz.Research.CoefficientDescent.Batch015

open FirstDescentClass

set_option maxRecDepth 20000
set_option maxHeartbeats 0

/-- Checked base and every prefix for input 939. -/
theorem certificate_939 : classCertificateB 5 939 = true := by
  decide

/-- The same exact first-descent time holds on an infinite dyadic ray. -/
theorem ray_939 (m : Nat) : stoppingTime (2 ^ 5 * m + 939) 5 :=
  stoppingTime_of_classCertificate certificate_939 m

/-- Checked base and every prefix for input 941. -/
theorem certificate_941 : classCertificateB 2 941 = true := by
  decide

/-- The same exact first-descent time holds on an infinite dyadic ray. -/
theorem ray_941 (m : Nat) : stoppingTime (2 ^ 2 * m + 941) 2 :=
  stoppingTime_of_classCertificate certificate_941 m

/-- Checked base and every prefix for input 943. -/
theorem certificate_943 : classCertificateB 8 943 = true := by
  decide

/-- The same exact first-descent time holds on an infinite dyadic ray. -/
theorem ray_943 (m : Nat) : stoppingTime (2 ^ 8 * m + 943) 8 :=
  stoppingTime_of_classCertificate certificate_943 m

/-- Checked base and every prefix for input 945. -/
theorem certificate_945 : classCertificateB 2 945 = true := by
  decide

/-- The same exact first-descent time holds on an infinite dyadic ray. -/
theorem ray_945 (m : Nat) : stoppingTime (2 ^ 2 * m + 945) 2 :=
  stoppingTime_of_classCertificate certificate_945 m

/-- Checked base and every prefix for input 947. -/
theorem certificate_947 : classCertificateB 4 947 = true := by
  decide

/-- The same exact first-descent time holds on an infinite dyadic ray. -/
theorem ray_947 (m : Nat) : stoppingTime (2 ^ 4 * m + 947) 4 :=
  stoppingTime_of_classCertificate certificate_947 m

/-- Checked base and every prefix for input 949. -/
theorem certificate_949 : classCertificateB 2 949 = true := by
  decide

/-- The same exact first-descent time holds on an infinite dyadic ray. -/
theorem ray_949 (m : Nat) : stoppingTime (2 ^ 2 * m + 949) 2 :=
  stoppingTime_of_classCertificate certificate_949 m

/-- Checked base and every prefix for input 951. -/
theorem certificate_951 : classCertificateB 5 951 = true := by
  decide

/-- The same exact first-descent time holds on an infinite dyadic ray. -/
theorem ray_951 (m : Nat) : stoppingTime (2 ^ 5 * m + 951) 5 :=
  stoppingTime_of_classCertificate certificate_951 m

/-- Checked base and every prefix for input 953. -/
theorem certificate_953 : classCertificateB 2 953 = true := by
  decide

/-- The same exact first-descent time holds on an infinite dyadic ray. -/
theorem ray_953 (m : Nat) : stoppingTime (2 ^ 2 * m + 953) 2 :=
  stoppingTime_of_classCertificate certificate_953 m

/-- Checked base and every prefix for input 955. -/
theorem certificate_955 : classCertificateB 7 955 = true := by
  decide

/-- The same exact first-descent time holds on an infinite dyadic ray. -/
theorem ray_955 (m : Nat) : stoppingTime (2 ^ 7 * m + 955) 7 :=
  stoppingTime_of_classCertificate certificate_955 m

/-- Checked base and every prefix for input 957. -/
theorem certificate_957 : classCertificateB 2 957 = true := by
  decide

/-- The same exact first-descent time holds on an infinite dyadic ray. -/
theorem ray_957 (m : Nat) : stoppingTime (2 ^ 2 * m + 957) 2 :=
  stoppingTime_of_classCertificate certificate_957 m

/-- Checked base and every prefix for input 959. -/
theorem certificate_959 : classCertificateB 21 959 = true := by
  decide

/-- The same exact first-descent time holds on an infinite dyadic ray. -/
theorem ray_959 (m : Nat) : stoppingTime (2 ^ 21 * m + 959) 21 :=
  stoppingTime_of_classCertificate certificate_959 m

/-- Checked base and every prefix for input 961. -/
theorem certificate_961 : classCertificateB 2 961 = true := by
  decide

/-- The same exact first-descent time holds on an infinite dyadic ray. -/
theorem ray_961 (m : Nat) : stoppingTime (2 ^ 2 * m + 961) 2 :=
  stoppingTime_of_classCertificate certificate_961 m

/-- Checked base and every prefix for input 963. -/
theorem certificate_963 : classCertificateB 4 963 = true := by
  decide

/-- The same exact first-descent time holds on an infinite dyadic ray. -/
theorem ray_963 (m : Nat) : stoppingTime (2 ^ 4 * m + 963) 4 :=
  stoppingTime_of_classCertificate certificate_963 m

/-- Checked base and every prefix for input 965. -/
theorem certificate_965 : classCertificateB 2 965 = true := by
  decide

/-- The same exact first-descent time holds on an infinite dyadic ray. -/
theorem ray_965 (m : Nat) : stoppingTime (2 ^ 2 * m + 965) 2 :=
  stoppingTime_of_classCertificate certificate_965 m

/-- Checked base and every prefix for input 967. -/
theorem certificate_967 : classCertificateB 8 967 = true := by
  decide

/-- The same exact first-descent time holds on an infinite dyadic ray. -/
theorem ray_967 (m : Nat) : stoppingTime (2 ^ 8 * m + 967) 8 :=
  stoppingTime_of_classCertificate certificate_967 m

/-- Checked base and every prefix for input 969. -/
theorem certificate_969 : classCertificateB 2 969 = true := by
  decide

/-- The same exact first-descent time holds on an infinite dyadic ray. -/
theorem ray_969 (m : Nat) : stoppingTime (2 ^ 2 * m + 969) 2 :=
  stoppingTime_of_classCertificate certificate_969 m

/-- Checked base and every prefix for input 971. -/
theorem certificate_971 : classCertificateB 5 971 = true := by
  decide

/-- The same exact first-descent time holds on an infinite dyadic ray. -/
theorem ray_971 (m : Nat) : stoppingTime (2 ^ 5 * m + 971) 5 :=
  stoppingTime_of_classCertificate certificate_971 m

/-- Checked base and every prefix for input 973. -/
theorem certificate_973 : classCertificateB 2 973 = true := by
  decide

/-- The same exact first-descent time holds on an infinite dyadic ray. -/
theorem ray_973 (m : Nat) : stoppingTime (2 ^ 2 * m + 973) 2 :=
  stoppingTime_of_classCertificate certificate_973 m

/-- Checked base and every prefix for input 975. -/
theorem certificate_975 : classCertificateB 10 975 = true := by
  decide

/-- The same exact first-descent time holds on an infinite dyadic ray. -/
theorem ray_975 (m : Nat) : stoppingTime (2 ^ 10 * m + 975) 10 :=
  stoppingTime_of_classCertificate certificate_975 m

/-- Checked base and every prefix for input 977. -/
theorem certificate_977 : classCertificateB 2 977 = true := by
  decide

/-- The same exact first-descent time holds on an infinite dyadic ray. -/
theorem ray_977 (m : Nat) : stoppingTime (2 ^ 2 * m + 977) 2 :=
  stoppingTime_of_classCertificate certificate_977 m

/-- Checked base and every prefix for input 979. -/
theorem certificate_979 : classCertificateB 4 979 = true := by
  decide

/-- The same exact first-descent time holds on an infinite dyadic ray. -/
theorem ray_979 (m : Nat) : stoppingTime (2 ^ 4 * m + 979) 4 :=
  stoppingTime_of_classCertificate certificate_979 m

/-- Checked base and every prefix for input 981. -/
theorem certificate_981 : classCertificateB 2 981 = true := by
  decide

/-- The same exact first-descent time holds on an infinite dyadic ray. -/
theorem ray_981 (m : Nat) : stoppingTime (2 ^ 2 * m + 981) 2 :=
  stoppingTime_of_classCertificate certificate_981 m

/-- Checked base and every prefix for input 983. -/
theorem certificate_983 : classCertificateB 5 983 = true := by
  decide

/-- The same exact first-descent time holds on an infinite dyadic ray. -/
theorem ray_983 (m : Nat) : stoppingTime (2 ^ 5 * m + 983) 5 :=
  stoppingTime_of_classCertificate certificate_983 m

/-- Checked base and every prefix for input 985. -/
theorem certificate_985 : classCertificateB 2 985 = true := by
  decide

/-- The same exact first-descent time holds on an infinite dyadic ray. -/
theorem ray_985 (m : Nat) : stoppingTime (2 ^ 2 * m + 985) 2 :=
  stoppingTime_of_classCertificate certificate_985 m

/-- Checked base and every prefix for input 987. -/
theorem certificate_987 : classCertificateB 8 987 = true := by
  decide

/-- The same exact first-descent time holds on an infinite dyadic ray. -/
theorem ray_987 (m : Nat) : stoppingTime (2 ^ 8 * m + 987) 8 :=
  stoppingTime_of_classCertificate certificate_987 m

/-- Checked base and every prefix for input 989. -/
theorem certificate_989 : classCertificateB 2 989 = true := by
  decide

/-- The same exact first-descent time holds on an infinite dyadic ray. -/
theorem ray_989 (m : Nat) : stoppingTime (2 ^ 2 * m + 989) 2 :=
  stoppingTime_of_classCertificate certificate_989 m

/-- Checked base and every prefix for input 991. -/
theorem certificate_991 : classCertificateB 26 991 = true := by
  decide

/-- The same exact first-descent time holds on an infinite dyadic ray. -/
theorem ray_991 (m : Nat) : stoppingTime (2 ^ 26 * m + 991) 26 :=
  stoppingTime_of_classCertificate certificate_991 m

/-- Checked base and every prefix for input 993. -/
theorem certificate_993 : classCertificateB 2 993 = true := by
  decide

/-- The same exact first-descent time holds on an infinite dyadic ray. -/
theorem ray_993 (m : Nat) : stoppingTime (2 ^ 2 * m + 993) 2 :=
  stoppingTime_of_classCertificate certificate_993 m

/-- Checked base and every prefix for input 995. -/
theorem certificate_995 : classCertificateB 4 995 = true := by
  decide

/-- The same exact first-descent time holds on an infinite dyadic ray. -/
theorem ray_995 (m : Nat) : stoppingTime (2 ^ 4 * m + 995) 4 :=
  stoppingTime_of_classCertificate certificate_995 m

/-- Checked base and every prefix for input 997. -/
theorem certificate_997 : classCertificateB 2 997 = true := by
  decide

/-- The same exact first-descent time holds on an infinite dyadic ray. -/
theorem ray_997 (m : Nat) : stoppingTime (2 ^ 2 * m + 997) 2 :=
  stoppingTime_of_classCertificate certificate_997 m

/-- Checked base and every prefix for input 999. -/
theorem certificate_999 : classCertificateB 10 999 = true := by
  decide

/-- The same exact first-descent time holds on an infinite dyadic ray. -/
theorem ray_999 (m : Nat) : stoppingTime (2 ^ 10 * m + 999) 10 :=
  stoppingTime_of_classCertificate certificate_999 m

/-- Checked base and every prefix for input 1001. -/
theorem certificate_1001 : classCertificateB 2 1001 = true := by
  decide

/-- The same exact first-descent time holds on an infinite dyadic ray. -/
theorem ray_1001 (m : Nat) : stoppingTime (2 ^ 2 * m + 1001) 2 :=
  stoppingTime_of_classCertificate certificate_1001 m

/-- Checked base and every prefix for input 1003. -/
theorem certificate_1003 : classCertificateB 5 1003 = true := by
  decide

/-- The same exact first-descent time holds on an infinite dyadic ray. -/
theorem ray_1003 (m : Nat) : stoppingTime (2 ^ 5 * m + 1003) 5 :=
  stoppingTime_of_classCertificate certificate_1003 m

/-- Checked base and every prefix for input 1005. -/
theorem certificate_1005 : classCertificateB 2 1005 = true := by
  decide

/-- The same exact first-descent time holds on an infinite dyadic ray. -/
theorem ray_1005 (m : Nat) : stoppingTime (2 ^ 2 * m + 1005) 2 :=
  stoppingTime_of_classCertificate certificate_1005 m

/-- Exhaustive coverage of the odd inputs in this batch, with no gaps. -/
theorem coverage : CertifiedRange 939 1007 := by
  intro n hlo hhi hodd
  have hn : n = 939 ∨ n = 941 ∨ n = 943 ∨ n = 945 ∨ n = 947 ∨ n = 949 ∨ n = 951 ∨ n = 953 ∨ n = 955 ∨ n = 957 ∨ n = 959 ∨ n = 961 ∨ n = 963 ∨ n = 965 ∨ n = 967 ∨ n = 969 ∨ n = 971 ∨ n = 973 ∨ n = 975 ∨ n = 977 ∨ n = 979 ∨ n = 981 ∨ n = 983 ∨ n = 985 ∨ n = 987 ∨ n = 989 ∨ n = 991 ∨ n = 993 ∨ n = 995 ∨ n = 997 ∨ n = 999 ∨ n = 1001 ∨ n = 1003 ∨ n = 1005 := by omega
  rcases hn with h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h
  · subst n
    exact ⟨5, witness_of_certificate certificate_939⟩
  · subst n
    exact ⟨2, witness_of_certificate certificate_941⟩
  · subst n
    exact ⟨8, witness_of_certificate certificate_943⟩
  · subst n
    exact ⟨2, witness_of_certificate certificate_945⟩
  · subst n
    exact ⟨4, witness_of_certificate certificate_947⟩
  · subst n
    exact ⟨2, witness_of_certificate certificate_949⟩
  · subst n
    exact ⟨5, witness_of_certificate certificate_951⟩
  · subst n
    exact ⟨2, witness_of_certificate certificate_953⟩
  · subst n
    exact ⟨7, witness_of_certificate certificate_955⟩
  · subst n
    exact ⟨2, witness_of_certificate certificate_957⟩
  · subst n
    exact ⟨21, witness_of_certificate certificate_959⟩
  · subst n
    exact ⟨2, witness_of_certificate certificate_961⟩
  · subst n
    exact ⟨4, witness_of_certificate certificate_963⟩
  · subst n
    exact ⟨2, witness_of_certificate certificate_965⟩
  · subst n
    exact ⟨8, witness_of_certificate certificate_967⟩
  · subst n
    exact ⟨2, witness_of_certificate certificate_969⟩
  · subst n
    exact ⟨5, witness_of_certificate certificate_971⟩
  · subst n
    exact ⟨2, witness_of_certificate certificate_973⟩
  · subst n
    exact ⟨10, witness_of_certificate certificate_975⟩
  · subst n
    exact ⟨2, witness_of_certificate certificate_977⟩
  · subst n
    exact ⟨4, witness_of_certificate certificate_979⟩
  · subst n
    exact ⟨2, witness_of_certificate certificate_981⟩
  · subst n
    exact ⟨5, witness_of_certificate certificate_983⟩
  · subst n
    exact ⟨2, witness_of_certificate certificate_985⟩
  · subst n
    exact ⟨8, witness_of_certificate certificate_987⟩
  · subst n
    exact ⟨2, witness_of_certificate certificate_989⟩
  · subst n
    exact ⟨26, witness_of_certificate certificate_991⟩
  · subst n
    exact ⟨2, witness_of_certificate certificate_993⟩
  · subst n
    exact ⟨4, witness_of_certificate certificate_995⟩
  · subst n
    exact ⟨2, witness_of_certificate certificate_997⟩
  · subst n
    exact ⟨10, witness_of_certificate certificate_999⟩
  · subst n
    exact ⟨2, witness_of_certificate certificate_1001⟩
  · subst n
    exact ⟨5, witness_of_certificate certificate_1003⟩
  · subst n
    exact ⟨2, witness_of_certificate certificate_1005⟩

end Collatz.Research.CoefficientDescent.Batch015
