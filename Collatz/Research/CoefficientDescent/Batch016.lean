import Collatz.Research.CoefficientDescent.Basic

namespace Collatz.Research.CoefficientDescent.Batch016

open FirstDescentClass

set_option maxRecDepth 20000
set_option maxHeartbeats 0

/-- Checked base and every prefix for input 1007. -/
theorem certificate_1007 : classCertificateB 21 1007 = true := by
  decide

/-- The same exact first-descent time holds on an infinite dyadic ray. -/
theorem ray_1007 (m : Nat) : stoppingTime (2 ^ 21 * m + 1007) 21 :=
  stoppingTime_of_classCertificate certificate_1007 m

/-- Checked base and every prefix for input 1009. -/
theorem certificate_1009 : classCertificateB 2 1009 = true := by
  decide

/-- The same exact first-descent time holds on an infinite dyadic ray. -/
theorem ray_1009 (m : Nat) : stoppingTime (2 ^ 2 * m + 1009) 2 :=
  stoppingTime_of_classCertificate certificate_1009 m

/-- Checked base and every prefix for input 1011. -/
theorem certificate_1011 : classCertificateB 4 1011 = true := by
  decide

/-- The same exact first-descent time holds on an infinite dyadic ray. -/
theorem ray_1011 (m : Nat) : stoppingTime (2 ^ 4 * m + 1011) 4 :=
  stoppingTime_of_classCertificate certificate_1011 m

/-- Checked base and every prefix for input 1013. -/
theorem certificate_1013 : classCertificateB 2 1013 = true := by
  decide

/-- The same exact first-descent time holds on an infinite dyadic ray. -/
theorem ray_1013 (m : Nat) : stoppingTime (2 ^ 2 * m + 1013) 2 :=
  stoppingTime_of_classCertificate certificate_1013 m

/-- Checked base and every prefix for input 1015. -/
theorem certificate_1015 : classCertificateB 5 1015 = true := by
  decide

/-- The same exact first-descent time holds on an infinite dyadic ray. -/
theorem ray_1015 (m : Nat) : stoppingTime (2 ^ 5 * m + 1015) 5 :=
  stoppingTime_of_classCertificate certificate_1015 m

/-- Checked base and every prefix for input 1017. -/
theorem certificate_1017 : classCertificateB 2 1017 = true := by
  decide

/-- The same exact first-descent time holds on an infinite dyadic ray. -/
theorem ray_1017 (m : Nat) : stoppingTime (2 ^ 2 * m + 1017) 2 :=
  stoppingTime_of_classCertificate certificate_1017 m

/-- Checked base and every prefix for input 1019. -/
theorem certificate_1019 : classCertificateB 12 1019 = true := by
  decide

/-- The same exact first-descent time holds on an infinite dyadic ray. -/
theorem ray_1019 (m : Nat) : stoppingTime (2 ^ 12 * m + 1019) 12 :=
  stoppingTime_of_classCertificate certificate_1019 m

/-- Checked base and every prefix for input 1021. -/
theorem certificate_1021 : classCertificateB 2 1021 = true := by
  decide

/-- The same exact first-descent time holds on an infinite dyadic ray. -/
theorem ray_1021 (m : Nat) : stoppingTime (2 ^ 2 * m + 1021) 2 :=
  stoppingTime_of_classCertificate certificate_1021 m

/-- Checked base and every prefix for input 1023. -/
theorem certificate_1023 : classCertificateB 18 1023 = true := by
  decide

/-- The same exact first-descent time holds on an infinite dyadic ray. -/
theorem ray_1023 (m : Nat) : stoppingTime (2 ^ 18 * m + 1023) 18 :=
  stoppingTime_of_classCertificate certificate_1023 m

/-- Checked base and every prefix for input 1025. -/
theorem certificate_1025 : classCertificateB 2 1025 = true := by
  decide

/-- The same exact first-descent time holds on an infinite dyadic ray. -/
theorem ray_1025 (m : Nat) : stoppingTime (2 ^ 2 * m + 1025) 2 :=
  stoppingTime_of_classCertificate certificate_1025 m

/-- Checked base and every prefix for input 1027. -/
theorem certificate_1027 : classCertificateB 4 1027 = true := by
  decide

/-- The same exact first-descent time holds on an infinite dyadic ray. -/
theorem ray_1027 (m : Nat) : stoppingTime (2 ^ 4 * m + 1027) 4 :=
  stoppingTime_of_classCertificate certificate_1027 m

/-- Checked base and every prefix for input 1029. -/
theorem certificate_1029 : classCertificateB 2 1029 = true := by
  decide

/-- The same exact first-descent time holds on an infinite dyadic ray. -/
theorem ray_1029 (m : Nat) : stoppingTime (2 ^ 2 * m + 1029) 2 :=
  stoppingTime_of_classCertificate certificate_1029 m

/-- Checked base and every prefix for input 1031. -/
theorem certificate_1031 : classCertificateB 7 1031 = true := by
  decide

/-- The same exact first-descent time holds on an infinite dyadic ray. -/
theorem ray_1031 (m : Nat) : stoppingTime (2 ^ 7 * m + 1031) 7 :=
  stoppingTime_of_classCertificate certificate_1031 m

/-- Checked base and every prefix for input 1033. -/
theorem certificate_1033 : classCertificateB 2 1033 = true := by
  decide

/-- The same exact first-descent time holds on an infinite dyadic ray. -/
theorem ray_1033 (m : Nat) : stoppingTime (2 ^ 2 * m + 1033) 2 :=
  stoppingTime_of_classCertificate certificate_1033 m

/-- Checked base and every prefix for input 1035. -/
theorem certificate_1035 : classCertificateB 5 1035 = true := by
  decide

/-- The same exact first-descent time holds on an infinite dyadic ray. -/
theorem ray_1035 (m : Nat) : stoppingTime (2 ^ 5 * m + 1035) 5 :=
  stoppingTime_of_classCertificate certificate_1035 m

/-- Checked base and every prefix for input 1037. -/
theorem certificate_1037 : classCertificateB 2 1037 = true := by
  decide

/-- The same exact first-descent time holds on an infinite dyadic ray. -/
theorem ray_1037 (m : Nat) : stoppingTime (2 ^ 2 * m + 1037) 2 :=
  stoppingTime_of_classCertificate certificate_1037 m

/-- Checked base and every prefix for input 1039. -/
theorem certificate_1039 : classCertificateB 7 1039 = true := by
  decide

/-- The same exact first-descent time holds on an infinite dyadic ray. -/
theorem ray_1039 (m : Nat) : stoppingTime (2 ^ 7 * m + 1039) 7 :=
  stoppingTime_of_classCertificate certificate_1039 m

/-- Checked base and every prefix for input 1041. -/
theorem certificate_1041 : classCertificateB 2 1041 = true := by
  decide

/-- The same exact first-descent time holds on an infinite dyadic ray. -/
theorem ray_1041 (m : Nat) : stoppingTime (2 ^ 2 * m + 1041) 2 :=
  stoppingTime_of_classCertificate certificate_1041 m

/-- Checked base and every prefix for input 1043. -/
theorem certificate_1043 : classCertificateB 4 1043 = true := by
  decide

/-- The same exact first-descent time holds on an infinite dyadic ray. -/
theorem ray_1043 (m : Nat) : stoppingTime (2 ^ 4 * m + 1043) 4 :=
  stoppingTime_of_classCertificate certificate_1043 m

/-- Checked base and every prefix for input 1045. -/
theorem certificate_1045 : classCertificateB 2 1045 = true := by
  decide

/-- The same exact first-descent time holds on an infinite dyadic ray. -/
theorem ray_1045 (m : Nat) : stoppingTime (2 ^ 2 * m + 1045) 2 :=
  stoppingTime_of_classCertificate certificate_1045 m

/-- Checked base and every prefix for input 1047. -/
theorem certificate_1047 : classCertificateB 5 1047 = true := by
  decide

/-- The same exact first-descent time holds on an infinite dyadic ray. -/
theorem ray_1047 (m : Nat) : stoppingTime (2 ^ 5 * m + 1047) 5 :=
  stoppingTime_of_classCertificate certificate_1047 m

/-- Checked base and every prefix for input 1049. -/
theorem certificate_1049 : classCertificateB 2 1049 = true := by
  decide

/-- The same exact first-descent time holds on an infinite dyadic ray. -/
theorem ray_1049 (m : Nat) : stoppingTime (2 ^ 2 * m + 1049) 2 :=
  stoppingTime_of_classCertificate certificate_1049 m

/-- Checked base and every prefix for input 1051. -/
theorem certificate_1051 : classCertificateB 24 1051 = true := by
  decide

/-- The same exact first-descent time holds on an infinite dyadic ray. -/
theorem ray_1051 (m : Nat) : stoppingTime (2 ^ 24 * m + 1051) 24 :=
  stoppingTime_of_classCertificate certificate_1051 m

/-- Checked base and every prefix for input 1053. -/
theorem certificate_1053 : classCertificateB 2 1053 = true := by
  decide

/-- The same exact first-descent time holds on an infinite dyadic ray. -/
theorem ray_1053 (m : Nat) : stoppingTime (2 ^ 2 * m + 1053) 2 :=
  stoppingTime_of_classCertificate certificate_1053 m

/-- Checked base and every prefix for input 1055. -/
theorem certificate_1055 : classCertificateB 80 1055 = true := by
  decide

/-- The same exact first-descent time holds on an infinite dyadic ray. -/
theorem ray_1055 (m : Nat) : stoppingTime (2 ^ 80 * m + 1055) 80 :=
  stoppingTime_of_classCertificate certificate_1055 m

/-- Checked base and every prefix for input 1057. -/
theorem certificate_1057 : classCertificateB 2 1057 = true := by
  decide

/-- The same exact first-descent time holds on an infinite dyadic ray. -/
theorem ray_1057 (m : Nat) : stoppingTime (2 ^ 2 * m + 1057) 2 :=
  stoppingTime_of_classCertificate certificate_1057 m

/-- Checked base and every prefix for input 1059. -/
theorem certificate_1059 : classCertificateB 4 1059 = true := by
  decide

/-- The same exact first-descent time holds on an infinite dyadic ray. -/
theorem ray_1059 (m : Nat) : stoppingTime (2 ^ 4 * m + 1059) 4 :=
  stoppingTime_of_classCertificate certificate_1059 m

/-- Checked base and every prefix for input 1061. -/
theorem certificate_1061 : classCertificateB 2 1061 = true := by
  decide

/-- The same exact first-descent time holds on an infinite dyadic ray. -/
theorem ray_1061 (m : Nat) : stoppingTime (2 ^ 2 * m + 1061) 2 :=
  stoppingTime_of_classCertificate certificate_1061 m

/-- Checked base and every prefix for input 1063. -/
theorem certificate_1063 : classCertificateB 8 1063 = true := by
  decide

/-- The same exact first-descent time holds on an infinite dyadic ray. -/
theorem ray_1063 (m : Nat) : stoppingTime (2 ^ 8 * m + 1063) 8 :=
  stoppingTime_of_classCertificate certificate_1063 m

/-- Checked base and every prefix for input 1065. -/
theorem certificate_1065 : classCertificateB 2 1065 = true := by
  decide

/-- The same exact first-descent time holds on an infinite dyadic ray. -/
theorem ray_1065 (m : Nat) : stoppingTime (2 ^ 2 * m + 1065) 2 :=
  stoppingTime_of_classCertificate certificate_1065 m

/-- Checked base and every prefix for input 1067. -/
theorem certificate_1067 : classCertificateB 5 1067 = true := by
  decide

/-- The same exact first-descent time holds on an infinite dyadic ray. -/
theorem ray_1067 (m : Nat) : stoppingTime (2 ^ 5 * m + 1067) 5 :=
  stoppingTime_of_classCertificate certificate_1067 m

/-- Checked base and every prefix for input 1069. -/
theorem certificate_1069 : classCertificateB 2 1069 = true := by
  decide

/-- The same exact first-descent time holds on an infinite dyadic ray. -/
theorem ray_1069 (m : Nat) : stoppingTime (2 ^ 2 * m + 1069) 2 :=
  stoppingTime_of_classCertificate certificate_1069 m

/-- Checked base and every prefix for input 1071. -/
theorem certificate_1071 : classCertificateB 13 1071 = true := by
  decide

/-- The same exact first-descent time holds on an infinite dyadic ray. -/
theorem ray_1071 (m : Nat) : stoppingTime (2 ^ 13 * m + 1071) 13 :=
  stoppingTime_of_classCertificate certificate_1071 m

/-- Exhaustive coverage of the odd inputs in this batch, with no gaps. -/
theorem coverage : CertifiedRange 1007 1073 := by
  intro n hlo hhi hodd
  have hn : n = 1007 ∨ n = 1009 ∨ n = 1011 ∨ n = 1013 ∨ n = 1015 ∨ n = 1017 ∨ n = 1019 ∨ n = 1021 ∨ n = 1023 ∨ n = 1025 ∨ n = 1027 ∨ n = 1029 ∨ n = 1031 ∨ n = 1033 ∨ n = 1035 ∨ n = 1037 ∨ n = 1039 ∨ n = 1041 ∨ n = 1043 ∨ n = 1045 ∨ n = 1047 ∨ n = 1049 ∨ n = 1051 ∨ n = 1053 ∨ n = 1055 ∨ n = 1057 ∨ n = 1059 ∨ n = 1061 ∨ n = 1063 ∨ n = 1065 ∨ n = 1067 ∨ n = 1069 ∨ n = 1071 := by omega
  rcases hn with h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h
  · subst n
    exact ⟨21, witness_of_certificate certificate_1007⟩
  · subst n
    exact ⟨2, witness_of_certificate certificate_1009⟩
  · subst n
    exact ⟨4, witness_of_certificate certificate_1011⟩
  · subst n
    exact ⟨2, witness_of_certificate certificate_1013⟩
  · subst n
    exact ⟨5, witness_of_certificate certificate_1015⟩
  · subst n
    exact ⟨2, witness_of_certificate certificate_1017⟩
  · subst n
    exact ⟨12, witness_of_certificate certificate_1019⟩
  · subst n
    exact ⟨2, witness_of_certificate certificate_1021⟩
  · subst n
    exact ⟨18, witness_of_certificate certificate_1023⟩
  · subst n
    exact ⟨2, witness_of_certificate certificate_1025⟩
  · subst n
    exact ⟨4, witness_of_certificate certificate_1027⟩
  · subst n
    exact ⟨2, witness_of_certificate certificate_1029⟩
  · subst n
    exact ⟨7, witness_of_certificate certificate_1031⟩
  · subst n
    exact ⟨2, witness_of_certificate certificate_1033⟩
  · subst n
    exact ⟨5, witness_of_certificate certificate_1035⟩
  · subst n
    exact ⟨2, witness_of_certificate certificate_1037⟩
  · subst n
    exact ⟨7, witness_of_certificate certificate_1039⟩
  · subst n
    exact ⟨2, witness_of_certificate certificate_1041⟩
  · subst n
    exact ⟨4, witness_of_certificate certificate_1043⟩
  · subst n
    exact ⟨2, witness_of_certificate certificate_1045⟩
  · subst n
    exact ⟨5, witness_of_certificate certificate_1047⟩
  · subst n
    exact ⟨2, witness_of_certificate certificate_1049⟩
  · subst n
    exact ⟨24, witness_of_certificate certificate_1051⟩
  · subst n
    exact ⟨2, witness_of_certificate certificate_1053⟩
  · subst n
    exact ⟨80, witness_of_certificate certificate_1055⟩
  · subst n
    exact ⟨2, witness_of_certificate certificate_1057⟩
  · subst n
    exact ⟨4, witness_of_certificate certificate_1059⟩
  · subst n
    exact ⟨2, witness_of_certificate certificate_1061⟩
  · subst n
    exact ⟨8, witness_of_certificate certificate_1063⟩
  · subst n
    exact ⟨2, witness_of_certificate certificate_1065⟩
  · subst n
    exact ⟨5, witness_of_certificate certificate_1067⟩
  · subst n
    exact ⟨2, witness_of_certificate certificate_1069⟩
  · subst n
    exact ⟨13, witness_of_certificate certificate_1071⟩

end Collatz.Research.CoefficientDescent.Batch016
