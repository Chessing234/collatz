import Collatz.Research.CoefficientDescent.Basic

namespace Collatz.Research.CoefficientDescent.Batch017

open FirstDescentClass

set_option maxRecDepth 20000
set_option maxHeartbeats 0

/-- Checked base and every prefix for input 1073. -/
theorem certificate_1073 : classCertificateB 2 1073 = true := by
  decide

/-- The same exact first-descent time holds on an infinite dyadic ray. -/
theorem ray_1073 (m : Nat) : stoppingTime (2 ^ 2 * m + 1073) 2 :=
  stoppingTime_of_classCertificate certificate_1073 m

/-- Checked base and every prefix for input 1075. -/
theorem certificate_1075 : classCertificateB 4 1075 = true := by
  decide

/-- The same exact first-descent time holds on an infinite dyadic ray. -/
theorem ray_1075 (m : Nat) : stoppingTime (2 ^ 4 * m + 1075) 4 :=
  stoppingTime_of_classCertificate certificate_1075 m

/-- Checked base and every prefix for input 1077. -/
theorem certificate_1077 : classCertificateB 2 1077 = true := by
  decide

/-- The same exact first-descent time holds on an infinite dyadic ray. -/
theorem ray_1077 (m : Nat) : stoppingTime (2 ^ 2 * m + 1077) 2 :=
  stoppingTime_of_classCertificate certificate_1077 m

/-- Checked base and every prefix for input 1079. -/
theorem certificate_1079 : classCertificateB 5 1079 = true := by
  decide

/-- The same exact first-descent time holds on an infinite dyadic ray. -/
theorem ray_1079 (m : Nat) : stoppingTime (2 ^ 5 * m + 1079) 5 :=
  stoppingTime_of_classCertificate certificate_1079 m

/-- Checked base and every prefix for input 1081. -/
theorem certificate_1081 : classCertificateB 2 1081 = true := by
  decide

/-- The same exact first-descent time holds on an infinite dyadic ray. -/
theorem ray_1081 (m : Nat) : stoppingTime (2 ^ 2 * m + 1081) 2 :=
  stoppingTime_of_classCertificate certificate_1081 m

/-- Checked base and every prefix for input 1083. -/
theorem certificate_1083 : classCertificateB 7 1083 = true := by
  decide

/-- The same exact first-descent time holds on an infinite dyadic ray. -/
theorem ray_1083 (m : Nat) : stoppingTime (2 ^ 7 * m + 1083) 7 :=
  stoppingTime_of_classCertificate certificate_1083 m

/-- Checked base and every prefix for input 1085. -/
theorem certificate_1085 : classCertificateB 2 1085 = true := by
  decide

/-- The same exact first-descent time holds on an infinite dyadic ray. -/
theorem ray_1085 (m : Nat) : stoppingTime (2 ^ 2 * m + 1085) 2 :=
  stoppingTime_of_classCertificate certificate_1085 m

/-- Checked base and every prefix for input 1087. -/
theorem certificate_1087 : classCertificateB 12 1087 = true := by
  decide

/-- The same exact first-descent time holds on an infinite dyadic ray. -/
theorem ray_1087 (m : Nat) : stoppingTime (2 ^ 12 * m + 1087) 12 :=
  stoppingTime_of_classCertificate certificate_1087 m

/-- Checked base and every prefix for input 1089. -/
theorem certificate_1089 : classCertificateB 2 1089 = true := by
  decide

/-- The same exact first-descent time holds on an infinite dyadic ray. -/
theorem ray_1089 (m : Nat) : stoppingTime (2 ^ 2 * m + 1089) 2 :=
  stoppingTime_of_classCertificate certificate_1089 m

/-- Checked base and every prefix for input 1091. -/
theorem certificate_1091 : classCertificateB 4 1091 = true := by
  decide

/-- The same exact first-descent time holds on an infinite dyadic ray. -/
theorem ray_1091 (m : Nat) : stoppingTime (2 ^ 4 * m + 1091) 4 :=
  stoppingTime_of_classCertificate certificate_1091 m

/-- Checked base and every prefix for input 1093. -/
theorem certificate_1093 : classCertificateB 2 1093 = true := by
  decide

/-- The same exact first-descent time holds on an infinite dyadic ray. -/
theorem ray_1093 (m : Nat) : stoppingTime (2 ^ 2 * m + 1093) 2 :=
  stoppingTime_of_classCertificate certificate_1093 m

/-- Checked base and every prefix for input 1095. -/
theorem certificate_1095 : classCertificateB 15 1095 = true := by
  decide

/-- The same exact first-descent time holds on an infinite dyadic ray. -/
theorem ray_1095 (m : Nat) : stoppingTime (2 ^ 15 * m + 1095) 15 :=
  stoppingTime_of_classCertificate certificate_1095 m

/-- Checked base and every prefix for input 1097. -/
theorem certificate_1097 : classCertificateB 2 1097 = true := by
  decide

/-- The same exact first-descent time holds on an infinite dyadic ray. -/
theorem ray_1097 (m : Nat) : stoppingTime (2 ^ 2 * m + 1097) 2 :=
  stoppingTime_of_classCertificate certificate_1097 m

/-- Checked base and every prefix for input 1099. -/
theorem certificate_1099 : classCertificateB 5 1099 = true := by
  decide

/-- The same exact first-descent time holds on an infinite dyadic ray. -/
theorem ray_1099 (m : Nat) : stoppingTime (2 ^ 5 * m + 1099) 5 :=
  stoppingTime_of_classCertificate certificate_1099 m

/-- Checked base and every prefix for input 1101. -/
theorem certificate_1101 : classCertificateB 2 1101 = true := by
  decide

/-- The same exact first-descent time holds on an infinite dyadic ray. -/
theorem ray_1101 (m : Nat) : stoppingTime (2 ^ 2 * m + 1101) 2 :=
  stoppingTime_of_classCertificate certificate_1101 m

/-- Checked base and every prefix for input 1103. -/
theorem certificate_1103 : classCertificateB 8 1103 = true := by
  decide

/-- The same exact first-descent time holds on an infinite dyadic ray. -/
theorem ray_1103 (m : Nat) : stoppingTime (2 ^ 8 * m + 1103) 8 :=
  stoppingTime_of_classCertificate certificate_1103 m

/-- Checked base and every prefix for input 1105. -/
theorem certificate_1105 : classCertificateB 2 1105 = true := by
  decide

/-- The same exact first-descent time holds on an infinite dyadic ray. -/
theorem ray_1105 (m : Nat) : stoppingTime (2 ^ 2 * m + 1105) 2 :=
  stoppingTime_of_classCertificate certificate_1105 m

/-- Checked base and every prefix for input 1107. -/
theorem certificate_1107 : classCertificateB 4 1107 = true := by
  decide

/-- The same exact first-descent time holds on an infinite dyadic ray. -/
theorem ray_1107 (m : Nat) : stoppingTime (2 ^ 4 * m + 1107) 4 :=
  stoppingTime_of_classCertificate certificate_1107 m

/-- Checked base and every prefix for input 1109. -/
theorem certificate_1109 : classCertificateB 2 1109 = true := by
  decide

/-- The same exact first-descent time holds on an infinite dyadic ray. -/
theorem ray_1109 (m : Nat) : stoppingTime (2 ^ 2 * m + 1109) 2 :=
  stoppingTime_of_classCertificate certificate_1109 m

/-- Checked base and every prefix for input 1111. -/
theorem certificate_1111 : classCertificateB 5 1111 = true := by
  decide

/-- The same exact first-descent time holds on an infinite dyadic ray. -/
theorem ray_1111 (m : Nat) : stoppingTime (2 ^ 5 * m + 1111) 5 :=
  stoppingTime_of_classCertificate certificate_1111 m

/-- Checked base and every prefix for input 1113. -/
theorem certificate_1113 : classCertificateB 2 1113 = true := by
  decide

/-- The same exact first-descent time holds on an infinite dyadic ray. -/
theorem ray_1113 (m : Nat) : stoppingTime (2 ^ 2 * m + 1113) 2 :=
  stoppingTime_of_classCertificate certificate_1113 m

/-- Checked base and every prefix for input 1115. -/
theorem certificate_1115 : classCertificateB 23 1115 = true := by
  decide

/-- The same exact first-descent time holds on an infinite dyadic ray. -/
theorem ray_1115 (m : Nat) : stoppingTime (2 ^ 23 * m + 1115) 23 :=
  stoppingTime_of_classCertificate certificate_1115 m

/-- Checked base and every prefix for input 1117. -/
theorem certificate_1117 : classCertificateB 2 1117 = true := by
  decide

/-- The same exact first-descent time holds on an infinite dyadic ray. -/
theorem ray_1117 (m : Nat) : stoppingTime (2 ^ 2 * m + 1117) 2 :=
  stoppingTime_of_classCertificate certificate_1117 m

/-- Checked base and every prefix for input 1119. -/
theorem certificate_1119 : classCertificateB 8 1119 = true := by
  decide

/-- The same exact first-descent time holds on an infinite dyadic ray. -/
theorem ray_1119 (m : Nat) : stoppingTime (2 ^ 8 * m + 1119) 8 :=
  stoppingTime_of_classCertificate certificate_1119 m

/-- Checked base and every prefix for input 1121. -/
theorem certificate_1121 : classCertificateB 2 1121 = true := by
  decide

/-- The same exact first-descent time holds on an infinite dyadic ray. -/
theorem ray_1121 (m : Nat) : stoppingTime (2 ^ 2 * m + 1121) 2 :=
  stoppingTime_of_classCertificate certificate_1121 m

/-- Checked base and every prefix for input 1123. -/
theorem certificate_1123 : classCertificateB 4 1123 = true := by
  decide

/-- The same exact first-descent time holds on an infinite dyadic ray. -/
theorem ray_1123 (m : Nat) : stoppingTime (2 ^ 4 * m + 1123) 4 :=
  stoppingTime_of_classCertificate certificate_1123 m

/-- Checked base and every prefix for input 1125. -/
theorem certificate_1125 : classCertificateB 2 1125 = true := by
  decide

/-- The same exact first-descent time holds on an infinite dyadic ray. -/
theorem ray_1125 (m : Nat) : stoppingTime (2 ^ 2 * m + 1125) 2 :=
  stoppingTime_of_classCertificate certificate_1125 m

/-- Checked base and every prefix for input 1127. -/
theorem certificate_1127 : classCertificateB 20 1127 = true := by
  decide

/-- The same exact first-descent time holds on an infinite dyadic ray. -/
theorem ray_1127 (m : Nat) : stoppingTime (2 ^ 20 * m + 1127) 20 :=
  stoppingTime_of_classCertificate certificate_1127 m

/-- Checked base and every prefix for input 1129. -/
theorem certificate_1129 : classCertificateB 2 1129 = true := by
  decide

/-- The same exact first-descent time holds on an infinite dyadic ray. -/
theorem ray_1129 (m : Nat) : stoppingTime (2 ^ 2 * m + 1129) 2 :=
  stoppingTime_of_classCertificate certificate_1129 m

/-- Checked base and every prefix for input 1131. -/
theorem certificate_1131 : classCertificateB 5 1131 = true := by
  decide

/-- The same exact first-descent time holds on an infinite dyadic ray. -/
theorem ray_1131 (m : Nat) : stoppingTime (2 ^ 5 * m + 1131) 5 :=
  stoppingTime_of_classCertificate certificate_1131 m

/-- Checked base and every prefix for input 1133. -/
theorem certificate_1133 : classCertificateB 2 1133 = true := by
  decide

/-- The same exact first-descent time holds on an infinite dyadic ray. -/
theorem ray_1133 (m : Nat) : stoppingTime (2 ^ 2 * m + 1133) 2 :=
  stoppingTime_of_classCertificate certificate_1133 m

/-- Checked base and every prefix for input 1135. -/
theorem certificate_1135 : classCertificateB 13 1135 = true := by
  decide

/-- The same exact first-descent time holds on an infinite dyadic ray. -/
theorem ray_1135 (m : Nat) : stoppingTime (2 ^ 13 * m + 1135) 13 :=
  stoppingTime_of_classCertificate certificate_1135 m

/-- Checked base and every prefix for input 1137. -/
theorem certificate_1137 : classCertificateB 2 1137 = true := by
  decide

/-- The same exact first-descent time holds on an infinite dyadic ray. -/
theorem ray_1137 (m : Nat) : stoppingTime (2 ^ 2 * m + 1137) 2 :=
  stoppingTime_of_classCertificate certificate_1137 m

/-- Checked base and every prefix for input 1139. -/
theorem certificate_1139 : classCertificateB 4 1139 = true := by
  decide

/-- The same exact first-descent time holds on an infinite dyadic ray. -/
theorem ray_1139 (m : Nat) : stoppingTime (2 ^ 4 * m + 1139) 4 :=
  stoppingTime_of_classCertificate certificate_1139 m

/-- Exhaustive coverage of the odd inputs in this batch, with no gaps. -/
theorem coverage : CertifiedRange 1073 1141 := by
  intro n hlo hhi hodd
  have hn : n = 1073 ∨ n = 1075 ∨ n = 1077 ∨ n = 1079 ∨ n = 1081 ∨ n = 1083 ∨ n = 1085 ∨ n = 1087 ∨ n = 1089 ∨ n = 1091 ∨ n = 1093 ∨ n = 1095 ∨ n = 1097 ∨ n = 1099 ∨ n = 1101 ∨ n = 1103 ∨ n = 1105 ∨ n = 1107 ∨ n = 1109 ∨ n = 1111 ∨ n = 1113 ∨ n = 1115 ∨ n = 1117 ∨ n = 1119 ∨ n = 1121 ∨ n = 1123 ∨ n = 1125 ∨ n = 1127 ∨ n = 1129 ∨ n = 1131 ∨ n = 1133 ∨ n = 1135 ∨ n = 1137 ∨ n = 1139 := by omega
  rcases hn with h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h
  · subst n
    exact ⟨2, witness_of_certificate certificate_1073⟩
  · subst n
    exact ⟨4, witness_of_certificate certificate_1075⟩
  · subst n
    exact ⟨2, witness_of_certificate certificate_1077⟩
  · subst n
    exact ⟨5, witness_of_certificate certificate_1079⟩
  · subst n
    exact ⟨2, witness_of_certificate certificate_1081⟩
  · subst n
    exact ⟨7, witness_of_certificate certificate_1083⟩
  · subst n
    exact ⟨2, witness_of_certificate certificate_1085⟩
  · subst n
    exact ⟨12, witness_of_certificate certificate_1087⟩
  · subst n
    exact ⟨2, witness_of_certificate certificate_1089⟩
  · subst n
    exact ⟨4, witness_of_certificate certificate_1091⟩
  · subst n
    exact ⟨2, witness_of_certificate certificate_1093⟩
  · subst n
    exact ⟨15, witness_of_certificate certificate_1095⟩
  · subst n
    exact ⟨2, witness_of_certificate certificate_1097⟩
  · subst n
    exact ⟨5, witness_of_certificate certificate_1099⟩
  · subst n
    exact ⟨2, witness_of_certificate certificate_1101⟩
  · subst n
    exact ⟨8, witness_of_certificate certificate_1103⟩
  · subst n
    exact ⟨2, witness_of_certificate certificate_1105⟩
  · subst n
    exact ⟨4, witness_of_certificate certificate_1107⟩
  · subst n
    exact ⟨2, witness_of_certificate certificate_1109⟩
  · subst n
    exact ⟨5, witness_of_certificate certificate_1111⟩
  · subst n
    exact ⟨2, witness_of_certificate certificate_1113⟩
  · subst n
    exact ⟨23, witness_of_certificate certificate_1115⟩
  · subst n
    exact ⟨2, witness_of_certificate certificate_1117⟩
  · subst n
    exact ⟨8, witness_of_certificate certificate_1119⟩
  · subst n
    exact ⟨2, witness_of_certificate certificate_1121⟩
  · subst n
    exact ⟨4, witness_of_certificate certificate_1123⟩
  · subst n
    exact ⟨2, witness_of_certificate certificate_1125⟩
  · subst n
    exact ⟨20, witness_of_certificate certificate_1127⟩
  · subst n
    exact ⟨2, witness_of_certificate certificate_1129⟩
  · subst n
    exact ⟨5, witness_of_certificate certificate_1131⟩
  · subst n
    exact ⟨2, witness_of_certificate certificate_1133⟩
  · subst n
    exact ⟨13, witness_of_certificate certificate_1135⟩
  · subst n
    exact ⟨2, witness_of_certificate certificate_1137⟩
  · subst n
    exact ⟨4, witness_of_certificate certificate_1139⟩

end Collatz.Research.CoefficientDescent.Batch017
