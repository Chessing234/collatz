import Collatz.Research.CoefficientDescent.Basic

namespace Collatz.Research.CoefficientDescent.Batch062

open FirstDescentClass

set_option maxRecDepth 20000
set_option maxHeartbeats 0

/-- Checked base and every prefix for input 4087. -/
theorem certificate_4087 : classCertificateB 5 4087 = true := by
  decide

/-- The same exact first-descent time holds on an infinite dyadic ray. -/
theorem ray_4087 (m : Nat) : stoppingTime (2 ^ 5 * m + 4087) 5 :=
  stoppingTime_of_classCertificate certificate_4087 m

/-- Checked base and every prefix for input 4089. -/
theorem certificate_4089 : classCertificateB 2 4089 = true := by
  decide

/-- The same exact first-descent time holds on an infinite dyadic ray. -/
theorem ray_4089 (m : Nat) : stoppingTime (2 ^ 2 * m + 4089) 2 :=
  stoppingTime_of_classCertificate certificate_4089 m

/-- Checked base and every prefix for input 4091. -/
theorem certificate_4091 : classCertificateB 13 4091 = true := by
  decide

/-- The same exact first-descent time holds on an infinite dyadic ray. -/
theorem ray_4091 (m : Nat) : stoppingTime (2 ^ 13 * m + 4091) 13 :=
  stoppingTime_of_classCertificate certificate_4091 m

/-- Checked base and every prefix for input 4093. -/
theorem certificate_4093 : classCertificateB 2 4093 = true := by
  decide

/-- The same exact first-descent time holds on an infinite dyadic ray. -/
theorem ray_4093 (m : Nat) : stoppingTime (2 ^ 2 * m + 4093) 2 :=
  stoppingTime_of_classCertificate certificate_4093 m

/-- Checked base and every prefix for input 4095. -/
theorem certificate_4095 : classCertificateB 51 4095 = true := by
  decide

/-- The same exact first-descent time holds on an infinite dyadic ray. -/
theorem ray_4095 (m : Nat) : stoppingTime (2 ^ 51 * m + 4095) 51 :=
  stoppingTime_of_classCertificate certificate_4095 m

/-- Checked base and every prefix for input 4097. -/
theorem certificate_4097 : classCertificateB 2 4097 = true := by
  decide

/-- The same exact first-descent time holds on an infinite dyadic ray. -/
theorem ray_4097 (m : Nat) : stoppingTime (2 ^ 2 * m + 4097) 2 :=
  stoppingTime_of_classCertificate certificate_4097 m

/-- Checked base and every prefix for input 4099. -/
theorem certificate_4099 : classCertificateB 4 4099 = true := by
  decide

/-- The same exact first-descent time holds on an infinite dyadic ray. -/
theorem ray_4099 (m : Nat) : stoppingTime (2 ^ 4 * m + 4099) 4 :=
  stoppingTime_of_classCertificate certificate_4099 m

/-- Checked base and every prefix for input 4101. -/
theorem certificate_4101 : classCertificateB 2 4101 = true := by
  decide

/-- The same exact first-descent time holds on an infinite dyadic ray. -/
theorem ray_4101 (m : Nat) : stoppingTime (2 ^ 2 * m + 4101) 2 :=
  stoppingTime_of_classCertificate certificate_4101 m

/-- Checked base and every prefix for input 4103. -/
theorem certificate_4103 : classCertificateB 7 4103 = true := by
  decide

/-- The same exact first-descent time holds on an infinite dyadic ray. -/
theorem ray_4103 (m : Nat) : stoppingTime (2 ^ 7 * m + 4103) 7 :=
  stoppingTime_of_classCertificate certificate_4103 m

/-- Checked base and every prefix for input 4105. -/
theorem certificate_4105 : classCertificateB 2 4105 = true := by
  decide

/-- The same exact first-descent time holds on an infinite dyadic ray. -/
theorem ray_4105 (m : Nat) : stoppingTime (2 ^ 2 * m + 4105) 2 :=
  stoppingTime_of_classCertificate certificate_4105 m

/-- Checked base and every prefix for input 4107. -/
theorem certificate_4107 : classCertificateB 5 4107 = true := by
  decide

/-- The same exact first-descent time holds on an infinite dyadic ray. -/
theorem ray_4107 (m : Nat) : stoppingTime (2 ^ 5 * m + 4107) 5 :=
  stoppingTime_of_classCertificate certificate_4107 m

/-- Checked base and every prefix for input 4109. -/
theorem certificate_4109 : classCertificateB 2 4109 = true := by
  decide

/-- The same exact first-descent time holds on an infinite dyadic ray. -/
theorem ray_4109 (m : Nat) : stoppingTime (2 ^ 2 * m + 4109) 2 :=
  stoppingTime_of_classCertificate certificate_4109 m

/-- Checked base and every prefix for input 4111. -/
theorem certificate_4111 : classCertificateB 7 4111 = true := by
  decide

/-- The same exact first-descent time holds on an infinite dyadic ray. -/
theorem ray_4111 (m : Nat) : stoppingTime (2 ^ 7 * m + 4111) 7 :=
  stoppingTime_of_classCertificate certificate_4111 m

/-- Checked base and every prefix for input 4113. -/
theorem certificate_4113 : classCertificateB 2 4113 = true := by
  decide

/-- The same exact first-descent time holds on an infinite dyadic ray. -/
theorem ray_4113 (m : Nat) : stoppingTime (2 ^ 2 * m + 4113) 2 :=
  stoppingTime_of_classCertificate certificate_4113 m

/-- Checked base and every prefix for input 4115. -/
theorem certificate_4115 : classCertificateB 4 4115 = true := by
  decide

/-- The same exact first-descent time holds on an infinite dyadic ray. -/
theorem ray_4115 (m : Nat) : stoppingTime (2 ^ 4 * m + 4115) 4 :=
  stoppingTime_of_classCertificate certificate_4115 m

/-- Checked base and every prefix for input 4117. -/
theorem certificate_4117 : classCertificateB 2 4117 = true := by
  decide

/-- The same exact first-descent time holds on an infinite dyadic ray. -/
theorem ray_4117 (m : Nat) : stoppingTime (2 ^ 2 * m + 4117) 2 :=
  stoppingTime_of_classCertificate certificate_4117 m

/-- Checked base and every prefix for input 4119. -/
theorem certificate_4119 : classCertificateB 5 4119 = true := by
  decide

/-- The same exact first-descent time holds on an infinite dyadic ray. -/
theorem ray_4119 (m : Nat) : stoppingTime (2 ^ 5 * m + 4119) 5 :=
  stoppingTime_of_classCertificate certificate_4119 m

/-- Checked base and every prefix for input 4121. -/
theorem certificate_4121 : classCertificateB 2 4121 = true := by
  decide

/-- The same exact first-descent time holds on an infinite dyadic ray. -/
theorem ray_4121 (m : Nat) : stoppingTime (2 ^ 2 * m + 4121) 2 :=
  stoppingTime_of_classCertificate certificate_4121 m

/-- Checked base and every prefix for input 4123. -/
theorem certificate_4123 : classCertificateB 27 4123 = true := by
  decide

/-- The same exact first-descent time holds on an infinite dyadic ray. -/
theorem ray_4123 (m : Nat) : stoppingTime (2 ^ 27 * m + 4123) 27 :=
  stoppingTime_of_classCertificate certificate_4123 m

/-- Checked base and every prefix for input 4125. -/
theorem certificate_4125 : classCertificateB 2 4125 = true := by
  decide

/-- The same exact first-descent time holds on an infinite dyadic ray. -/
theorem ray_4125 (m : Nat) : stoppingTime (2 ^ 2 * m + 4125) 2 :=
  stoppingTime_of_classCertificate certificate_4125 m

/-- Checked base and every prefix for input 4127. -/
theorem certificate_4127 : classCertificateB 42 4127 = true := by
  decide

/-- The same exact first-descent time holds on an infinite dyadic ray. -/
theorem ray_4127 (m : Nat) : stoppingTime (2 ^ 42 * m + 4127) 42 :=
  stoppingTime_of_classCertificate certificate_4127 m

/-- Checked base and every prefix for input 4129. -/
theorem certificate_4129 : classCertificateB 2 4129 = true := by
  decide

/-- The same exact first-descent time holds on an infinite dyadic ray. -/
theorem ray_4129 (m : Nat) : stoppingTime (2 ^ 2 * m + 4129) 2 :=
  stoppingTime_of_classCertificate certificate_4129 m

/-- Checked base and every prefix for input 4131. -/
theorem certificate_4131 : classCertificateB 4 4131 = true := by
  decide

/-- The same exact first-descent time holds on an infinite dyadic ray. -/
theorem ray_4131 (m : Nat) : stoppingTime (2 ^ 4 * m + 4131) 4 :=
  stoppingTime_of_classCertificate certificate_4131 m

/-- Checked base and every prefix for input 4133. -/
theorem certificate_4133 : classCertificateB 2 4133 = true := by
  decide

/-- The same exact first-descent time holds on an infinite dyadic ray. -/
theorem ray_4133 (m : Nat) : stoppingTime (2 ^ 2 * m + 4133) 2 :=
  stoppingTime_of_classCertificate certificate_4133 m

/-- Checked base and every prefix for input 4135. -/
theorem certificate_4135 : classCertificateB 8 4135 = true := by
  decide

/-- The same exact first-descent time holds on an infinite dyadic ray. -/
theorem ray_4135 (m : Nat) : stoppingTime (2 ^ 8 * m + 4135) 8 :=
  stoppingTime_of_classCertificate certificate_4135 m

/-- Checked base and every prefix for input 4137. -/
theorem certificate_4137 : classCertificateB 2 4137 = true := by
  decide

/-- The same exact first-descent time holds on an infinite dyadic ray. -/
theorem ray_4137 (m : Nat) : stoppingTime (2 ^ 2 * m + 4137) 2 :=
  stoppingTime_of_classCertificate certificate_4137 m

/-- Checked base and every prefix for input 4139. -/
theorem certificate_4139 : classCertificateB 5 4139 = true := by
  decide

/-- The same exact first-descent time holds on an infinite dyadic ray. -/
theorem ray_4139 (m : Nat) : stoppingTime (2 ^ 5 * m + 4139) 5 :=
  stoppingTime_of_classCertificate certificate_4139 m

/-- Checked base and every prefix for input 4141. -/
theorem certificate_4141 : classCertificateB 2 4141 = true := by
  decide

/-- The same exact first-descent time holds on an infinite dyadic ray. -/
theorem ray_4141 (m : Nat) : stoppingTime (2 ^ 2 * m + 4141) 2 :=
  stoppingTime_of_classCertificate certificate_4141 m

/-- Checked base and every prefix for input 4143. -/
theorem certificate_4143 : classCertificateB 18 4143 = true := by
  decide

/-- The same exact first-descent time holds on an infinite dyadic ray. -/
theorem ray_4143 (m : Nat) : stoppingTime (2 ^ 18 * m + 4143) 18 :=
  stoppingTime_of_classCertificate certificate_4143 m

/-- Checked base and every prefix for input 4145. -/
theorem certificate_4145 : classCertificateB 2 4145 = true := by
  decide

/-- The same exact first-descent time holds on an infinite dyadic ray. -/
theorem ray_4145 (m : Nat) : stoppingTime (2 ^ 2 * m + 4145) 2 :=
  stoppingTime_of_classCertificate certificate_4145 m

/-- Checked base and every prefix for input 4147. -/
theorem certificate_4147 : classCertificateB 4 4147 = true := by
  decide

/-- The same exact first-descent time holds on an infinite dyadic ray. -/
theorem ray_4147 (m : Nat) : stoppingTime (2 ^ 4 * m + 4147) 4 :=
  stoppingTime_of_classCertificate certificate_4147 m

/-- Checked base and every prefix for input 4149. -/
theorem certificate_4149 : classCertificateB 2 4149 = true := by
  decide

/-- The same exact first-descent time holds on an infinite dyadic ray. -/
theorem ray_4149 (m : Nat) : stoppingTime (2 ^ 2 * m + 4149) 2 :=
  stoppingTime_of_classCertificate certificate_4149 m

/-- Checked base and every prefix for input 4151. -/
theorem certificate_4151 : classCertificateB 5 4151 = true := by
  decide

/-- The same exact first-descent time holds on an infinite dyadic ray. -/
theorem ray_4151 (m : Nat) : stoppingTime (2 ^ 5 * m + 4151) 5 :=
  stoppingTime_of_classCertificate certificate_4151 m

/-- Checked base and every prefix for input 4153. -/
theorem certificate_4153 : classCertificateB 2 4153 = true := by
  decide

/-- The same exact first-descent time holds on an infinite dyadic ray. -/
theorem ray_4153 (m : Nat) : stoppingTime (2 ^ 2 * m + 4153) 2 :=
  stoppingTime_of_classCertificate certificate_4153 m

/-- Exhaustive coverage of the odd inputs in this batch, with no gaps. -/
theorem coverage : CertifiedRange 4087 4155 := by
  intro n hlo hhi hodd
  have hn : n = 4087 ∨ n = 4089 ∨ n = 4091 ∨ n = 4093 ∨ n = 4095 ∨ n = 4097 ∨ n = 4099 ∨ n = 4101 ∨ n = 4103 ∨ n = 4105 ∨ n = 4107 ∨ n = 4109 ∨ n = 4111 ∨ n = 4113 ∨ n = 4115 ∨ n = 4117 ∨ n = 4119 ∨ n = 4121 ∨ n = 4123 ∨ n = 4125 ∨ n = 4127 ∨ n = 4129 ∨ n = 4131 ∨ n = 4133 ∨ n = 4135 ∨ n = 4137 ∨ n = 4139 ∨ n = 4141 ∨ n = 4143 ∨ n = 4145 ∨ n = 4147 ∨ n = 4149 ∨ n = 4151 ∨ n = 4153 := by omega
  rcases hn with h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h
  · subst n
    exact ⟨5, witness_of_certificate certificate_4087⟩
  · subst n
    exact ⟨2, witness_of_certificate certificate_4089⟩
  · subst n
    exact ⟨13, witness_of_certificate certificate_4091⟩
  · subst n
    exact ⟨2, witness_of_certificate certificate_4093⟩
  · subst n
    exact ⟨51, witness_of_certificate certificate_4095⟩
  · subst n
    exact ⟨2, witness_of_certificate certificate_4097⟩
  · subst n
    exact ⟨4, witness_of_certificate certificate_4099⟩
  · subst n
    exact ⟨2, witness_of_certificate certificate_4101⟩
  · subst n
    exact ⟨7, witness_of_certificate certificate_4103⟩
  · subst n
    exact ⟨2, witness_of_certificate certificate_4105⟩
  · subst n
    exact ⟨5, witness_of_certificate certificate_4107⟩
  · subst n
    exact ⟨2, witness_of_certificate certificate_4109⟩
  · subst n
    exact ⟨7, witness_of_certificate certificate_4111⟩
  · subst n
    exact ⟨2, witness_of_certificate certificate_4113⟩
  · subst n
    exact ⟨4, witness_of_certificate certificate_4115⟩
  · subst n
    exact ⟨2, witness_of_certificate certificate_4117⟩
  · subst n
    exact ⟨5, witness_of_certificate certificate_4119⟩
  · subst n
    exact ⟨2, witness_of_certificate certificate_4121⟩
  · subst n
    exact ⟨27, witness_of_certificate certificate_4123⟩
  · subst n
    exact ⟨2, witness_of_certificate certificate_4125⟩
  · subst n
    exact ⟨42, witness_of_certificate certificate_4127⟩
  · subst n
    exact ⟨2, witness_of_certificate certificate_4129⟩
  · subst n
    exact ⟨4, witness_of_certificate certificate_4131⟩
  · subst n
    exact ⟨2, witness_of_certificate certificate_4133⟩
  · subst n
    exact ⟨8, witness_of_certificate certificate_4135⟩
  · subst n
    exact ⟨2, witness_of_certificate certificate_4137⟩
  · subst n
    exact ⟨5, witness_of_certificate certificate_4139⟩
  · subst n
    exact ⟨2, witness_of_certificate certificate_4141⟩
  · subst n
    exact ⟨18, witness_of_certificate certificate_4143⟩
  · subst n
    exact ⟨2, witness_of_certificate certificate_4145⟩
  · subst n
    exact ⟨4, witness_of_certificate certificate_4147⟩
  · subst n
    exact ⟨2, witness_of_certificate certificate_4149⟩
  · subst n
    exact ⟨5, witness_of_certificate certificate_4151⟩
  · subst n
    exact ⟨2, witness_of_certificate certificate_4153⟩

end Collatz.Research.CoefficientDescent.Batch062
