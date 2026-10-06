import Collatz.Research.CoefficientDescent.Basic

namespace Collatz.Research.CoefficientDescent.Batch092

open FirstDescentClass

set_option maxRecDepth 20000
set_option maxHeartbeats 0

/-- Checked base and every prefix for input 6097. -/
theorem certificate_6097 : classCertificateB 2 6097 = true := by
  decide

/-- The same exact first-descent time holds on an infinite dyadic ray. -/
theorem ray_6097 (m : Nat) : stoppingTime (2 ^ 2 * m + 6097) 2 :=
  stoppingTime_of_classCertificate certificate_6097 m

/-- Checked base and every prefix for input 6099. -/
theorem certificate_6099 : classCertificateB 4 6099 = true := by
  decide

/-- The same exact first-descent time holds on an infinite dyadic ray. -/
theorem ray_6099 (m : Nat) : stoppingTime (2 ^ 4 * m + 6099) 4 :=
  stoppingTime_of_classCertificate certificate_6099 m

/-- Checked base and every prefix for input 6101. -/
theorem certificate_6101 : classCertificateB 2 6101 = true := by
  decide

/-- The same exact first-descent time holds on an infinite dyadic ray. -/
theorem ray_6101 (m : Nat) : stoppingTime (2 ^ 2 * m + 6101) 2 :=
  stoppingTime_of_classCertificate certificate_6101 m

/-- Checked base and every prefix for input 6103. -/
theorem certificate_6103 : classCertificateB 5 6103 = true := by
  decide

/-- The same exact first-descent time holds on an infinite dyadic ray. -/
theorem ray_6103 (m : Nat) : stoppingTime (2 ^ 5 * m + 6103) 5 :=
  stoppingTime_of_classCertificate certificate_6103 m

/-- Checked base and every prefix for input 6105. -/
theorem certificate_6105 : classCertificateB 2 6105 = true := by
  decide

/-- The same exact first-descent time holds on an infinite dyadic ray. -/
theorem ray_6105 (m : Nat) : stoppingTime (2 ^ 2 * m + 6105) 2 :=
  stoppingTime_of_classCertificate certificate_6105 m

/-- Checked base and every prefix for input 6107. -/
theorem certificate_6107 : classCertificateB 8 6107 = true := by
  decide

/-- The same exact first-descent time holds on an infinite dyadic ray. -/
theorem ray_6107 (m : Nat) : stoppingTime (2 ^ 8 * m + 6107) 8 :=
  stoppingTime_of_classCertificate certificate_6107 m

/-- Checked base and every prefix for input 6109. -/
theorem certificate_6109 : classCertificateB 2 6109 = true := by
  decide

/-- The same exact first-descent time holds on an infinite dyadic ray. -/
theorem ray_6109 (m : Nat) : stoppingTime (2 ^ 2 * m + 6109) 2 :=
  stoppingTime_of_classCertificate certificate_6109 m

/-- Checked base and every prefix for input 6111. -/
theorem certificate_6111 : classCertificateB 29 6111 = true := by
  decide

/-- The same exact first-descent time holds on an infinite dyadic ray. -/
theorem ray_6111 (m : Nat) : stoppingTime (2 ^ 29 * m + 6111) 29 :=
  stoppingTime_of_classCertificate certificate_6111 m

/-- Checked base and every prefix for input 6113. -/
theorem certificate_6113 : classCertificateB 2 6113 = true := by
  decide

/-- The same exact first-descent time holds on an infinite dyadic ray. -/
theorem ray_6113 (m : Nat) : stoppingTime (2 ^ 2 * m + 6113) 2 :=
  stoppingTime_of_classCertificate certificate_6113 m

/-- Checked base and every prefix for input 6115. -/
theorem certificate_6115 : classCertificateB 4 6115 = true := by
  decide

/-- The same exact first-descent time holds on an infinite dyadic ray. -/
theorem ray_6115 (m : Nat) : stoppingTime (2 ^ 4 * m + 6115) 4 :=
  stoppingTime_of_classCertificate certificate_6115 m

/-- Checked base and every prefix for input 6117. -/
theorem certificate_6117 : classCertificateB 2 6117 = true := by
  decide

/-- The same exact first-descent time holds on an infinite dyadic ray. -/
theorem ray_6117 (m : Nat) : stoppingTime (2 ^ 2 * m + 6117) 2 :=
  stoppingTime_of_classCertificate certificate_6117 m

/-- Checked base and every prefix for input 6119. -/
theorem certificate_6119 : classCertificateB 10 6119 = true := by
  decide

/-- The same exact first-descent time holds on an infinite dyadic ray. -/
theorem ray_6119 (m : Nat) : stoppingTime (2 ^ 10 * m + 6119) 10 :=
  stoppingTime_of_classCertificate certificate_6119 m

/-- Checked base and every prefix for input 6121. -/
theorem certificate_6121 : classCertificateB 2 6121 = true := by
  decide

/-- The same exact first-descent time holds on an infinite dyadic ray. -/
theorem ray_6121 (m : Nat) : stoppingTime (2 ^ 2 * m + 6121) 2 :=
  stoppingTime_of_classCertificate certificate_6121 m

/-- Checked base and every prefix for input 6123. -/
theorem certificate_6123 : classCertificateB 5 6123 = true := by
  decide

/-- The same exact first-descent time holds on an infinite dyadic ray. -/
theorem ray_6123 (m : Nat) : stoppingTime (2 ^ 5 * m + 6123) 5 :=
  stoppingTime_of_classCertificate certificate_6123 m

/-- Checked base and every prefix for input 6125. -/
theorem certificate_6125 : classCertificateB 2 6125 = true := by
  decide

/-- The same exact first-descent time holds on an infinite dyadic ray. -/
theorem ray_6125 (m : Nat) : stoppingTime (2 ^ 2 * m + 6125) 2 :=
  stoppingTime_of_classCertificate certificate_6125 m

/-- Checked base and every prefix for input 6127. -/
theorem certificate_6127 : classCertificateB 12 6127 = true := by
  decide

/-- The same exact first-descent time holds on an infinite dyadic ray. -/
theorem ray_6127 (m : Nat) : stoppingTime (2 ^ 12 * m + 6127) 12 :=
  stoppingTime_of_classCertificate certificate_6127 m

/-- Checked base and every prefix for input 6129. -/
theorem certificate_6129 : classCertificateB 2 6129 = true := by
  decide

/-- The same exact first-descent time holds on an infinite dyadic ray. -/
theorem ray_6129 (m : Nat) : stoppingTime (2 ^ 2 * m + 6129) 2 :=
  stoppingTime_of_classCertificate certificate_6129 m

/-- Checked base and every prefix for input 6131. -/
theorem certificate_6131 : classCertificateB 4 6131 = true := by
  decide

/-- The same exact first-descent time holds on an infinite dyadic ray. -/
theorem ray_6131 (m : Nat) : stoppingTime (2 ^ 4 * m + 6131) 4 :=
  stoppingTime_of_classCertificate certificate_6131 m

/-- Checked base and every prefix for input 6133. -/
theorem certificate_6133 : classCertificateB 2 6133 = true := by
  decide

/-- The same exact first-descent time holds on an infinite dyadic ray. -/
theorem ray_6133 (m : Nat) : stoppingTime (2 ^ 2 * m + 6133) 2 :=
  stoppingTime_of_classCertificate certificate_6133 m

/-- Checked base and every prefix for input 6135. -/
theorem certificate_6135 : classCertificateB 5 6135 = true := by
  decide

/-- The same exact first-descent time holds on an infinite dyadic ray. -/
theorem ray_6135 (m : Nat) : stoppingTime (2 ^ 5 * m + 6135) 5 :=
  stoppingTime_of_classCertificate certificate_6135 m

/-- Checked base and every prefix for input 6137. -/
theorem certificate_6137 : classCertificateB 2 6137 = true := by
  decide

/-- The same exact first-descent time holds on an infinite dyadic ray. -/
theorem ray_6137 (m : Nat) : stoppingTime (2 ^ 2 * m + 6137) 2 :=
  stoppingTime_of_classCertificate certificate_6137 m

/-- Checked base and every prefix for input 6139. -/
theorem certificate_6139 : classCertificateB 18 6139 = true := by
  decide

/-- The same exact first-descent time holds on an infinite dyadic ray. -/
theorem ray_6139 (m : Nat) : stoppingTime (2 ^ 18 * m + 6139) 18 :=
  stoppingTime_of_classCertificate certificate_6139 m

/-- Checked base and every prefix for input 6141. -/
theorem certificate_6141 : classCertificateB 2 6141 = true := by
  decide

/-- The same exact first-descent time holds on an infinite dyadic ray. -/
theorem ray_6141 (m : Nat) : stoppingTime (2 ^ 2 * m + 6141) 2 :=
  stoppingTime_of_classCertificate certificate_6141 m

/-- Checked base and every prefix for input 6143. -/
theorem certificate_6143 : classCertificateB 50 6143 = true := by
  decide

/-- The same exact first-descent time holds on an infinite dyadic ray. -/
theorem ray_6143 (m : Nat) : stoppingTime (2 ^ 50 * m + 6143) 50 :=
  stoppingTime_of_classCertificate certificate_6143 m

/-- Checked base and every prefix for input 6145. -/
theorem certificate_6145 : classCertificateB 2 6145 = true := by
  decide

/-- The same exact first-descent time holds on an infinite dyadic ray. -/
theorem ray_6145 (m : Nat) : stoppingTime (2 ^ 2 * m + 6145) 2 :=
  stoppingTime_of_classCertificate certificate_6145 m

/-- Checked base and every prefix for input 6147. -/
theorem certificate_6147 : classCertificateB 4 6147 = true := by
  decide

/-- The same exact first-descent time holds on an infinite dyadic ray. -/
theorem ray_6147 (m : Nat) : stoppingTime (2 ^ 4 * m + 6147) 4 :=
  stoppingTime_of_classCertificate certificate_6147 m

/-- Checked base and every prefix for input 6149. -/
theorem certificate_6149 : classCertificateB 2 6149 = true := by
  decide

/-- The same exact first-descent time holds on an infinite dyadic ray. -/
theorem ray_6149 (m : Nat) : stoppingTime (2 ^ 2 * m + 6149) 2 :=
  stoppingTime_of_classCertificate certificate_6149 m

/-- Checked base and every prefix for input 6151. -/
theorem certificate_6151 : classCertificateB 7 6151 = true := by
  decide

/-- The same exact first-descent time holds on an infinite dyadic ray. -/
theorem ray_6151 (m : Nat) : stoppingTime (2 ^ 7 * m + 6151) 7 :=
  stoppingTime_of_classCertificate certificate_6151 m

/-- Checked base and every prefix for input 6153. -/
theorem certificate_6153 : classCertificateB 2 6153 = true := by
  decide

/-- The same exact first-descent time holds on an infinite dyadic ray. -/
theorem ray_6153 (m : Nat) : stoppingTime (2 ^ 2 * m + 6153) 2 :=
  stoppingTime_of_classCertificate certificate_6153 m

/-- Checked base and every prefix for input 6155. -/
theorem certificate_6155 : classCertificateB 5 6155 = true := by
  decide

/-- The same exact first-descent time holds on an infinite dyadic ray. -/
theorem ray_6155 (m : Nat) : stoppingTime (2 ^ 5 * m + 6155) 5 :=
  stoppingTime_of_classCertificate certificate_6155 m

/-- Checked base and every prefix for input 6157. -/
theorem certificate_6157 : classCertificateB 2 6157 = true := by
  decide

/-- The same exact first-descent time holds on an infinite dyadic ray. -/
theorem ray_6157 (m : Nat) : stoppingTime (2 ^ 2 * m + 6157) 2 :=
  stoppingTime_of_classCertificate certificate_6157 m

/-- Checked base and every prefix for input 6159. -/
theorem certificate_6159 : classCertificateB 7 6159 = true := by
  decide

/-- The same exact first-descent time holds on an infinite dyadic ray. -/
theorem ray_6159 (m : Nat) : stoppingTime (2 ^ 7 * m + 6159) 7 :=
  stoppingTime_of_classCertificate certificate_6159 m

/-- Checked base and every prefix for input 6161. -/
theorem certificate_6161 : classCertificateB 2 6161 = true := by
  decide

/-- The same exact first-descent time holds on an infinite dyadic ray. -/
theorem ray_6161 (m : Nat) : stoppingTime (2 ^ 2 * m + 6161) 2 :=
  stoppingTime_of_classCertificate certificate_6161 m

/-- Checked base and every prefix for input 6163. -/
theorem certificate_6163 : classCertificateB 4 6163 = true := by
  decide

/-- The same exact first-descent time holds on an infinite dyadic ray. -/
theorem ray_6163 (m : Nat) : stoppingTime (2 ^ 4 * m + 6163) 4 :=
  stoppingTime_of_classCertificate certificate_6163 m

/-- Exhaustive coverage of the odd inputs in this batch, with no gaps. -/
theorem coverage : CertifiedRange 6097 6165 := by
  intro n hlo hhi hodd
  have hn : n = 6097 ∨ n = 6099 ∨ n = 6101 ∨ n = 6103 ∨ n = 6105 ∨ n = 6107 ∨ n = 6109 ∨ n = 6111 ∨ n = 6113 ∨ n = 6115 ∨ n = 6117 ∨ n = 6119 ∨ n = 6121 ∨ n = 6123 ∨ n = 6125 ∨ n = 6127 ∨ n = 6129 ∨ n = 6131 ∨ n = 6133 ∨ n = 6135 ∨ n = 6137 ∨ n = 6139 ∨ n = 6141 ∨ n = 6143 ∨ n = 6145 ∨ n = 6147 ∨ n = 6149 ∨ n = 6151 ∨ n = 6153 ∨ n = 6155 ∨ n = 6157 ∨ n = 6159 ∨ n = 6161 ∨ n = 6163 := by omega
  rcases hn with h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h
  · subst n
    exact ⟨2, witness_of_certificate certificate_6097⟩
  · subst n
    exact ⟨4, witness_of_certificate certificate_6099⟩
  · subst n
    exact ⟨2, witness_of_certificate certificate_6101⟩
  · subst n
    exact ⟨5, witness_of_certificate certificate_6103⟩
  · subst n
    exact ⟨2, witness_of_certificate certificate_6105⟩
  · subst n
    exact ⟨8, witness_of_certificate certificate_6107⟩
  · subst n
    exact ⟨2, witness_of_certificate certificate_6109⟩
  · subst n
    exact ⟨29, witness_of_certificate certificate_6111⟩
  · subst n
    exact ⟨2, witness_of_certificate certificate_6113⟩
  · subst n
    exact ⟨4, witness_of_certificate certificate_6115⟩
  · subst n
    exact ⟨2, witness_of_certificate certificate_6117⟩
  · subst n
    exact ⟨10, witness_of_certificate certificate_6119⟩
  · subst n
    exact ⟨2, witness_of_certificate certificate_6121⟩
  · subst n
    exact ⟨5, witness_of_certificate certificate_6123⟩
  · subst n
    exact ⟨2, witness_of_certificate certificate_6125⟩
  · subst n
    exact ⟨12, witness_of_certificate certificate_6127⟩
  · subst n
    exact ⟨2, witness_of_certificate certificate_6129⟩
  · subst n
    exact ⟨4, witness_of_certificate certificate_6131⟩
  · subst n
    exact ⟨2, witness_of_certificate certificate_6133⟩
  · subst n
    exact ⟨5, witness_of_certificate certificate_6135⟩
  · subst n
    exact ⟨2, witness_of_certificate certificate_6137⟩
  · subst n
    exact ⟨18, witness_of_certificate certificate_6139⟩
  · subst n
    exact ⟨2, witness_of_certificate certificate_6141⟩
  · subst n
    exact ⟨50, witness_of_certificate certificate_6143⟩
  · subst n
    exact ⟨2, witness_of_certificate certificate_6145⟩
  · subst n
    exact ⟨4, witness_of_certificate certificate_6147⟩
  · subst n
    exact ⟨2, witness_of_certificate certificate_6149⟩
  · subst n
    exact ⟨7, witness_of_certificate certificate_6151⟩
  · subst n
    exact ⟨2, witness_of_certificate certificate_6153⟩
  · subst n
    exact ⟨5, witness_of_certificate certificate_6155⟩
  · subst n
    exact ⟨2, witness_of_certificate certificate_6157⟩
  · subst n
    exact ⟨7, witness_of_certificate certificate_6159⟩
  · subst n
    exact ⟨2, witness_of_certificate certificate_6161⟩
  · subst n
    exact ⟨4, witness_of_certificate certificate_6163⟩

end Collatz.Research.CoefficientDescent.Batch092
