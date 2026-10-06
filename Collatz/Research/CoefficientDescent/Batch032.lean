import Collatz.Research.CoefficientDescent.Basic

namespace Collatz.Research.CoefficientDescent.Batch032

open FirstDescentClass

set_option maxRecDepth 20000
set_option maxHeartbeats 0

/-- Checked base and every prefix for input 2079. -/
theorem certificate_2079 : classCertificateB 13 2079 = true := by
  decide

/-- The same exact first-descent time holds on an infinite dyadic ray. -/
theorem ray_2079 (m : Nat) : stoppingTime (2 ^ 13 * m + 2079) 13 :=
  stoppingTime_of_classCertificate certificate_2079 m

/-- Checked base and every prefix for input 2081. -/
theorem certificate_2081 : classCertificateB 2 2081 = true := by
  decide

/-- The same exact first-descent time holds on an infinite dyadic ray. -/
theorem ray_2081 (m : Nat) : stoppingTime (2 ^ 2 * m + 2081) 2 :=
  stoppingTime_of_classCertificate certificate_2081 m

/-- Checked base and every prefix for input 2083. -/
theorem certificate_2083 : classCertificateB 4 2083 = true := by
  decide

/-- The same exact first-descent time holds on an infinite dyadic ray. -/
theorem ray_2083 (m : Nat) : stoppingTime (2 ^ 4 * m + 2083) 4 :=
  stoppingTime_of_classCertificate certificate_2083 m

/-- Checked base and every prefix for input 2085. -/
theorem certificate_2085 : classCertificateB 2 2085 = true := by
  decide

/-- The same exact first-descent time holds on an infinite dyadic ray. -/
theorem ray_2085 (m : Nat) : stoppingTime (2 ^ 2 * m + 2085) 2 :=
  stoppingTime_of_classCertificate certificate_2085 m

/-- Checked base and every prefix for input 2087. -/
theorem certificate_2087 : classCertificateB 8 2087 = true := by
  decide

/-- The same exact first-descent time holds on an infinite dyadic ray. -/
theorem ray_2087 (m : Nat) : stoppingTime (2 ^ 8 * m + 2087) 8 :=
  stoppingTime_of_classCertificate certificate_2087 m

/-- Checked base and every prefix for input 2089. -/
theorem certificate_2089 : classCertificateB 2 2089 = true := by
  decide

/-- The same exact first-descent time holds on an infinite dyadic ray. -/
theorem ray_2089 (m : Nat) : stoppingTime (2 ^ 2 * m + 2089) 2 :=
  stoppingTime_of_classCertificate certificate_2089 m

/-- Checked base and every prefix for input 2091. -/
theorem certificate_2091 : classCertificateB 5 2091 = true := by
  decide

/-- The same exact first-descent time holds on an infinite dyadic ray. -/
theorem ray_2091 (m : Nat) : stoppingTime (2 ^ 5 * m + 2091) 5 :=
  stoppingTime_of_classCertificate certificate_2091 m

/-- Checked base and every prefix for input 2093. -/
theorem certificate_2093 : classCertificateB 2 2093 = true := by
  decide

/-- The same exact first-descent time holds on an infinite dyadic ray. -/
theorem ray_2093 (m : Nat) : stoppingTime (2 ^ 2 * m + 2093) 2 :=
  stoppingTime_of_classCertificate certificate_2093 m

/-- Checked base and every prefix for input 2095. -/
theorem certificate_2095 : classCertificateB 13 2095 = true := by
  decide

/-- The same exact first-descent time holds on an infinite dyadic ray. -/
theorem ray_2095 (m : Nat) : stoppingTime (2 ^ 13 * m + 2095) 13 :=
  stoppingTime_of_classCertificate certificate_2095 m

/-- Checked base and every prefix for input 2097. -/
theorem certificate_2097 : classCertificateB 2 2097 = true := by
  decide

/-- The same exact first-descent time holds on an infinite dyadic ray. -/
theorem ray_2097 (m : Nat) : stoppingTime (2 ^ 2 * m + 2097) 2 :=
  stoppingTime_of_classCertificate certificate_2097 m

/-- Checked base and every prefix for input 2099. -/
theorem certificate_2099 : classCertificateB 4 2099 = true := by
  decide

/-- The same exact first-descent time holds on an infinite dyadic ray. -/
theorem ray_2099 (m : Nat) : stoppingTime (2 ^ 4 * m + 2099) 4 :=
  stoppingTime_of_classCertificate certificate_2099 m

/-- Checked base and every prefix for input 2101. -/
theorem certificate_2101 : classCertificateB 2 2101 = true := by
  decide

/-- The same exact first-descent time holds on an infinite dyadic ray. -/
theorem ray_2101 (m : Nat) : stoppingTime (2 ^ 2 * m + 2101) 2 :=
  stoppingTime_of_classCertificate certificate_2101 m

/-- Checked base and every prefix for input 2103. -/
theorem certificate_2103 : classCertificateB 5 2103 = true := by
  decide

/-- The same exact first-descent time holds on an infinite dyadic ray. -/
theorem ray_2103 (m : Nat) : stoppingTime (2 ^ 5 * m + 2103) 5 :=
  stoppingTime_of_classCertificate certificate_2103 m

/-- Checked base and every prefix for input 2105. -/
theorem certificate_2105 : classCertificateB 2 2105 = true := by
  decide

/-- The same exact first-descent time holds on an infinite dyadic ray. -/
theorem ray_2105 (m : Nat) : stoppingTime (2 ^ 2 * m + 2105) 2 :=
  stoppingTime_of_classCertificate certificate_2105 m

/-- Checked base and every prefix for input 2107. -/
theorem certificate_2107 : classCertificateB 7 2107 = true := by
  decide

/-- The same exact first-descent time holds on an infinite dyadic ray. -/
theorem ray_2107 (m : Nat) : stoppingTime (2 ^ 7 * m + 2107) 7 :=
  stoppingTime_of_classCertificate certificate_2107 m

/-- Checked base and every prefix for input 2109. -/
theorem certificate_2109 : classCertificateB 2 2109 = true := by
  decide

/-- The same exact first-descent time holds on an infinite dyadic ray. -/
theorem ray_2109 (m : Nat) : stoppingTime (2 ^ 2 * m + 2109) 2 :=
  stoppingTime_of_classCertificate certificate_2109 m

/-- Checked base and every prefix for input 2111. -/
theorem certificate_2111 : classCertificateB 80 2111 = true := by
  decide

/-- The same exact first-descent time holds on an infinite dyadic ray. -/
theorem ray_2111 (m : Nat) : stoppingTime (2 ^ 80 * m + 2111) 80 :=
  stoppingTime_of_classCertificate certificate_2111 m

/-- Checked base and every prefix for input 2113. -/
theorem certificate_2113 : classCertificateB 2 2113 = true := by
  decide

/-- The same exact first-descent time holds on an infinite dyadic ray. -/
theorem ray_2113 (m : Nat) : stoppingTime (2 ^ 2 * m + 2113) 2 :=
  stoppingTime_of_classCertificate certificate_2113 m

/-- Checked base and every prefix for input 2115. -/
theorem certificate_2115 : classCertificateB 4 2115 = true := by
  decide

/-- The same exact first-descent time holds on an infinite dyadic ray. -/
theorem ray_2115 (m : Nat) : stoppingTime (2 ^ 4 * m + 2115) 4 :=
  stoppingTime_of_classCertificate certificate_2115 m

/-- Checked base and every prefix for input 2117. -/
theorem certificate_2117 : classCertificateB 2 2117 = true := by
  decide

/-- The same exact first-descent time holds on an infinite dyadic ray. -/
theorem ray_2117 (m : Nat) : stoppingTime (2 ^ 2 * m + 2117) 2 :=
  stoppingTime_of_classCertificate certificate_2117 m

/-- Checked base and every prefix for input 2119. -/
theorem certificate_2119 : classCertificateB 15 2119 = true := by
  decide

/-- The same exact first-descent time holds on an infinite dyadic ray. -/
theorem ray_2119 (m : Nat) : stoppingTime (2 ^ 15 * m + 2119) 15 :=
  stoppingTime_of_classCertificate certificate_2119 m

/-- Checked base and every prefix for input 2121. -/
theorem certificate_2121 : classCertificateB 2 2121 = true := by
  decide

/-- The same exact first-descent time holds on an infinite dyadic ray. -/
theorem ray_2121 (m : Nat) : stoppingTime (2 ^ 2 * m + 2121) 2 :=
  stoppingTime_of_classCertificate certificate_2121 m

/-- Checked base and every prefix for input 2123. -/
theorem certificate_2123 : classCertificateB 5 2123 = true := by
  decide

/-- The same exact first-descent time holds on an infinite dyadic ray. -/
theorem ray_2123 (m : Nat) : stoppingTime (2 ^ 5 * m + 2123) 5 :=
  stoppingTime_of_classCertificate certificate_2123 m

/-- Checked base and every prefix for input 2125. -/
theorem certificate_2125 : classCertificateB 2 2125 = true := by
  decide

/-- The same exact first-descent time holds on an infinite dyadic ray. -/
theorem ray_2125 (m : Nat) : stoppingTime (2 ^ 2 * m + 2125) 2 :=
  stoppingTime_of_classCertificate certificate_2125 m

/-- Checked base and every prefix for input 2127. -/
theorem certificate_2127 : classCertificateB 8 2127 = true := by
  decide

/-- The same exact first-descent time holds on an infinite dyadic ray. -/
theorem ray_2127 (m : Nat) : stoppingTime (2 ^ 8 * m + 2127) 8 :=
  stoppingTime_of_classCertificate certificate_2127 m

/-- Checked base and every prefix for input 2129. -/
theorem certificate_2129 : classCertificateB 2 2129 = true := by
  decide

/-- The same exact first-descent time holds on an infinite dyadic ray. -/
theorem ray_2129 (m : Nat) : stoppingTime (2 ^ 2 * m + 2129) 2 :=
  stoppingTime_of_classCertificate certificate_2129 m

/-- Checked base and every prefix for input 2131. -/
theorem certificate_2131 : classCertificateB 4 2131 = true := by
  decide

/-- The same exact first-descent time holds on an infinite dyadic ray. -/
theorem ray_2131 (m : Nat) : stoppingTime (2 ^ 4 * m + 2131) 4 :=
  stoppingTime_of_classCertificate certificate_2131 m

/-- Checked base and every prefix for input 2133. -/
theorem certificate_2133 : classCertificateB 2 2133 = true := by
  decide

/-- The same exact first-descent time holds on an infinite dyadic ray. -/
theorem ray_2133 (m : Nat) : stoppingTime (2 ^ 2 * m + 2133) 2 :=
  stoppingTime_of_classCertificate certificate_2133 m

/-- Checked base and every prefix for input 2135. -/
theorem certificate_2135 : classCertificateB 5 2135 = true := by
  decide

/-- The same exact first-descent time holds on an infinite dyadic ray. -/
theorem ray_2135 (m : Nat) : stoppingTime (2 ^ 5 * m + 2135) 5 :=
  stoppingTime_of_classCertificate certificate_2135 m

/-- Checked base and every prefix for input 2137. -/
theorem certificate_2137 : classCertificateB 2 2137 = true := by
  decide

/-- The same exact first-descent time holds on an infinite dyadic ray. -/
theorem ray_2137 (m : Nat) : stoppingTime (2 ^ 2 * m + 2137) 2 :=
  stoppingTime_of_classCertificate certificate_2137 m

/-- Checked base and every prefix for input 2139. -/
theorem certificate_2139 : classCertificateB 20 2139 = true := by
  decide

/-- The same exact first-descent time holds on an infinite dyadic ray. -/
theorem ray_2139 (m : Nat) : stoppingTime (2 ^ 20 * m + 2139) 20 :=
  stoppingTime_of_classCertificate certificate_2139 m

/-- Checked base and every prefix for input 2141. -/
theorem certificate_2141 : classCertificateB 2 2141 = true := by
  decide

/-- The same exact first-descent time holds on an infinite dyadic ray. -/
theorem ray_2141 (m : Nat) : stoppingTime (2 ^ 2 * m + 2141) 2 :=
  stoppingTime_of_classCertificate certificate_2141 m

/-- Checked base and every prefix for input 2143. -/
theorem certificate_2143 : classCertificateB 8 2143 = true := by
  decide

/-- The same exact first-descent time holds on an infinite dyadic ray. -/
theorem ray_2143 (m : Nat) : stoppingTime (2 ^ 8 * m + 2143) 8 :=
  stoppingTime_of_classCertificate certificate_2143 m

/-- Exhaustive coverage of the odd inputs in this batch, with no gaps. -/
theorem coverage : CertifiedRange 2079 2145 := by
  intro n hlo hhi hodd
  have hn : n = 2079 ∨ n = 2081 ∨ n = 2083 ∨ n = 2085 ∨ n = 2087 ∨ n = 2089 ∨ n = 2091 ∨ n = 2093 ∨ n = 2095 ∨ n = 2097 ∨ n = 2099 ∨ n = 2101 ∨ n = 2103 ∨ n = 2105 ∨ n = 2107 ∨ n = 2109 ∨ n = 2111 ∨ n = 2113 ∨ n = 2115 ∨ n = 2117 ∨ n = 2119 ∨ n = 2121 ∨ n = 2123 ∨ n = 2125 ∨ n = 2127 ∨ n = 2129 ∨ n = 2131 ∨ n = 2133 ∨ n = 2135 ∨ n = 2137 ∨ n = 2139 ∨ n = 2141 ∨ n = 2143 := by omega
  rcases hn with h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h
  · subst n
    exact ⟨13, witness_of_certificate certificate_2079⟩
  · subst n
    exact ⟨2, witness_of_certificate certificate_2081⟩
  · subst n
    exact ⟨4, witness_of_certificate certificate_2083⟩
  · subst n
    exact ⟨2, witness_of_certificate certificate_2085⟩
  · subst n
    exact ⟨8, witness_of_certificate certificate_2087⟩
  · subst n
    exact ⟨2, witness_of_certificate certificate_2089⟩
  · subst n
    exact ⟨5, witness_of_certificate certificate_2091⟩
  · subst n
    exact ⟨2, witness_of_certificate certificate_2093⟩
  · subst n
    exact ⟨13, witness_of_certificate certificate_2095⟩
  · subst n
    exact ⟨2, witness_of_certificate certificate_2097⟩
  · subst n
    exact ⟨4, witness_of_certificate certificate_2099⟩
  · subst n
    exact ⟨2, witness_of_certificate certificate_2101⟩
  · subst n
    exact ⟨5, witness_of_certificate certificate_2103⟩
  · subst n
    exact ⟨2, witness_of_certificate certificate_2105⟩
  · subst n
    exact ⟨7, witness_of_certificate certificate_2107⟩
  · subst n
    exact ⟨2, witness_of_certificate certificate_2109⟩
  · subst n
    exact ⟨80, witness_of_certificate certificate_2111⟩
  · subst n
    exact ⟨2, witness_of_certificate certificate_2113⟩
  · subst n
    exact ⟨4, witness_of_certificate certificate_2115⟩
  · subst n
    exact ⟨2, witness_of_certificate certificate_2117⟩
  · subst n
    exact ⟨15, witness_of_certificate certificate_2119⟩
  · subst n
    exact ⟨2, witness_of_certificate certificate_2121⟩
  · subst n
    exact ⟨5, witness_of_certificate certificate_2123⟩
  · subst n
    exact ⟨2, witness_of_certificate certificate_2125⟩
  · subst n
    exact ⟨8, witness_of_certificate certificate_2127⟩
  · subst n
    exact ⟨2, witness_of_certificate certificate_2129⟩
  · subst n
    exact ⟨4, witness_of_certificate certificate_2131⟩
  · subst n
    exact ⟨2, witness_of_certificate certificate_2133⟩
  · subst n
    exact ⟨5, witness_of_certificate certificate_2135⟩
  · subst n
    exact ⟨2, witness_of_certificate certificate_2137⟩
  · subst n
    exact ⟨20, witness_of_certificate certificate_2139⟩
  · subst n
    exact ⟨2, witness_of_certificate certificate_2141⟩
  · subst n
    exact ⟨8, witness_of_certificate certificate_2143⟩

end Collatz.Research.CoefficientDescent.Batch032
