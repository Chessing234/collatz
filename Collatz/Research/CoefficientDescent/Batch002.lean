import Collatz.Research.CoefficientDescent.Basic

namespace Collatz.Research.CoefficientDescent.Batch002

open FirstDescentClass

set_option maxRecDepth 20000
set_option maxHeartbeats 0

/-- Checked base and every prefix for input 69. -/
theorem certificate_69 : classCertificateB 2 69 = true := by
  decide

/-- The same exact first-descent time holds on an infinite dyadic ray. -/
theorem ray_69 (m : Nat) : stoppingTime (2 ^ 2 * m + 69) 2 :=
  stoppingTime_of_classCertificate certificate_69 m

/-- Checked base and every prefix for input 71. -/
theorem certificate_71 : classCertificateB 51 71 = true := by
  decide

/-- The same exact first-descent time holds on an infinite dyadic ray. -/
theorem ray_71 (m : Nat) : stoppingTime (2 ^ 51 * m + 71) 51 :=
  stoppingTime_of_classCertificate certificate_71 m

/-- Checked base and every prefix for input 73. -/
theorem certificate_73 : classCertificateB 2 73 = true := by
  decide

/-- The same exact first-descent time holds on an infinite dyadic ray. -/
theorem ray_73 (m : Nat) : stoppingTime (2 ^ 2 * m + 73) 2 :=
  stoppingTime_of_classCertificate certificate_73 m

/-- Checked base and every prefix for input 75. -/
theorem certificate_75 : classCertificateB 5 75 = true := by
  decide

/-- The same exact first-descent time holds on an infinite dyadic ray. -/
theorem ray_75 (m : Nat) : stoppingTime (2 ^ 5 * m + 75) 5 :=
  stoppingTime_of_classCertificate certificate_75 m

/-- Checked base and every prefix for input 77. -/
theorem certificate_77 : classCertificateB 2 77 = true := by
  decide

/-- The same exact first-descent time holds on an infinite dyadic ray. -/
theorem ray_77 (m : Nat) : stoppingTime (2 ^ 2 * m + 77) 2 :=
  stoppingTime_of_classCertificate certificate_77 m

/-- Checked base and every prefix for input 79. -/
theorem certificate_79 : classCertificateB 8 79 = true := by
  decide

/-- The same exact first-descent time holds on an infinite dyadic ray. -/
theorem ray_79 (m : Nat) : stoppingTime (2 ^ 8 * m + 79) 8 :=
  stoppingTime_of_classCertificate certificate_79 m

/-- Checked base and every prefix for input 81. -/
theorem certificate_81 : classCertificateB 2 81 = true := by
  decide

/-- The same exact first-descent time holds on an infinite dyadic ray. -/
theorem ray_81 (m : Nat) : stoppingTime (2 ^ 2 * m + 81) 2 :=
  stoppingTime_of_classCertificate certificate_81 m

/-- Checked base and every prefix for input 83. -/
theorem certificate_83 : classCertificateB 4 83 = true := by
  decide

/-- The same exact first-descent time holds on an infinite dyadic ray. -/
theorem ray_83 (m : Nat) : stoppingTime (2 ^ 4 * m + 83) 4 :=
  stoppingTime_of_classCertificate certificate_83 m

/-- Checked base and every prefix for input 85. -/
theorem certificate_85 : classCertificateB 2 85 = true := by
  decide

/-- The same exact first-descent time holds on an infinite dyadic ray. -/
theorem ray_85 (m : Nat) : stoppingTime (2 ^ 2 * m + 85) 2 :=
  stoppingTime_of_classCertificate certificate_85 m

/-- Checked base and every prefix for input 87. -/
theorem certificate_87 : classCertificateB 5 87 = true := by
  decide

/-- The same exact first-descent time holds on an infinite dyadic ray. -/
theorem ray_87 (m : Nat) : stoppingTime (2 ^ 5 * m + 87) 5 :=
  stoppingTime_of_classCertificate certificate_87 m

/-- Checked base and every prefix for input 89. -/
theorem certificate_89 : classCertificateB 2 89 = true := by
  decide

/-- The same exact first-descent time holds on an infinite dyadic ray. -/
theorem ray_89 (m : Nat) : stoppingTime (2 ^ 2 * m + 89) 2 :=
  stoppingTime_of_classCertificate certificate_89 m

/-- Checked base and every prefix for input 91. -/
theorem certificate_91 : classCertificateB 45 91 = true := by
  decide

/-- The same exact first-descent time holds on an infinite dyadic ray. -/
theorem ray_91 (m : Nat) : stoppingTime (2 ^ 45 * m + 91) 45 :=
  stoppingTime_of_classCertificate certificate_91 m

/-- Checked base and every prefix for input 93. -/
theorem certificate_93 : classCertificateB 2 93 = true := by
  decide

/-- The same exact first-descent time holds on an infinite dyadic ray. -/
theorem ray_93 (m : Nat) : stoppingTime (2 ^ 2 * m + 93) 2 :=
  stoppingTime_of_classCertificate certificate_93 m

/-- Checked base and every prefix for input 95. -/
theorem certificate_95 : classCertificateB 8 95 = true := by
  decide

/-- The same exact first-descent time holds on an infinite dyadic ray. -/
theorem ray_95 (m : Nat) : stoppingTime (2 ^ 8 * m + 95) 8 :=
  stoppingTime_of_classCertificate certificate_95 m

/-- Checked base and every prefix for input 97. -/
theorem certificate_97 : classCertificateB 2 97 = true := by
  decide

/-- The same exact first-descent time holds on an infinite dyadic ray. -/
theorem ray_97 (m : Nat) : stoppingTime (2 ^ 2 * m + 97) 2 :=
  stoppingTime_of_classCertificate certificate_97 m

/-- Checked base and every prefix for input 99. -/
theorem certificate_99 : classCertificateB 4 99 = true := by
  decide

/-- The same exact first-descent time holds on an infinite dyadic ray. -/
theorem ray_99 (m : Nat) : stoppingTime (2 ^ 4 * m + 99) 4 :=
  stoppingTime_of_classCertificate certificate_99 m

/-- Checked base and every prefix for input 101. -/
theorem certificate_101 : classCertificateB 2 101 = true := by
  decide

/-- The same exact first-descent time holds on an infinite dyadic ray. -/
theorem ray_101 (m : Nat) : stoppingTime (2 ^ 2 * m + 101) 2 :=
  stoppingTime_of_classCertificate certificate_101 m

/-- Checked base and every prefix for input 103. -/
theorem certificate_103 : classCertificateB 42 103 = true := by
  decide

/-- The same exact first-descent time holds on an infinite dyadic ray. -/
theorem ray_103 (m : Nat) : stoppingTime (2 ^ 42 * m + 103) 42 :=
  stoppingTime_of_classCertificate certificate_103 m

/-- Checked base and every prefix for input 105. -/
theorem certificate_105 : classCertificateB 2 105 = true := by
  decide

/-- The same exact first-descent time holds on an infinite dyadic ray. -/
theorem ray_105 (m : Nat) : stoppingTime (2 ^ 2 * m + 105) 2 :=
  stoppingTime_of_classCertificate certificate_105 m

/-- Checked base and every prefix for input 107. -/
theorem certificate_107 : classCertificateB 5 107 = true := by
  decide

/-- The same exact first-descent time holds on an infinite dyadic ray. -/
theorem ray_107 (m : Nat) : stoppingTime (2 ^ 5 * m + 107) 5 :=
  stoppingTime_of_classCertificate certificate_107 m

/-- Checked base and every prefix for input 109. -/
theorem certificate_109 : classCertificateB 2 109 = true := by
  decide

/-- The same exact first-descent time holds on an infinite dyadic ray. -/
theorem ray_109 (m : Nat) : stoppingTime (2 ^ 2 * m + 109) 2 :=
  stoppingTime_of_classCertificate certificate_109 m

/-- Checked base and every prefix for input 111. -/
theorem certificate_111 : classCertificateB 31 111 = true := by
  decide

/-- The same exact first-descent time holds on an infinite dyadic ray. -/
theorem ray_111 (m : Nat) : stoppingTime (2 ^ 31 * m + 111) 31 :=
  stoppingTime_of_classCertificate certificate_111 m

/-- Checked base and every prefix for input 113. -/
theorem certificate_113 : classCertificateB 2 113 = true := by
  decide

/-- The same exact first-descent time holds on an infinite dyadic ray. -/
theorem ray_113 (m : Nat) : stoppingTime (2 ^ 2 * m + 113) 2 :=
  stoppingTime_of_classCertificate certificate_113 m

/-- Checked base and every prefix for input 115. -/
theorem certificate_115 : classCertificateB 4 115 = true := by
  decide

/-- The same exact first-descent time holds on an infinite dyadic ray. -/
theorem ray_115 (m : Nat) : stoppingTime (2 ^ 4 * m + 115) 4 :=
  stoppingTime_of_classCertificate certificate_115 m

/-- Checked base and every prefix for input 117. -/
theorem certificate_117 : classCertificateB 2 117 = true := by
  decide

/-- The same exact first-descent time holds on an infinite dyadic ray. -/
theorem ray_117 (m : Nat) : stoppingTime (2 ^ 2 * m + 117) 2 :=
  stoppingTime_of_classCertificate certificate_117 m

/-- Checked base and every prefix for input 119. -/
theorem certificate_119 : classCertificateB 5 119 = true := by
  decide

/-- The same exact first-descent time holds on an infinite dyadic ray. -/
theorem ray_119 (m : Nat) : stoppingTime (2 ^ 5 * m + 119) 5 :=
  stoppingTime_of_classCertificate certificate_119 m

/-- Checked base and every prefix for input 121. -/
theorem certificate_121 : classCertificateB 2 121 = true := by
  decide

/-- The same exact first-descent time holds on an infinite dyadic ray. -/
theorem ray_121 (m : Nat) : stoppingTime (2 ^ 2 * m + 121) 2 :=
  stoppingTime_of_classCertificate certificate_121 m

/-- Checked base and every prefix for input 123. -/
theorem certificate_123 : classCertificateB 8 123 = true := by
  decide

/-- The same exact first-descent time holds on an infinite dyadic ray. -/
theorem ray_123 (m : Nat) : stoppingTime (2 ^ 8 * m + 123) 8 :=
  stoppingTime_of_classCertificate certificate_123 m

/-- Checked base and every prefix for input 125. -/
theorem certificate_125 : classCertificateB 2 125 = true := by
  decide

/-- The same exact first-descent time holds on an infinite dyadic ray. -/
theorem ray_125 (m : Nat) : stoppingTime (2 ^ 2 * m + 125) 2 :=
  stoppingTime_of_classCertificate certificate_125 m

/-- Checked base and every prefix for input 127. -/
theorem certificate_127 : classCertificateB 15 127 = true := by
  decide

/-- The same exact first-descent time holds on an infinite dyadic ray. -/
theorem ray_127 (m : Nat) : stoppingTime (2 ^ 15 * m + 127) 15 :=
  stoppingTime_of_classCertificate certificate_127 m

/-- Checked base and every prefix for input 129. -/
theorem certificate_129 : classCertificateB 2 129 = true := by
  decide

/-- The same exact first-descent time holds on an infinite dyadic ray. -/
theorem ray_129 (m : Nat) : stoppingTime (2 ^ 2 * m + 129) 2 :=
  stoppingTime_of_classCertificate certificate_129 m

/-- Checked base and every prefix for input 131. -/
theorem certificate_131 : classCertificateB 4 131 = true := by
  decide

/-- The same exact first-descent time holds on an infinite dyadic ray. -/
theorem ray_131 (m : Nat) : stoppingTime (2 ^ 4 * m + 131) 4 :=
  stoppingTime_of_classCertificate certificate_131 m

/-- Checked base and every prefix for input 133. -/
theorem certificate_133 : classCertificateB 2 133 = true := by
  decide

/-- The same exact first-descent time holds on an infinite dyadic ray. -/
theorem ray_133 (m : Nat) : stoppingTime (2 ^ 2 * m + 133) 2 :=
  stoppingTime_of_classCertificate certificate_133 m

/-- Exhaustive coverage of the odd inputs in this batch, with no gaps. -/
theorem coverage : CertifiedRange 69 135 := by
  intro n hlo hhi hodd
  have hn : n = 69 ∨ n = 71 ∨ n = 73 ∨ n = 75 ∨ n = 77 ∨ n = 79 ∨ n = 81 ∨ n = 83 ∨ n = 85 ∨ n = 87 ∨ n = 89 ∨ n = 91 ∨ n = 93 ∨ n = 95 ∨ n = 97 ∨ n = 99 ∨ n = 101 ∨ n = 103 ∨ n = 105 ∨ n = 107 ∨ n = 109 ∨ n = 111 ∨ n = 113 ∨ n = 115 ∨ n = 117 ∨ n = 119 ∨ n = 121 ∨ n = 123 ∨ n = 125 ∨ n = 127 ∨ n = 129 ∨ n = 131 ∨ n = 133 := by omega
  rcases hn with h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h
  · subst n
    exact ⟨2, witness_of_certificate certificate_69⟩
  · subst n
    exact ⟨51, witness_of_certificate certificate_71⟩
  · subst n
    exact ⟨2, witness_of_certificate certificate_73⟩
  · subst n
    exact ⟨5, witness_of_certificate certificate_75⟩
  · subst n
    exact ⟨2, witness_of_certificate certificate_77⟩
  · subst n
    exact ⟨8, witness_of_certificate certificate_79⟩
  · subst n
    exact ⟨2, witness_of_certificate certificate_81⟩
  · subst n
    exact ⟨4, witness_of_certificate certificate_83⟩
  · subst n
    exact ⟨2, witness_of_certificate certificate_85⟩
  · subst n
    exact ⟨5, witness_of_certificate certificate_87⟩
  · subst n
    exact ⟨2, witness_of_certificate certificate_89⟩
  · subst n
    exact ⟨45, witness_of_certificate certificate_91⟩
  · subst n
    exact ⟨2, witness_of_certificate certificate_93⟩
  · subst n
    exact ⟨8, witness_of_certificate certificate_95⟩
  · subst n
    exact ⟨2, witness_of_certificate certificate_97⟩
  · subst n
    exact ⟨4, witness_of_certificate certificate_99⟩
  · subst n
    exact ⟨2, witness_of_certificate certificate_101⟩
  · subst n
    exact ⟨42, witness_of_certificate certificate_103⟩
  · subst n
    exact ⟨2, witness_of_certificate certificate_105⟩
  · subst n
    exact ⟨5, witness_of_certificate certificate_107⟩
  · subst n
    exact ⟨2, witness_of_certificate certificate_109⟩
  · subst n
    exact ⟨31, witness_of_certificate certificate_111⟩
  · subst n
    exact ⟨2, witness_of_certificate certificate_113⟩
  · subst n
    exact ⟨4, witness_of_certificate certificate_115⟩
  · subst n
    exact ⟨2, witness_of_certificate certificate_117⟩
  · subst n
    exact ⟨5, witness_of_certificate certificate_119⟩
  · subst n
    exact ⟨2, witness_of_certificate certificate_121⟩
  · subst n
    exact ⟨8, witness_of_certificate certificate_123⟩
  · subst n
    exact ⟨2, witness_of_certificate certificate_125⟩
  · subst n
    exact ⟨15, witness_of_certificate certificate_127⟩
  · subst n
    exact ⟨2, witness_of_certificate certificate_129⟩
  · subst n
    exact ⟨4, witness_of_certificate certificate_131⟩
  · subst n
    exact ⟨2, witness_of_certificate certificate_133⟩

end Collatz.Research.CoefficientDescent.Batch002
