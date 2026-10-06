import Collatz.Research.CoefficientDescent.Basic

namespace Collatz.Research.CoefficientDescent.Batch003

open FirstDescentClass

set_option maxRecDepth 20000
set_option maxHeartbeats 0

/-- Checked base and every prefix for input 135. -/
theorem certificate_135 : classCertificateB 7 135 = true := by
  decide

/-- The same exact first-descent time holds on an infinite dyadic ray. -/
theorem ray_135 (m : Nat) : stoppingTime (2 ^ 7 * m + 135) 7 :=
  stoppingTime_of_classCertificate certificate_135 m

/-- Checked base and every prefix for input 137. -/
theorem certificate_137 : classCertificateB 2 137 = true := by
  decide

/-- The same exact first-descent time holds on an infinite dyadic ray. -/
theorem ray_137 (m : Nat) : stoppingTime (2 ^ 2 * m + 137) 2 :=
  stoppingTime_of_classCertificate certificate_137 m

/-- Checked base and every prefix for input 139. -/
theorem certificate_139 : classCertificateB 5 139 = true := by
  decide

/-- The same exact first-descent time holds on an infinite dyadic ray. -/
theorem ray_139 (m : Nat) : stoppingTime (2 ^ 5 * m + 139) 5 :=
  stoppingTime_of_classCertificate certificate_139 m

/-- Checked base and every prefix for input 141. -/
theorem certificate_141 : classCertificateB 2 141 = true := by
  decide

/-- The same exact first-descent time holds on an infinite dyadic ray. -/
theorem ray_141 (m : Nat) : stoppingTime (2 ^ 2 * m + 141) 2 :=
  stoppingTime_of_classCertificate certificate_141 m

/-- Checked base and every prefix for input 143. -/
theorem certificate_143 : classCertificateB 7 143 = true := by
  decide

/-- The same exact first-descent time holds on an infinite dyadic ray. -/
theorem ray_143 (m : Nat) : stoppingTime (2 ^ 7 * m + 143) 7 :=
  stoppingTime_of_classCertificate certificate_143 m

/-- Checked base and every prefix for input 145. -/
theorem certificate_145 : classCertificateB 2 145 = true := by
  decide

/-- The same exact first-descent time holds on an infinite dyadic ray. -/
theorem ray_145 (m : Nat) : stoppingTime (2 ^ 2 * m + 145) 2 :=
  stoppingTime_of_classCertificate certificate_145 m

/-- Checked base and every prefix for input 147. -/
theorem certificate_147 : classCertificateB 4 147 = true := by
  decide

/-- The same exact first-descent time holds on an infinite dyadic ray. -/
theorem ray_147 (m : Nat) : stoppingTime (2 ^ 4 * m + 147) 4 :=
  stoppingTime_of_classCertificate certificate_147 m

/-- Checked base and every prefix for input 149. -/
theorem certificate_149 : classCertificateB 2 149 = true := by
  decide

/-- The same exact first-descent time holds on an infinite dyadic ray. -/
theorem ray_149 (m : Nat) : stoppingTime (2 ^ 2 * m + 149) 2 :=
  stoppingTime_of_classCertificate certificate_149 m

/-- Checked base and every prefix for input 151. -/
theorem certificate_151 : classCertificateB 5 151 = true := by
  decide

/-- The same exact first-descent time holds on an infinite dyadic ray. -/
theorem ray_151 (m : Nat) : stoppingTime (2 ^ 5 * m + 151) 5 :=
  stoppingTime_of_classCertificate certificate_151 m

/-- Checked base and every prefix for input 153. -/
theorem certificate_153 : classCertificateB 2 153 = true := by
  decide

/-- The same exact first-descent time holds on an infinite dyadic ray. -/
theorem ray_153 (m : Nat) : stoppingTime (2 ^ 2 * m + 153) 2 :=
  stoppingTime_of_classCertificate certificate_153 m

/-- Checked base and every prefix for input 155. -/
theorem certificate_155 : classCertificateB 40 155 = true := by
  decide

/-- The same exact first-descent time holds on an infinite dyadic ray. -/
theorem ray_155 (m : Nat) : stoppingTime (2 ^ 40 * m + 155) 40 :=
  stoppingTime_of_classCertificate certificate_155 m

/-- Checked base and every prefix for input 157. -/
theorem certificate_157 : classCertificateB 2 157 = true := by
  decide

/-- The same exact first-descent time holds on an infinite dyadic ray. -/
theorem ray_157 (m : Nat) : stoppingTime (2 ^ 2 * m + 157) 2 :=
  stoppingTime_of_classCertificate certificate_157 m

/-- Checked base and every prefix for input 159. -/
theorem certificate_159 : classCertificateB 21 159 = true := by
  decide

/-- The same exact first-descent time holds on an infinite dyadic ray. -/
theorem ray_159 (m : Nat) : stoppingTime (2 ^ 21 * m + 159) 21 :=
  stoppingTime_of_classCertificate certificate_159 m

/-- Checked base and every prefix for input 161. -/
theorem certificate_161 : classCertificateB 2 161 = true := by
  decide

/-- The same exact first-descent time holds on an infinite dyadic ray. -/
theorem ray_161 (m : Nat) : stoppingTime (2 ^ 2 * m + 161) 2 :=
  stoppingTime_of_classCertificate certificate_161 m

/-- Checked base and every prefix for input 163. -/
theorem certificate_163 : classCertificateB 4 163 = true := by
  decide

/-- The same exact first-descent time holds on an infinite dyadic ray. -/
theorem ray_163 (m : Nat) : stoppingTime (2 ^ 4 * m + 163) 4 :=
  stoppingTime_of_classCertificate certificate_163 m

/-- Checked base and every prefix for input 165. -/
theorem certificate_165 : classCertificateB 2 165 = true := by
  decide

/-- The same exact first-descent time holds on an infinite dyadic ray. -/
theorem ray_165 (m : Nat) : stoppingTime (2 ^ 2 * m + 165) 2 :=
  stoppingTime_of_classCertificate certificate_165 m

/-- Checked base and every prefix for input 167. -/
theorem certificate_167 : classCertificateB 29 167 = true := by
  decide

/-- The same exact first-descent time holds on an infinite dyadic ray. -/
theorem ray_167 (m : Nat) : stoppingTime (2 ^ 29 * m + 167) 29 :=
  stoppingTime_of_classCertificate certificate_167 m

/-- Checked base and every prefix for input 169. -/
theorem certificate_169 : classCertificateB 2 169 = true := by
  decide

/-- The same exact first-descent time holds on an infinite dyadic ray. -/
theorem ray_169 (m : Nat) : stoppingTime (2 ^ 2 * m + 169) 2 :=
  stoppingTime_of_classCertificate certificate_169 m

/-- Checked base and every prefix for input 171. -/
theorem certificate_171 : classCertificateB 5 171 = true := by
  decide

/-- The same exact first-descent time holds on an infinite dyadic ray. -/
theorem ray_171 (m : Nat) : stoppingTime (2 ^ 5 * m + 171) 5 :=
  stoppingTime_of_classCertificate certificate_171 m

/-- Checked base and every prefix for input 173. -/
theorem certificate_173 : classCertificateB 2 173 = true := by
  decide

/-- The same exact first-descent time holds on an infinite dyadic ray. -/
theorem ray_173 (m : Nat) : stoppingTime (2 ^ 2 * m + 173) 2 :=
  stoppingTime_of_classCertificate certificate_173 m

/-- Checked base and every prefix for input 175. -/
theorem certificate_175 : classCertificateB 8 175 = true := by
  decide

/-- The same exact first-descent time holds on an infinite dyadic ray. -/
theorem ray_175 (m : Nat) : stoppingTime (2 ^ 8 * m + 175) 8 :=
  stoppingTime_of_classCertificate certificate_175 m

/-- Checked base and every prefix for input 177. -/
theorem certificate_177 : classCertificateB 2 177 = true := by
  decide

/-- The same exact first-descent time holds on an infinite dyadic ray. -/
theorem ray_177 (m : Nat) : stoppingTime (2 ^ 2 * m + 177) 2 :=
  stoppingTime_of_classCertificate certificate_177 m

/-- Checked base and every prefix for input 179. -/
theorem certificate_179 : classCertificateB 4 179 = true := by
  decide

/-- The same exact first-descent time holds on an infinite dyadic ray. -/
theorem ray_179 (m : Nat) : stoppingTime (2 ^ 4 * m + 179) 4 :=
  stoppingTime_of_classCertificate certificate_179 m

/-- Checked base and every prefix for input 181. -/
theorem certificate_181 : classCertificateB 2 181 = true := by
  decide

/-- The same exact first-descent time holds on an infinite dyadic ray. -/
theorem ray_181 (m : Nat) : stoppingTime (2 ^ 2 * m + 181) 2 :=
  stoppingTime_of_classCertificate certificate_181 m

/-- Checked base and every prefix for input 183. -/
theorem certificate_183 : classCertificateB 5 183 = true := by
  decide

/-- The same exact first-descent time holds on an infinite dyadic ray. -/
theorem ray_183 (m : Nat) : stoppingTime (2 ^ 5 * m + 183) 5 :=
  stoppingTime_of_classCertificate certificate_183 m

/-- Checked base and every prefix for input 185. -/
theorem certificate_185 : classCertificateB 2 185 = true := by
  decide

/-- The same exact first-descent time holds on an infinite dyadic ray. -/
theorem ray_185 (m : Nat) : stoppingTime (2 ^ 2 * m + 185) 2 :=
  stoppingTime_of_classCertificate certificate_185 m

/-- Checked base and every prefix for input 187. -/
theorem certificate_187 : classCertificateB 7 187 = true := by
  decide

/-- The same exact first-descent time holds on an infinite dyadic ray. -/
theorem ray_187 (m : Nat) : stoppingTime (2 ^ 7 * m + 187) 7 :=
  stoppingTime_of_classCertificate certificate_187 m

/-- Checked base and every prefix for input 189. -/
theorem certificate_189 : classCertificateB 2 189 = true := by
  decide

/-- The same exact first-descent time holds on an infinite dyadic ray. -/
theorem ray_189 (m : Nat) : stoppingTime (2 ^ 2 * m + 189) 2 :=
  stoppingTime_of_classCertificate certificate_189 m

/-- Checked base and every prefix for input 191. -/
theorem certificate_191 : classCertificateB 13 191 = true := by
  decide

/-- The same exact first-descent time holds on an infinite dyadic ray. -/
theorem ray_191 (m : Nat) : stoppingTime (2 ^ 13 * m + 191) 13 :=
  stoppingTime_of_classCertificate certificate_191 m

/-- Checked base and every prefix for input 193. -/
theorem certificate_193 : classCertificateB 2 193 = true := by
  decide

/-- The same exact first-descent time holds on an infinite dyadic ray. -/
theorem ray_193 (m : Nat) : stoppingTime (2 ^ 2 * m + 193) 2 :=
  stoppingTime_of_classCertificate certificate_193 m

/-- Checked base and every prefix for input 195. -/
theorem certificate_195 : classCertificateB 4 195 = true := by
  decide

/-- The same exact first-descent time holds on an infinite dyadic ray. -/
theorem ray_195 (m : Nat) : stoppingTime (2 ^ 4 * m + 195) 4 :=
  stoppingTime_of_classCertificate certificate_195 m

/-- Checked base and every prefix for input 197. -/
theorem certificate_197 : classCertificateB 2 197 = true := by
  decide

/-- The same exact first-descent time holds on an infinite dyadic ray. -/
theorem ray_197 (m : Nat) : stoppingTime (2 ^ 2 * m + 197) 2 :=
  stoppingTime_of_classCertificate certificate_197 m

/-- Checked base and every prefix for input 199. -/
theorem certificate_199 : classCertificateB 8 199 = true := by
  decide

/-- The same exact first-descent time holds on an infinite dyadic ray. -/
theorem ray_199 (m : Nat) : stoppingTime (2 ^ 8 * m + 199) 8 :=
  stoppingTime_of_classCertificate certificate_199 m

/-- Checked base and every prefix for input 201. -/
theorem certificate_201 : classCertificateB 2 201 = true := by
  decide

/-- The same exact first-descent time holds on an infinite dyadic ray. -/
theorem ray_201 (m : Nat) : stoppingTime (2 ^ 2 * m + 201) 2 :=
  stoppingTime_of_classCertificate certificate_201 m

/-- Exhaustive coverage of the odd inputs in this batch, with no gaps. -/
theorem coverage : CertifiedRange 135 203 := by
  intro n hlo hhi hodd
  have hn : n = 135 ∨ n = 137 ∨ n = 139 ∨ n = 141 ∨ n = 143 ∨ n = 145 ∨ n = 147 ∨ n = 149 ∨ n = 151 ∨ n = 153 ∨ n = 155 ∨ n = 157 ∨ n = 159 ∨ n = 161 ∨ n = 163 ∨ n = 165 ∨ n = 167 ∨ n = 169 ∨ n = 171 ∨ n = 173 ∨ n = 175 ∨ n = 177 ∨ n = 179 ∨ n = 181 ∨ n = 183 ∨ n = 185 ∨ n = 187 ∨ n = 189 ∨ n = 191 ∨ n = 193 ∨ n = 195 ∨ n = 197 ∨ n = 199 ∨ n = 201 := by omega
  rcases hn with h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h
  · subst n
    exact ⟨7, witness_of_certificate certificate_135⟩
  · subst n
    exact ⟨2, witness_of_certificate certificate_137⟩
  · subst n
    exact ⟨5, witness_of_certificate certificate_139⟩
  · subst n
    exact ⟨2, witness_of_certificate certificate_141⟩
  · subst n
    exact ⟨7, witness_of_certificate certificate_143⟩
  · subst n
    exact ⟨2, witness_of_certificate certificate_145⟩
  · subst n
    exact ⟨4, witness_of_certificate certificate_147⟩
  · subst n
    exact ⟨2, witness_of_certificate certificate_149⟩
  · subst n
    exact ⟨5, witness_of_certificate certificate_151⟩
  · subst n
    exact ⟨2, witness_of_certificate certificate_153⟩
  · subst n
    exact ⟨40, witness_of_certificate certificate_155⟩
  · subst n
    exact ⟨2, witness_of_certificate certificate_157⟩
  · subst n
    exact ⟨21, witness_of_certificate certificate_159⟩
  · subst n
    exact ⟨2, witness_of_certificate certificate_161⟩
  · subst n
    exact ⟨4, witness_of_certificate certificate_163⟩
  · subst n
    exact ⟨2, witness_of_certificate certificate_165⟩
  · subst n
    exact ⟨29, witness_of_certificate certificate_167⟩
  · subst n
    exact ⟨2, witness_of_certificate certificate_169⟩
  · subst n
    exact ⟨5, witness_of_certificate certificate_171⟩
  · subst n
    exact ⟨2, witness_of_certificate certificate_173⟩
  · subst n
    exact ⟨8, witness_of_certificate certificate_175⟩
  · subst n
    exact ⟨2, witness_of_certificate certificate_177⟩
  · subst n
    exact ⟨4, witness_of_certificate certificate_179⟩
  · subst n
    exact ⟨2, witness_of_certificate certificate_181⟩
  · subst n
    exact ⟨5, witness_of_certificate certificate_183⟩
  · subst n
    exact ⟨2, witness_of_certificate certificate_185⟩
  · subst n
    exact ⟨7, witness_of_certificate certificate_187⟩
  · subst n
    exact ⟨2, witness_of_certificate certificate_189⟩
  · subst n
    exact ⟨13, witness_of_certificate certificate_191⟩
  · subst n
    exact ⟨2, witness_of_certificate certificate_193⟩
  · subst n
    exact ⟨4, witness_of_certificate certificate_195⟩
  · subst n
    exact ⟨2, witness_of_certificate certificate_197⟩
  · subst n
    exact ⟨8, witness_of_certificate certificate_199⟩
  · subst n
    exact ⟨2, witness_of_certificate certificate_201⟩

end Collatz.Research.CoefficientDescent.Batch003
