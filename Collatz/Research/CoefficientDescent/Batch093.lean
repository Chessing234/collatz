import Collatz.Research.CoefficientDescent.Basic

namespace Collatz.Research.CoefficientDescent.Batch093

open FirstDescentClass

set_option maxRecDepth 20000
set_option maxHeartbeats 0

/-- Checked base and every prefix for input 6165. -/
theorem certificate_6165 : classCertificateB 2 6165 = true := by
  decide

/-- The same exact first-descent time holds on an infinite dyadic ray. -/
theorem ray_6165 (m : Nat) : stoppingTime (2 ^ 2 * m + 6165) 2 :=
  stoppingTime_of_classCertificate certificate_6165 m

/-- Checked base and every prefix for input 6167. -/
theorem certificate_6167 : classCertificateB 5 6167 = true := by
  decide

/-- The same exact first-descent time holds on an infinite dyadic ray. -/
theorem ray_6167 (m : Nat) : stoppingTime (2 ^ 5 * m + 6167) 5 :=
  stoppingTime_of_classCertificate certificate_6167 m

/-- Checked base and every prefix for input 6169. -/
theorem certificate_6169 : classCertificateB 2 6169 = true := by
  decide

/-- The same exact first-descent time holds on an infinite dyadic ray. -/
theorem ray_6169 (m : Nat) : stoppingTime (2 ^ 2 * m + 6169) 2 :=
  stoppingTime_of_classCertificate certificate_6169 m

/-- Checked base and every prefix for input 6171. -/
theorem certificate_6171 : classCertificateB 58 6171 = true := by
  decide

/-- The same exact first-descent time holds on an infinite dyadic ray. -/
theorem ray_6171 (m : Nat) : stoppingTime (2 ^ 58 * m + 6171) 58 :=
  stoppingTime_of_classCertificate certificate_6171 m

/-- Checked base and every prefix for input 6173. -/
theorem certificate_6173 : classCertificateB 2 6173 = true := by
  decide

/-- The same exact first-descent time holds on an infinite dyadic ray. -/
theorem ray_6173 (m : Nat) : stoppingTime (2 ^ 2 * m + 6173) 2 :=
  stoppingTime_of_classCertificate certificate_6173 m

/-- Checked base and every prefix for input 6175. -/
theorem certificate_6175 : classCertificateB 15 6175 = true := by
  decide

/-- The same exact first-descent time holds on an infinite dyadic ray. -/
theorem ray_6175 (m : Nat) : stoppingTime (2 ^ 15 * m + 6175) 15 :=
  stoppingTime_of_classCertificate certificate_6175 m

/-- Checked base and every prefix for input 6177. -/
theorem certificate_6177 : classCertificateB 2 6177 = true := by
  decide

/-- The same exact first-descent time holds on an infinite dyadic ray. -/
theorem ray_6177 (m : Nat) : stoppingTime (2 ^ 2 * m + 6177) 2 :=
  stoppingTime_of_classCertificate certificate_6177 m

/-- Checked base and every prefix for input 6179. -/
theorem certificate_6179 : classCertificateB 4 6179 = true := by
  decide

/-- The same exact first-descent time holds on an infinite dyadic ray. -/
theorem ray_6179 (m : Nat) : stoppingTime (2 ^ 4 * m + 6179) 4 :=
  stoppingTime_of_classCertificate certificate_6179 m

/-- Checked base and every prefix for input 6181. -/
theorem certificate_6181 : classCertificateB 2 6181 = true := by
  decide

/-- The same exact first-descent time holds on an infinite dyadic ray. -/
theorem ray_6181 (m : Nat) : stoppingTime (2 ^ 2 * m + 6181) 2 :=
  stoppingTime_of_classCertificate certificate_6181 m

/-- Checked base and every prefix for input 6183. -/
theorem certificate_6183 : classCertificateB 8 6183 = true := by
  decide

/-- The same exact first-descent time holds on an infinite dyadic ray. -/
theorem ray_6183 (m : Nat) : stoppingTime (2 ^ 8 * m + 6183) 8 :=
  stoppingTime_of_classCertificate certificate_6183 m

/-- Checked base and every prefix for input 6185. -/
theorem certificate_6185 : classCertificateB 2 6185 = true := by
  decide

/-- The same exact first-descent time holds on an infinite dyadic ray. -/
theorem ray_6185 (m : Nat) : stoppingTime (2 ^ 2 * m + 6185) 2 :=
  stoppingTime_of_classCertificate certificate_6185 m

/-- Checked base and every prefix for input 6187. -/
theorem certificate_6187 : classCertificateB 5 6187 = true := by
  decide

/-- The same exact first-descent time holds on an infinite dyadic ray. -/
theorem ray_6187 (m : Nat) : stoppingTime (2 ^ 5 * m + 6187) 5 :=
  stoppingTime_of_classCertificate certificate_6187 m

/-- Checked base and every prefix for input 6189. -/
theorem certificate_6189 : classCertificateB 2 6189 = true := by
  decide

/-- The same exact first-descent time holds on an infinite dyadic ray. -/
theorem ray_6189 (m : Nat) : stoppingTime (2 ^ 2 * m + 6189) 2 :=
  stoppingTime_of_classCertificate certificate_6189 m

/-- Checked base and every prefix for input 6191. -/
theorem certificate_6191 : classCertificateB 27 6191 = true := by
  decide

/-- The same exact first-descent time holds on an infinite dyadic ray. -/
theorem ray_6191 (m : Nat) : stoppingTime (2 ^ 27 * m + 6191) 27 :=
  stoppingTime_of_classCertificate certificate_6191 m

/-- Checked base and every prefix for input 6193. -/
theorem certificate_6193 : classCertificateB 2 6193 = true := by
  decide

/-- The same exact first-descent time holds on an infinite dyadic ray. -/
theorem ray_6193 (m : Nat) : stoppingTime (2 ^ 2 * m + 6193) 2 :=
  stoppingTime_of_classCertificate certificate_6193 m

/-- Checked base and every prefix for input 6195. -/
theorem certificate_6195 : classCertificateB 4 6195 = true := by
  decide

/-- The same exact first-descent time holds on an infinite dyadic ray. -/
theorem ray_6195 (m : Nat) : stoppingTime (2 ^ 4 * m + 6195) 4 :=
  stoppingTime_of_classCertificate certificate_6195 m

/-- Checked base and every prefix for input 6197. -/
theorem certificate_6197 : classCertificateB 2 6197 = true := by
  decide

/-- The same exact first-descent time holds on an infinite dyadic ray. -/
theorem ray_6197 (m : Nat) : stoppingTime (2 ^ 2 * m + 6197) 2 :=
  stoppingTime_of_classCertificate certificate_6197 m

/-- Checked base and every prefix for input 6199. -/
theorem certificate_6199 : classCertificateB 5 6199 = true := by
  decide

/-- The same exact first-descent time holds on an infinite dyadic ray. -/
theorem ray_6199 (m : Nat) : stoppingTime (2 ^ 5 * m + 6199) 5 :=
  stoppingTime_of_classCertificate certificate_6199 m

/-- Checked base and every prefix for input 6201. -/
theorem certificate_6201 : classCertificateB 2 6201 = true := by
  decide

/-- The same exact first-descent time holds on an infinite dyadic ray. -/
theorem ray_6201 (m : Nat) : stoppingTime (2 ^ 2 * m + 6201) 2 :=
  stoppingTime_of_classCertificate certificate_6201 m

/-- Checked base and every prefix for input 6203. -/
theorem certificate_6203 : classCertificateB 7 6203 = true := by
  decide

/-- The same exact first-descent time holds on an infinite dyadic ray. -/
theorem ray_6203 (m : Nat) : stoppingTime (2 ^ 7 * m + 6203) 7 :=
  stoppingTime_of_classCertificate certificate_6203 m

/-- Checked base and every prefix for input 6205. -/
theorem certificate_6205 : classCertificateB 2 6205 = true := by
  decide

/-- The same exact first-descent time holds on an infinite dyadic ray. -/
theorem ray_6205 (m : Nat) : stoppingTime (2 ^ 2 * m + 6205) 2 :=
  stoppingTime_of_classCertificate certificate_6205 m

/-- Checked base and every prefix for input 6207. -/
theorem certificate_6207 : classCertificateB 16 6207 = true := by
  decide

/-- The same exact first-descent time holds on an infinite dyadic ray. -/
theorem ray_6207 (m : Nat) : stoppingTime (2 ^ 16 * m + 6207) 16 :=
  stoppingTime_of_classCertificate certificate_6207 m

/-- Checked base and every prefix for input 6209. -/
theorem certificate_6209 : classCertificateB 2 6209 = true := by
  decide

/-- The same exact first-descent time holds on an infinite dyadic ray. -/
theorem ray_6209 (m : Nat) : stoppingTime (2 ^ 2 * m + 6209) 2 :=
  stoppingTime_of_classCertificate certificate_6209 m

/-- Checked base and every prefix for input 6211. -/
theorem certificate_6211 : classCertificateB 4 6211 = true := by
  decide

/-- The same exact first-descent time holds on an infinite dyadic ray. -/
theorem ray_6211 (m : Nat) : stoppingTime (2 ^ 4 * m + 6211) 4 :=
  stoppingTime_of_classCertificate certificate_6211 m

/-- Checked base and every prefix for input 6213. -/
theorem certificate_6213 : classCertificateB 2 6213 = true := by
  decide

/-- The same exact first-descent time holds on an infinite dyadic ray. -/
theorem ray_6213 (m : Nat) : stoppingTime (2 ^ 2 * m + 6213) 2 :=
  stoppingTime_of_classCertificate certificate_6213 m

/-- Checked base and every prefix for input 6215. -/
theorem certificate_6215 : classCertificateB 13 6215 = true := by
  decide

/-- The same exact first-descent time holds on an infinite dyadic ray. -/
theorem ray_6215 (m : Nat) : stoppingTime (2 ^ 13 * m + 6215) 13 :=
  stoppingTime_of_classCertificate certificate_6215 m

/-- Checked base and every prefix for input 6217. -/
theorem certificate_6217 : classCertificateB 2 6217 = true := by
  decide

/-- The same exact first-descent time holds on an infinite dyadic ray. -/
theorem ray_6217 (m : Nat) : stoppingTime (2 ^ 2 * m + 6217) 2 :=
  stoppingTime_of_classCertificate certificate_6217 m

/-- Checked base and every prefix for input 6219. -/
theorem certificate_6219 : classCertificateB 5 6219 = true := by
  decide

/-- The same exact first-descent time holds on an infinite dyadic ray. -/
theorem ray_6219 (m : Nat) : stoppingTime (2 ^ 5 * m + 6219) 5 :=
  stoppingTime_of_classCertificate certificate_6219 m

/-- Checked base and every prefix for input 6221. -/
theorem certificate_6221 : classCertificateB 2 6221 = true := by
  decide

/-- The same exact first-descent time holds on an infinite dyadic ray. -/
theorem ray_6221 (m : Nat) : stoppingTime (2 ^ 2 * m + 6221) 2 :=
  stoppingTime_of_classCertificate certificate_6221 m

/-- Checked base and every prefix for input 6223. -/
theorem certificate_6223 : classCertificateB 8 6223 = true := by
  decide

/-- The same exact first-descent time holds on an infinite dyadic ray. -/
theorem ray_6223 (m : Nat) : stoppingTime (2 ^ 8 * m + 6223) 8 :=
  stoppingTime_of_classCertificate certificate_6223 m

/-- Checked base and every prefix for input 6225. -/
theorem certificate_6225 : classCertificateB 2 6225 = true := by
  decide

/-- The same exact first-descent time holds on an infinite dyadic ray. -/
theorem ray_6225 (m : Nat) : stoppingTime (2 ^ 2 * m + 6225) 2 :=
  stoppingTime_of_classCertificate certificate_6225 m

/-- Checked base and every prefix for input 6227. -/
theorem certificate_6227 : classCertificateB 4 6227 = true := by
  decide

/-- The same exact first-descent time holds on an infinite dyadic ray. -/
theorem ray_6227 (m : Nat) : stoppingTime (2 ^ 4 * m + 6227) 4 :=
  stoppingTime_of_classCertificate certificate_6227 m

/-- Checked base and every prefix for input 6229. -/
theorem certificate_6229 : classCertificateB 2 6229 = true := by
  decide

/-- The same exact first-descent time holds on an infinite dyadic ray. -/
theorem ray_6229 (m : Nat) : stoppingTime (2 ^ 2 * m + 6229) 2 :=
  stoppingTime_of_classCertificate certificate_6229 m

/-- Exhaustive coverage of the odd inputs in this batch, with no gaps. -/
theorem coverage : CertifiedRange 6165 6231 := by
  intro n hlo hhi hodd
  have hn : n = 6165 ∨ n = 6167 ∨ n = 6169 ∨ n = 6171 ∨ n = 6173 ∨ n = 6175 ∨ n = 6177 ∨ n = 6179 ∨ n = 6181 ∨ n = 6183 ∨ n = 6185 ∨ n = 6187 ∨ n = 6189 ∨ n = 6191 ∨ n = 6193 ∨ n = 6195 ∨ n = 6197 ∨ n = 6199 ∨ n = 6201 ∨ n = 6203 ∨ n = 6205 ∨ n = 6207 ∨ n = 6209 ∨ n = 6211 ∨ n = 6213 ∨ n = 6215 ∨ n = 6217 ∨ n = 6219 ∨ n = 6221 ∨ n = 6223 ∨ n = 6225 ∨ n = 6227 ∨ n = 6229 := by omega
  rcases hn with h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h
  · subst n
    exact ⟨2, witness_of_certificate certificate_6165⟩
  · subst n
    exact ⟨5, witness_of_certificate certificate_6167⟩
  · subst n
    exact ⟨2, witness_of_certificate certificate_6169⟩
  · subst n
    exact ⟨58, witness_of_certificate certificate_6171⟩
  · subst n
    exact ⟨2, witness_of_certificate certificate_6173⟩
  · subst n
    exact ⟨15, witness_of_certificate certificate_6175⟩
  · subst n
    exact ⟨2, witness_of_certificate certificate_6177⟩
  · subst n
    exact ⟨4, witness_of_certificate certificate_6179⟩
  · subst n
    exact ⟨2, witness_of_certificate certificate_6181⟩
  · subst n
    exact ⟨8, witness_of_certificate certificate_6183⟩
  · subst n
    exact ⟨2, witness_of_certificate certificate_6185⟩
  · subst n
    exact ⟨5, witness_of_certificate certificate_6187⟩
  · subst n
    exact ⟨2, witness_of_certificate certificate_6189⟩
  · subst n
    exact ⟨27, witness_of_certificate certificate_6191⟩
  · subst n
    exact ⟨2, witness_of_certificate certificate_6193⟩
  · subst n
    exact ⟨4, witness_of_certificate certificate_6195⟩
  · subst n
    exact ⟨2, witness_of_certificate certificate_6197⟩
  · subst n
    exact ⟨5, witness_of_certificate certificate_6199⟩
  · subst n
    exact ⟨2, witness_of_certificate certificate_6201⟩
  · subst n
    exact ⟨7, witness_of_certificate certificate_6203⟩
  · subst n
    exact ⟨2, witness_of_certificate certificate_6205⟩
  · subst n
    exact ⟨16, witness_of_certificate certificate_6207⟩
  · subst n
    exact ⟨2, witness_of_certificate certificate_6209⟩
  · subst n
    exact ⟨4, witness_of_certificate certificate_6211⟩
  · subst n
    exact ⟨2, witness_of_certificate certificate_6213⟩
  · subst n
    exact ⟨13, witness_of_certificate certificate_6215⟩
  · subst n
    exact ⟨2, witness_of_certificate certificate_6217⟩
  · subst n
    exact ⟨5, witness_of_certificate certificate_6219⟩
  · subst n
    exact ⟨2, witness_of_certificate certificate_6221⟩
  · subst n
    exact ⟨8, witness_of_certificate certificate_6223⟩
  · subst n
    exact ⟨2, witness_of_certificate certificate_6225⟩
  · subst n
    exact ⟨4, witness_of_certificate certificate_6227⟩
  · subst n
    exact ⟨2, witness_of_certificate certificate_6229⟩

end Collatz.Research.CoefficientDescent.Batch093
