import Collatz.Research.CoefficientDescent.Basic

namespace Collatz.Research.CoefficientDescent.Batch078

open FirstDescentClass

set_option maxRecDepth 20000
set_option maxHeartbeats 0

/-- Checked base and every prefix for input 5159. -/
theorem certificate_5159 : classCertificateB 8 5159 = true := by
  decide

/-- The same exact first-descent time holds on an infinite dyadic ray. -/
theorem ray_5159 (m : Nat) : stoppingTime (2 ^ 8 * m + 5159) 8 :=
  stoppingTime_of_classCertificate certificate_5159 m

/-- Checked base and every prefix for input 5161. -/
theorem certificate_5161 : classCertificateB 2 5161 = true := by
  decide

/-- The same exact first-descent time holds on an infinite dyadic ray. -/
theorem ray_5161 (m : Nat) : stoppingTime (2 ^ 2 * m + 5161) 2 :=
  stoppingTime_of_classCertificate certificate_5161 m

/-- Checked base and every prefix for input 5163. -/
theorem certificate_5163 : classCertificateB 5 5163 = true := by
  decide

/-- The same exact first-descent time holds on an infinite dyadic ray. -/
theorem ray_5163 (m : Nat) : stoppingTime (2 ^ 5 * m + 5163) 5 :=
  stoppingTime_of_classCertificate certificate_5163 m

/-- Checked base and every prefix for input 5165. -/
theorem certificate_5165 : classCertificateB 2 5165 = true := by
  decide

/-- The same exact first-descent time holds on an infinite dyadic ray. -/
theorem ray_5165 (m : Nat) : stoppingTime (2 ^ 2 * m + 5165) 2 :=
  stoppingTime_of_classCertificate certificate_5165 m

/-- Checked base and every prefix for input 5167. -/
theorem certificate_5167 : classCertificateB 18 5167 = true := by
  decide

/-- The same exact first-descent time holds on an infinite dyadic ray. -/
theorem ray_5167 (m : Nat) : stoppingTime (2 ^ 18 * m + 5167) 18 :=
  stoppingTime_of_classCertificate certificate_5167 m

/-- Checked base and every prefix for input 5169. -/
theorem certificate_5169 : classCertificateB 2 5169 = true := by
  decide

/-- The same exact first-descent time holds on an infinite dyadic ray. -/
theorem ray_5169 (m : Nat) : stoppingTime (2 ^ 2 * m + 5169) 2 :=
  stoppingTime_of_classCertificate certificate_5169 m

/-- Checked base and every prefix for input 5171. -/
theorem certificate_5171 : classCertificateB 4 5171 = true := by
  decide

/-- The same exact first-descent time holds on an infinite dyadic ray. -/
theorem ray_5171 (m : Nat) : stoppingTime (2 ^ 4 * m + 5171) 4 :=
  stoppingTime_of_classCertificate certificate_5171 m

/-- Checked base and every prefix for input 5173. -/
theorem certificate_5173 : classCertificateB 2 5173 = true := by
  decide

/-- The same exact first-descent time holds on an infinite dyadic ray. -/
theorem ray_5173 (m : Nat) : stoppingTime (2 ^ 2 * m + 5173) 2 :=
  stoppingTime_of_classCertificate certificate_5173 m

/-- Checked base and every prefix for input 5175. -/
theorem certificate_5175 : classCertificateB 5 5175 = true := by
  decide

/-- The same exact first-descent time holds on an infinite dyadic ray. -/
theorem ray_5175 (m : Nat) : stoppingTime (2 ^ 5 * m + 5175) 5 :=
  stoppingTime_of_classCertificate certificate_5175 m

/-- Checked base and every prefix for input 5177. -/
theorem certificate_5177 : classCertificateB 2 5177 = true := by
  decide

/-- The same exact first-descent time holds on an infinite dyadic ray. -/
theorem ray_5177 (m : Nat) : stoppingTime (2 ^ 2 * m + 5177) 2 :=
  stoppingTime_of_classCertificate certificate_5177 m

/-- Checked base and every prefix for input 5179. -/
theorem certificate_5179 : classCertificateB 7 5179 = true := by
  decide

/-- The same exact first-descent time holds on an infinite dyadic ray. -/
theorem ray_5179 (m : Nat) : stoppingTime (2 ^ 7 * m + 5179) 7 :=
  stoppingTime_of_classCertificate certificate_5179 m

/-- Checked base and every prefix for input 5181. -/
theorem certificate_5181 : classCertificateB 2 5181 = true := by
  decide

/-- The same exact first-descent time holds on an infinite dyadic ray. -/
theorem ray_5181 (m : Nat) : stoppingTime (2 ^ 2 * m + 5181) 2 :=
  stoppingTime_of_classCertificate certificate_5181 m

/-- Checked base and every prefix for input 5183. -/
theorem certificate_5183 : classCertificateB 12 5183 = true := by
  decide

/-- The same exact first-descent time holds on an infinite dyadic ray. -/
theorem ray_5183 (m : Nat) : stoppingTime (2 ^ 12 * m + 5183) 12 :=
  stoppingTime_of_classCertificate certificate_5183 m

/-- Checked base and every prefix for input 5185. -/
theorem certificate_5185 : classCertificateB 2 5185 = true := by
  decide

/-- The same exact first-descent time holds on an infinite dyadic ray. -/
theorem ray_5185 (m : Nat) : stoppingTime (2 ^ 2 * m + 5185) 2 :=
  stoppingTime_of_classCertificate certificate_5185 m

/-- Checked base and every prefix for input 5187. -/
theorem certificate_5187 : classCertificateB 4 5187 = true := by
  decide

/-- The same exact first-descent time holds on an infinite dyadic ray. -/
theorem ray_5187 (m : Nat) : stoppingTime (2 ^ 4 * m + 5187) 4 :=
  stoppingTime_of_classCertificate certificate_5187 m

/-- Checked base and every prefix for input 5189. -/
theorem certificate_5189 : classCertificateB 2 5189 = true := by
  decide

/-- The same exact first-descent time holds on an infinite dyadic ray. -/
theorem ray_5189 (m : Nat) : stoppingTime (2 ^ 2 * m + 5189) 2 :=
  stoppingTime_of_classCertificate certificate_5189 m

/-- Checked base and every prefix for input 5191. -/
theorem certificate_5191 : classCertificateB 13 5191 = true := by
  decide

/-- The same exact first-descent time holds on an infinite dyadic ray. -/
theorem ray_5191 (m : Nat) : stoppingTime (2 ^ 13 * m + 5191) 13 :=
  stoppingTime_of_classCertificate certificate_5191 m

/-- Checked base and every prefix for input 5193. -/
theorem certificate_5193 : classCertificateB 2 5193 = true := by
  decide

/-- The same exact first-descent time holds on an infinite dyadic ray. -/
theorem ray_5193 (m : Nat) : stoppingTime (2 ^ 2 * m + 5193) 2 :=
  stoppingTime_of_classCertificate certificate_5193 m

/-- Checked base and every prefix for input 5195. -/
theorem certificate_5195 : classCertificateB 5 5195 = true := by
  decide

/-- The same exact first-descent time holds on an infinite dyadic ray. -/
theorem ray_5195 (m : Nat) : stoppingTime (2 ^ 5 * m + 5195) 5 :=
  stoppingTime_of_classCertificate certificate_5195 m

/-- Checked base and every prefix for input 5197. -/
theorem certificate_5197 : classCertificateB 2 5197 = true := by
  decide

/-- The same exact first-descent time holds on an infinite dyadic ray. -/
theorem ray_5197 (m : Nat) : stoppingTime (2 ^ 2 * m + 5197) 2 :=
  stoppingTime_of_classCertificate certificate_5197 m

/-- Checked base and every prefix for input 5199. -/
theorem certificate_5199 : classCertificateB 8 5199 = true := by
  decide

/-- The same exact first-descent time holds on an infinite dyadic ray. -/
theorem ray_5199 (m : Nat) : stoppingTime (2 ^ 8 * m + 5199) 8 :=
  stoppingTime_of_classCertificate certificate_5199 m

/-- Checked base and every prefix for input 5201. -/
theorem certificate_5201 : classCertificateB 2 5201 = true := by
  decide

/-- The same exact first-descent time holds on an infinite dyadic ray. -/
theorem ray_5201 (m : Nat) : stoppingTime (2 ^ 2 * m + 5201) 2 :=
  stoppingTime_of_classCertificate certificate_5201 m

/-- Checked base and every prefix for input 5203. -/
theorem certificate_5203 : classCertificateB 4 5203 = true := by
  decide

/-- The same exact first-descent time holds on an infinite dyadic ray. -/
theorem ray_5203 (m : Nat) : stoppingTime (2 ^ 4 * m + 5203) 4 :=
  stoppingTime_of_classCertificate certificate_5203 m

/-- Checked base and every prefix for input 5205. -/
theorem certificate_5205 : classCertificateB 2 5205 = true := by
  decide

/-- The same exact first-descent time holds on an infinite dyadic ray. -/
theorem ray_5205 (m : Nat) : stoppingTime (2 ^ 2 * m + 5205) 2 :=
  stoppingTime_of_classCertificate certificate_5205 m

/-- Checked base and every prefix for input 5207. -/
theorem certificate_5207 : classCertificateB 5 5207 = true := by
  decide

/-- The same exact first-descent time holds on an infinite dyadic ray. -/
theorem ray_5207 (m : Nat) : stoppingTime (2 ^ 5 * m + 5207) 5 :=
  stoppingTime_of_classCertificate certificate_5207 m

/-- Checked base and every prefix for input 5209. -/
theorem certificate_5209 : classCertificateB 2 5209 = true := by
  decide

/-- The same exact first-descent time holds on an infinite dyadic ray. -/
theorem ray_5209 (m : Nat) : stoppingTime (2 ^ 2 * m + 5209) 2 :=
  stoppingTime_of_classCertificate certificate_5209 m

/-- Checked base and every prefix for input 5211. -/
theorem certificate_5211 : classCertificateB 20 5211 = true := by
  decide

/-- The same exact first-descent time holds on an infinite dyadic ray. -/
theorem ray_5211 (m : Nat) : stoppingTime (2 ^ 20 * m + 5211) 20 :=
  stoppingTime_of_classCertificate certificate_5211 m

/-- Checked base and every prefix for input 5213. -/
theorem certificate_5213 : classCertificateB 2 5213 = true := by
  decide

/-- The same exact first-descent time holds on an infinite dyadic ray. -/
theorem ray_5213 (m : Nat) : stoppingTime (2 ^ 2 * m + 5213) 2 :=
  stoppingTime_of_classCertificate certificate_5213 m

/-- Checked base and every prefix for input 5215. -/
theorem certificate_5215 : classCertificateB 8 5215 = true := by
  decide

/-- The same exact first-descent time holds on an infinite dyadic ray. -/
theorem ray_5215 (m : Nat) : stoppingTime (2 ^ 8 * m + 5215) 8 :=
  stoppingTime_of_classCertificate certificate_5215 m

/-- Checked base and every prefix for input 5217. -/
theorem certificate_5217 : classCertificateB 2 5217 = true := by
  decide

/-- The same exact first-descent time holds on an infinite dyadic ray. -/
theorem ray_5217 (m : Nat) : stoppingTime (2 ^ 2 * m + 5217) 2 :=
  stoppingTime_of_classCertificate certificate_5217 m

/-- Checked base and every prefix for input 5219. -/
theorem certificate_5219 : classCertificateB 4 5219 = true := by
  decide

/-- The same exact first-descent time holds on an infinite dyadic ray. -/
theorem ray_5219 (m : Nat) : stoppingTime (2 ^ 4 * m + 5219) 4 :=
  stoppingTime_of_classCertificate certificate_5219 m

/-- Checked base and every prefix for input 5221. -/
theorem certificate_5221 : classCertificateB 2 5221 = true := by
  decide

/-- The same exact first-descent time holds on an infinite dyadic ray. -/
theorem ray_5221 (m : Nat) : stoppingTime (2 ^ 2 * m + 5221) 2 :=
  stoppingTime_of_classCertificate certificate_5221 m

/-- Checked base and every prefix for input 5223. -/
theorem certificate_5223 : classCertificateB 20 5223 = true := by
  decide

/-- The same exact first-descent time holds on an infinite dyadic ray. -/
theorem ray_5223 (m : Nat) : stoppingTime (2 ^ 20 * m + 5223) 20 :=
  stoppingTime_of_classCertificate certificate_5223 m

/-- Checked base and every prefix for input 5225. -/
theorem certificate_5225 : classCertificateB 2 5225 = true := by
  decide

/-- The same exact first-descent time holds on an infinite dyadic ray. -/
theorem ray_5225 (m : Nat) : stoppingTime (2 ^ 2 * m + 5225) 2 :=
  stoppingTime_of_classCertificate certificate_5225 m

/-- Exhaustive coverage of the odd inputs in this batch, with no gaps. -/
theorem coverage : CertifiedRange 5159 5227 := by
  intro n hlo hhi hodd
  have hn : n = 5159 ∨ n = 5161 ∨ n = 5163 ∨ n = 5165 ∨ n = 5167 ∨ n = 5169 ∨ n = 5171 ∨ n = 5173 ∨ n = 5175 ∨ n = 5177 ∨ n = 5179 ∨ n = 5181 ∨ n = 5183 ∨ n = 5185 ∨ n = 5187 ∨ n = 5189 ∨ n = 5191 ∨ n = 5193 ∨ n = 5195 ∨ n = 5197 ∨ n = 5199 ∨ n = 5201 ∨ n = 5203 ∨ n = 5205 ∨ n = 5207 ∨ n = 5209 ∨ n = 5211 ∨ n = 5213 ∨ n = 5215 ∨ n = 5217 ∨ n = 5219 ∨ n = 5221 ∨ n = 5223 ∨ n = 5225 := by omega
  rcases hn with h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h
  · subst n
    exact ⟨8, witness_of_certificate certificate_5159⟩
  · subst n
    exact ⟨2, witness_of_certificate certificate_5161⟩
  · subst n
    exact ⟨5, witness_of_certificate certificate_5163⟩
  · subst n
    exact ⟨2, witness_of_certificate certificate_5165⟩
  · subst n
    exact ⟨18, witness_of_certificate certificate_5167⟩
  · subst n
    exact ⟨2, witness_of_certificate certificate_5169⟩
  · subst n
    exact ⟨4, witness_of_certificate certificate_5171⟩
  · subst n
    exact ⟨2, witness_of_certificate certificate_5173⟩
  · subst n
    exact ⟨5, witness_of_certificate certificate_5175⟩
  · subst n
    exact ⟨2, witness_of_certificate certificate_5177⟩
  · subst n
    exact ⟨7, witness_of_certificate certificate_5179⟩
  · subst n
    exact ⟨2, witness_of_certificate certificate_5181⟩
  · subst n
    exact ⟨12, witness_of_certificate certificate_5183⟩
  · subst n
    exact ⟨2, witness_of_certificate certificate_5185⟩
  · subst n
    exact ⟨4, witness_of_certificate certificate_5187⟩
  · subst n
    exact ⟨2, witness_of_certificate certificate_5189⟩
  · subst n
    exact ⟨13, witness_of_certificate certificate_5191⟩
  · subst n
    exact ⟨2, witness_of_certificate certificate_5193⟩
  · subst n
    exact ⟨5, witness_of_certificate certificate_5195⟩
  · subst n
    exact ⟨2, witness_of_certificate certificate_5197⟩
  · subst n
    exact ⟨8, witness_of_certificate certificate_5199⟩
  · subst n
    exact ⟨2, witness_of_certificate certificate_5201⟩
  · subst n
    exact ⟨4, witness_of_certificate certificate_5203⟩
  · subst n
    exact ⟨2, witness_of_certificate certificate_5205⟩
  · subst n
    exact ⟨5, witness_of_certificate certificate_5207⟩
  · subst n
    exact ⟨2, witness_of_certificate certificate_5209⟩
  · subst n
    exact ⟨20, witness_of_certificate certificate_5211⟩
  · subst n
    exact ⟨2, witness_of_certificate certificate_5213⟩
  · subst n
    exact ⟨8, witness_of_certificate certificate_5215⟩
  · subst n
    exact ⟨2, witness_of_certificate certificate_5217⟩
  · subst n
    exact ⟨4, witness_of_certificate certificate_5219⟩
  · subst n
    exact ⟨2, witness_of_certificate certificate_5221⟩
  · subst n
    exact ⟨20, witness_of_certificate certificate_5223⟩
  · subst n
    exact ⟨2, witness_of_certificate certificate_5225⟩

end Collatz.Research.CoefficientDescent.Batch078
