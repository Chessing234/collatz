import Collatz.Research.CoefficientDescent.Basic

namespace Collatz.Research.CoefficientDescent.Batch063

open FirstDescentClass

set_option maxRecDepth 20000
set_option maxHeartbeats 0

/-- Checked base and every prefix for input 4155. -/
theorem certificate_4155 : classCertificateB 7 4155 = true := by
  decide

/-- The same exact first-descent time holds on an infinite dyadic ray. -/
theorem ray_4155 (m : Nat) : stoppingTime (2 ^ 7 * m + 4155) 7 :=
  stoppingTime_of_classCertificate certificate_4155 m

/-- Checked base and every prefix for input 4157. -/
theorem certificate_4157 : classCertificateB 2 4157 = true := by
  decide

/-- The same exact first-descent time holds on an infinite dyadic ray. -/
theorem ray_4157 (m : Nat) : stoppingTime (2 ^ 2 * m + 4157) 2 :=
  stoppingTime_of_classCertificate certificate_4157 m

/-- Checked base and every prefix for input 4159. -/
theorem certificate_4159 : classCertificateB 13 4159 = true := by
  decide

/-- The same exact first-descent time holds on an infinite dyadic ray. -/
theorem ray_4159 (m : Nat) : stoppingTime (2 ^ 13 * m + 4159) 13 :=
  stoppingTime_of_classCertificate certificate_4159 m

/-- Checked base and every prefix for input 4161. -/
theorem certificate_4161 : classCertificateB 2 4161 = true := by
  decide

/-- The same exact first-descent time holds on an infinite dyadic ray. -/
theorem ray_4161 (m : Nat) : stoppingTime (2 ^ 2 * m + 4161) 2 :=
  stoppingTime_of_classCertificate certificate_4161 m

/-- Checked base and every prefix for input 4163. -/
theorem certificate_4163 : classCertificateB 4 4163 = true := by
  decide

/-- The same exact first-descent time holds on an infinite dyadic ray. -/
theorem ray_4163 (m : Nat) : stoppingTime (2 ^ 4 * m + 4163) 4 :=
  stoppingTime_of_classCertificate certificate_4163 m

/-- Checked base and every prefix for input 4165. -/
theorem certificate_4165 : classCertificateB 2 4165 = true := by
  decide

/-- The same exact first-descent time holds on an infinite dyadic ray. -/
theorem ray_4165 (m : Nat) : stoppingTime (2 ^ 2 * m + 4165) 2 :=
  stoppingTime_of_classCertificate certificate_4165 m

/-- Checked base and every prefix for input 4167. -/
theorem certificate_4167 : classCertificateB 20 4167 = true := by
  decide

/-- The same exact first-descent time holds on an infinite dyadic ray. -/
theorem ray_4167 (m : Nat) : stoppingTime (2 ^ 20 * m + 4167) 20 :=
  stoppingTime_of_classCertificate certificate_4167 m

/-- Checked base and every prefix for input 4169. -/
theorem certificate_4169 : classCertificateB 2 4169 = true := by
  decide

/-- The same exact first-descent time holds on an infinite dyadic ray. -/
theorem ray_4169 (m : Nat) : stoppingTime (2 ^ 2 * m + 4169) 2 :=
  stoppingTime_of_classCertificate certificate_4169 m

/-- Checked base and every prefix for input 4171. -/
theorem certificate_4171 : classCertificateB 5 4171 = true := by
  decide

/-- The same exact first-descent time holds on an infinite dyadic ray. -/
theorem ray_4171 (m : Nat) : stoppingTime (2 ^ 5 * m + 4171) 5 :=
  stoppingTime_of_classCertificate certificate_4171 m

/-- Checked base and every prefix for input 4173. -/
theorem certificate_4173 : classCertificateB 2 4173 = true := by
  decide

/-- The same exact first-descent time holds on an infinite dyadic ray. -/
theorem ray_4173 (m : Nat) : stoppingTime (2 ^ 2 * m + 4173) 2 :=
  stoppingTime_of_classCertificate certificate_4173 m

/-- Checked base and every prefix for input 4175. -/
theorem certificate_4175 : classCertificateB 8 4175 = true := by
  decide

/-- The same exact first-descent time holds on an infinite dyadic ray. -/
theorem ray_4175 (m : Nat) : stoppingTime (2 ^ 8 * m + 4175) 8 :=
  stoppingTime_of_classCertificate certificate_4175 m

/-- Checked base and every prefix for input 4177. -/
theorem certificate_4177 : classCertificateB 2 4177 = true := by
  decide

/-- The same exact first-descent time holds on an infinite dyadic ray. -/
theorem ray_4177 (m : Nat) : stoppingTime (2 ^ 2 * m + 4177) 2 :=
  stoppingTime_of_classCertificate certificate_4177 m

/-- Checked base and every prefix for input 4179. -/
theorem certificate_4179 : classCertificateB 4 4179 = true := by
  decide

/-- The same exact first-descent time holds on an infinite dyadic ray. -/
theorem ray_4179 (m : Nat) : stoppingTime (2 ^ 4 * m + 4179) 4 :=
  stoppingTime_of_classCertificate certificate_4179 m

/-- Checked base and every prefix for input 4181. -/
theorem certificate_4181 : classCertificateB 2 4181 = true := by
  decide

/-- The same exact first-descent time holds on an infinite dyadic ray. -/
theorem ray_4181 (m : Nat) : stoppingTime (2 ^ 2 * m + 4181) 2 :=
  stoppingTime_of_classCertificate certificate_4181 m

/-- Checked base and every prefix for input 4183. -/
theorem certificate_4183 : classCertificateB 5 4183 = true := by
  decide

/-- The same exact first-descent time holds on an infinite dyadic ray. -/
theorem ray_4183 (m : Nat) : stoppingTime (2 ^ 5 * m + 4183) 5 :=
  stoppingTime_of_classCertificate certificate_4183 m

/-- Checked base and every prefix for input 4185. -/
theorem certificate_4185 : classCertificateB 2 4185 = true := by
  decide

/-- The same exact first-descent time holds on an infinite dyadic ray. -/
theorem ray_4185 (m : Nat) : stoppingTime (2 ^ 2 * m + 4185) 2 :=
  stoppingTime_of_classCertificate certificate_4185 m

/-- Checked base and every prefix for input 4187. -/
theorem certificate_4187 : classCertificateB 15 4187 = true := by
  decide

/-- The same exact first-descent time holds on an infinite dyadic ray. -/
theorem ray_4187 (m : Nat) : stoppingTime (2 ^ 15 * m + 4187) 15 :=
  stoppingTime_of_classCertificate certificate_4187 m

/-- Checked base and every prefix for input 4189. -/
theorem certificate_4189 : classCertificateB 2 4189 = true := by
  decide

/-- The same exact first-descent time holds on an infinite dyadic ray. -/
theorem ray_4189 (m : Nat) : stoppingTime (2 ^ 2 * m + 4189) 2 :=
  stoppingTime_of_classCertificate certificate_4189 m

/-- Checked base and every prefix for input 4191. -/
theorem certificate_4191 : classCertificateB 8 4191 = true := by
  decide

/-- The same exact first-descent time holds on an infinite dyadic ray. -/
theorem ray_4191 (m : Nat) : stoppingTime (2 ^ 8 * m + 4191) 8 :=
  stoppingTime_of_classCertificate certificate_4191 m

/-- Checked base and every prefix for input 4193. -/
theorem certificate_4193 : classCertificateB 2 4193 = true := by
  decide

/-- The same exact first-descent time holds on an infinite dyadic ray. -/
theorem ray_4193 (m : Nat) : stoppingTime (2 ^ 2 * m + 4193) 2 :=
  stoppingTime_of_classCertificate certificate_4193 m

/-- Checked base and every prefix for input 4195. -/
theorem certificate_4195 : classCertificateB 4 4195 = true := by
  decide

/-- The same exact first-descent time holds on an infinite dyadic ray. -/
theorem ray_4195 (m : Nat) : stoppingTime (2 ^ 4 * m + 4195) 4 :=
  stoppingTime_of_classCertificate certificate_4195 m

/-- Checked base and every prefix for input 4197. -/
theorem certificate_4197 : classCertificateB 2 4197 = true := by
  decide

/-- The same exact first-descent time holds on an infinite dyadic ray. -/
theorem ray_4197 (m : Nat) : stoppingTime (2 ^ 2 * m + 4197) 2 :=
  stoppingTime_of_classCertificate certificate_4197 m

/-- Checked base and every prefix for input 4199. -/
theorem certificate_4199 : classCertificateB 13 4199 = true := by
  decide

/-- The same exact first-descent time holds on an infinite dyadic ray. -/
theorem ray_4199 (m : Nat) : stoppingTime (2 ^ 13 * m + 4199) 13 :=
  stoppingTime_of_classCertificate certificate_4199 m

/-- Checked base and every prefix for input 4201. -/
theorem certificate_4201 : classCertificateB 2 4201 = true := by
  decide

/-- The same exact first-descent time holds on an infinite dyadic ray. -/
theorem ray_4201 (m : Nat) : stoppingTime (2 ^ 2 * m + 4201) 2 :=
  stoppingTime_of_classCertificate certificate_4201 m

/-- Checked base and every prefix for input 4203. -/
theorem certificate_4203 : classCertificateB 5 4203 = true := by
  decide

/-- The same exact first-descent time holds on an infinite dyadic ray. -/
theorem ray_4203 (m : Nat) : stoppingTime (2 ^ 5 * m + 4203) 5 :=
  stoppingTime_of_classCertificate certificate_4203 m

/-- Checked base and every prefix for input 4205. -/
theorem certificate_4205 : classCertificateB 2 4205 = true := by
  decide

/-- The same exact first-descent time holds on an infinite dyadic ray. -/
theorem ray_4205 (m : Nat) : stoppingTime (2 ^ 2 * m + 4205) 2 :=
  stoppingTime_of_classCertificate certificate_4205 m

/-- Checked base and every prefix for input 4207. -/
theorem certificate_4207 : classCertificateB 35 4207 = true := by
  decide

/-- The same exact first-descent time holds on an infinite dyadic ray. -/
theorem ray_4207 (m : Nat) : stoppingTime (2 ^ 35 * m + 4207) 35 :=
  stoppingTime_of_classCertificate certificate_4207 m

/-- Checked base and every prefix for input 4209. -/
theorem certificate_4209 : classCertificateB 2 4209 = true := by
  decide

/-- The same exact first-descent time holds on an infinite dyadic ray. -/
theorem ray_4209 (m : Nat) : stoppingTime (2 ^ 2 * m + 4209) 2 :=
  stoppingTime_of_classCertificate certificate_4209 m

/-- Checked base and every prefix for input 4211. -/
theorem certificate_4211 : classCertificateB 4 4211 = true := by
  decide

/-- The same exact first-descent time holds on an infinite dyadic ray. -/
theorem ray_4211 (m : Nat) : stoppingTime (2 ^ 4 * m + 4211) 4 :=
  stoppingTime_of_classCertificate certificate_4211 m

/-- Checked base and every prefix for input 4213. -/
theorem certificate_4213 : classCertificateB 2 4213 = true := by
  decide

/-- The same exact first-descent time holds on an infinite dyadic ray. -/
theorem ray_4213 (m : Nat) : stoppingTime (2 ^ 2 * m + 4213) 2 :=
  stoppingTime_of_classCertificate certificate_4213 m

/-- Checked base and every prefix for input 4215. -/
theorem certificate_4215 : classCertificateB 5 4215 = true := by
  decide

/-- The same exact first-descent time holds on an infinite dyadic ray. -/
theorem ray_4215 (m : Nat) : stoppingTime (2 ^ 5 * m + 4215) 5 :=
  stoppingTime_of_classCertificate certificate_4215 m

/-- Checked base and every prefix for input 4217. -/
theorem certificate_4217 : classCertificateB 2 4217 = true := by
  decide

/-- The same exact first-descent time holds on an infinite dyadic ray. -/
theorem ray_4217 (m : Nat) : stoppingTime (2 ^ 2 * m + 4217) 2 :=
  stoppingTime_of_classCertificate certificate_4217 m

/-- Checked base and every prefix for input 4219. -/
theorem certificate_4219 : classCertificateB 8 4219 = true := by
  decide

/-- The same exact first-descent time holds on an infinite dyadic ray. -/
theorem ray_4219 (m : Nat) : stoppingTime (2 ^ 8 * m + 4219) 8 :=
  stoppingTime_of_classCertificate certificate_4219 m

/-- Exhaustive coverage of the odd inputs in this batch, with no gaps. -/
theorem coverage : CertifiedRange 4155 4221 := by
  intro n hlo hhi hodd
  have hn : n = 4155 ∨ n = 4157 ∨ n = 4159 ∨ n = 4161 ∨ n = 4163 ∨ n = 4165 ∨ n = 4167 ∨ n = 4169 ∨ n = 4171 ∨ n = 4173 ∨ n = 4175 ∨ n = 4177 ∨ n = 4179 ∨ n = 4181 ∨ n = 4183 ∨ n = 4185 ∨ n = 4187 ∨ n = 4189 ∨ n = 4191 ∨ n = 4193 ∨ n = 4195 ∨ n = 4197 ∨ n = 4199 ∨ n = 4201 ∨ n = 4203 ∨ n = 4205 ∨ n = 4207 ∨ n = 4209 ∨ n = 4211 ∨ n = 4213 ∨ n = 4215 ∨ n = 4217 ∨ n = 4219 := by omega
  rcases hn with h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h
  · subst n
    exact ⟨7, witness_of_certificate certificate_4155⟩
  · subst n
    exact ⟨2, witness_of_certificate certificate_4157⟩
  · subst n
    exact ⟨13, witness_of_certificate certificate_4159⟩
  · subst n
    exact ⟨2, witness_of_certificate certificate_4161⟩
  · subst n
    exact ⟨4, witness_of_certificate certificate_4163⟩
  · subst n
    exact ⟨2, witness_of_certificate certificate_4165⟩
  · subst n
    exact ⟨20, witness_of_certificate certificate_4167⟩
  · subst n
    exact ⟨2, witness_of_certificate certificate_4169⟩
  · subst n
    exact ⟨5, witness_of_certificate certificate_4171⟩
  · subst n
    exact ⟨2, witness_of_certificate certificate_4173⟩
  · subst n
    exact ⟨8, witness_of_certificate certificate_4175⟩
  · subst n
    exact ⟨2, witness_of_certificate certificate_4177⟩
  · subst n
    exact ⟨4, witness_of_certificate certificate_4179⟩
  · subst n
    exact ⟨2, witness_of_certificate certificate_4181⟩
  · subst n
    exact ⟨5, witness_of_certificate certificate_4183⟩
  · subst n
    exact ⟨2, witness_of_certificate certificate_4185⟩
  · subst n
    exact ⟨15, witness_of_certificate certificate_4187⟩
  · subst n
    exact ⟨2, witness_of_certificate certificate_4189⟩
  · subst n
    exact ⟨8, witness_of_certificate certificate_4191⟩
  · subst n
    exact ⟨2, witness_of_certificate certificate_4193⟩
  · subst n
    exact ⟨4, witness_of_certificate certificate_4195⟩
  · subst n
    exact ⟨2, witness_of_certificate certificate_4197⟩
  · subst n
    exact ⟨13, witness_of_certificate certificate_4199⟩
  · subst n
    exact ⟨2, witness_of_certificate certificate_4201⟩
  · subst n
    exact ⟨5, witness_of_certificate certificate_4203⟩
  · subst n
    exact ⟨2, witness_of_certificate certificate_4205⟩
  · subst n
    exact ⟨35, witness_of_certificate certificate_4207⟩
  · subst n
    exact ⟨2, witness_of_certificate certificate_4209⟩
  · subst n
    exact ⟨4, witness_of_certificate certificate_4211⟩
  · subst n
    exact ⟨2, witness_of_certificate certificate_4213⟩
  · subst n
    exact ⟨5, witness_of_certificate certificate_4215⟩
  · subst n
    exact ⟨2, witness_of_certificate certificate_4217⟩
  · subst n
    exact ⟨8, witness_of_certificate certificate_4219⟩

end Collatz.Research.CoefficientDescent.Batch063
