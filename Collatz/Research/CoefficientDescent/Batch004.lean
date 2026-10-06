import Collatz.Research.CoefficientDescent.Basic

namespace Collatz.Research.CoefficientDescent.Batch004

open FirstDescentClass

set_option maxRecDepth 20000
set_option maxHeartbeats 0

/-- Checked base and every prefix for input 203. -/
theorem certificate_203 : classCertificateB 5 203 = true := by
  decide

/-- The same exact first-descent time holds on an infinite dyadic ray. -/
theorem ray_203 (m : Nat) : stoppingTime (2 ^ 5 * m + 203) 5 :=
  stoppingTime_of_classCertificate certificate_203 m

/-- Checked base and every prefix for input 205. -/
theorem certificate_205 : classCertificateB 2 205 = true := by
  decide

/-- The same exact first-descent time holds on an infinite dyadic ray. -/
theorem ray_205 (m : Nat) : stoppingTime (2 ^ 2 * m + 205) 2 :=
  stoppingTime_of_classCertificate certificate_205 m

/-- Checked base and every prefix for input 207. -/
theorem certificate_207 : classCertificateB 13 207 = true := by
  decide

/-- The same exact first-descent time holds on an infinite dyadic ray. -/
theorem ray_207 (m : Nat) : stoppingTime (2 ^ 13 * m + 207) 13 :=
  stoppingTime_of_classCertificate certificate_207 m

/-- Checked base and every prefix for input 209. -/
theorem certificate_209 : classCertificateB 2 209 = true := by
  decide

/-- The same exact first-descent time holds on an infinite dyadic ray. -/
theorem ray_209 (m : Nat) : stoppingTime (2 ^ 2 * m + 209) 2 :=
  stoppingTime_of_classCertificate certificate_209 m

/-- Checked base and every prefix for input 211. -/
theorem certificate_211 : classCertificateB 4 211 = true := by
  decide

/-- The same exact first-descent time holds on an infinite dyadic ray. -/
theorem ray_211 (m : Nat) : stoppingTime (2 ^ 4 * m + 211) 4 :=
  stoppingTime_of_classCertificate certificate_211 m

/-- Checked base and every prefix for input 213. -/
theorem certificate_213 : classCertificateB 2 213 = true := by
  decide

/-- The same exact first-descent time holds on an infinite dyadic ray. -/
theorem ray_213 (m : Nat) : stoppingTime (2 ^ 2 * m + 213) 2 :=
  stoppingTime_of_classCertificate certificate_213 m

/-- Checked base and every prefix for input 215. -/
theorem certificate_215 : classCertificateB 5 215 = true := by
  decide

/-- The same exact first-descent time holds on an infinite dyadic ray. -/
theorem ray_215 (m : Nat) : stoppingTime (2 ^ 5 * m + 215) 5 :=
  stoppingTime_of_classCertificate certificate_215 m

/-- Checked base and every prefix for input 217. -/
theorem certificate_217 : classCertificateB 2 217 = true := by
  decide

/-- The same exact first-descent time holds on an infinite dyadic ray. -/
theorem ray_217 (m : Nat) : stoppingTime (2 ^ 2 * m + 217) 2 :=
  stoppingTime_of_classCertificate certificate_217 m

/-- Checked base and every prefix for input 219. -/
theorem certificate_219 : classCertificateB 8 219 = true := by
  decide

/-- The same exact first-descent time holds on an infinite dyadic ray. -/
theorem ray_219 (m : Nat) : stoppingTime (2 ^ 8 * m + 219) 8 :=
  stoppingTime_of_classCertificate certificate_219 m

/-- Checked base and every prefix for input 221. -/
theorem certificate_221 : classCertificateB 2 221 = true := by
  decide

/-- The same exact first-descent time holds on an infinite dyadic ray. -/
theorem ray_221 (m : Nat) : stoppingTime (2 ^ 2 * m + 221) 2 :=
  stoppingTime_of_classCertificate certificate_221 m

/-- Checked base and every prefix for input 223. -/
theorem certificate_223 : classCertificateB 31 223 = true := by
  decide

/-- The same exact first-descent time holds on an infinite dyadic ray. -/
theorem ray_223 (m : Nat) : stoppingTime (2 ^ 31 * m + 223) 31 :=
  stoppingTime_of_classCertificate certificate_223 m

/-- Checked base and every prefix for input 225. -/
theorem certificate_225 : classCertificateB 2 225 = true := by
  decide

/-- The same exact first-descent time holds on an infinite dyadic ray. -/
theorem ray_225 (m : Nat) : stoppingTime (2 ^ 2 * m + 225) 2 :=
  stoppingTime_of_classCertificate certificate_225 m

/-- Checked base and every prefix for input 227. -/
theorem certificate_227 : classCertificateB 4 227 = true := by
  decide

/-- The same exact first-descent time holds on an infinite dyadic ray. -/
theorem ray_227 (m : Nat) : stoppingTime (2 ^ 4 * m + 227) 4 :=
  stoppingTime_of_classCertificate certificate_227 m

/-- Checked base and every prefix for input 229. -/
theorem certificate_229 : classCertificateB 2 229 = true := by
  decide

/-- The same exact first-descent time holds on an infinite dyadic ray. -/
theorem ray_229 (m : Nat) : stoppingTime (2 ^ 2 * m + 229) 2 :=
  stoppingTime_of_classCertificate certificate_229 m

/-- Checked base and every prefix for input 231. -/
theorem certificate_231 : classCertificateB 12 231 = true := by
  decide

/-- The same exact first-descent time holds on an infinite dyadic ray. -/
theorem ray_231 (m : Nat) : stoppingTime (2 ^ 12 * m + 231) 12 :=
  stoppingTime_of_classCertificate certificate_231 m

/-- Checked base and every prefix for input 233. -/
theorem certificate_233 : classCertificateB 2 233 = true := by
  decide

/-- The same exact first-descent time holds on an infinite dyadic ray. -/
theorem ray_233 (m : Nat) : stoppingTime (2 ^ 2 * m + 233) 2 :=
  stoppingTime_of_classCertificate certificate_233 m

/-- Checked base and every prefix for input 235. -/
theorem certificate_235 : classCertificateB 5 235 = true := by
  decide

/-- The same exact first-descent time holds on an infinite dyadic ray. -/
theorem ray_235 (m : Nat) : stoppingTime (2 ^ 5 * m + 235) 5 :=
  stoppingTime_of_classCertificate certificate_235 m

/-- Checked base and every prefix for input 237. -/
theorem certificate_237 : classCertificateB 2 237 = true := by
  decide

/-- The same exact first-descent time holds on an infinite dyadic ray. -/
theorem ray_237 (m : Nat) : stoppingTime (2 ^ 2 * m + 237) 2 :=
  stoppingTime_of_classCertificate certificate_237 m

/-- Checked base and every prefix for input 239. -/
theorem certificate_239 : classCertificateB 20 239 = true := by
  decide

/-- The same exact first-descent time holds on an infinite dyadic ray. -/
theorem ray_239 (m : Nat) : stoppingTime (2 ^ 20 * m + 239) 20 :=
  stoppingTime_of_classCertificate certificate_239 m

/-- Checked base and every prefix for input 241. -/
theorem certificate_241 : classCertificateB 2 241 = true := by
  decide

/-- The same exact first-descent time holds on an infinite dyadic ray. -/
theorem ray_241 (m : Nat) : stoppingTime (2 ^ 2 * m + 241) 2 :=
  stoppingTime_of_classCertificate certificate_241 m

/-- Checked base and every prefix for input 243. -/
theorem certificate_243 : classCertificateB 4 243 = true := by
  decide

/-- The same exact first-descent time holds on an infinite dyadic ray. -/
theorem ray_243 (m : Nat) : stoppingTime (2 ^ 4 * m + 243) 4 :=
  stoppingTime_of_classCertificate certificate_243 m

/-- Checked base and every prefix for input 245. -/
theorem certificate_245 : classCertificateB 2 245 = true := by
  decide

/-- The same exact first-descent time holds on an infinite dyadic ray. -/
theorem ray_245 (m : Nat) : stoppingTime (2 ^ 2 * m + 245) 2 :=
  stoppingTime_of_classCertificate certificate_245 m

/-- Checked base and every prefix for input 247. -/
theorem certificate_247 : classCertificateB 5 247 = true := by
  decide

/-- The same exact first-descent time holds on an infinite dyadic ray. -/
theorem ray_247 (m : Nat) : stoppingTime (2 ^ 5 * m + 247) 5 :=
  stoppingTime_of_classCertificate certificate_247 m

/-- Checked base and every prefix for input 249. -/
theorem certificate_249 : classCertificateB 2 249 = true := by
  decide

/-- The same exact first-descent time holds on an infinite dyadic ray. -/
theorem ray_249 (m : Nat) : stoppingTime (2 ^ 2 * m + 249) 2 :=
  stoppingTime_of_classCertificate certificate_249 m

/-- Checked base and every prefix for input 251. -/
theorem certificate_251 : classCertificateB 27 251 = true := by
  decide

/-- The same exact first-descent time holds on an infinite dyadic ray. -/
theorem ray_251 (m : Nat) : stoppingTime (2 ^ 27 * m + 251) 27 :=
  stoppingTime_of_classCertificate certificate_251 m

/-- Checked base and every prefix for input 253. -/
theorem certificate_253 : classCertificateB 2 253 = true := by
  decide

/-- The same exact first-descent time holds on an infinite dyadic ray. -/
theorem ray_253 (m : Nat) : stoppingTime (2 ^ 2 * m + 253) 2 :=
  stoppingTime_of_classCertificate certificate_253 m

/-- Checked base and every prefix for input 255. -/
theorem certificate_255 : classCertificateB 13 255 = true := by
  decide

/-- The same exact first-descent time holds on an infinite dyadic ray. -/
theorem ray_255 (m : Nat) : stoppingTime (2 ^ 13 * m + 255) 13 :=
  stoppingTime_of_classCertificate certificate_255 m

/-- Checked base and every prefix for input 257. -/
theorem certificate_257 : classCertificateB 2 257 = true := by
  decide

/-- The same exact first-descent time holds on an infinite dyadic ray. -/
theorem ray_257 (m : Nat) : stoppingTime (2 ^ 2 * m + 257) 2 :=
  stoppingTime_of_classCertificate certificate_257 m

/-- Checked base and every prefix for input 259. -/
theorem certificate_259 : classCertificateB 4 259 = true := by
  decide

/-- The same exact first-descent time holds on an infinite dyadic ray. -/
theorem ray_259 (m : Nat) : stoppingTime (2 ^ 4 * m + 259) 4 :=
  stoppingTime_of_classCertificate certificate_259 m

/-- Checked base and every prefix for input 261. -/
theorem certificate_261 : classCertificateB 2 261 = true := by
  decide

/-- The same exact first-descent time holds on an infinite dyadic ray. -/
theorem ray_261 (m : Nat) : stoppingTime (2 ^ 2 * m + 261) 2 :=
  stoppingTime_of_classCertificate certificate_261 m

/-- Checked base and every prefix for input 263. -/
theorem certificate_263 : classCertificateB 7 263 = true := by
  decide

/-- The same exact first-descent time holds on an infinite dyadic ray. -/
theorem ray_263 (m : Nat) : stoppingTime (2 ^ 7 * m + 263) 7 :=
  stoppingTime_of_classCertificate certificate_263 m

/-- Checked base and every prefix for input 265. -/
theorem certificate_265 : classCertificateB 2 265 = true := by
  decide

/-- The same exact first-descent time holds on an infinite dyadic ray. -/
theorem ray_265 (m : Nat) : stoppingTime (2 ^ 2 * m + 265) 2 :=
  stoppingTime_of_classCertificate certificate_265 m

/-- Checked base and every prefix for input 267. -/
theorem certificate_267 : classCertificateB 5 267 = true := by
  decide

/-- The same exact first-descent time holds on an infinite dyadic ray. -/
theorem ray_267 (m : Nat) : stoppingTime (2 ^ 5 * m + 267) 5 :=
  stoppingTime_of_classCertificate certificate_267 m

/-- Exhaustive coverage of the odd inputs in this batch, with no gaps. -/
theorem coverage : CertifiedRange 203 269 := by
  intro n hlo hhi hodd
  have hn : n = 203 ∨ n = 205 ∨ n = 207 ∨ n = 209 ∨ n = 211 ∨ n = 213 ∨ n = 215 ∨ n = 217 ∨ n = 219 ∨ n = 221 ∨ n = 223 ∨ n = 225 ∨ n = 227 ∨ n = 229 ∨ n = 231 ∨ n = 233 ∨ n = 235 ∨ n = 237 ∨ n = 239 ∨ n = 241 ∨ n = 243 ∨ n = 245 ∨ n = 247 ∨ n = 249 ∨ n = 251 ∨ n = 253 ∨ n = 255 ∨ n = 257 ∨ n = 259 ∨ n = 261 ∨ n = 263 ∨ n = 265 ∨ n = 267 := by omega
  rcases hn with h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h
  · subst n
    exact ⟨5, witness_of_certificate certificate_203⟩
  · subst n
    exact ⟨2, witness_of_certificate certificate_205⟩
  · subst n
    exact ⟨13, witness_of_certificate certificate_207⟩
  · subst n
    exact ⟨2, witness_of_certificate certificate_209⟩
  · subst n
    exact ⟨4, witness_of_certificate certificate_211⟩
  · subst n
    exact ⟨2, witness_of_certificate certificate_213⟩
  · subst n
    exact ⟨5, witness_of_certificate certificate_215⟩
  · subst n
    exact ⟨2, witness_of_certificate certificate_217⟩
  · subst n
    exact ⟨8, witness_of_certificate certificate_219⟩
  · subst n
    exact ⟨2, witness_of_certificate certificate_221⟩
  · subst n
    exact ⟨31, witness_of_certificate certificate_223⟩
  · subst n
    exact ⟨2, witness_of_certificate certificate_225⟩
  · subst n
    exact ⟨4, witness_of_certificate certificate_227⟩
  · subst n
    exact ⟨2, witness_of_certificate certificate_229⟩
  · subst n
    exact ⟨12, witness_of_certificate certificate_231⟩
  · subst n
    exact ⟨2, witness_of_certificate certificate_233⟩
  · subst n
    exact ⟨5, witness_of_certificate certificate_235⟩
  · subst n
    exact ⟨2, witness_of_certificate certificate_237⟩
  · subst n
    exact ⟨20, witness_of_certificate certificate_239⟩
  · subst n
    exact ⟨2, witness_of_certificate certificate_241⟩
  · subst n
    exact ⟨4, witness_of_certificate certificate_243⟩
  · subst n
    exact ⟨2, witness_of_certificate certificate_245⟩
  · subst n
    exact ⟨5, witness_of_certificate certificate_247⟩
  · subst n
    exact ⟨2, witness_of_certificate certificate_249⟩
  · subst n
    exact ⟨27, witness_of_certificate certificate_251⟩
  · subst n
    exact ⟨2, witness_of_certificate certificate_253⟩
  · subst n
    exact ⟨13, witness_of_certificate certificate_255⟩
  · subst n
    exact ⟨2, witness_of_certificate certificate_257⟩
  · subst n
    exact ⟨4, witness_of_certificate certificate_259⟩
  · subst n
    exact ⟨2, witness_of_certificate certificate_261⟩
  · subst n
    exact ⟨7, witness_of_certificate certificate_263⟩
  · subst n
    exact ⟨2, witness_of_certificate certificate_265⟩
  · subst n
    exact ⟨5, witness_of_certificate certificate_267⟩

end Collatz.Research.CoefficientDescent.Batch004
