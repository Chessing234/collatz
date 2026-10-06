import Collatz.Research.CoefficientDescent.Basic

namespace Collatz.Research.CoefficientDescent.Batch094

open FirstDescentClass

set_option maxRecDepth 20000
set_option maxHeartbeats 0

/-- Checked base and every prefix for input 6231. -/
theorem certificate_6231 : classCertificateB 5 6231 = true := by
  decide

/-- The same exact first-descent time holds on an infinite dyadic ray. -/
theorem ray_6231 (m : Nat) : stoppingTime (2 ^ 5 * m + 6231) 5 :=
  stoppingTime_of_classCertificate certificate_6231 m

/-- Checked base and every prefix for input 6233. -/
theorem certificate_6233 : classCertificateB 2 6233 = true := by
  decide

/-- The same exact first-descent time holds on an infinite dyadic ray. -/
theorem ray_6233 (m : Nat) : stoppingTime (2 ^ 2 * m + 6233) 2 :=
  stoppingTime_of_classCertificate certificate_6233 m

/-- Checked base and every prefix for input 6235. -/
theorem certificate_6235 : classCertificateB 20 6235 = true := by
  decide

/-- The same exact first-descent time holds on an infinite dyadic ray. -/
theorem ray_6235 (m : Nat) : stoppingTime (2 ^ 20 * m + 6235) 20 :=
  stoppingTime_of_classCertificate certificate_6235 m

/-- Checked base and every prefix for input 6237. -/
theorem certificate_6237 : classCertificateB 2 6237 = true := by
  decide

/-- The same exact first-descent time holds on an infinite dyadic ray. -/
theorem ray_6237 (m : Nat) : stoppingTime (2 ^ 2 * m + 6237) 2 :=
  stoppingTime_of_classCertificate certificate_6237 m

/-- Checked base and every prefix for input 6239. -/
theorem certificate_6239 : classCertificateB 8 6239 = true := by
  decide

/-- The same exact first-descent time holds on an infinite dyadic ray. -/
theorem ray_6239 (m : Nat) : stoppingTime (2 ^ 8 * m + 6239) 8 :=
  stoppingTime_of_classCertificate certificate_6239 m

/-- Checked base and every prefix for input 6241. -/
theorem certificate_6241 : classCertificateB 2 6241 = true := by
  decide

/-- The same exact first-descent time holds on an infinite dyadic ray. -/
theorem ray_6241 (m : Nat) : stoppingTime (2 ^ 2 * m + 6241) 2 :=
  stoppingTime_of_classCertificate certificate_6241 m

/-- Checked base and every prefix for input 6243. -/
theorem certificate_6243 : classCertificateB 4 6243 = true := by
  decide

/-- The same exact first-descent time holds on an infinite dyadic ray. -/
theorem ray_6243 (m : Nat) : stoppingTime (2 ^ 4 * m + 6243) 4 :=
  stoppingTime_of_classCertificate certificate_6243 m

/-- Checked base and every prefix for input 6245. -/
theorem certificate_6245 : classCertificateB 2 6245 = true := by
  decide

/-- The same exact first-descent time holds on an infinite dyadic ray. -/
theorem ray_6245 (m : Nat) : stoppingTime (2 ^ 2 * m + 6245) 2 :=
  stoppingTime_of_classCertificate certificate_6245 m

/-- Checked base and every prefix for input 6247. -/
theorem certificate_6247 : classCertificateB 16 6247 = true := by
  decide

/-- The same exact first-descent time holds on an infinite dyadic ray. -/
theorem ray_6247 (m : Nat) : stoppingTime (2 ^ 16 * m + 6247) 16 :=
  stoppingTime_of_classCertificate certificate_6247 m

/-- Checked base and every prefix for input 6249. -/
theorem certificate_6249 : classCertificateB 2 6249 = true := by
  decide

/-- The same exact first-descent time holds on an infinite dyadic ray. -/
theorem ray_6249 (m : Nat) : stoppingTime (2 ^ 2 * m + 6249) 2 :=
  stoppingTime_of_classCertificate certificate_6249 m

/-- Checked base and every prefix for input 6251. -/
theorem certificate_6251 : classCertificateB 5 6251 = true := by
  decide

/-- The same exact first-descent time holds on an infinite dyadic ray. -/
theorem ray_6251 (m : Nat) : stoppingTime (2 ^ 5 * m + 6251) 5 :=
  stoppingTime_of_classCertificate certificate_6251 m

/-- Checked base and every prefix for input 6253. -/
theorem certificate_6253 : classCertificateB 2 6253 = true := by
  decide

/-- The same exact first-descent time holds on an infinite dyadic ray. -/
theorem ray_6253 (m : Nat) : stoppingTime (2 ^ 2 * m + 6253) 2 :=
  stoppingTime_of_classCertificate certificate_6253 m

/-- Checked base and every prefix for input 6255. -/
theorem certificate_6255 : classCertificateB 15 6255 = true := by
  decide

/-- The same exact first-descent time holds on an infinite dyadic ray. -/
theorem ray_6255 (m : Nat) : stoppingTime (2 ^ 15 * m + 6255) 15 :=
  stoppingTime_of_classCertificate certificate_6255 m

/-- Checked base and every prefix for input 6257. -/
theorem certificate_6257 : classCertificateB 2 6257 = true := by
  decide

/-- The same exact first-descent time holds on an infinite dyadic ray. -/
theorem ray_6257 (m : Nat) : stoppingTime (2 ^ 2 * m + 6257) 2 :=
  stoppingTime_of_classCertificate certificate_6257 m

/-- Checked base and every prefix for input 6259. -/
theorem certificate_6259 : classCertificateB 4 6259 = true := by
  decide

/-- The same exact first-descent time holds on an infinite dyadic ray. -/
theorem ray_6259 (m : Nat) : stoppingTime (2 ^ 4 * m + 6259) 4 :=
  stoppingTime_of_classCertificate certificate_6259 m

/-- Checked base and every prefix for input 6261. -/
theorem certificate_6261 : classCertificateB 2 6261 = true := by
  decide

/-- The same exact first-descent time holds on an infinite dyadic ray. -/
theorem ray_6261 (m : Nat) : stoppingTime (2 ^ 2 * m + 6261) 2 :=
  stoppingTime_of_classCertificate certificate_6261 m

/-- Checked base and every prefix for input 6263. -/
theorem certificate_6263 : classCertificateB 5 6263 = true := by
  decide

/-- The same exact first-descent time holds on an infinite dyadic ray. -/
theorem ray_6263 (m : Nat) : stoppingTime (2 ^ 5 * m + 6263) 5 :=
  stoppingTime_of_classCertificate certificate_6263 m

/-- Checked base and every prefix for input 6265. -/
theorem certificate_6265 : classCertificateB 2 6265 = true := by
  decide

/-- The same exact first-descent time holds on an infinite dyadic ray. -/
theorem ray_6265 (m : Nat) : stoppingTime (2 ^ 2 * m + 6265) 2 :=
  stoppingTime_of_classCertificate certificate_6265 m

/-- Checked base and every prefix for input 6267. -/
theorem certificate_6267 : classCertificateB 8 6267 = true := by
  decide

/-- The same exact first-descent time holds on an infinite dyadic ray. -/
theorem ray_6267 (m : Nat) : stoppingTime (2 ^ 8 * m + 6267) 8 :=
  stoppingTime_of_classCertificate certificate_6267 m

/-- Checked base and every prefix for input 6269. -/
theorem certificate_6269 : classCertificateB 2 6269 = true := by
  decide

/-- The same exact first-descent time holds on an infinite dyadic ray. -/
theorem ray_6269 (m : Nat) : stoppingTime (2 ^ 2 * m + 6269) 2 :=
  stoppingTime_of_classCertificate certificate_6269 m

/-- Checked base and every prefix for input 6271. -/
theorem certificate_6271 : classCertificateB 24 6271 = true := by
  decide

/-- The same exact first-descent time holds on an infinite dyadic ray. -/
theorem ray_6271 (m : Nat) : stoppingTime (2 ^ 24 * m + 6271) 24 :=
  stoppingTime_of_classCertificate certificate_6271 m

/-- Checked base and every prefix for input 6273. -/
theorem certificate_6273 : classCertificateB 2 6273 = true := by
  decide

/-- The same exact first-descent time holds on an infinite dyadic ray. -/
theorem ray_6273 (m : Nat) : stoppingTime (2 ^ 2 * m + 6273) 2 :=
  stoppingTime_of_classCertificate certificate_6273 m

/-- Checked base and every prefix for input 6275. -/
theorem certificate_6275 : classCertificateB 4 6275 = true := by
  decide

/-- The same exact first-descent time holds on an infinite dyadic ray. -/
theorem ray_6275 (m : Nat) : stoppingTime (2 ^ 4 * m + 6275) 4 :=
  stoppingTime_of_classCertificate certificate_6275 m

/-- Checked base and every prefix for input 6277. -/
theorem certificate_6277 : classCertificateB 2 6277 = true := by
  decide

/-- The same exact first-descent time holds on an infinite dyadic ray. -/
theorem ray_6277 (m : Nat) : stoppingTime (2 ^ 2 * m + 6277) 2 :=
  stoppingTime_of_classCertificate certificate_6277 m

/-- Checked base and every prefix for input 6279. -/
theorem certificate_6279 : classCertificateB 7 6279 = true := by
  decide

/-- The same exact first-descent time holds on an infinite dyadic ray. -/
theorem ray_6279 (m : Nat) : stoppingTime (2 ^ 7 * m + 6279) 7 :=
  stoppingTime_of_classCertificate certificate_6279 m

/-- Checked base and every prefix for input 6281. -/
theorem certificate_6281 : classCertificateB 2 6281 = true := by
  decide

/-- The same exact first-descent time holds on an infinite dyadic ray. -/
theorem ray_6281 (m : Nat) : stoppingTime (2 ^ 2 * m + 6281) 2 :=
  stoppingTime_of_classCertificate certificate_6281 m

/-- Checked base and every prefix for input 6283. -/
theorem certificate_6283 : classCertificateB 5 6283 = true := by
  decide

/-- The same exact first-descent time holds on an infinite dyadic ray. -/
theorem ray_6283 (m : Nat) : stoppingTime (2 ^ 5 * m + 6283) 5 :=
  stoppingTime_of_classCertificate certificate_6283 m

/-- Checked base and every prefix for input 6285. -/
theorem certificate_6285 : classCertificateB 2 6285 = true := by
  decide

/-- The same exact first-descent time holds on an infinite dyadic ray. -/
theorem ray_6285 (m : Nat) : stoppingTime (2 ^ 2 * m + 6285) 2 :=
  stoppingTime_of_classCertificate certificate_6285 m

/-- Checked base and every prefix for input 6287. -/
theorem certificate_6287 : classCertificateB 7 6287 = true := by
  decide

/-- The same exact first-descent time holds on an infinite dyadic ray. -/
theorem ray_6287 (m : Nat) : stoppingTime (2 ^ 7 * m + 6287) 7 :=
  stoppingTime_of_classCertificate certificate_6287 m

/-- Checked base and every prefix for input 6289. -/
theorem certificate_6289 : classCertificateB 2 6289 = true := by
  decide

/-- The same exact first-descent time holds on an infinite dyadic ray. -/
theorem ray_6289 (m : Nat) : stoppingTime (2 ^ 2 * m + 6289) 2 :=
  stoppingTime_of_classCertificate certificate_6289 m

/-- Checked base and every prefix for input 6291. -/
theorem certificate_6291 : classCertificateB 4 6291 = true := by
  decide

/-- The same exact first-descent time holds on an infinite dyadic ray. -/
theorem ray_6291 (m : Nat) : stoppingTime (2 ^ 4 * m + 6291) 4 :=
  stoppingTime_of_classCertificate certificate_6291 m

/-- Checked base and every prefix for input 6293. -/
theorem certificate_6293 : classCertificateB 2 6293 = true := by
  decide

/-- The same exact first-descent time holds on an infinite dyadic ray. -/
theorem ray_6293 (m : Nat) : stoppingTime (2 ^ 2 * m + 6293) 2 :=
  stoppingTime_of_classCertificate certificate_6293 m

/-- Checked base and every prefix for input 6295. -/
theorem certificate_6295 : classCertificateB 5 6295 = true := by
  decide

/-- The same exact first-descent time holds on an infinite dyadic ray. -/
theorem ray_6295 (m : Nat) : stoppingTime (2 ^ 5 * m + 6295) 5 :=
  stoppingTime_of_classCertificate certificate_6295 m

/-- Checked base and every prefix for input 6297. -/
theorem certificate_6297 : classCertificateB 2 6297 = true := by
  decide

/-- The same exact first-descent time holds on an infinite dyadic ray. -/
theorem ray_6297 (m : Nat) : stoppingTime (2 ^ 2 * m + 6297) 2 :=
  stoppingTime_of_classCertificate certificate_6297 m

/-- Exhaustive coverage of the odd inputs in this batch, with no gaps. -/
theorem coverage : CertifiedRange 6231 6299 := by
  intro n hlo hhi hodd
  have hn : n = 6231 ∨ n = 6233 ∨ n = 6235 ∨ n = 6237 ∨ n = 6239 ∨ n = 6241 ∨ n = 6243 ∨ n = 6245 ∨ n = 6247 ∨ n = 6249 ∨ n = 6251 ∨ n = 6253 ∨ n = 6255 ∨ n = 6257 ∨ n = 6259 ∨ n = 6261 ∨ n = 6263 ∨ n = 6265 ∨ n = 6267 ∨ n = 6269 ∨ n = 6271 ∨ n = 6273 ∨ n = 6275 ∨ n = 6277 ∨ n = 6279 ∨ n = 6281 ∨ n = 6283 ∨ n = 6285 ∨ n = 6287 ∨ n = 6289 ∨ n = 6291 ∨ n = 6293 ∨ n = 6295 ∨ n = 6297 := by omega
  rcases hn with h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h
  · subst n
    exact ⟨5, witness_of_certificate certificate_6231⟩
  · subst n
    exact ⟨2, witness_of_certificate certificate_6233⟩
  · subst n
    exact ⟨20, witness_of_certificate certificate_6235⟩
  · subst n
    exact ⟨2, witness_of_certificate certificate_6237⟩
  · subst n
    exact ⟨8, witness_of_certificate certificate_6239⟩
  · subst n
    exact ⟨2, witness_of_certificate certificate_6241⟩
  · subst n
    exact ⟨4, witness_of_certificate certificate_6243⟩
  · subst n
    exact ⟨2, witness_of_certificate certificate_6245⟩
  · subst n
    exact ⟨16, witness_of_certificate certificate_6247⟩
  · subst n
    exact ⟨2, witness_of_certificate certificate_6249⟩
  · subst n
    exact ⟨5, witness_of_certificate certificate_6251⟩
  · subst n
    exact ⟨2, witness_of_certificate certificate_6253⟩
  · subst n
    exact ⟨15, witness_of_certificate certificate_6255⟩
  · subst n
    exact ⟨2, witness_of_certificate certificate_6257⟩
  · subst n
    exact ⟨4, witness_of_certificate certificate_6259⟩
  · subst n
    exact ⟨2, witness_of_certificate certificate_6261⟩
  · subst n
    exact ⟨5, witness_of_certificate certificate_6263⟩
  · subst n
    exact ⟨2, witness_of_certificate certificate_6265⟩
  · subst n
    exact ⟨8, witness_of_certificate certificate_6267⟩
  · subst n
    exact ⟨2, witness_of_certificate certificate_6269⟩
  · subst n
    exact ⟨24, witness_of_certificate certificate_6271⟩
  · subst n
    exact ⟨2, witness_of_certificate certificate_6273⟩
  · subst n
    exact ⟨4, witness_of_certificate certificate_6275⟩
  · subst n
    exact ⟨2, witness_of_certificate certificate_6277⟩
  · subst n
    exact ⟨7, witness_of_certificate certificate_6279⟩
  · subst n
    exact ⟨2, witness_of_certificate certificate_6281⟩
  · subst n
    exact ⟨5, witness_of_certificate certificate_6283⟩
  · subst n
    exact ⟨2, witness_of_certificate certificate_6285⟩
  · subst n
    exact ⟨7, witness_of_certificate certificate_6287⟩
  · subst n
    exact ⟨2, witness_of_certificate certificate_6289⟩
  · subst n
    exact ⟨4, witness_of_certificate certificate_6291⟩
  · subst n
    exact ⟨2, witness_of_certificate certificate_6293⟩
  · subst n
    exact ⟨5, witness_of_certificate certificate_6295⟩
  · subst n
    exact ⟨2, witness_of_certificate certificate_6297⟩

end Collatz.Research.CoefficientDescent.Batch094
