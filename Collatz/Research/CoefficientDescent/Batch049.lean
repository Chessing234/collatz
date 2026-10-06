import Collatz.Research.CoefficientDescent.Basic

namespace Collatz.Research.CoefficientDescent.Batch049

open FirstDescentClass

set_option maxRecDepth 20000
set_option maxHeartbeats 0

/-- Checked base and every prefix for input 3217. -/
theorem certificate_3217 : classCertificateB 2 3217 = true := by
  decide

/-- The same exact first-descent time holds on an infinite dyadic ray. -/
theorem ray_3217 (m : Nat) : stoppingTime (2 ^ 2 * m + 3217) 2 :=
  stoppingTime_of_classCertificate certificate_3217 m

/-- Checked base and every prefix for input 3219. -/
theorem certificate_3219 : classCertificateB 4 3219 = true := by
  decide

/-- The same exact first-descent time holds on an infinite dyadic ray. -/
theorem ray_3219 (m : Nat) : stoppingTime (2 ^ 4 * m + 3219) 4 :=
  stoppingTime_of_classCertificate certificate_3219 m

/-- Checked base and every prefix for input 3221. -/
theorem certificate_3221 : classCertificateB 2 3221 = true := by
  decide

/-- The same exact first-descent time holds on an infinite dyadic ray. -/
theorem ray_3221 (m : Nat) : stoppingTime (2 ^ 2 * m + 3221) 2 :=
  stoppingTime_of_classCertificate certificate_3221 m

/-- Checked base and every prefix for input 3223. -/
theorem certificate_3223 : classCertificateB 5 3223 = true := by
  decide

/-- The same exact first-descent time holds on an infinite dyadic ray. -/
theorem ray_3223 (m : Nat) : stoppingTime (2 ^ 5 * m + 3223) 5 :=
  stoppingTime_of_classCertificate certificate_3223 m

/-- Checked base and every prefix for input 3225. -/
theorem certificate_3225 : classCertificateB 2 3225 = true := by
  decide

/-- The same exact first-descent time holds on an infinite dyadic ray. -/
theorem ray_3225 (m : Nat) : stoppingTime (2 ^ 2 * m + 3225) 2 :=
  stoppingTime_of_classCertificate certificate_3225 m

/-- Checked base and every prefix for input 3227. -/
theorem certificate_3227 : classCertificateB 40 3227 = true := by
  decide

/-- The same exact first-descent time holds on an infinite dyadic ray. -/
theorem ray_3227 (m : Nat) : stoppingTime (2 ^ 40 * m + 3227) 40 :=
  stoppingTime_of_classCertificate certificate_3227 m

/-- Checked base and every prefix for input 3229. -/
theorem certificate_3229 : classCertificateB 2 3229 = true := by
  decide

/-- The same exact first-descent time holds on an infinite dyadic ray. -/
theorem ray_3229 (m : Nat) : stoppingTime (2 ^ 2 * m + 3229) 2 :=
  stoppingTime_of_classCertificate certificate_3229 m

/-- Checked base and every prefix for input 3231. -/
theorem certificate_3231 : classCertificateB 23 3231 = true := by
  decide

/-- The same exact first-descent time holds on an infinite dyadic ray. -/
theorem ray_3231 (m : Nat) : stoppingTime (2 ^ 23 * m + 3231) 23 :=
  stoppingTime_of_classCertificate certificate_3231 m

/-- Checked base and every prefix for input 3233. -/
theorem certificate_3233 : classCertificateB 2 3233 = true := by
  decide

/-- The same exact first-descent time holds on an infinite dyadic ray. -/
theorem ray_3233 (m : Nat) : stoppingTime (2 ^ 2 * m + 3233) 2 :=
  stoppingTime_of_classCertificate certificate_3233 m

/-- Checked base and every prefix for input 3235. -/
theorem certificate_3235 : classCertificateB 4 3235 = true := by
  decide

/-- The same exact first-descent time holds on an infinite dyadic ray. -/
theorem ray_3235 (m : Nat) : stoppingTime (2 ^ 4 * m + 3235) 4 :=
  stoppingTime_of_classCertificate certificate_3235 m

/-- Checked base and every prefix for input 3237. -/
theorem certificate_3237 : classCertificateB 2 3237 = true := by
  decide

/-- The same exact first-descent time holds on an infinite dyadic ray. -/
theorem ray_3237 (m : Nat) : stoppingTime (2 ^ 2 * m + 3237) 2 :=
  stoppingTime_of_classCertificate certificate_3237 m

/-- Checked base and every prefix for input 3239. -/
theorem certificate_3239 : classCertificateB 16 3239 = true := by
  decide

/-- The same exact first-descent time holds on an infinite dyadic ray. -/
theorem ray_3239 (m : Nat) : stoppingTime (2 ^ 16 * m + 3239) 16 :=
  stoppingTime_of_classCertificate certificate_3239 m

/-- Checked base and every prefix for input 3241. -/
theorem certificate_3241 : classCertificateB 2 3241 = true := by
  decide

/-- The same exact first-descent time holds on an infinite dyadic ray. -/
theorem ray_3241 (m : Nat) : stoppingTime (2 ^ 2 * m + 3241) 2 :=
  stoppingTime_of_classCertificate certificate_3241 m

/-- Checked base and every prefix for input 3243. -/
theorem certificate_3243 : classCertificateB 5 3243 = true := by
  decide

/-- The same exact first-descent time holds on an infinite dyadic ray. -/
theorem ray_3243 (m : Nat) : stoppingTime (2 ^ 5 * m + 3243) 5 :=
  stoppingTime_of_classCertificate certificate_3243 m

/-- Checked base and every prefix for input 3245. -/
theorem certificate_3245 : classCertificateB 2 3245 = true := by
  decide

/-- The same exact first-descent time holds on an infinite dyadic ray. -/
theorem ray_3245 (m : Nat) : stoppingTime (2 ^ 2 * m + 3245) 2 :=
  stoppingTime_of_classCertificate certificate_3245 m

/-- Checked base and every prefix for input 3247. -/
theorem certificate_3247 : classCertificateB 8 3247 = true := by
  decide

/-- The same exact first-descent time holds on an infinite dyadic ray. -/
theorem ray_3247 (m : Nat) : stoppingTime (2 ^ 8 * m + 3247) 8 :=
  stoppingTime_of_classCertificate certificate_3247 m

/-- Checked base and every prefix for input 3249. -/
theorem certificate_3249 : classCertificateB 2 3249 = true := by
  decide

/-- The same exact first-descent time holds on an infinite dyadic ray. -/
theorem ray_3249 (m : Nat) : stoppingTime (2 ^ 2 * m + 3249) 2 :=
  stoppingTime_of_classCertificate certificate_3249 m

/-- Checked base and every prefix for input 3251. -/
theorem certificate_3251 : classCertificateB 4 3251 = true := by
  decide

/-- The same exact first-descent time holds on an infinite dyadic ray. -/
theorem ray_3251 (m : Nat) : stoppingTime (2 ^ 4 * m + 3251) 4 :=
  stoppingTime_of_classCertificate certificate_3251 m

/-- Checked base and every prefix for input 3253. -/
theorem certificate_3253 : classCertificateB 2 3253 = true := by
  decide

/-- The same exact first-descent time holds on an infinite dyadic ray. -/
theorem ray_3253 (m : Nat) : stoppingTime (2 ^ 2 * m + 3253) 2 :=
  stoppingTime_of_classCertificate certificate_3253 m

/-- Checked base and every prefix for input 3255. -/
theorem certificate_3255 : classCertificateB 5 3255 = true := by
  decide

/-- The same exact first-descent time holds on an infinite dyadic ray. -/
theorem ray_3255 (m : Nat) : stoppingTime (2 ^ 5 * m + 3255) 5 :=
  stoppingTime_of_classCertificate certificate_3255 m

/-- Checked base and every prefix for input 3257. -/
theorem certificate_3257 : classCertificateB 2 3257 = true := by
  decide

/-- The same exact first-descent time holds on an infinite dyadic ray. -/
theorem ray_3257 (m : Nat) : stoppingTime (2 ^ 2 * m + 3257) 2 :=
  stoppingTime_of_classCertificate certificate_3257 m

/-- Checked base and every prefix for input 3259. -/
theorem certificate_3259 : classCertificateB 7 3259 = true := by
  decide

/-- The same exact first-descent time holds on an infinite dyadic ray. -/
theorem ray_3259 (m : Nat) : stoppingTime (2 ^ 7 * m + 3259) 7 :=
  stoppingTime_of_classCertificate certificate_3259 m

/-- Checked base and every prefix for input 3261. -/
theorem certificate_3261 : classCertificateB 2 3261 = true := by
  decide

/-- The same exact first-descent time holds on an infinite dyadic ray. -/
theorem ray_3261 (m : Nat) : stoppingTime (2 ^ 2 * m + 3261) 2 :=
  stoppingTime_of_classCertificate certificate_3261 m

/-- Checked base and every prefix for input 3263. -/
theorem certificate_3263 : classCertificateB 18 3263 = true := by
  decide

/-- The same exact first-descent time holds on an infinite dyadic ray. -/
theorem ray_3263 (m : Nat) : stoppingTime (2 ^ 18 * m + 3263) 18 :=
  stoppingTime_of_classCertificate certificate_3263 m

/-- Checked base and every prefix for input 3265. -/
theorem certificate_3265 : classCertificateB 2 3265 = true := by
  decide

/-- The same exact first-descent time holds on an infinite dyadic ray. -/
theorem ray_3265 (m : Nat) : stoppingTime (2 ^ 2 * m + 3265) 2 :=
  stoppingTime_of_classCertificate certificate_3265 m

/-- Checked base and every prefix for input 3267. -/
theorem certificate_3267 : classCertificateB 4 3267 = true := by
  decide

/-- The same exact first-descent time holds on an infinite dyadic ray. -/
theorem ray_3267 (m : Nat) : stoppingTime (2 ^ 4 * m + 3267) 4 :=
  stoppingTime_of_classCertificate certificate_3267 m

/-- Checked base and every prefix for input 3269. -/
theorem certificate_3269 : classCertificateB 2 3269 = true := by
  decide

/-- The same exact first-descent time holds on an infinite dyadic ray. -/
theorem ray_3269 (m : Nat) : stoppingTime (2 ^ 2 * m + 3269) 2 :=
  stoppingTime_of_classCertificate certificate_3269 m

/-- Checked base and every prefix for input 3271. -/
theorem certificate_3271 : classCertificateB 8 3271 = true := by
  decide

/-- The same exact first-descent time holds on an infinite dyadic ray. -/
theorem ray_3271 (m : Nat) : stoppingTime (2 ^ 8 * m + 3271) 8 :=
  stoppingTime_of_classCertificate certificate_3271 m

/-- Checked base and every prefix for input 3273. -/
theorem certificate_3273 : classCertificateB 2 3273 = true := by
  decide

/-- The same exact first-descent time holds on an infinite dyadic ray. -/
theorem ray_3273 (m : Nat) : stoppingTime (2 ^ 2 * m + 3273) 2 :=
  stoppingTime_of_classCertificate certificate_3273 m

/-- Checked base and every prefix for input 3275. -/
theorem certificate_3275 : classCertificateB 5 3275 = true := by
  decide

/-- The same exact first-descent time holds on an infinite dyadic ray. -/
theorem ray_3275 (m : Nat) : stoppingTime (2 ^ 5 * m + 3275) 5 :=
  stoppingTime_of_classCertificate certificate_3275 m

/-- Checked base and every prefix for input 3277. -/
theorem certificate_3277 : classCertificateB 2 3277 = true := by
  decide

/-- The same exact first-descent time holds on an infinite dyadic ray. -/
theorem ray_3277 (m : Nat) : stoppingTime (2 ^ 2 * m + 3277) 2 :=
  stoppingTime_of_classCertificate certificate_3277 m

/-- Checked base and every prefix for input 3279. -/
theorem certificate_3279 : classCertificateB 20 3279 = true := by
  decide

/-- The same exact first-descent time holds on an infinite dyadic ray. -/
theorem ray_3279 (m : Nat) : stoppingTime (2 ^ 20 * m + 3279) 20 :=
  stoppingTime_of_classCertificate certificate_3279 m

/-- Checked base and every prefix for input 3281. -/
theorem certificate_3281 : classCertificateB 2 3281 = true := by
  decide

/-- The same exact first-descent time holds on an infinite dyadic ray. -/
theorem ray_3281 (m : Nat) : stoppingTime (2 ^ 2 * m + 3281) 2 :=
  stoppingTime_of_classCertificate certificate_3281 m

/-- Checked base and every prefix for input 3283. -/
theorem certificate_3283 : classCertificateB 4 3283 = true := by
  decide

/-- The same exact first-descent time holds on an infinite dyadic ray. -/
theorem ray_3283 (m : Nat) : stoppingTime (2 ^ 4 * m + 3283) 4 :=
  stoppingTime_of_classCertificate certificate_3283 m

/-- Exhaustive coverage of the odd inputs in this batch, with no gaps. -/
theorem coverage : CertifiedRange 3217 3285 := by
  intro n hlo hhi hodd
  have hn : n = 3217 ∨ n = 3219 ∨ n = 3221 ∨ n = 3223 ∨ n = 3225 ∨ n = 3227 ∨ n = 3229 ∨ n = 3231 ∨ n = 3233 ∨ n = 3235 ∨ n = 3237 ∨ n = 3239 ∨ n = 3241 ∨ n = 3243 ∨ n = 3245 ∨ n = 3247 ∨ n = 3249 ∨ n = 3251 ∨ n = 3253 ∨ n = 3255 ∨ n = 3257 ∨ n = 3259 ∨ n = 3261 ∨ n = 3263 ∨ n = 3265 ∨ n = 3267 ∨ n = 3269 ∨ n = 3271 ∨ n = 3273 ∨ n = 3275 ∨ n = 3277 ∨ n = 3279 ∨ n = 3281 ∨ n = 3283 := by omega
  rcases hn with h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h
  · subst n
    exact ⟨2, witness_of_certificate certificate_3217⟩
  · subst n
    exact ⟨4, witness_of_certificate certificate_3219⟩
  · subst n
    exact ⟨2, witness_of_certificate certificate_3221⟩
  · subst n
    exact ⟨5, witness_of_certificate certificate_3223⟩
  · subst n
    exact ⟨2, witness_of_certificate certificate_3225⟩
  · subst n
    exact ⟨40, witness_of_certificate certificate_3227⟩
  · subst n
    exact ⟨2, witness_of_certificate certificate_3229⟩
  · subst n
    exact ⟨23, witness_of_certificate certificate_3231⟩
  · subst n
    exact ⟨2, witness_of_certificate certificate_3233⟩
  · subst n
    exact ⟨4, witness_of_certificate certificate_3235⟩
  · subst n
    exact ⟨2, witness_of_certificate certificate_3237⟩
  · subst n
    exact ⟨16, witness_of_certificate certificate_3239⟩
  · subst n
    exact ⟨2, witness_of_certificate certificate_3241⟩
  · subst n
    exact ⟨5, witness_of_certificate certificate_3243⟩
  · subst n
    exact ⟨2, witness_of_certificate certificate_3245⟩
  · subst n
    exact ⟨8, witness_of_certificate certificate_3247⟩
  · subst n
    exact ⟨2, witness_of_certificate certificate_3249⟩
  · subst n
    exact ⟨4, witness_of_certificate certificate_3251⟩
  · subst n
    exact ⟨2, witness_of_certificate certificate_3253⟩
  · subst n
    exact ⟨5, witness_of_certificate certificate_3255⟩
  · subst n
    exact ⟨2, witness_of_certificate certificate_3257⟩
  · subst n
    exact ⟨7, witness_of_certificate certificate_3259⟩
  · subst n
    exact ⟨2, witness_of_certificate certificate_3261⟩
  · subst n
    exact ⟨18, witness_of_certificate certificate_3263⟩
  · subst n
    exact ⟨2, witness_of_certificate certificate_3265⟩
  · subst n
    exact ⟨4, witness_of_certificate certificate_3267⟩
  · subst n
    exact ⟨2, witness_of_certificate certificate_3269⟩
  · subst n
    exact ⟨8, witness_of_certificate certificate_3271⟩
  · subst n
    exact ⟨2, witness_of_certificate certificate_3273⟩
  · subst n
    exact ⟨5, witness_of_certificate certificate_3275⟩
  · subst n
    exact ⟨2, witness_of_certificate certificate_3277⟩
  · subst n
    exact ⟨20, witness_of_certificate certificate_3279⟩
  · subst n
    exact ⟨2, witness_of_certificate certificate_3281⟩
  · subst n
    exact ⟨4, witness_of_certificate certificate_3283⟩

end Collatz.Research.CoefficientDescent.Batch049
