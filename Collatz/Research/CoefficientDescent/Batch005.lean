import Collatz.Research.CoefficientDescent.Basic

namespace Collatz.Research.CoefficientDescent.Batch005

open FirstDescentClass

set_option maxRecDepth 20000
set_option maxHeartbeats 0

/-- Checked base and every prefix for input 269. -/
theorem certificate_269 : classCertificateB 2 269 = true := by
  decide

/-- The same exact first-descent time holds on an infinite dyadic ray. -/
theorem ray_269 (m : Nat) : stoppingTime (2 ^ 2 * m + 269) 2 :=
  stoppingTime_of_classCertificate certificate_269 m

/-- Checked base and every prefix for input 271. -/
theorem certificate_271 : classCertificateB 7 271 = true := by
  decide

/-- The same exact first-descent time holds on an infinite dyadic ray. -/
theorem ray_271 (m : Nat) : stoppingTime (2 ^ 7 * m + 271) 7 :=
  stoppingTime_of_classCertificate certificate_271 m

/-- Checked base and every prefix for input 273. -/
theorem certificate_273 : classCertificateB 2 273 = true := by
  decide

/-- The same exact first-descent time holds on an infinite dyadic ray. -/
theorem ray_273 (m : Nat) : stoppingTime (2 ^ 2 * m + 273) 2 :=
  stoppingTime_of_classCertificate certificate_273 m

/-- Checked base and every prefix for input 275. -/
theorem certificate_275 : classCertificateB 4 275 = true := by
  decide

/-- The same exact first-descent time holds on an infinite dyadic ray. -/
theorem ray_275 (m : Nat) : stoppingTime (2 ^ 4 * m + 275) 4 :=
  stoppingTime_of_classCertificate certificate_275 m

/-- Checked base and every prefix for input 277. -/
theorem certificate_277 : classCertificateB 2 277 = true := by
  decide

/-- The same exact first-descent time holds on an infinite dyadic ray. -/
theorem ray_277 (m : Nat) : stoppingTime (2 ^ 2 * m + 277) 2 :=
  stoppingTime_of_classCertificate certificate_277 m

/-- Checked base and every prefix for input 279. -/
theorem certificate_279 : classCertificateB 5 279 = true := by
  decide

/-- The same exact first-descent time holds on an infinite dyadic ray. -/
theorem ray_279 (m : Nat) : stoppingTime (2 ^ 5 * m + 279) 5 :=
  stoppingTime_of_classCertificate certificate_279 m

/-- Checked base and every prefix for input 281. -/
theorem certificate_281 : classCertificateB 2 281 = true := by
  decide

/-- The same exact first-descent time holds on an infinite dyadic ray. -/
theorem ray_281 (m : Nat) : stoppingTime (2 ^ 2 * m + 281) 2 :=
  stoppingTime_of_classCertificate certificate_281 m

/-- Checked base and every prefix for input 283. -/
theorem certificate_283 : classCertificateB 24 283 = true := by
  decide

/-- The same exact first-descent time holds on an infinite dyadic ray. -/
theorem ray_283 (m : Nat) : stoppingTime (2 ^ 24 * m + 283) 24 :=
  stoppingTime_of_classCertificate certificate_283 m

/-- Checked base and every prefix for input 285. -/
theorem certificate_285 : classCertificateB 2 285 = true := by
  decide

/-- The same exact first-descent time holds on an infinite dyadic ray. -/
theorem ray_285 (m : Nat) : stoppingTime (2 ^ 2 * m + 285) 2 :=
  stoppingTime_of_classCertificate certificate_285 m

/-- Checked base and every prefix for input 287. -/
theorem certificate_287 : classCertificateB 10 287 = true := by
  decide

/-- The same exact first-descent time holds on an infinite dyadic ray. -/
theorem ray_287 (m : Nat) : stoppingTime (2 ^ 10 * m + 287) 10 :=
  stoppingTime_of_classCertificate certificate_287 m

/-- Checked base and every prefix for input 289. -/
theorem certificate_289 : classCertificateB 2 289 = true := by
  decide

/-- The same exact first-descent time holds on an infinite dyadic ray. -/
theorem ray_289 (m : Nat) : stoppingTime (2 ^ 2 * m + 289) 2 :=
  stoppingTime_of_classCertificate certificate_289 m

/-- Checked base and every prefix for input 291. -/
theorem certificate_291 : classCertificateB 4 291 = true := by
  decide

/-- The same exact first-descent time holds on an infinite dyadic ray. -/
theorem ray_291 (m : Nat) : stoppingTime (2 ^ 4 * m + 291) 4 :=
  stoppingTime_of_classCertificate certificate_291 m

/-- Checked base and every prefix for input 293. -/
theorem certificate_293 : classCertificateB 2 293 = true := by
  decide

/-- The same exact first-descent time holds on an infinite dyadic ray. -/
theorem ray_293 (m : Nat) : stoppingTime (2 ^ 2 * m + 293) 2 :=
  stoppingTime_of_classCertificate certificate_293 m

/-- Checked base and every prefix for input 295. -/
theorem certificate_295 : classCertificateB 8 295 = true := by
  decide

/-- The same exact first-descent time holds on an infinite dyadic ray. -/
theorem ray_295 (m : Nat) : stoppingTime (2 ^ 8 * m + 295) 8 :=
  stoppingTime_of_classCertificate certificate_295 m

/-- Checked base and every prefix for input 297. -/
theorem certificate_297 : classCertificateB 2 297 = true := by
  decide

/-- The same exact first-descent time holds on an infinite dyadic ray. -/
theorem ray_297 (m : Nat) : stoppingTime (2 ^ 2 * m + 297) 2 :=
  stoppingTime_of_classCertificate certificate_297 m

/-- Checked base and every prefix for input 299. -/
theorem certificate_299 : classCertificateB 5 299 = true := by
  decide

/-- The same exact first-descent time holds on an infinite dyadic ray. -/
theorem ray_299 (m : Nat) : stoppingTime (2 ^ 5 * m + 299) 5 :=
  stoppingTime_of_classCertificate certificate_299 m

/-- Checked base and every prefix for input 301. -/
theorem certificate_301 : classCertificateB 2 301 = true := by
  decide

/-- The same exact first-descent time holds on an infinite dyadic ray. -/
theorem ray_301 (m : Nat) : stoppingTime (2 ^ 2 * m + 301) 2 :=
  stoppingTime_of_classCertificate certificate_301 m

/-- Checked base and every prefix for input 303. -/
theorem certificate_303 : classCertificateB 13 303 = true := by
  decide

/-- The same exact first-descent time holds on an infinite dyadic ray. -/
theorem ray_303 (m : Nat) : stoppingTime (2 ^ 13 * m + 303) 13 :=
  stoppingTime_of_classCertificate certificate_303 m

/-- Checked base and every prefix for input 305. -/
theorem certificate_305 : classCertificateB 2 305 = true := by
  decide

/-- The same exact first-descent time holds on an infinite dyadic ray. -/
theorem ray_305 (m : Nat) : stoppingTime (2 ^ 2 * m + 305) 2 :=
  stoppingTime_of_classCertificate certificate_305 m

/-- Checked base and every prefix for input 307. -/
theorem certificate_307 : classCertificateB 4 307 = true := by
  decide

/-- The same exact first-descent time holds on an infinite dyadic ray. -/
theorem ray_307 (m : Nat) : stoppingTime (2 ^ 4 * m + 307) 4 :=
  stoppingTime_of_classCertificate certificate_307 m

/-- Checked base and every prefix for input 309. -/
theorem certificate_309 : classCertificateB 2 309 = true := by
  decide

/-- The same exact first-descent time holds on an infinite dyadic ray. -/
theorem ray_309 (m : Nat) : stoppingTime (2 ^ 2 * m + 309) 2 :=
  stoppingTime_of_classCertificate certificate_309 m

/-- Checked base and every prefix for input 311. -/
theorem certificate_311 : classCertificateB 5 311 = true := by
  decide

/-- The same exact first-descent time holds on an infinite dyadic ray. -/
theorem ray_311 (m : Nat) : stoppingTime (2 ^ 5 * m + 311) 5 :=
  stoppingTime_of_classCertificate certificate_311 m

/-- Checked base and every prefix for input 313. -/
theorem certificate_313 : classCertificateB 2 313 = true := by
  decide

/-- The same exact first-descent time holds on an infinite dyadic ray. -/
theorem ray_313 (m : Nat) : stoppingTime (2 ^ 2 * m + 313) 2 :=
  stoppingTime_of_classCertificate certificate_313 m

/-- Checked base and every prefix for input 315. -/
theorem certificate_315 : classCertificateB 7 315 = true := by
  decide

/-- The same exact first-descent time holds on an infinite dyadic ray. -/
theorem ray_315 (m : Nat) : stoppingTime (2 ^ 7 * m + 315) 7 :=
  stoppingTime_of_classCertificate certificate_315 m

/-- Checked base and every prefix for input 317. -/
theorem certificate_317 : classCertificateB 2 317 = true := by
  decide

/-- The same exact first-descent time holds on an infinite dyadic ray. -/
theorem ray_317 (m : Nat) : stoppingTime (2 ^ 2 * m + 317) 2 :=
  stoppingTime_of_classCertificate certificate_317 m

/-- Checked base and every prefix for input 319. -/
theorem certificate_319 : classCertificateB 21 319 = true := by
  decide

/-- The same exact first-descent time holds on an infinite dyadic ray. -/
theorem ray_319 (m : Nat) : stoppingTime (2 ^ 21 * m + 319) 21 :=
  stoppingTime_of_classCertificate certificate_319 m

/-- Checked base and every prefix for input 321. -/
theorem certificate_321 : classCertificateB 2 321 = true := by
  decide

/-- The same exact first-descent time holds on an infinite dyadic ray. -/
theorem ray_321 (m : Nat) : stoppingTime (2 ^ 2 * m + 321) 2 :=
  stoppingTime_of_classCertificate certificate_321 m

/-- Checked base and every prefix for input 323. -/
theorem certificate_323 : classCertificateB 4 323 = true := by
  decide

/-- The same exact first-descent time holds on an infinite dyadic ray. -/
theorem ray_323 (m : Nat) : stoppingTime (2 ^ 4 * m + 323) 4 :=
  stoppingTime_of_classCertificate certificate_323 m

/-- Checked base and every prefix for input 325. -/
theorem certificate_325 : classCertificateB 2 325 = true := by
  decide

/-- The same exact first-descent time holds on an infinite dyadic ray. -/
theorem ray_325 (m : Nat) : stoppingTime (2 ^ 2 * m + 325) 2 :=
  stoppingTime_of_classCertificate certificate_325 m

/-- Checked base and every prefix for input 327. -/
theorem certificate_327 : classCertificateB 21 327 = true := by
  decide

/-- The same exact first-descent time holds on an infinite dyadic ray. -/
theorem ray_327 (m : Nat) : stoppingTime (2 ^ 21 * m + 327) 21 :=
  stoppingTime_of_classCertificate certificate_327 m

/-- Checked base and every prefix for input 329. -/
theorem certificate_329 : classCertificateB 2 329 = true := by
  decide

/-- The same exact first-descent time holds on an infinite dyadic ray. -/
theorem ray_329 (m : Nat) : stoppingTime (2 ^ 2 * m + 329) 2 :=
  stoppingTime_of_classCertificate certificate_329 m

/-- Checked base and every prefix for input 331. -/
theorem certificate_331 : classCertificateB 5 331 = true := by
  decide

/-- The same exact first-descent time holds on an infinite dyadic ray. -/
theorem ray_331 (m : Nat) : stoppingTime (2 ^ 5 * m + 331) 5 :=
  stoppingTime_of_classCertificate certificate_331 m

/-- Checked base and every prefix for input 333. -/
theorem certificate_333 : classCertificateB 2 333 = true := by
  decide

/-- The same exact first-descent time holds on an infinite dyadic ray. -/
theorem ray_333 (m : Nat) : stoppingTime (2 ^ 2 * m + 333) 2 :=
  stoppingTime_of_classCertificate certificate_333 m

/-- Checked base and every prefix for input 335. -/
theorem certificate_335 : classCertificateB 8 335 = true := by
  decide

/-- The same exact first-descent time holds on an infinite dyadic ray. -/
theorem ray_335 (m : Nat) : stoppingTime (2 ^ 8 * m + 335) 8 :=
  stoppingTime_of_classCertificate certificate_335 m

/-- Exhaustive coverage of the odd inputs in this batch, with no gaps. -/
theorem coverage : CertifiedRange 269 337 := by
  intro n hlo hhi hodd
  have hn : n = 269 ∨ n = 271 ∨ n = 273 ∨ n = 275 ∨ n = 277 ∨ n = 279 ∨ n = 281 ∨ n = 283 ∨ n = 285 ∨ n = 287 ∨ n = 289 ∨ n = 291 ∨ n = 293 ∨ n = 295 ∨ n = 297 ∨ n = 299 ∨ n = 301 ∨ n = 303 ∨ n = 305 ∨ n = 307 ∨ n = 309 ∨ n = 311 ∨ n = 313 ∨ n = 315 ∨ n = 317 ∨ n = 319 ∨ n = 321 ∨ n = 323 ∨ n = 325 ∨ n = 327 ∨ n = 329 ∨ n = 331 ∨ n = 333 ∨ n = 335 := by omega
  rcases hn with h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h
  · subst n
    exact ⟨2, witness_of_certificate certificate_269⟩
  · subst n
    exact ⟨7, witness_of_certificate certificate_271⟩
  · subst n
    exact ⟨2, witness_of_certificate certificate_273⟩
  · subst n
    exact ⟨4, witness_of_certificate certificate_275⟩
  · subst n
    exact ⟨2, witness_of_certificate certificate_277⟩
  · subst n
    exact ⟨5, witness_of_certificate certificate_279⟩
  · subst n
    exact ⟨2, witness_of_certificate certificate_281⟩
  · subst n
    exact ⟨24, witness_of_certificate certificate_283⟩
  · subst n
    exact ⟨2, witness_of_certificate certificate_285⟩
  · subst n
    exact ⟨10, witness_of_certificate certificate_287⟩
  · subst n
    exact ⟨2, witness_of_certificate certificate_289⟩
  · subst n
    exact ⟨4, witness_of_certificate certificate_291⟩
  · subst n
    exact ⟨2, witness_of_certificate certificate_293⟩
  · subst n
    exact ⟨8, witness_of_certificate certificate_295⟩
  · subst n
    exact ⟨2, witness_of_certificate certificate_297⟩
  · subst n
    exact ⟨5, witness_of_certificate certificate_299⟩
  · subst n
    exact ⟨2, witness_of_certificate certificate_301⟩
  · subst n
    exact ⟨13, witness_of_certificate certificate_303⟩
  · subst n
    exact ⟨2, witness_of_certificate certificate_305⟩
  · subst n
    exact ⟨4, witness_of_certificate certificate_307⟩
  · subst n
    exact ⟨2, witness_of_certificate certificate_309⟩
  · subst n
    exact ⟨5, witness_of_certificate certificate_311⟩
  · subst n
    exact ⟨2, witness_of_certificate certificate_313⟩
  · subst n
    exact ⟨7, witness_of_certificate certificate_315⟩
  · subst n
    exact ⟨2, witness_of_certificate certificate_317⟩
  · subst n
    exact ⟨21, witness_of_certificate certificate_319⟩
  · subst n
    exact ⟨2, witness_of_certificate certificate_321⟩
  · subst n
    exact ⟨4, witness_of_certificate certificate_323⟩
  · subst n
    exact ⟨2, witness_of_certificate certificate_325⟩
  · subst n
    exact ⟨21, witness_of_certificate certificate_327⟩
  · subst n
    exact ⟨2, witness_of_certificate certificate_329⟩
  · subst n
    exact ⟨5, witness_of_certificate certificate_331⟩
  · subst n
    exact ⟨2, witness_of_certificate certificate_333⟩
  · subst n
    exact ⟨8, witness_of_certificate certificate_335⟩

end Collatz.Research.CoefficientDescent.Batch005
