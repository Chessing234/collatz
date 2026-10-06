import Collatz.Research.CoefficientDescent.Basic

namespace Collatz.Research.CoefficientDescent.Batch050

open FirstDescentClass

set_option maxRecDepth 20000
set_option maxHeartbeats 0

/-- Checked base and every prefix for input 3285. -/
theorem certificate_3285 : classCertificateB 2 3285 = true := by
  decide

/-- The same exact first-descent time holds on an infinite dyadic ray. -/
theorem ray_3285 (m : Nat) : stoppingTime (2 ^ 2 * m + 3285) 2 :=
  stoppingTime_of_classCertificate certificate_3285 m

/-- Checked base and every prefix for input 3287. -/
theorem certificate_3287 : classCertificateB 5 3287 = true := by
  decide

/-- The same exact first-descent time holds on an infinite dyadic ray. -/
theorem ray_3287 (m : Nat) : stoppingTime (2 ^ 5 * m + 3287) 5 :=
  stoppingTime_of_classCertificate certificate_3287 m

/-- Checked base and every prefix for input 3289. -/
theorem certificate_3289 : classCertificateB 2 3289 = true := by
  decide

/-- The same exact first-descent time holds on an infinite dyadic ray. -/
theorem ray_3289 (m : Nat) : stoppingTime (2 ^ 2 * m + 3289) 2 :=
  stoppingTime_of_classCertificate certificate_3289 m

/-- Checked base and every prefix for input 3291. -/
theorem certificate_3291 : classCertificateB 8 3291 = true := by
  decide

/-- The same exact first-descent time holds on an infinite dyadic ray. -/
theorem ray_3291 (m : Nat) : stoppingTime (2 ^ 8 * m + 3291) 8 :=
  stoppingTime_of_classCertificate certificate_3291 m

/-- Checked base and every prefix for input 3293. -/
theorem certificate_3293 : classCertificateB 2 3293 = true := by
  decide

/-- The same exact first-descent time holds on an infinite dyadic ray. -/
theorem ray_3293 (m : Nat) : stoppingTime (2 ^ 2 * m + 3293) 2 :=
  stoppingTime_of_classCertificate certificate_3293 m

/-- Checked base and every prefix for input 3295. -/
theorem certificate_3295 : classCertificateB 12 3295 = true := by
  decide

/-- The same exact first-descent time holds on an infinite dyadic ray. -/
theorem ray_3295 (m : Nat) : stoppingTime (2 ^ 12 * m + 3295) 12 :=
  stoppingTime_of_classCertificate certificate_3295 m

/-- Checked base and every prefix for input 3297. -/
theorem certificate_3297 : classCertificateB 2 3297 = true := by
  decide

/-- The same exact first-descent time holds on an infinite dyadic ray. -/
theorem ray_3297 (m : Nat) : stoppingTime (2 ^ 2 * m + 3297) 2 :=
  stoppingTime_of_classCertificate certificate_3297 m

/-- Checked base and every prefix for input 3299. -/
theorem certificate_3299 : classCertificateB 4 3299 = true := by
  decide

/-- The same exact first-descent time holds on an infinite dyadic ray. -/
theorem ray_3299 (m : Nat) : stoppingTime (2 ^ 4 * m + 3299) 4 :=
  stoppingTime_of_classCertificate certificate_3299 m

/-- Checked base and every prefix for input 3301. -/
theorem certificate_3301 : classCertificateB 2 3301 = true := by
  decide

/-- The same exact first-descent time holds on an infinite dyadic ray. -/
theorem ray_3301 (m : Nat) : stoppingTime (2 ^ 2 * m + 3301) 2 :=
  stoppingTime_of_classCertificate certificate_3301 m

/-- Checked base and every prefix for input 3303. -/
theorem certificate_3303 : classCertificateB 15 3303 = true := by
  decide

/-- The same exact first-descent time holds on an infinite dyadic ray. -/
theorem ray_3303 (m : Nat) : stoppingTime (2 ^ 15 * m + 3303) 15 :=
  stoppingTime_of_classCertificate certificate_3303 m

/-- Checked base and every prefix for input 3305. -/
theorem certificate_3305 : classCertificateB 2 3305 = true := by
  decide

/-- The same exact first-descent time holds on an infinite dyadic ray. -/
theorem ray_3305 (m : Nat) : stoppingTime (2 ^ 2 * m + 3305) 2 :=
  stoppingTime_of_classCertificate certificate_3305 m

/-- Checked base and every prefix for input 3307. -/
theorem certificate_3307 : classCertificateB 5 3307 = true := by
  decide

/-- The same exact first-descent time holds on an infinite dyadic ray. -/
theorem ray_3307 (m : Nat) : stoppingTime (2 ^ 5 * m + 3307) 5 :=
  stoppingTime_of_classCertificate certificate_3307 m

/-- Checked base and every prefix for input 3309. -/
theorem certificate_3309 : classCertificateB 2 3309 = true := by
  decide

/-- The same exact first-descent time holds on an infinite dyadic ray. -/
theorem ray_3309 (m : Nat) : stoppingTime (2 ^ 2 * m + 3309) 2 :=
  stoppingTime_of_classCertificate certificate_3309 m

/-- Checked base and every prefix for input 3311. -/
theorem certificate_3311 : classCertificateB 26 3311 = true := by
  decide

/-- The same exact first-descent time holds on an infinite dyadic ray. -/
theorem ray_3311 (m : Nat) : stoppingTime (2 ^ 26 * m + 3311) 26 :=
  stoppingTime_of_classCertificate certificate_3311 m

/-- Checked base and every prefix for input 3313. -/
theorem certificate_3313 : classCertificateB 2 3313 = true := by
  decide

/-- The same exact first-descent time holds on an infinite dyadic ray. -/
theorem ray_3313 (m : Nat) : stoppingTime (2 ^ 2 * m + 3313) 2 :=
  stoppingTime_of_classCertificate certificate_3313 m

/-- Checked base and every prefix for input 3315. -/
theorem certificate_3315 : classCertificateB 4 3315 = true := by
  decide

/-- The same exact first-descent time holds on an infinite dyadic ray. -/
theorem ray_3315 (m : Nat) : stoppingTime (2 ^ 4 * m + 3315) 4 :=
  stoppingTime_of_classCertificate certificate_3315 m

/-- Checked base and every prefix for input 3317. -/
theorem certificate_3317 : classCertificateB 2 3317 = true := by
  decide

/-- The same exact first-descent time holds on an infinite dyadic ray. -/
theorem ray_3317 (m : Nat) : stoppingTime (2 ^ 2 * m + 3317) 2 :=
  stoppingTime_of_classCertificate certificate_3317 m

/-- Checked base and every prefix for input 3319. -/
theorem certificate_3319 : classCertificateB 5 3319 = true := by
  decide

/-- The same exact first-descent time holds on an infinite dyadic ray. -/
theorem ray_3319 (m : Nat) : stoppingTime (2 ^ 5 * m + 3319) 5 :=
  stoppingTime_of_classCertificate certificate_3319 m

/-- Checked base and every prefix for input 3321. -/
theorem certificate_3321 : classCertificateB 2 3321 = true := by
  decide

/-- The same exact first-descent time holds on an infinite dyadic ray. -/
theorem ray_3321 (m : Nat) : stoppingTime (2 ^ 2 * m + 3321) 2 :=
  stoppingTime_of_classCertificate certificate_3321 m

/-- Checked base and every prefix for input 3323. -/
theorem certificate_3323 : classCertificateB 42 3323 = true := by
  decide

/-- The same exact first-descent time holds on an infinite dyadic ray. -/
theorem ray_3323 (m : Nat) : stoppingTime (2 ^ 42 * m + 3323) 42 :=
  stoppingTime_of_classCertificate certificate_3323 m

/-- Checked base and every prefix for input 3325. -/
theorem certificate_3325 : classCertificateB 2 3325 = true := by
  decide

/-- The same exact first-descent time holds on an infinite dyadic ray. -/
theorem ray_3325 (m : Nat) : stoppingTime (2 ^ 2 * m + 3325) 2 :=
  stoppingTime_of_classCertificate certificate_3325 m

/-- Checked base and every prefix for input 3327. -/
theorem certificate_3327 : classCertificateB 18 3327 = true := by
  decide

/-- The same exact first-descent time holds on an infinite dyadic ray. -/
theorem ray_3327 (m : Nat) : stoppingTime (2 ^ 18 * m + 3327) 18 :=
  stoppingTime_of_classCertificate certificate_3327 m

/-- Checked base and every prefix for input 3329. -/
theorem certificate_3329 : classCertificateB 2 3329 = true := by
  decide

/-- The same exact first-descent time holds on an infinite dyadic ray. -/
theorem ray_3329 (m : Nat) : stoppingTime (2 ^ 2 * m + 3329) 2 :=
  stoppingTime_of_classCertificate certificate_3329 m

/-- Checked base and every prefix for input 3331. -/
theorem certificate_3331 : classCertificateB 4 3331 = true := by
  decide

/-- The same exact first-descent time holds on an infinite dyadic ray. -/
theorem ray_3331 (m : Nat) : stoppingTime (2 ^ 4 * m + 3331) 4 :=
  stoppingTime_of_classCertificate certificate_3331 m

/-- Checked base and every prefix for input 3333. -/
theorem certificate_3333 : classCertificateB 2 3333 = true := by
  decide

/-- The same exact first-descent time holds on an infinite dyadic ray. -/
theorem ray_3333 (m : Nat) : stoppingTime (2 ^ 2 * m + 3333) 2 :=
  stoppingTime_of_classCertificate certificate_3333 m

/-- Checked base and every prefix for input 3335. -/
theorem certificate_3335 : classCertificateB 7 3335 = true := by
  decide

/-- The same exact first-descent time holds on an infinite dyadic ray. -/
theorem ray_3335 (m : Nat) : stoppingTime (2 ^ 7 * m + 3335) 7 :=
  stoppingTime_of_classCertificate certificate_3335 m

/-- Checked base and every prefix for input 3337. -/
theorem certificate_3337 : classCertificateB 2 3337 = true := by
  decide

/-- The same exact first-descent time holds on an infinite dyadic ray. -/
theorem ray_3337 (m : Nat) : stoppingTime (2 ^ 2 * m + 3337) 2 :=
  stoppingTime_of_classCertificate certificate_3337 m

/-- Checked base and every prefix for input 3339. -/
theorem certificate_3339 : classCertificateB 5 3339 = true := by
  decide

/-- The same exact first-descent time holds on an infinite dyadic ray. -/
theorem ray_3339 (m : Nat) : stoppingTime (2 ^ 5 * m + 3339) 5 :=
  stoppingTime_of_classCertificate certificate_3339 m

/-- Checked base and every prefix for input 3341. -/
theorem certificate_3341 : classCertificateB 2 3341 = true := by
  decide

/-- The same exact first-descent time holds on an infinite dyadic ray. -/
theorem ray_3341 (m : Nat) : stoppingTime (2 ^ 2 * m + 3341) 2 :=
  stoppingTime_of_classCertificate certificate_3341 m

/-- Checked base and every prefix for input 3343. -/
theorem certificate_3343 : classCertificateB 7 3343 = true := by
  decide

/-- The same exact first-descent time holds on an infinite dyadic ray. -/
theorem ray_3343 (m : Nat) : stoppingTime (2 ^ 7 * m + 3343) 7 :=
  stoppingTime_of_classCertificate certificate_3343 m

/-- Checked base and every prefix for input 3345. -/
theorem certificate_3345 : classCertificateB 2 3345 = true := by
  decide

/-- The same exact first-descent time holds on an infinite dyadic ray. -/
theorem ray_3345 (m : Nat) : stoppingTime (2 ^ 2 * m + 3345) 2 :=
  stoppingTime_of_classCertificate certificate_3345 m

/-- Checked base and every prefix for input 3347. -/
theorem certificate_3347 : classCertificateB 4 3347 = true := by
  decide

/-- The same exact first-descent time holds on an infinite dyadic ray. -/
theorem ray_3347 (m : Nat) : stoppingTime (2 ^ 4 * m + 3347) 4 :=
  stoppingTime_of_classCertificate certificate_3347 m

/-- Checked base and every prefix for input 3349. -/
theorem certificate_3349 : classCertificateB 2 3349 = true := by
  decide

/-- The same exact first-descent time holds on an infinite dyadic ray. -/
theorem ray_3349 (m : Nat) : stoppingTime (2 ^ 2 * m + 3349) 2 :=
  stoppingTime_of_classCertificate certificate_3349 m

/-- Exhaustive coverage of the odd inputs in this batch, with no gaps. -/
theorem coverage : CertifiedRange 3285 3351 := by
  intro n hlo hhi hodd
  have hn : n = 3285 ∨ n = 3287 ∨ n = 3289 ∨ n = 3291 ∨ n = 3293 ∨ n = 3295 ∨ n = 3297 ∨ n = 3299 ∨ n = 3301 ∨ n = 3303 ∨ n = 3305 ∨ n = 3307 ∨ n = 3309 ∨ n = 3311 ∨ n = 3313 ∨ n = 3315 ∨ n = 3317 ∨ n = 3319 ∨ n = 3321 ∨ n = 3323 ∨ n = 3325 ∨ n = 3327 ∨ n = 3329 ∨ n = 3331 ∨ n = 3333 ∨ n = 3335 ∨ n = 3337 ∨ n = 3339 ∨ n = 3341 ∨ n = 3343 ∨ n = 3345 ∨ n = 3347 ∨ n = 3349 := by omega
  rcases hn with h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h
  · subst n
    exact ⟨2, witness_of_certificate certificate_3285⟩
  · subst n
    exact ⟨5, witness_of_certificate certificate_3287⟩
  · subst n
    exact ⟨2, witness_of_certificate certificate_3289⟩
  · subst n
    exact ⟨8, witness_of_certificate certificate_3291⟩
  · subst n
    exact ⟨2, witness_of_certificate certificate_3293⟩
  · subst n
    exact ⟨12, witness_of_certificate certificate_3295⟩
  · subst n
    exact ⟨2, witness_of_certificate certificate_3297⟩
  · subst n
    exact ⟨4, witness_of_certificate certificate_3299⟩
  · subst n
    exact ⟨2, witness_of_certificate certificate_3301⟩
  · subst n
    exact ⟨15, witness_of_certificate certificate_3303⟩
  · subst n
    exact ⟨2, witness_of_certificate certificate_3305⟩
  · subst n
    exact ⟨5, witness_of_certificate certificate_3307⟩
  · subst n
    exact ⟨2, witness_of_certificate certificate_3309⟩
  · subst n
    exact ⟨26, witness_of_certificate certificate_3311⟩
  · subst n
    exact ⟨2, witness_of_certificate certificate_3313⟩
  · subst n
    exact ⟨4, witness_of_certificate certificate_3315⟩
  · subst n
    exact ⟨2, witness_of_certificate certificate_3317⟩
  · subst n
    exact ⟨5, witness_of_certificate certificate_3319⟩
  · subst n
    exact ⟨2, witness_of_certificate certificate_3321⟩
  · subst n
    exact ⟨42, witness_of_certificate certificate_3323⟩
  · subst n
    exact ⟨2, witness_of_certificate certificate_3325⟩
  · subst n
    exact ⟨18, witness_of_certificate certificate_3327⟩
  · subst n
    exact ⟨2, witness_of_certificate certificate_3329⟩
  · subst n
    exact ⟨4, witness_of_certificate certificate_3331⟩
  · subst n
    exact ⟨2, witness_of_certificate certificate_3333⟩
  · subst n
    exact ⟨7, witness_of_certificate certificate_3335⟩
  · subst n
    exact ⟨2, witness_of_certificate certificate_3337⟩
  · subst n
    exact ⟨5, witness_of_certificate certificate_3339⟩
  · subst n
    exact ⟨2, witness_of_certificate certificate_3341⟩
  · subst n
    exact ⟨7, witness_of_certificate certificate_3343⟩
  · subst n
    exact ⟨2, witness_of_certificate certificate_3345⟩
  · subst n
    exact ⟨4, witness_of_certificate certificate_3347⟩
  · subst n
    exact ⟨2, witness_of_certificate certificate_3349⟩

end Collatz.Research.CoefficientDescent.Batch050
