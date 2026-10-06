import Collatz.Research.CoefficientDescent.Basic

namespace Collatz.Research.CoefficientDescent.Batch006

open FirstDescentClass

set_option maxRecDepth 20000
set_option maxHeartbeats 0

/-- Checked base and every prefix for input 337. -/
theorem certificate_337 : classCertificateB 2 337 = true := by
  decide

/-- The same exact first-descent time holds on an infinite dyadic ray. -/
theorem ray_337 (m : Nat) : stoppingTime (2 ^ 2 * m + 337) 2 :=
  stoppingTime_of_classCertificate certificate_337 m

/-- Checked base and every prefix for input 339. -/
theorem certificate_339 : classCertificateB 4 339 = true := by
  decide

/-- The same exact first-descent time holds on an infinite dyadic ray. -/
theorem ray_339 (m : Nat) : stoppingTime (2 ^ 4 * m + 339) 4 :=
  stoppingTime_of_classCertificate certificate_339 m

/-- Checked base and every prefix for input 341. -/
theorem certificate_341 : classCertificateB 2 341 = true := by
  decide

/-- The same exact first-descent time holds on an infinite dyadic ray. -/
theorem ray_341 (m : Nat) : stoppingTime (2 ^ 2 * m + 341) 2 :=
  stoppingTime_of_classCertificate certificate_341 m

/-- Checked base and every prefix for input 343. -/
theorem certificate_343 : classCertificateB 5 343 = true := by
  decide

/-- The same exact first-descent time holds on an infinite dyadic ray. -/
theorem ray_343 (m : Nat) : stoppingTime (2 ^ 5 * m + 343) 5 :=
  stoppingTime_of_classCertificate certificate_343 m

/-- Checked base and every prefix for input 345. -/
theorem certificate_345 : classCertificateB 2 345 = true := by
  decide

/-- The same exact first-descent time holds on an infinite dyadic ray. -/
theorem ray_345 (m : Nat) : stoppingTime (2 ^ 2 * m + 345) 2 :=
  stoppingTime_of_classCertificate certificate_345 m

/-- Checked base and every prefix for input 347. -/
theorem certificate_347 : classCertificateB 10 347 = true := by
  decide

/-- The same exact first-descent time holds on an infinite dyadic ray. -/
theorem ray_347 (m : Nat) : stoppingTime (2 ^ 10 * m + 347) 10 :=
  stoppingTime_of_classCertificate certificate_347 m

/-- Checked base and every prefix for input 349. -/
theorem certificate_349 : classCertificateB 2 349 = true := by
  decide

/-- The same exact first-descent time holds on an infinite dyadic ray. -/
theorem ray_349 (m : Nat) : stoppingTime (2 ^ 2 * m + 349) 2 :=
  stoppingTime_of_classCertificate certificate_349 m

/-- Checked base and every prefix for input 351. -/
theorem certificate_351 : classCertificateB 8 351 = true := by
  decide

/-- The same exact first-descent time holds on an infinite dyadic ray. -/
theorem ray_351 (m : Nat) : stoppingTime (2 ^ 8 * m + 351) 8 :=
  stoppingTime_of_classCertificate certificate_351 m

/-- Checked base and every prefix for input 353. -/
theorem certificate_353 : classCertificateB 2 353 = true := by
  decide

/-- The same exact first-descent time holds on an infinite dyadic ray. -/
theorem ray_353 (m : Nat) : stoppingTime (2 ^ 2 * m + 353) 2 :=
  stoppingTime_of_classCertificate certificate_353 m

/-- Checked base and every prefix for input 355. -/
theorem certificate_355 : classCertificateB 4 355 = true := by
  decide

/-- The same exact first-descent time holds on an infinite dyadic ray. -/
theorem ray_355 (m : Nat) : stoppingTime (2 ^ 4 * m + 355) 4 :=
  stoppingTime_of_classCertificate certificate_355 m

/-- Checked base and every prefix for input 357. -/
theorem certificate_357 : classCertificateB 2 357 = true := by
  decide

/-- The same exact first-descent time holds on an infinite dyadic ray. -/
theorem ray_357 (m : Nat) : stoppingTime (2 ^ 2 * m + 357) 2 :=
  stoppingTime_of_classCertificate certificate_357 m

/-- Checked base and every prefix for input 359. -/
theorem certificate_359 : classCertificateB 16 359 = true := by
  decide

/-- The same exact first-descent time holds on an infinite dyadic ray. -/
theorem ray_359 (m : Nat) : stoppingTime (2 ^ 16 * m + 359) 16 :=
  stoppingTime_of_classCertificate certificate_359 m

/-- Checked base and every prefix for input 361. -/
theorem certificate_361 : classCertificateB 2 361 = true := by
  decide

/-- The same exact first-descent time holds on an infinite dyadic ray. -/
theorem ray_361 (m : Nat) : stoppingTime (2 ^ 2 * m + 361) 2 :=
  stoppingTime_of_classCertificate certificate_361 m

/-- Checked base and every prefix for input 363. -/
theorem certificate_363 : classCertificateB 5 363 = true := by
  decide

/-- The same exact first-descent time holds on an infinite dyadic ray. -/
theorem ray_363 (m : Nat) : stoppingTime (2 ^ 5 * m + 363) 5 :=
  stoppingTime_of_classCertificate certificate_363 m

/-- Checked base and every prefix for input 365. -/
theorem certificate_365 : classCertificateB 2 365 = true := by
  decide

/-- The same exact first-descent time holds on an infinite dyadic ray. -/
theorem ray_365 (m : Nat) : stoppingTime (2 ^ 2 * m + 365) 2 :=
  stoppingTime_of_classCertificate certificate_365 m

/-- Checked base and every prefix for input 367. -/
theorem certificate_367 : classCertificateB 10 367 = true := by
  decide

/-- The same exact first-descent time holds on an infinite dyadic ray. -/
theorem ray_367 (m : Nat) : stoppingTime (2 ^ 10 * m + 367) 10 :=
  stoppingTime_of_classCertificate certificate_367 m

/-- Checked base and every prefix for input 369. -/
theorem certificate_369 : classCertificateB 2 369 = true := by
  decide

/-- The same exact first-descent time holds on an infinite dyadic ray. -/
theorem ray_369 (m : Nat) : stoppingTime (2 ^ 2 * m + 369) 2 :=
  stoppingTime_of_classCertificate certificate_369 m

/-- Checked base and every prefix for input 371. -/
theorem certificate_371 : classCertificateB 4 371 = true := by
  decide

/-- The same exact first-descent time holds on an infinite dyadic ray. -/
theorem ray_371 (m : Nat) : stoppingTime (2 ^ 4 * m + 371) 4 :=
  stoppingTime_of_classCertificate certificate_371 m

/-- Checked base and every prefix for input 373. -/
theorem certificate_373 : classCertificateB 2 373 = true := by
  decide

/-- The same exact first-descent time holds on an infinite dyadic ray. -/
theorem ray_373 (m : Nat) : stoppingTime (2 ^ 2 * m + 373) 2 :=
  stoppingTime_of_classCertificate certificate_373 m

/-- Checked base and every prefix for input 375. -/
theorem certificate_375 : classCertificateB 5 375 = true := by
  decide

/-- The same exact first-descent time holds on an infinite dyadic ray. -/
theorem ray_375 (m : Nat) : stoppingTime (2 ^ 5 * m + 375) 5 :=
  stoppingTime_of_classCertificate certificate_375 m

/-- Checked base and every prefix for input 377. -/
theorem certificate_377 : classCertificateB 2 377 = true := by
  decide

/-- The same exact first-descent time holds on an infinite dyadic ray. -/
theorem ray_377 (m : Nat) : stoppingTime (2 ^ 2 * m + 377) 2 :=
  stoppingTime_of_classCertificate certificate_377 m

/-- Checked base and every prefix for input 379. -/
theorem certificate_379 : classCertificateB 8 379 = true := by
  decide

/-- The same exact first-descent time holds on an infinite dyadic ray. -/
theorem ray_379 (m : Nat) : stoppingTime (2 ^ 8 * m + 379) 8 :=
  stoppingTime_of_classCertificate certificate_379 m

/-- Checked base and every prefix for input 381. -/
theorem certificate_381 : classCertificateB 2 381 = true := by
  decide

/-- The same exact first-descent time holds on an infinite dyadic ray. -/
theorem ray_381 (m : Nat) : stoppingTime (2 ^ 2 * m + 381) 2 :=
  stoppingTime_of_classCertificate certificate_381 m

/-- Checked base and every prefix for input 383. -/
theorem certificate_383 : classCertificateB 12 383 = true := by
  decide

/-- The same exact first-descent time holds on an infinite dyadic ray. -/
theorem ray_383 (m : Nat) : stoppingTime (2 ^ 12 * m + 383) 12 :=
  stoppingTime_of_classCertificate certificate_383 m

/-- Checked base and every prefix for input 385. -/
theorem certificate_385 : classCertificateB 2 385 = true := by
  decide

/-- The same exact first-descent time holds on an infinite dyadic ray. -/
theorem ray_385 (m : Nat) : stoppingTime (2 ^ 2 * m + 385) 2 :=
  stoppingTime_of_classCertificate certificate_385 m

/-- Checked base and every prefix for input 387. -/
theorem certificate_387 : classCertificateB 4 387 = true := by
  decide

/-- The same exact first-descent time holds on an infinite dyadic ray. -/
theorem ray_387 (m : Nat) : stoppingTime (2 ^ 4 * m + 387) 4 :=
  stoppingTime_of_classCertificate certificate_387 m

/-- Checked base and every prefix for input 389. -/
theorem certificate_389 : classCertificateB 2 389 = true := by
  decide

/-- The same exact first-descent time holds on an infinite dyadic ray. -/
theorem ray_389 (m : Nat) : stoppingTime (2 ^ 2 * m + 389) 2 :=
  stoppingTime_of_classCertificate certificate_389 m

/-- Checked base and every prefix for input 391. -/
theorem certificate_391 : classCertificateB 7 391 = true := by
  decide

/-- The same exact first-descent time holds on an infinite dyadic ray. -/
theorem ray_391 (m : Nat) : stoppingTime (2 ^ 7 * m + 391) 7 :=
  stoppingTime_of_classCertificate certificate_391 m

/-- Checked base and every prefix for input 393. -/
theorem certificate_393 : classCertificateB 2 393 = true := by
  decide

/-- The same exact first-descent time holds on an infinite dyadic ray. -/
theorem ray_393 (m : Nat) : stoppingTime (2 ^ 2 * m + 393) 2 :=
  stoppingTime_of_classCertificate certificate_393 m

/-- Checked base and every prefix for input 395. -/
theorem certificate_395 : classCertificateB 5 395 = true := by
  decide

/-- The same exact first-descent time holds on an infinite dyadic ray. -/
theorem ray_395 (m : Nat) : stoppingTime (2 ^ 5 * m + 395) 5 :=
  stoppingTime_of_classCertificate certificate_395 m

/-- Checked base and every prefix for input 397. -/
theorem certificate_397 : classCertificateB 2 397 = true := by
  decide

/-- The same exact first-descent time holds on an infinite dyadic ray. -/
theorem ray_397 (m : Nat) : stoppingTime (2 ^ 2 * m + 397) 2 :=
  stoppingTime_of_classCertificate certificate_397 m

/-- Checked base and every prefix for input 399. -/
theorem certificate_399 : classCertificateB 7 399 = true := by
  decide

/-- The same exact first-descent time holds on an infinite dyadic ray. -/
theorem ray_399 (m : Nat) : stoppingTime (2 ^ 7 * m + 399) 7 :=
  stoppingTime_of_classCertificate certificate_399 m

/-- Checked base and every prefix for input 401. -/
theorem certificate_401 : classCertificateB 2 401 = true := by
  decide

/-- The same exact first-descent time holds on an infinite dyadic ray. -/
theorem ray_401 (m : Nat) : stoppingTime (2 ^ 2 * m + 401) 2 :=
  stoppingTime_of_classCertificate certificate_401 m

/-- Exhaustive coverage of the odd inputs in this batch, with no gaps. -/
theorem coverage : CertifiedRange 337 403 := by
  intro n hlo hhi hodd
  have hn : n = 337 ∨ n = 339 ∨ n = 341 ∨ n = 343 ∨ n = 345 ∨ n = 347 ∨ n = 349 ∨ n = 351 ∨ n = 353 ∨ n = 355 ∨ n = 357 ∨ n = 359 ∨ n = 361 ∨ n = 363 ∨ n = 365 ∨ n = 367 ∨ n = 369 ∨ n = 371 ∨ n = 373 ∨ n = 375 ∨ n = 377 ∨ n = 379 ∨ n = 381 ∨ n = 383 ∨ n = 385 ∨ n = 387 ∨ n = 389 ∨ n = 391 ∨ n = 393 ∨ n = 395 ∨ n = 397 ∨ n = 399 ∨ n = 401 := by omega
  rcases hn with h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h
  · subst n
    exact ⟨2, witness_of_certificate certificate_337⟩
  · subst n
    exact ⟨4, witness_of_certificate certificate_339⟩
  · subst n
    exact ⟨2, witness_of_certificate certificate_341⟩
  · subst n
    exact ⟨5, witness_of_certificate certificate_343⟩
  · subst n
    exact ⟨2, witness_of_certificate certificate_345⟩
  · subst n
    exact ⟨10, witness_of_certificate certificate_347⟩
  · subst n
    exact ⟨2, witness_of_certificate certificate_349⟩
  · subst n
    exact ⟨8, witness_of_certificate certificate_351⟩
  · subst n
    exact ⟨2, witness_of_certificate certificate_353⟩
  · subst n
    exact ⟨4, witness_of_certificate certificate_355⟩
  · subst n
    exact ⟨2, witness_of_certificate certificate_357⟩
  · subst n
    exact ⟨16, witness_of_certificate certificate_359⟩
  · subst n
    exact ⟨2, witness_of_certificate certificate_361⟩
  · subst n
    exact ⟨5, witness_of_certificate certificate_363⟩
  · subst n
    exact ⟨2, witness_of_certificate certificate_365⟩
  · subst n
    exact ⟨10, witness_of_certificate certificate_367⟩
  · subst n
    exact ⟨2, witness_of_certificate certificate_369⟩
  · subst n
    exact ⟨4, witness_of_certificate certificate_371⟩
  · subst n
    exact ⟨2, witness_of_certificate certificate_373⟩
  · subst n
    exact ⟨5, witness_of_certificate certificate_375⟩
  · subst n
    exact ⟨2, witness_of_certificate certificate_377⟩
  · subst n
    exact ⟨8, witness_of_certificate certificate_379⟩
  · subst n
    exact ⟨2, witness_of_certificate certificate_381⟩
  · subst n
    exact ⟨12, witness_of_certificate certificate_383⟩
  · subst n
    exact ⟨2, witness_of_certificate certificate_385⟩
  · subst n
    exact ⟨4, witness_of_certificate certificate_387⟩
  · subst n
    exact ⟨2, witness_of_certificate certificate_389⟩
  · subst n
    exact ⟨7, witness_of_certificate certificate_391⟩
  · subst n
    exact ⟨2, witness_of_certificate certificate_393⟩
  · subst n
    exact ⟨5, witness_of_certificate certificate_395⟩
  · subst n
    exact ⟨2, witness_of_certificate certificate_397⟩
  · subst n
    exact ⟨7, witness_of_certificate certificate_399⟩
  · subst n
    exact ⟨2, witness_of_certificate certificate_401⟩

end Collatz.Research.CoefficientDescent.Batch006
