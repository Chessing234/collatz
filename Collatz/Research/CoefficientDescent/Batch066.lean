import Collatz.Research.CoefficientDescent.Basic

namespace Collatz.Research.CoefficientDescent.Batch066

open FirstDescentClass

set_option maxRecDepth 20000
set_option maxHeartbeats 0

/-- Checked base and every prefix for input 4355. -/
theorem certificate_4355 : classCertificateB 4 4355 = true := by
  decide

/-- The same exact first-descent time holds on an infinite dyadic ray. -/
theorem ray_4355 (m : Nat) : stoppingTime (2 ^ 4 * m + 4355) 4 :=
  stoppingTime_of_classCertificate certificate_4355 m

/-- Checked base and every prefix for input 4357. -/
theorem certificate_4357 : classCertificateB 2 4357 = true := by
  decide

/-- The same exact first-descent time holds on an infinite dyadic ray. -/
theorem ray_4357 (m : Nat) : stoppingTime (2 ^ 2 * m + 4357) 2 :=
  stoppingTime_of_classCertificate certificate_4357 m

/-- Checked base and every prefix for input 4359. -/
theorem certificate_4359 : classCertificateB 7 4359 = true := by
  decide

/-- The same exact first-descent time holds on an infinite dyadic ray. -/
theorem ray_4359 (m : Nat) : stoppingTime (2 ^ 7 * m + 4359) 7 :=
  stoppingTime_of_classCertificate certificate_4359 m

/-- Checked base and every prefix for input 4361. -/
theorem certificate_4361 : classCertificateB 2 4361 = true := by
  decide

/-- The same exact first-descent time holds on an infinite dyadic ray. -/
theorem ray_4361 (m : Nat) : stoppingTime (2 ^ 2 * m + 4361) 2 :=
  stoppingTime_of_classCertificate certificate_4361 m

/-- Checked base and every prefix for input 4363. -/
theorem certificate_4363 : classCertificateB 5 4363 = true := by
  decide

/-- The same exact first-descent time holds on an infinite dyadic ray. -/
theorem ray_4363 (m : Nat) : stoppingTime (2 ^ 5 * m + 4363) 5 :=
  stoppingTime_of_classCertificate certificate_4363 m

/-- Checked base and every prefix for input 4365. -/
theorem certificate_4365 : classCertificateB 2 4365 = true := by
  decide

/-- The same exact first-descent time holds on an infinite dyadic ray. -/
theorem ray_4365 (m : Nat) : stoppingTime (2 ^ 2 * m + 4365) 2 :=
  stoppingTime_of_classCertificate certificate_4365 m

/-- Checked base and every prefix for input 4367. -/
theorem certificate_4367 : classCertificateB 7 4367 = true := by
  decide

/-- The same exact first-descent time holds on an infinite dyadic ray. -/
theorem ray_4367 (m : Nat) : stoppingTime (2 ^ 7 * m + 4367) 7 :=
  stoppingTime_of_classCertificate certificate_4367 m

/-- Checked base and every prefix for input 4369. -/
theorem certificate_4369 : classCertificateB 2 4369 = true := by
  decide

/-- The same exact first-descent time holds on an infinite dyadic ray. -/
theorem ray_4369 (m : Nat) : stoppingTime (2 ^ 2 * m + 4369) 2 :=
  stoppingTime_of_classCertificate certificate_4369 m

/-- Checked base and every prefix for input 4371. -/
theorem certificate_4371 : classCertificateB 4 4371 = true := by
  decide

/-- The same exact first-descent time holds on an infinite dyadic ray. -/
theorem ray_4371 (m : Nat) : stoppingTime (2 ^ 4 * m + 4371) 4 :=
  stoppingTime_of_classCertificate certificate_4371 m

/-- Checked base and every prefix for input 4373. -/
theorem certificate_4373 : classCertificateB 2 4373 = true := by
  decide

/-- The same exact first-descent time holds on an infinite dyadic ray. -/
theorem ray_4373 (m : Nat) : stoppingTime (2 ^ 2 * m + 4373) 2 :=
  stoppingTime_of_classCertificate certificate_4373 m

/-- Checked base and every prefix for input 4375. -/
theorem certificate_4375 : classCertificateB 5 4375 = true := by
  decide

/-- The same exact first-descent time holds on an infinite dyadic ray. -/
theorem ray_4375 (m : Nat) : stoppingTime (2 ^ 5 * m + 4375) 5 :=
  stoppingTime_of_classCertificate certificate_4375 m

/-- Checked base and every prefix for input 4377. -/
theorem certificate_4377 : classCertificateB 2 4377 = true := by
  decide

/-- The same exact first-descent time holds on an infinite dyadic ray. -/
theorem ray_4377 (m : Nat) : stoppingTime (2 ^ 2 * m + 4377) 2 :=
  stoppingTime_of_classCertificate certificate_4377 m

/-- Checked base and every prefix for input 4379. -/
theorem certificate_4379 : classCertificateB 16 4379 = true := by
  decide

/-- The same exact first-descent time holds on an infinite dyadic ray. -/
theorem ray_4379 (m : Nat) : stoppingTime (2 ^ 16 * m + 4379) 16 :=
  stoppingTime_of_classCertificate certificate_4379 m

/-- Checked base and every prefix for input 4381. -/
theorem certificate_4381 : classCertificateB 2 4381 = true := by
  decide

/-- The same exact first-descent time holds on an infinite dyadic ray. -/
theorem ray_4381 (m : Nat) : stoppingTime (2 ^ 2 * m + 4381) 2 :=
  stoppingTime_of_classCertificate certificate_4381 m

/-- Checked base and every prefix for input 4383. -/
theorem certificate_4383 : classCertificateB 10 4383 = true := by
  decide

/-- The same exact first-descent time holds on an infinite dyadic ray. -/
theorem ray_4383 (m : Nat) : stoppingTime (2 ^ 10 * m + 4383) 10 :=
  stoppingTime_of_classCertificate certificate_4383 m

/-- Checked base and every prefix for input 4385. -/
theorem certificate_4385 : classCertificateB 2 4385 = true := by
  decide

/-- The same exact first-descent time holds on an infinite dyadic ray. -/
theorem ray_4385 (m : Nat) : stoppingTime (2 ^ 2 * m + 4385) 2 :=
  stoppingTime_of_classCertificate certificate_4385 m

/-- Checked base and every prefix for input 4387. -/
theorem certificate_4387 : classCertificateB 4 4387 = true := by
  decide

/-- The same exact first-descent time holds on an infinite dyadic ray. -/
theorem ray_4387 (m : Nat) : stoppingTime (2 ^ 4 * m + 4387) 4 :=
  stoppingTime_of_classCertificate certificate_4387 m

/-- Checked base and every prefix for input 4389. -/
theorem certificate_4389 : classCertificateB 2 4389 = true := by
  decide

/-- The same exact first-descent time holds on an infinite dyadic ray. -/
theorem ray_4389 (m : Nat) : stoppingTime (2 ^ 2 * m + 4389) 2 :=
  stoppingTime_of_classCertificate certificate_4389 m

/-- Checked base and every prefix for input 4391. -/
theorem certificate_4391 : classCertificateB 8 4391 = true := by
  decide

/-- The same exact first-descent time holds on an infinite dyadic ray. -/
theorem ray_4391 (m : Nat) : stoppingTime (2 ^ 8 * m + 4391) 8 :=
  stoppingTime_of_classCertificate certificate_4391 m

/-- Checked base and every prefix for input 4393. -/
theorem certificate_4393 : classCertificateB 2 4393 = true := by
  decide

/-- The same exact first-descent time holds on an infinite dyadic ray. -/
theorem ray_4393 (m : Nat) : stoppingTime (2 ^ 2 * m + 4393) 2 :=
  stoppingTime_of_classCertificate certificate_4393 m

/-- Checked base and every prefix for input 4395. -/
theorem certificate_4395 : classCertificateB 5 4395 = true := by
  decide

/-- The same exact first-descent time holds on an infinite dyadic ray. -/
theorem ray_4395 (m : Nat) : stoppingTime (2 ^ 5 * m + 4395) 5 :=
  stoppingTime_of_classCertificate certificate_4395 m

/-- Checked base and every prefix for input 4397. -/
theorem certificate_4397 : classCertificateB 2 4397 = true := by
  decide

/-- The same exact first-descent time holds on an infinite dyadic ray. -/
theorem ray_4397 (m : Nat) : stoppingTime (2 ^ 2 * m + 4397) 2 :=
  stoppingTime_of_classCertificate certificate_4397 m

/-- Checked base and every prefix for input 4399. -/
theorem certificate_4399 : classCertificateB 32 4399 = true := by
  decide

/-- The same exact first-descent time holds on an infinite dyadic ray. -/
theorem ray_4399 (m : Nat) : stoppingTime (2 ^ 32 * m + 4399) 32 :=
  stoppingTime_of_classCertificate certificate_4399 m

/-- Checked base and every prefix for input 4401. -/
theorem certificate_4401 : classCertificateB 2 4401 = true := by
  decide

/-- The same exact first-descent time holds on an infinite dyadic ray. -/
theorem ray_4401 (m : Nat) : stoppingTime (2 ^ 2 * m + 4401) 2 :=
  stoppingTime_of_classCertificate certificate_4401 m

/-- Checked base and every prefix for input 4403. -/
theorem certificate_4403 : classCertificateB 4 4403 = true := by
  decide

/-- The same exact first-descent time holds on an infinite dyadic ray. -/
theorem ray_4403 (m : Nat) : stoppingTime (2 ^ 4 * m + 4403) 4 :=
  stoppingTime_of_classCertificate certificate_4403 m

/-- Checked base and every prefix for input 4405. -/
theorem certificate_4405 : classCertificateB 2 4405 = true := by
  decide

/-- The same exact first-descent time holds on an infinite dyadic ray. -/
theorem ray_4405 (m : Nat) : stoppingTime (2 ^ 2 * m + 4405) 2 :=
  stoppingTime_of_classCertificate certificate_4405 m

/-- Checked base and every prefix for input 4407. -/
theorem certificate_4407 : classCertificateB 5 4407 = true := by
  decide

/-- The same exact first-descent time holds on an infinite dyadic ray. -/
theorem ray_4407 (m : Nat) : stoppingTime (2 ^ 5 * m + 4407) 5 :=
  stoppingTime_of_classCertificate certificate_4407 m

/-- Checked base and every prefix for input 4409. -/
theorem certificate_4409 : classCertificateB 2 4409 = true := by
  decide

/-- The same exact first-descent time holds on an infinite dyadic ray. -/
theorem ray_4409 (m : Nat) : stoppingTime (2 ^ 2 * m + 4409) 2 :=
  stoppingTime_of_classCertificate certificate_4409 m

/-- Checked base and every prefix for input 4411. -/
theorem certificate_4411 : classCertificateB 7 4411 = true := by
  decide

/-- The same exact first-descent time holds on an infinite dyadic ray. -/
theorem ray_4411 (m : Nat) : stoppingTime (2 ^ 7 * m + 4411) 7 :=
  stoppingTime_of_classCertificate certificate_4411 m

/-- Checked base and every prefix for input 4413. -/
theorem certificate_4413 : classCertificateB 2 4413 = true := by
  decide

/-- The same exact first-descent time holds on an infinite dyadic ray. -/
theorem ray_4413 (m : Nat) : stoppingTime (2 ^ 2 * m + 4413) 2 :=
  stoppingTime_of_classCertificate certificate_4413 m

/-- Checked base and every prefix for input 4415. -/
theorem certificate_4415 : classCertificateB 27 4415 = true := by
  decide

/-- The same exact first-descent time holds on an infinite dyadic ray. -/
theorem ray_4415 (m : Nat) : stoppingTime (2 ^ 27 * m + 4415) 27 :=
  stoppingTime_of_classCertificate certificate_4415 m

/-- Checked base and every prefix for input 4417. -/
theorem certificate_4417 : classCertificateB 2 4417 = true := by
  decide

/-- The same exact first-descent time holds on an infinite dyadic ray. -/
theorem ray_4417 (m : Nat) : stoppingTime (2 ^ 2 * m + 4417) 2 :=
  stoppingTime_of_classCertificate certificate_4417 m

/-- Checked base and every prefix for input 4419. -/
theorem certificate_4419 : classCertificateB 4 4419 = true := by
  decide

/-- The same exact first-descent time holds on an infinite dyadic ray. -/
theorem ray_4419 (m : Nat) : stoppingTime (2 ^ 4 * m + 4419) 4 :=
  stoppingTime_of_classCertificate certificate_4419 m

/-- Checked base and every prefix for input 4421. -/
theorem certificate_4421 : classCertificateB 2 4421 = true := by
  decide

/-- The same exact first-descent time holds on an infinite dyadic ray. -/
theorem ray_4421 (m : Nat) : stoppingTime (2 ^ 2 * m + 4421) 2 :=
  stoppingTime_of_classCertificate certificate_4421 m

/-- Exhaustive coverage of the odd inputs in this batch, with no gaps. -/
theorem coverage : CertifiedRange 4355 4423 := by
  intro n hlo hhi hodd
  have hn : n = 4355 ∨ n = 4357 ∨ n = 4359 ∨ n = 4361 ∨ n = 4363 ∨ n = 4365 ∨ n = 4367 ∨ n = 4369 ∨ n = 4371 ∨ n = 4373 ∨ n = 4375 ∨ n = 4377 ∨ n = 4379 ∨ n = 4381 ∨ n = 4383 ∨ n = 4385 ∨ n = 4387 ∨ n = 4389 ∨ n = 4391 ∨ n = 4393 ∨ n = 4395 ∨ n = 4397 ∨ n = 4399 ∨ n = 4401 ∨ n = 4403 ∨ n = 4405 ∨ n = 4407 ∨ n = 4409 ∨ n = 4411 ∨ n = 4413 ∨ n = 4415 ∨ n = 4417 ∨ n = 4419 ∨ n = 4421 := by omega
  rcases hn with h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h
  · subst n
    exact ⟨4, witness_of_certificate certificate_4355⟩
  · subst n
    exact ⟨2, witness_of_certificate certificate_4357⟩
  · subst n
    exact ⟨7, witness_of_certificate certificate_4359⟩
  · subst n
    exact ⟨2, witness_of_certificate certificate_4361⟩
  · subst n
    exact ⟨5, witness_of_certificate certificate_4363⟩
  · subst n
    exact ⟨2, witness_of_certificate certificate_4365⟩
  · subst n
    exact ⟨7, witness_of_certificate certificate_4367⟩
  · subst n
    exact ⟨2, witness_of_certificate certificate_4369⟩
  · subst n
    exact ⟨4, witness_of_certificate certificate_4371⟩
  · subst n
    exact ⟨2, witness_of_certificate certificate_4373⟩
  · subst n
    exact ⟨5, witness_of_certificate certificate_4375⟩
  · subst n
    exact ⟨2, witness_of_certificate certificate_4377⟩
  · subst n
    exact ⟨16, witness_of_certificate certificate_4379⟩
  · subst n
    exact ⟨2, witness_of_certificate certificate_4381⟩
  · subst n
    exact ⟨10, witness_of_certificate certificate_4383⟩
  · subst n
    exact ⟨2, witness_of_certificate certificate_4385⟩
  · subst n
    exact ⟨4, witness_of_certificate certificate_4387⟩
  · subst n
    exact ⟨2, witness_of_certificate certificate_4389⟩
  · subst n
    exact ⟨8, witness_of_certificate certificate_4391⟩
  · subst n
    exact ⟨2, witness_of_certificate certificate_4393⟩
  · subst n
    exact ⟨5, witness_of_certificate certificate_4395⟩
  · subst n
    exact ⟨2, witness_of_certificate certificate_4397⟩
  · subst n
    exact ⟨32, witness_of_certificate certificate_4399⟩
  · subst n
    exact ⟨2, witness_of_certificate certificate_4401⟩
  · subst n
    exact ⟨4, witness_of_certificate certificate_4403⟩
  · subst n
    exact ⟨2, witness_of_certificate certificate_4405⟩
  · subst n
    exact ⟨5, witness_of_certificate certificate_4407⟩
  · subst n
    exact ⟨2, witness_of_certificate certificate_4409⟩
  · subst n
    exact ⟨7, witness_of_certificate certificate_4411⟩
  · subst n
    exact ⟨2, witness_of_certificate certificate_4413⟩
  · subst n
    exact ⟨27, witness_of_certificate certificate_4415⟩
  · subst n
    exact ⟨2, witness_of_certificate certificate_4417⟩
  · subst n
    exact ⟨4, witness_of_certificate certificate_4419⟩
  · subst n
    exact ⟨2, witness_of_certificate certificate_4421⟩

end Collatz.Research.CoefficientDescent.Batch066
