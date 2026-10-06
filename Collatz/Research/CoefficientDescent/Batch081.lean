import Collatz.Research.CoefficientDescent.Basic

namespace Collatz.Research.CoefficientDescent.Batch081

open FirstDescentClass

set_option maxRecDepth 20000
set_option maxHeartbeats 0

/-- Checked base and every prefix for input 5361. -/
theorem certificate_5361 : classCertificateB 2 5361 = true := by
  decide

/-- The same exact first-descent time holds on an infinite dyadic ray. -/
theorem ray_5361 (m : Nat) : stoppingTime (2 ^ 2 * m + 5361) 2 :=
  stoppingTime_of_classCertificate certificate_5361 m

/-- Checked base and every prefix for input 5363. -/
theorem certificate_5363 : classCertificateB 4 5363 = true := by
  decide

/-- The same exact first-descent time holds on an infinite dyadic ray. -/
theorem ray_5363 (m : Nat) : stoppingTime (2 ^ 4 * m + 5363) 4 :=
  stoppingTime_of_classCertificate certificate_5363 m

/-- Checked base and every prefix for input 5365. -/
theorem certificate_5365 : classCertificateB 2 5365 = true := by
  decide

/-- The same exact first-descent time holds on an infinite dyadic ray. -/
theorem ray_5365 (m : Nat) : stoppingTime (2 ^ 2 * m + 5365) 2 :=
  stoppingTime_of_classCertificate certificate_5365 m

/-- Checked base and every prefix for input 5367. -/
theorem certificate_5367 : classCertificateB 5 5367 = true := by
  decide

/-- The same exact first-descent time holds on an infinite dyadic ray. -/
theorem ray_5367 (m : Nat) : stoppingTime (2 ^ 5 * m + 5367) 5 :=
  stoppingTime_of_classCertificate certificate_5367 m

/-- Checked base and every prefix for input 5369. -/
theorem certificate_5369 : classCertificateB 2 5369 = true := by
  decide

/-- The same exact first-descent time holds on an infinite dyadic ray. -/
theorem ray_5369 (m : Nat) : stoppingTime (2 ^ 2 * m + 5369) 2 :=
  stoppingTime_of_classCertificate certificate_5369 m

/-- Checked base and every prefix for input 5371. -/
theorem certificate_5371 : classCertificateB 13 5371 = true := by
  decide

/-- The same exact first-descent time holds on an infinite dyadic ray. -/
theorem ray_5371 (m : Nat) : stoppingTime (2 ^ 13 * m + 5371) 13 :=
  stoppingTime_of_classCertificate certificate_5371 m

/-- Checked base and every prefix for input 5373. -/
theorem certificate_5373 : classCertificateB 2 5373 = true := by
  decide

/-- The same exact first-descent time holds on an infinite dyadic ray. -/
theorem ray_5373 (m : Nat) : stoppingTime (2 ^ 2 * m + 5373) 2 :=
  stoppingTime_of_classCertificate certificate_5373 m

/-- Checked base and every prefix for input 5375. -/
theorem certificate_5375 : classCertificateB 16 5375 = true := by
  decide

/-- The same exact first-descent time holds on an infinite dyadic ray. -/
theorem ray_5375 (m : Nat) : stoppingTime (2 ^ 16 * m + 5375) 16 :=
  stoppingTime_of_classCertificate certificate_5375 m

/-- Checked base and every prefix for input 5377. -/
theorem certificate_5377 : classCertificateB 2 5377 = true := by
  decide

/-- The same exact first-descent time holds on an infinite dyadic ray. -/
theorem ray_5377 (m : Nat) : stoppingTime (2 ^ 2 * m + 5377) 2 :=
  stoppingTime_of_classCertificate certificate_5377 m

/-- Checked base and every prefix for input 5379. -/
theorem certificate_5379 : classCertificateB 4 5379 = true := by
  decide

/-- The same exact first-descent time holds on an infinite dyadic ray. -/
theorem ray_5379 (m : Nat) : stoppingTime (2 ^ 4 * m + 5379) 4 :=
  stoppingTime_of_classCertificate certificate_5379 m

/-- Checked base and every prefix for input 5381. -/
theorem certificate_5381 : classCertificateB 2 5381 = true := by
  decide

/-- The same exact first-descent time holds on an infinite dyadic ray. -/
theorem ray_5381 (m : Nat) : stoppingTime (2 ^ 2 * m + 5381) 2 :=
  stoppingTime_of_classCertificate certificate_5381 m

/-- Checked base and every prefix for input 5383. -/
theorem certificate_5383 : classCertificateB 7 5383 = true := by
  decide

/-- The same exact first-descent time holds on an infinite dyadic ray. -/
theorem ray_5383 (m : Nat) : stoppingTime (2 ^ 7 * m + 5383) 7 :=
  stoppingTime_of_classCertificate certificate_5383 m

/-- Checked base and every prefix for input 5385. -/
theorem certificate_5385 : classCertificateB 2 5385 = true := by
  decide

/-- The same exact first-descent time holds on an infinite dyadic ray. -/
theorem ray_5385 (m : Nat) : stoppingTime (2 ^ 2 * m + 5385) 2 :=
  stoppingTime_of_classCertificate certificate_5385 m

/-- Checked base and every prefix for input 5387. -/
theorem certificate_5387 : classCertificateB 5 5387 = true := by
  decide

/-- The same exact first-descent time holds on an infinite dyadic ray. -/
theorem ray_5387 (m : Nat) : stoppingTime (2 ^ 5 * m + 5387) 5 :=
  stoppingTime_of_classCertificate certificate_5387 m

/-- Checked base and every prefix for input 5389. -/
theorem certificate_5389 : classCertificateB 2 5389 = true := by
  decide

/-- The same exact first-descent time holds on an infinite dyadic ray. -/
theorem ray_5389 (m : Nat) : stoppingTime (2 ^ 2 * m + 5389) 2 :=
  stoppingTime_of_classCertificate certificate_5389 m

/-- Checked base and every prefix for input 5391. -/
theorem certificate_5391 : classCertificateB 7 5391 = true := by
  decide

/-- The same exact first-descent time holds on an infinite dyadic ray. -/
theorem ray_5391 (m : Nat) : stoppingTime (2 ^ 7 * m + 5391) 7 :=
  stoppingTime_of_classCertificate certificate_5391 m

/-- Checked base and every prefix for input 5393. -/
theorem certificate_5393 : classCertificateB 2 5393 = true := by
  decide

/-- The same exact first-descent time holds on an infinite dyadic ray. -/
theorem ray_5393 (m : Nat) : stoppingTime (2 ^ 2 * m + 5393) 2 :=
  stoppingTime_of_classCertificate certificate_5393 m

/-- Checked base and every prefix for input 5395. -/
theorem certificate_5395 : classCertificateB 4 5395 = true := by
  decide

/-- The same exact first-descent time holds on an infinite dyadic ray. -/
theorem ray_5395 (m : Nat) : stoppingTime (2 ^ 4 * m + 5395) 4 :=
  stoppingTime_of_classCertificate certificate_5395 m

/-- Checked base and every prefix for input 5397. -/
theorem certificate_5397 : classCertificateB 2 5397 = true := by
  decide

/-- The same exact first-descent time holds on an infinite dyadic ray. -/
theorem ray_5397 (m : Nat) : stoppingTime (2 ^ 2 * m + 5397) 2 :=
  stoppingTime_of_classCertificate certificate_5397 m

/-- Checked base and every prefix for input 5399. -/
theorem certificate_5399 : classCertificateB 5 5399 = true := by
  decide

/-- The same exact first-descent time holds on an infinite dyadic ray. -/
theorem ray_5399 (m : Nat) : stoppingTime (2 ^ 5 * m + 5399) 5 :=
  stoppingTime_of_classCertificate certificate_5399 m

/-- Checked base and every prefix for input 5401. -/
theorem certificate_5401 : classCertificateB 2 5401 = true := by
  decide

/-- The same exact first-descent time holds on an infinite dyadic ray. -/
theorem ray_5401 (m : Nat) : stoppingTime (2 ^ 2 * m + 5401) 2 :=
  stoppingTime_of_classCertificate certificate_5401 m

/-- Checked base and every prefix for input 5403. -/
theorem certificate_5403 : classCertificateB 21 5403 = true := by
  decide

/-- The same exact first-descent time holds on an infinite dyadic ray. -/
theorem ray_5403 (m : Nat) : stoppingTime (2 ^ 21 * m + 5403) 21 :=
  stoppingTime_of_classCertificate certificate_5403 m

/-- Checked base and every prefix for input 5405. -/
theorem certificate_5405 : classCertificateB 2 5405 = true := by
  decide

/-- The same exact first-descent time holds on an infinite dyadic ray. -/
theorem ray_5405 (m : Nat) : stoppingTime (2 ^ 2 * m + 5405) 2 :=
  stoppingTime_of_classCertificate certificate_5405 m

/-- Checked base and every prefix for input 5407. -/
theorem certificate_5407 : classCertificateB 10 5407 = true := by
  decide

/-- The same exact first-descent time holds on an infinite dyadic ray. -/
theorem ray_5407 (m : Nat) : stoppingTime (2 ^ 10 * m + 5407) 10 :=
  stoppingTime_of_classCertificate certificate_5407 m

/-- Checked base and every prefix for input 5409. -/
theorem certificate_5409 : classCertificateB 2 5409 = true := by
  decide

/-- The same exact first-descent time holds on an infinite dyadic ray. -/
theorem ray_5409 (m : Nat) : stoppingTime (2 ^ 2 * m + 5409) 2 :=
  stoppingTime_of_classCertificate certificate_5409 m

/-- Checked base and every prefix for input 5411. -/
theorem certificate_5411 : classCertificateB 4 5411 = true := by
  decide

/-- The same exact first-descent time holds on an infinite dyadic ray. -/
theorem ray_5411 (m : Nat) : stoppingTime (2 ^ 4 * m + 5411) 4 :=
  stoppingTime_of_classCertificate certificate_5411 m

/-- Checked base and every prefix for input 5413. -/
theorem certificate_5413 : classCertificateB 2 5413 = true := by
  decide

/-- The same exact first-descent time holds on an infinite dyadic ray. -/
theorem ray_5413 (m : Nat) : stoppingTime (2 ^ 2 * m + 5413) 2 :=
  stoppingTime_of_classCertificate certificate_5413 m

/-- Checked base and every prefix for input 5415. -/
theorem certificate_5415 : classCertificateB 8 5415 = true := by
  decide

/-- The same exact first-descent time holds on an infinite dyadic ray. -/
theorem ray_5415 (m : Nat) : stoppingTime (2 ^ 8 * m + 5415) 8 :=
  stoppingTime_of_classCertificate certificate_5415 m

/-- Checked base and every prefix for input 5417. -/
theorem certificate_5417 : classCertificateB 2 5417 = true := by
  decide

/-- The same exact first-descent time holds on an infinite dyadic ray. -/
theorem ray_5417 (m : Nat) : stoppingTime (2 ^ 2 * m + 5417) 2 :=
  stoppingTime_of_classCertificate certificate_5417 m

/-- Checked base and every prefix for input 5419. -/
theorem certificate_5419 : classCertificateB 5 5419 = true := by
  decide

/-- The same exact first-descent time holds on an infinite dyadic ray. -/
theorem ray_5419 (m : Nat) : stoppingTime (2 ^ 5 * m + 5419) 5 :=
  stoppingTime_of_classCertificate certificate_5419 m

/-- Checked base and every prefix for input 5421. -/
theorem certificate_5421 : classCertificateB 2 5421 = true := by
  decide

/-- The same exact first-descent time holds on an infinite dyadic ray. -/
theorem ray_5421 (m : Nat) : stoppingTime (2 ^ 2 * m + 5421) 2 :=
  stoppingTime_of_classCertificate certificate_5421 m

/-- Checked base and every prefix for input 5423. -/
theorem certificate_5423 : classCertificateB 16 5423 = true := by
  decide

/-- The same exact first-descent time holds on an infinite dyadic ray. -/
theorem ray_5423 (m : Nat) : stoppingTime (2 ^ 16 * m + 5423) 16 :=
  stoppingTime_of_classCertificate certificate_5423 m

/-- Checked base and every prefix for input 5425. -/
theorem certificate_5425 : classCertificateB 2 5425 = true := by
  decide

/-- The same exact first-descent time holds on an infinite dyadic ray. -/
theorem ray_5425 (m : Nat) : stoppingTime (2 ^ 2 * m + 5425) 2 :=
  stoppingTime_of_classCertificate certificate_5425 m

/-- Exhaustive coverage of the odd inputs in this batch, with no gaps. -/
theorem coverage : CertifiedRange 5361 5427 := by
  intro n hlo hhi hodd
  have hn : n = 5361 ∨ n = 5363 ∨ n = 5365 ∨ n = 5367 ∨ n = 5369 ∨ n = 5371 ∨ n = 5373 ∨ n = 5375 ∨ n = 5377 ∨ n = 5379 ∨ n = 5381 ∨ n = 5383 ∨ n = 5385 ∨ n = 5387 ∨ n = 5389 ∨ n = 5391 ∨ n = 5393 ∨ n = 5395 ∨ n = 5397 ∨ n = 5399 ∨ n = 5401 ∨ n = 5403 ∨ n = 5405 ∨ n = 5407 ∨ n = 5409 ∨ n = 5411 ∨ n = 5413 ∨ n = 5415 ∨ n = 5417 ∨ n = 5419 ∨ n = 5421 ∨ n = 5423 ∨ n = 5425 := by omega
  rcases hn with h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h
  · subst n
    exact ⟨2, witness_of_certificate certificate_5361⟩
  · subst n
    exact ⟨4, witness_of_certificate certificate_5363⟩
  · subst n
    exact ⟨2, witness_of_certificate certificate_5365⟩
  · subst n
    exact ⟨5, witness_of_certificate certificate_5367⟩
  · subst n
    exact ⟨2, witness_of_certificate certificate_5369⟩
  · subst n
    exact ⟨13, witness_of_certificate certificate_5371⟩
  · subst n
    exact ⟨2, witness_of_certificate certificate_5373⟩
  · subst n
    exact ⟨16, witness_of_certificate certificate_5375⟩
  · subst n
    exact ⟨2, witness_of_certificate certificate_5377⟩
  · subst n
    exact ⟨4, witness_of_certificate certificate_5379⟩
  · subst n
    exact ⟨2, witness_of_certificate certificate_5381⟩
  · subst n
    exact ⟨7, witness_of_certificate certificate_5383⟩
  · subst n
    exact ⟨2, witness_of_certificate certificate_5385⟩
  · subst n
    exact ⟨5, witness_of_certificate certificate_5387⟩
  · subst n
    exact ⟨2, witness_of_certificate certificate_5389⟩
  · subst n
    exact ⟨7, witness_of_certificate certificate_5391⟩
  · subst n
    exact ⟨2, witness_of_certificate certificate_5393⟩
  · subst n
    exact ⟨4, witness_of_certificate certificate_5395⟩
  · subst n
    exact ⟨2, witness_of_certificate certificate_5397⟩
  · subst n
    exact ⟨5, witness_of_certificate certificate_5399⟩
  · subst n
    exact ⟨2, witness_of_certificate certificate_5401⟩
  · subst n
    exact ⟨21, witness_of_certificate certificate_5403⟩
  · subst n
    exact ⟨2, witness_of_certificate certificate_5405⟩
  · subst n
    exact ⟨10, witness_of_certificate certificate_5407⟩
  · subst n
    exact ⟨2, witness_of_certificate certificate_5409⟩
  · subst n
    exact ⟨4, witness_of_certificate certificate_5411⟩
  · subst n
    exact ⟨2, witness_of_certificate certificate_5413⟩
  · subst n
    exact ⟨8, witness_of_certificate certificate_5415⟩
  · subst n
    exact ⟨2, witness_of_certificate certificate_5417⟩
  · subst n
    exact ⟨5, witness_of_certificate certificate_5419⟩
  · subst n
    exact ⟨2, witness_of_certificate certificate_5421⟩
  · subst n
    exact ⟨16, witness_of_certificate certificate_5423⟩
  · subst n
    exact ⟨2, witness_of_certificate certificate_5425⟩

end Collatz.Research.CoefficientDescent.Batch081
