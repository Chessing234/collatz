import Collatz.Research.CoefficientDescent.Basic

namespace Collatz.Research.CoefficientDescent.Batch096

open FirstDescentClass

set_option maxRecDepth 20000
set_option maxHeartbeats 0

/-- Checked base and every prefix for input 6365. -/
theorem certificate_6365 : classCertificateB 2 6365 = true := by
  decide

/-- The same exact first-descent time holds on an infinite dyadic ray. -/
theorem ray_6365 (m : Nat) : stoppingTime (2 ^ 2 * m + 6365) 2 :=
  stoppingTime_of_classCertificate certificate_6365 m

/-- Checked base and every prefix for input 6367. -/
theorem certificate_6367 : classCertificateB 18 6367 = true := by
  decide

/-- The same exact first-descent time holds on an infinite dyadic ray. -/
theorem ray_6367 (m : Nat) : stoppingTime (2 ^ 18 * m + 6367) 18 :=
  stoppingTime_of_classCertificate certificate_6367 m

/-- Checked base and every prefix for input 6369. -/
theorem certificate_6369 : classCertificateB 2 6369 = true := by
  decide

/-- The same exact first-descent time holds on an infinite dyadic ray. -/
theorem ray_6369 (m : Nat) : stoppingTime (2 ^ 2 * m + 6369) 2 :=
  stoppingTime_of_classCertificate certificate_6369 m

/-- Checked base and every prefix for input 6371. -/
theorem certificate_6371 : classCertificateB 4 6371 = true := by
  decide

/-- The same exact first-descent time holds on an infinite dyadic ray. -/
theorem ray_6371 (m : Nat) : stoppingTime (2 ^ 4 * m + 6371) 4 :=
  stoppingTime_of_classCertificate certificate_6371 m

/-- Checked base and every prefix for input 6373. -/
theorem certificate_6373 : classCertificateB 2 6373 = true := by
  decide

/-- The same exact first-descent time holds on an infinite dyadic ray. -/
theorem ray_6373 (m : Nat) : stoppingTime (2 ^ 2 * m + 6373) 2 :=
  stoppingTime_of_classCertificate certificate_6373 m

/-- Checked base and every prefix for input 6375. -/
theorem certificate_6375 : classCertificateB 13 6375 = true := by
  decide

/-- The same exact first-descent time holds on an infinite dyadic ray. -/
theorem ray_6375 (m : Nat) : stoppingTime (2 ^ 13 * m + 6375) 13 :=
  stoppingTime_of_classCertificate certificate_6375 m

/-- Checked base and every prefix for input 6377. -/
theorem certificate_6377 : classCertificateB 2 6377 = true := by
  decide

/-- The same exact first-descent time holds on an infinite dyadic ray. -/
theorem ray_6377 (m : Nat) : stoppingTime (2 ^ 2 * m + 6377) 2 :=
  stoppingTime_of_classCertificate certificate_6377 m

/-- Checked base and every prefix for input 6379. -/
theorem certificate_6379 : classCertificateB 5 6379 = true := by
  decide

/-- The same exact first-descent time holds on an infinite dyadic ray. -/
theorem ray_6379 (m : Nat) : stoppingTime (2 ^ 5 * m + 6379) 5 :=
  stoppingTime_of_classCertificate certificate_6379 m

/-- Checked base and every prefix for input 6381. -/
theorem certificate_6381 : classCertificateB 2 6381 = true := by
  decide

/-- The same exact first-descent time holds on an infinite dyadic ray. -/
theorem ray_6381 (m : Nat) : stoppingTime (2 ^ 2 * m + 6381) 2 :=
  stoppingTime_of_classCertificate certificate_6381 m

/-- Checked base and every prefix for input 6383. -/
theorem certificate_6383 : classCertificateB 69 6383 = true := by
  decide

/-- The same exact first-descent time holds on an infinite dyadic ray. -/
theorem ray_6383 (m : Nat) : stoppingTime (2 ^ 69 * m + 6383) 69 :=
  stoppingTime_of_classCertificate certificate_6383 m

/-- Checked base and every prefix for input 6385. -/
theorem certificate_6385 : classCertificateB 2 6385 = true := by
  decide

/-- The same exact first-descent time holds on an infinite dyadic ray. -/
theorem ray_6385 (m : Nat) : stoppingTime (2 ^ 2 * m + 6385) 2 :=
  stoppingTime_of_classCertificate certificate_6385 m

/-- Checked base and every prefix for input 6387. -/
theorem certificate_6387 : classCertificateB 4 6387 = true := by
  decide

/-- The same exact first-descent time holds on an infinite dyadic ray. -/
theorem ray_6387 (m : Nat) : stoppingTime (2 ^ 4 * m + 6387) 4 :=
  stoppingTime_of_classCertificate certificate_6387 m

/-- Checked base and every prefix for input 6389. -/
theorem certificate_6389 : classCertificateB 2 6389 = true := by
  decide

/-- The same exact first-descent time holds on an infinite dyadic ray. -/
theorem ray_6389 (m : Nat) : stoppingTime (2 ^ 2 * m + 6389) 2 :=
  stoppingTime_of_classCertificate certificate_6389 m

/-- Checked base and every prefix for input 6391. -/
theorem certificate_6391 : classCertificateB 5 6391 = true := by
  decide

/-- The same exact first-descent time holds on an infinite dyadic ray. -/
theorem ray_6391 (m : Nat) : stoppingTime (2 ^ 5 * m + 6391) 5 :=
  stoppingTime_of_classCertificate certificate_6391 m

/-- Checked base and every prefix for input 6393. -/
theorem certificate_6393 : classCertificateB 2 6393 = true := by
  decide

/-- The same exact first-descent time holds on an infinite dyadic ray. -/
theorem ray_6393 (m : Nat) : stoppingTime (2 ^ 2 * m + 6393) 2 :=
  stoppingTime_of_classCertificate certificate_6393 m

/-- Checked base and every prefix for input 6395. -/
theorem certificate_6395 : classCertificateB 53 6395 = true := by
  decide

/-- The same exact first-descent time holds on an infinite dyadic ray. -/
theorem ray_6395 (m : Nat) : stoppingTime (2 ^ 53 * m + 6395) 53 :=
  stoppingTime_of_classCertificate certificate_6395 m

/-- Checked base and every prefix for input 6397. -/
theorem certificate_6397 : classCertificateB 2 6397 = true := by
  decide

/-- The same exact first-descent time holds on an infinite dyadic ray. -/
theorem ray_6397 (m : Nat) : stoppingTime (2 ^ 2 * m + 6397) 2 :=
  stoppingTime_of_classCertificate certificate_6397 m

/-- Checked base and every prefix for input 6399. -/
theorem certificate_6399 : classCertificateB 18 6399 = true := by
  decide

/-- The same exact first-descent time holds on an infinite dyadic ray. -/
theorem ray_6399 (m : Nat) : stoppingTime (2 ^ 18 * m + 6399) 18 :=
  stoppingTime_of_classCertificate certificate_6399 m

/-- Checked base and every prefix for input 6401. -/
theorem certificate_6401 : classCertificateB 2 6401 = true := by
  decide

/-- The same exact first-descent time holds on an infinite dyadic ray. -/
theorem ray_6401 (m : Nat) : stoppingTime (2 ^ 2 * m + 6401) 2 :=
  stoppingTime_of_classCertificate certificate_6401 m

/-- Checked base and every prefix for input 6403. -/
theorem certificate_6403 : classCertificateB 4 6403 = true := by
  decide

/-- The same exact first-descent time holds on an infinite dyadic ray. -/
theorem ray_6403 (m : Nat) : stoppingTime (2 ^ 4 * m + 6403) 4 :=
  stoppingTime_of_classCertificate certificate_6403 m

/-- Checked base and every prefix for input 6405. -/
theorem certificate_6405 : classCertificateB 2 6405 = true := by
  decide

/-- The same exact first-descent time holds on an infinite dyadic ray. -/
theorem ray_6405 (m : Nat) : stoppingTime (2 ^ 2 * m + 6405) 2 :=
  stoppingTime_of_classCertificate certificate_6405 m

/-- Checked base and every prefix for input 6407. -/
theorem certificate_6407 : classCertificateB 7 6407 = true := by
  decide

/-- The same exact first-descent time holds on an infinite dyadic ray. -/
theorem ray_6407 (m : Nat) : stoppingTime (2 ^ 7 * m + 6407) 7 :=
  stoppingTime_of_classCertificate certificate_6407 m

/-- Checked base and every prefix for input 6409. -/
theorem certificate_6409 : classCertificateB 2 6409 = true := by
  decide

/-- The same exact first-descent time holds on an infinite dyadic ray. -/
theorem ray_6409 (m : Nat) : stoppingTime (2 ^ 2 * m + 6409) 2 :=
  stoppingTime_of_classCertificate certificate_6409 m

/-- Checked base and every prefix for input 6411. -/
theorem certificate_6411 : classCertificateB 5 6411 = true := by
  decide

/-- The same exact first-descent time holds on an infinite dyadic ray. -/
theorem ray_6411 (m : Nat) : stoppingTime (2 ^ 5 * m + 6411) 5 :=
  stoppingTime_of_classCertificate certificate_6411 m

/-- Checked base and every prefix for input 6413. -/
theorem certificate_6413 : classCertificateB 2 6413 = true := by
  decide

/-- The same exact first-descent time holds on an infinite dyadic ray. -/
theorem ray_6413 (m : Nat) : stoppingTime (2 ^ 2 * m + 6413) 2 :=
  stoppingTime_of_classCertificate certificate_6413 m

/-- Checked base and every prefix for input 6415. -/
theorem certificate_6415 : classCertificateB 7 6415 = true := by
  decide

/-- The same exact first-descent time holds on an infinite dyadic ray. -/
theorem ray_6415 (m : Nat) : stoppingTime (2 ^ 7 * m + 6415) 7 :=
  stoppingTime_of_classCertificate certificate_6415 m

/-- Checked base and every prefix for input 6417. -/
theorem certificate_6417 : classCertificateB 2 6417 = true := by
  decide

/-- The same exact first-descent time holds on an infinite dyadic ray. -/
theorem ray_6417 (m : Nat) : stoppingTime (2 ^ 2 * m + 6417) 2 :=
  stoppingTime_of_classCertificate certificate_6417 m

/-- Checked base and every prefix for input 6419. -/
theorem certificate_6419 : classCertificateB 4 6419 = true := by
  decide

/-- The same exact first-descent time holds on an infinite dyadic ray. -/
theorem ray_6419 (m : Nat) : stoppingTime (2 ^ 4 * m + 6419) 4 :=
  stoppingTime_of_classCertificate certificate_6419 m

/-- Checked base and every prefix for input 6421. -/
theorem certificate_6421 : classCertificateB 2 6421 = true := by
  decide

/-- The same exact first-descent time holds on an infinite dyadic ray. -/
theorem ray_6421 (m : Nat) : stoppingTime (2 ^ 2 * m + 6421) 2 :=
  stoppingTime_of_classCertificate certificate_6421 m

/-- Checked base and every prefix for input 6423. -/
theorem certificate_6423 : classCertificateB 5 6423 = true := by
  decide

/-- The same exact first-descent time holds on an infinite dyadic ray. -/
theorem ray_6423 (m : Nat) : stoppingTime (2 ^ 5 * m + 6423) 5 :=
  stoppingTime_of_classCertificate certificate_6423 m

/-- Checked base and every prefix for input 6425. -/
theorem certificate_6425 : classCertificateB 2 6425 = true := by
  decide

/-- The same exact first-descent time holds on an infinite dyadic ray. -/
theorem ray_6425 (m : Nat) : stoppingTime (2 ^ 2 * m + 6425) 2 :=
  stoppingTime_of_classCertificate certificate_6425 m

/-- Checked base and every prefix for input 6427. -/
theorem certificate_6427 : classCertificateB 21 6427 = true := by
  decide

/-- The same exact first-descent time holds on an infinite dyadic ray. -/
theorem ray_6427 (m : Nat) : stoppingTime (2 ^ 21 * m + 6427) 21 :=
  stoppingTime_of_classCertificate certificate_6427 m

/-- Checked base and every prefix for input 6429. -/
theorem certificate_6429 : classCertificateB 2 6429 = true := by
  decide

/-- The same exact first-descent time holds on an infinite dyadic ray. -/
theorem ray_6429 (m : Nat) : stoppingTime (2 ^ 2 * m + 6429) 2 :=
  stoppingTime_of_classCertificate certificate_6429 m

/-- Checked base and every prefix for input 6431. -/
theorem certificate_6431 : classCertificateB 10 6431 = true := by
  decide

/-- The same exact first-descent time holds on an infinite dyadic ray. -/
theorem ray_6431 (m : Nat) : stoppingTime (2 ^ 10 * m + 6431) 10 :=
  stoppingTime_of_classCertificate certificate_6431 m

/-- Exhaustive coverage of the odd inputs in this batch, with no gaps. -/
theorem coverage : CertifiedRange 6365 6433 := by
  intro n hlo hhi hodd
  have hn : n = 6365 ∨ n = 6367 ∨ n = 6369 ∨ n = 6371 ∨ n = 6373 ∨ n = 6375 ∨ n = 6377 ∨ n = 6379 ∨ n = 6381 ∨ n = 6383 ∨ n = 6385 ∨ n = 6387 ∨ n = 6389 ∨ n = 6391 ∨ n = 6393 ∨ n = 6395 ∨ n = 6397 ∨ n = 6399 ∨ n = 6401 ∨ n = 6403 ∨ n = 6405 ∨ n = 6407 ∨ n = 6409 ∨ n = 6411 ∨ n = 6413 ∨ n = 6415 ∨ n = 6417 ∨ n = 6419 ∨ n = 6421 ∨ n = 6423 ∨ n = 6425 ∨ n = 6427 ∨ n = 6429 ∨ n = 6431 := by omega
  rcases hn with h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h
  · subst n
    exact ⟨2, witness_of_certificate certificate_6365⟩
  · subst n
    exact ⟨18, witness_of_certificate certificate_6367⟩
  · subst n
    exact ⟨2, witness_of_certificate certificate_6369⟩
  · subst n
    exact ⟨4, witness_of_certificate certificate_6371⟩
  · subst n
    exact ⟨2, witness_of_certificate certificate_6373⟩
  · subst n
    exact ⟨13, witness_of_certificate certificate_6375⟩
  · subst n
    exact ⟨2, witness_of_certificate certificate_6377⟩
  · subst n
    exact ⟨5, witness_of_certificate certificate_6379⟩
  · subst n
    exact ⟨2, witness_of_certificate certificate_6381⟩
  · subst n
    exact ⟨69, witness_of_certificate certificate_6383⟩
  · subst n
    exact ⟨2, witness_of_certificate certificate_6385⟩
  · subst n
    exact ⟨4, witness_of_certificate certificate_6387⟩
  · subst n
    exact ⟨2, witness_of_certificate certificate_6389⟩
  · subst n
    exact ⟨5, witness_of_certificate certificate_6391⟩
  · subst n
    exact ⟨2, witness_of_certificate certificate_6393⟩
  · subst n
    exact ⟨53, witness_of_certificate certificate_6395⟩
  · subst n
    exact ⟨2, witness_of_certificate certificate_6397⟩
  · subst n
    exact ⟨18, witness_of_certificate certificate_6399⟩
  · subst n
    exact ⟨2, witness_of_certificate certificate_6401⟩
  · subst n
    exact ⟨4, witness_of_certificate certificate_6403⟩
  · subst n
    exact ⟨2, witness_of_certificate certificate_6405⟩
  · subst n
    exact ⟨7, witness_of_certificate certificate_6407⟩
  · subst n
    exact ⟨2, witness_of_certificate certificate_6409⟩
  · subst n
    exact ⟨5, witness_of_certificate certificate_6411⟩
  · subst n
    exact ⟨2, witness_of_certificate certificate_6413⟩
  · subst n
    exact ⟨7, witness_of_certificate certificate_6415⟩
  · subst n
    exact ⟨2, witness_of_certificate certificate_6417⟩
  · subst n
    exact ⟨4, witness_of_certificate certificate_6419⟩
  · subst n
    exact ⟨2, witness_of_certificate certificate_6421⟩
  · subst n
    exact ⟨5, witness_of_certificate certificate_6423⟩
  · subst n
    exact ⟨2, witness_of_certificate certificate_6425⟩
  · subst n
    exact ⟨21, witness_of_certificate certificate_6427⟩
  · subst n
    exact ⟨2, witness_of_certificate certificate_6429⟩
  · subst n
    exact ⟨10, witness_of_certificate certificate_6431⟩

end Collatz.Research.CoefficientDescent.Batch096
