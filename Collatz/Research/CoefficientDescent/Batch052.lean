import Collatz.Research.CoefficientDescent.Basic

namespace Collatz.Research.CoefficientDescent.Batch052

open FirstDescentClass

set_option maxRecDepth 20000
set_option maxHeartbeats 0

/-- Checked base and every prefix for input 3417. -/
theorem certificate_3417 : classCertificateB 2 3417 = true := by
  decide

/-- The same exact first-descent time holds on an infinite dyadic ray. -/
theorem ray_3417 (m : Nat) : stoppingTime (2 ^ 2 * m + 3417) 2 :=
  stoppingTime_of_classCertificate certificate_3417 m

/-- Checked base and every prefix for input 3419. -/
theorem certificate_3419 : classCertificateB 10 3419 = true := by
  decide

/-- The same exact first-descent time holds on an infinite dyadic ray. -/
theorem ray_3419 (m : Nat) : stoppingTime (2 ^ 10 * m + 3419) 10 :=
  stoppingTime_of_classCertificate certificate_3419 m

/-- Checked base and every prefix for input 3421. -/
theorem certificate_3421 : classCertificateB 2 3421 = true := by
  decide

/-- The same exact first-descent time holds on an infinite dyadic ray. -/
theorem ray_3421 (m : Nat) : stoppingTime (2 ^ 2 * m + 3421) 2 :=
  stoppingTime_of_classCertificate certificate_3421 m

/-- Checked base and every prefix for input 3423. -/
theorem certificate_3423 : classCertificateB 8 3423 = true := by
  decide

/-- The same exact first-descent time holds on an infinite dyadic ray. -/
theorem ray_3423 (m : Nat) : stoppingTime (2 ^ 8 * m + 3423) 8 :=
  stoppingTime_of_classCertificate certificate_3423 m

/-- Checked base and every prefix for input 3425. -/
theorem certificate_3425 : classCertificateB 2 3425 = true := by
  decide

/-- The same exact first-descent time holds on an infinite dyadic ray. -/
theorem ray_3425 (m : Nat) : stoppingTime (2 ^ 2 * m + 3425) 2 :=
  stoppingTime_of_classCertificate certificate_3425 m

/-- Checked base and every prefix for input 3427. -/
theorem certificate_3427 : classCertificateB 4 3427 = true := by
  decide

/-- The same exact first-descent time holds on an infinite dyadic ray. -/
theorem ray_3427 (m : Nat) : stoppingTime (2 ^ 4 * m + 3427) 4 :=
  stoppingTime_of_classCertificate certificate_3427 m

/-- Checked base and every prefix for input 3429. -/
theorem certificate_3429 : classCertificateB 2 3429 = true := by
  decide

/-- The same exact first-descent time holds on an infinite dyadic ray. -/
theorem ray_3429 (m : Nat) : stoppingTime (2 ^ 2 * m + 3429) 2 :=
  stoppingTime_of_classCertificate certificate_3429 m

/-- Checked base and every prefix for input 3431. -/
theorem certificate_3431 : classCertificateB 46 3431 = true := by
  decide

/-- The same exact first-descent time holds on an infinite dyadic ray. -/
theorem ray_3431 (m : Nat) : stoppingTime (2 ^ 46 * m + 3431) 46 :=
  stoppingTime_of_classCertificate certificate_3431 m

/-- Checked base and every prefix for input 3433. -/
theorem certificate_3433 : classCertificateB 2 3433 = true := by
  decide

/-- The same exact first-descent time holds on an infinite dyadic ray. -/
theorem ray_3433 (m : Nat) : stoppingTime (2 ^ 2 * m + 3433) 2 :=
  stoppingTime_of_classCertificate certificate_3433 m

/-- Checked base and every prefix for input 3435. -/
theorem certificate_3435 : classCertificateB 5 3435 = true := by
  decide

/-- The same exact first-descent time holds on an infinite dyadic ray. -/
theorem ray_3435 (m : Nat) : stoppingTime (2 ^ 5 * m + 3435) 5 :=
  stoppingTime_of_classCertificate certificate_3435 m

/-- Checked base and every prefix for input 3437. -/
theorem certificate_3437 : classCertificateB 2 3437 = true := by
  decide

/-- The same exact first-descent time holds on an infinite dyadic ray. -/
theorem ray_3437 (m : Nat) : stoppingTime (2 ^ 2 * m + 3437) 2 :=
  stoppingTime_of_classCertificate certificate_3437 m

/-- Checked base and every prefix for input 3439. -/
theorem certificate_3439 : classCertificateB 10 3439 = true := by
  decide

/-- The same exact first-descent time holds on an infinite dyadic ray. -/
theorem ray_3439 (m : Nat) : stoppingTime (2 ^ 10 * m + 3439) 10 :=
  stoppingTime_of_classCertificate certificate_3439 m

/-- Checked base and every prefix for input 3441. -/
theorem certificate_3441 : classCertificateB 2 3441 = true := by
  decide

/-- The same exact first-descent time holds on an infinite dyadic ray. -/
theorem ray_3441 (m : Nat) : stoppingTime (2 ^ 2 * m + 3441) 2 :=
  stoppingTime_of_classCertificate certificate_3441 m

/-- Checked base and every prefix for input 3443. -/
theorem certificate_3443 : classCertificateB 4 3443 = true := by
  decide

/-- The same exact first-descent time holds on an infinite dyadic ray. -/
theorem ray_3443 (m : Nat) : stoppingTime (2 ^ 4 * m + 3443) 4 :=
  stoppingTime_of_classCertificate certificate_3443 m

/-- Checked base and every prefix for input 3445. -/
theorem certificate_3445 : classCertificateB 2 3445 = true := by
  decide

/-- The same exact first-descent time holds on an infinite dyadic ray. -/
theorem ray_3445 (m : Nat) : stoppingTime (2 ^ 2 * m + 3445) 2 :=
  stoppingTime_of_classCertificate certificate_3445 m

/-- Checked base and every prefix for input 3447. -/
theorem certificate_3447 : classCertificateB 5 3447 = true := by
  decide

/-- The same exact first-descent time holds on an infinite dyadic ray. -/
theorem ray_3447 (m : Nat) : stoppingTime (2 ^ 5 * m + 3447) 5 :=
  stoppingTime_of_classCertificate certificate_3447 m

/-- Checked base and every prefix for input 3449. -/
theorem certificate_3449 : classCertificateB 2 3449 = true := by
  decide

/-- The same exact first-descent time holds on an infinite dyadic ray. -/
theorem ray_3449 (m : Nat) : stoppingTime (2 ^ 2 * m + 3449) 2 :=
  stoppingTime_of_classCertificate certificate_3449 m

/-- Checked base and every prefix for input 3451. -/
theorem certificate_3451 : classCertificateB 8 3451 = true := by
  decide

/-- The same exact first-descent time holds on an infinite dyadic ray. -/
theorem ray_3451 (m : Nat) : stoppingTime (2 ^ 8 * m + 3451) 8 :=
  stoppingTime_of_classCertificate certificate_3451 m

/-- Checked base and every prefix for input 3453. -/
theorem certificate_3453 : classCertificateB 2 3453 = true := by
  decide

/-- The same exact first-descent time holds on an infinite dyadic ray. -/
theorem ray_3453 (m : Nat) : stoppingTime (2 ^ 2 * m + 3453) 2 :=
  stoppingTime_of_classCertificate certificate_3453 m

/-- Checked base and every prefix for input 3455. -/
theorem certificate_3455 : classCertificateB 13 3455 = true := by
  decide

/-- The same exact first-descent time holds on an infinite dyadic ray. -/
theorem ray_3455 (m : Nat) : stoppingTime (2 ^ 13 * m + 3455) 13 :=
  stoppingTime_of_classCertificate certificate_3455 m

/-- Checked base and every prefix for input 3457. -/
theorem certificate_3457 : classCertificateB 2 3457 = true := by
  decide

/-- The same exact first-descent time holds on an infinite dyadic ray. -/
theorem ray_3457 (m : Nat) : stoppingTime (2 ^ 2 * m + 3457) 2 :=
  stoppingTime_of_classCertificate certificate_3457 m

/-- Checked base and every prefix for input 3459. -/
theorem certificate_3459 : classCertificateB 4 3459 = true := by
  decide

/-- The same exact first-descent time holds on an infinite dyadic ray. -/
theorem ray_3459 (m : Nat) : stoppingTime (2 ^ 4 * m + 3459) 4 :=
  stoppingTime_of_classCertificate certificate_3459 m

/-- Checked base and every prefix for input 3461. -/
theorem certificate_3461 : classCertificateB 2 3461 = true := by
  decide

/-- The same exact first-descent time holds on an infinite dyadic ray. -/
theorem ray_3461 (m : Nat) : stoppingTime (2 ^ 2 * m + 3461) 2 :=
  stoppingTime_of_classCertificate certificate_3461 m

/-- Checked base and every prefix for input 3463. -/
theorem certificate_3463 : classCertificateB 7 3463 = true := by
  decide

/-- The same exact first-descent time holds on an infinite dyadic ray. -/
theorem ray_3463 (m : Nat) : stoppingTime (2 ^ 7 * m + 3463) 7 :=
  stoppingTime_of_classCertificate certificate_3463 m

/-- Checked base and every prefix for input 3465. -/
theorem certificate_3465 : classCertificateB 2 3465 = true := by
  decide

/-- The same exact first-descent time holds on an infinite dyadic ray. -/
theorem ray_3465 (m : Nat) : stoppingTime (2 ^ 2 * m + 3465) 2 :=
  stoppingTime_of_classCertificate certificate_3465 m

/-- Checked base and every prefix for input 3467. -/
theorem certificate_3467 : classCertificateB 5 3467 = true := by
  decide

/-- The same exact first-descent time holds on an infinite dyadic ray. -/
theorem ray_3467 (m : Nat) : stoppingTime (2 ^ 5 * m + 3467) 5 :=
  stoppingTime_of_classCertificate certificate_3467 m

/-- Checked base and every prefix for input 3469. -/
theorem certificate_3469 : classCertificateB 2 3469 = true := by
  decide

/-- The same exact first-descent time holds on an infinite dyadic ray. -/
theorem ray_3469 (m : Nat) : stoppingTime (2 ^ 2 * m + 3469) 2 :=
  stoppingTime_of_classCertificate certificate_3469 m

/-- Checked base and every prefix for input 3471. -/
theorem certificate_3471 : classCertificateB 7 3471 = true := by
  decide

/-- The same exact first-descent time holds on an infinite dyadic ray. -/
theorem ray_3471 (m : Nat) : stoppingTime (2 ^ 7 * m + 3471) 7 :=
  stoppingTime_of_classCertificate certificate_3471 m

/-- Checked base and every prefix for input 3473. -/
theorem certificate_3473 : classCertificateB 2 3473 = true := by
  decide

/-- The same exact first-descent time holds on an infinite dyadic ray. -/
theorem ray_3473 (m : Nat) : stoppingTime (2 ^ 2 * m + 3473) 2 :=
  stoppingTime_of_classCertificate certificate_3473 m

/-- Checked base and every prefix for input 3475. -/
theorem certificate_3475 : classCertificateB 4 3475 = true := by
  decide

/-- The same exact first-descent time holds on an infinite dyadic ray. -/
theorem ray_3475 (m : Nat) : stoppingTime (2 ^ 4 * m + 3475) 4 :=
  stoppingTime_of_classCertificate certificate_3475 m

/-- Checked base and every prefix for input 3477. -/
theorem certificate_3477 : classCertificateB 2 3477 = true := by
  decide

/-- The same exact first-descent time holds on an infinite dyadic ray. -/
theorem ray_3477 (m : Nat) : stoppingTime (2 ^ 2 * m + 3477) 2 :=
  stoppingTime_of_classCertificate certificate_3477 m

/-- Checked base and every prefix for input 3479. -/
theorem certificate_3479 : classCertificateB 5 3479 = true := by
  decide

/-- The same exact first-descent time holds on an infinite dyadic ray. -/
theorem ray_3479 (m : Nat) : stoppingTime (2 ^ 5 * m + 3479) 5 :=
  stoppingTime_of_classCertificate certificate_3479 m

/-- Checked base and every prefix for input 3481. -/
theorem certificate_3481 : classCertificateB 2 3481 = true := by
  decide

/-- The same exact first-descent time holds on an infinite dyadic ray. -/
theorem ray_3481 (m : Nat) : stoppingTime (2 ^ 2 * m + 3481) 2 :=
  stoppingTime_of_classCertificate certificate_3481 m

/-- Checked base and every prefix for input 3483. -/
theorem certificate_3483 : classCertificateB 13 3483 = true := by
  decide

/-- The same exact first-descent time holds on an infinite dyadic ray. -/
theorem ray_3483 (m : Nat) : stoppingTime (2 ^ 13 * m + 3483) 13 :=
  stoppingTime_of_classCertificate certificate_3483 m

/-- Exhaustive coverage of the odd inputs in this batch, with no gaps. -/
theorem coverage : CertifiedRange 3417 3485 := by
  intro n hlo hhi hodd
  have hn : n = 3417 ∨ n = 3419 ∨ n = 3421 ∨ n = 3423 ∨ n = 3425 ∨ n = 3427 ∨ n = 3429 ∨ n = 3431 ∨ n = 3433 ∨ n = 3435 ∨ n = 3437 ∨ n = 3439 ∨ n = 3441 ∨ n = 3443 ∨ n = 3445 ∨ n = 3447 ∨ n = 3449 ∨ n = 3451 ∨ n = 3453 ∨ n = 3455 ∨ n = 3457 ∨ n = 3459 ∨ n = 3461 ∨ n = 3463 ∨ n = 3465 ∨ n = 3467 ∨ n = 3469 ∨ n = 3471 ∨ n = 3473 ∨ n = 3475 ∨ n = 3477 ∨ n = 3479 ∨ n = 3481 ∨ n = 3483 := by omega
  rcases hn with h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h
  · subst n
    exact ⟨2, witness_of_certificate certificate_3417⟩
  · subst n
    exact ⟨10, witness_of_certificate certificate_3419⟩
  · subst n
    exact ⟨2, witness_of_certificate certificate_3421⟩
  · subst n
    exact ⟨8, witness_of_certificate certificate_3423⟩
  · subst n
    exact ⟨2, witness_of_certificate certificate_3425⟩
  · subst n
    exact ⟨4, witness_of_certificate certificate_3427⟩
  · subst n
    exact ⟨2, witness_of_certificate certificate_3429⟩
  · subst n
    exact ⟨46, witness_of_certificate certificate_3431⟩
  · subst n
    exact ⟨2, witness_of_certificate certificate_3433⟩
  · subst n
    exact ⟨5, witness_of_certificate certificate_3435⟩
  · subst n
    exact ⟨2, witness_of_certificate certificate_3437⟩
  · subst n
    exact ⟨10, witness_of_certificate certificate_3439⟩
  · subst n
    exact ⟨2, witness_of_certificate certificate_3441⟩
  · subst n
    exact ⟨4, witness_of_certificate certificate_3443⟩
  · subst n
    exact ⟨2, witness_of_certificate certificate_3445⟩
  · subst n
    exact ⟨5, witness_of_certificate certificate_3447⟩
  · subst n
    exact ⟨2, witness_of_certificate certificate_3449⟩
  · subst n
    exact ⟨8, witness_of_certificate certificate_3451⟩
  · subst n
    exact ⟨2, witness_of_certificate certificate_3453⟩
  · subst n
    exact ⟨13, witness_of_certificate certificate_3455⟩
  · subst n
    exact ⟨2, witness_of_certificate certificate_3457⟩
  · subst n
    exact ⟨4, witness_of_certificate certificate_3459⟩
  · subst n
    exact ⟨2, witness_of_certificate certificate_3461⟩
  · subst n
    exact ⟨7, witness_of_certificate certificate_3463⟩
  · subst n
    exact ⟨2, witness_of_certificate certificate_3465⟩
  · subst n
    exact ⟨5, witness_of_certificate certificate_3467⟩
  · subst n
    exact ⟨2, witness_of_certificate certificate_3469⟩
  · subst n
    exact ⟨7, witness_of_certificate certificate_3471⟩
  · subst n
    exact ⟨2, witness_of_certificate certificate_3473⟩
  · subst n
    exact ⟨4, witness_of_certificate certificate_3475⟩
  · subst n
    exact ⟨2, witness_of_certificate certificate_3477⟩
  · subst n
    exact ⟨5, witness_of_certificate certificate_3479⟩
  · subst n
    exact ⟨2, witness_of_certificate certificate_3481⟩
  · subst n
    exact ⟨13, witness_of_certificate certificate_3483⟩

end Collatz.Research.CoefficientDescent.Batch052
