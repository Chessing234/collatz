import Collatz.Research.CoefficientDescent.Basic

namespace Collatz.Research.CoefficientDescent.Batch007

open FirstDescentClass

set_option maxRecDepth 20000
set_option maxHeartbeats 0

/-- Checked base and every prefix for input 403. -/
theorem certificate_403 : classCertificateB 4 403 = true := by
  decide

/-- The same exact first-descent time holds on an infinite dyadic ray. -/
theorem ray_403 (m : Nat) : stoppingTime (2 ^ 4 * m + 403) 4 :=
  stoppingTime_of_classCertificate certificate_403 m

/-- Checked base and every prefix for input 405. -/
theorem certificate_405 : classCertificateB 2 405 = true := by
  decide

/-- The same exact first-descent time holds on an infinite dyadic ray. -/
theorem ray_405 (m : Nat) : stoppingTime (2 ^ 2 * m + 405) 2 :=
  stoppingTime_of_classCertificate certificate_405 m

/-- Checked base and every prefix for input 407. -/
theorem certificate_407 : classCertificateB 5 407 = true := by
  decide

/-- The same exact first-descent time holds on an infinite dyadic ray. -/
theorem ray_407 (m : Nat) : stoppingTime (2 ^ 5 * m + 407) 5 :=
  stoppingTime_of_classCertificate certificate_407 m

/-- Checked base and every prefix for input 409. -/
theorem certificate_409 : classCertificateB 2 409 = true := by
  decide

/-- The same exact first-descent time holds on an infinite dyadic ray. -/
theorem ray_409 (m : Nat) : stoppingTime (2 ^ 2 * m + 409) 2 :=
  stoppingTime_of_classCertificate certificate_409 m

/-- Checked base and every prefix for input 411. -/
theorem certificate_411 : classCertificateB 15 411 = true := by
  decide

/-- The same exact first-descent time holds on an infinite dyadic ray. -/
theorem ray_411 (m : Nat) : stoppingTime (2 ^ 15 * m + 411) 15 :=
  stoppingTime_of_classCertificate certificate_411 m

/-- Checked base and every prefix for input 413. -/
theorem certificate_413 : classCertificateB 2 413 = true := by
  decide

/-- The same exact first-descent time holds on an infinite dyadic ray. -/
theorem ray_413 (m : Nat) : stoppingTime (2 ^ 2 * m + 413) 2 :=
  stoppingTime_of_classCertificate certificate_413 m

/-- Checked base and every prefix for input 415. -/
theorem certificate_415 : classCertificateB 15 415 = true := by
  decide

/-- The same exact first-descent time holds on an infinite dyadic ray. -/
theorem ray_415 (m : Nat) : stoppingTime (2 ^ 15 * m + 415) 15 :=
  stoppingTime_of_classCertificate certificate_415 m

/-- Checked base and every prefix for input 417. -/
theorem certificate_417 : classCertificateB 2 417 = true := by
  decide

/-- The same exact first-descent time holds on an infinite dyadic ray. -/
theorem ray_417 (m : Nat) : stoppingTime (2 ^ 2 * m + 417) 2 :=
  stoppingTime_of_classCertificate certificate_417 m

/-- Checked base and every prefix for input 419. -/
theorem certificate_419 : classCertificateB 4 419 = true := by
  decide

/-- The same exact first-descent time holds on an infinite dyadic ray. -/
theorem ray_419 (m : Nat) : stoppingTime (2 ^ 4 * m + 419) 4 :=
  stoppingTime_of_classCertificate certificate_419 m

/-- Checked base and every prefix for input 421. -/
theorem certificate_421 : classCertificateB 2 421 = true := by
  decide

/-- The same exact first-descent time holds on an infinite dyadic ray. -/
theorem ray_421 (m : Nat) : stoppingTime (2 ^ 2 * m + 421) 2 :=
  stoppingTime_of_classCertificate certificate_421 m

/-- Checked base and every prefix for input 423. -/
theorem certificate_423 : classCertificateB 10 423 = true := by
  decide

/-- The same exact first-descent time holds on an infinite dyadic ray. -/
theorem ray_423 (m : Nat) : stoppingTime (2 ^ 10 * m + 423) 10 :=
  stoppingTime_of_classCertificate certificate_423 m

/-- Checked base and every prefix for input 425. -/
theorem certificate_425 : classCertificateB 2 425 = true := by
  decide

/-- The same exact first-descent time holds on an infinite dyadic ray. -/
theorem ray_425 (m : Nat) : stoppingTime (2 ^ 2 * m + 425) 2 :=
  stoppingTime_of_classCertificate certificate_425 m

/-- Checked base and every prefix for input 427. -/
theorem certificate_427 : classCertificateB 5 427 = true := by
  decide

/-- The same exact first-descent time holds on an infinite dyadic ray. -/
theorem ray_427 (m : Nat) : stoppingTime (2 ^ 5 * m + 427) 5 :=
  stoppingTime_of_classCertificate certificate_427 m

/-- Checked base and every prefix for input 429. -/
theorem certificate_429 : classCertificateB 2 429 = true := by
  decide

/-- The same exact first-descent time holds on an infinite dyadic ray. -/
theorem ray_429 (m : Nat) : stoppingTime (2 ^ 2 * m + 429) 2 :=
  stoppingTime_of_classCertificate certificate_429 m

/-- Checked base and every prefix for input 431. -/
theorem certificate_431 : classCertificateB 8 431 = true := by
  decide

/-- The same exact first-descent time holds on an infinite dyadic ray. -/
theorem ray_431 (m : Nat) : stoppingTime (2 ^ 8 * m + 431) 8 :=
  stoppingTime_of_classCertificate certificate_431 m

/-- Checked base and every prefix for input 433. -/
theorem certificate_433 : classCertificateB 2 433 = true := by
  decide

/-- The same exact first-descent time holds on an infinite dyadic ray. -/
theorem ray_433 (m : Nat) : stoppingTime (2 ^ 2 * m + 433) 2 :=
  stoppingTime_of_classCertificate certificate_433 m

/-- Checked base and every prefix for input 435. -/
theorem certificate_435 : classCertificateB 4 435 = true := by
  decide

/-- The same exact first-descent time holds on an infinite dyadic ray. -/
theorem ray_435 (m : Nat) : stoppingTime (2 ^ 4 * m + 435) 4 :=
  stoppingTime_of_classCertificate certificate_435 m

/-- Checked base and every prefix for input 437. -/
theorem certificate_437 : classCertificateB 2 437 = true := by
  decide

/-- The same exact first-descent time holds on an infinite dyadic ray. -/
theorem ray_437 (m : Nat) : stoppingTime (2 ^ 2 * m + 437) 2 :=
  stoppingTime_of_classCertificate certificate_437 m

/-- Checked base and every prefix for input 439. -/
theorem certificate_439 : classCertificateB 5 439 = true := by
  decide

/-- The same exact first-descent time holds on an infinite dyadic ray. -/
theorem ray_439 (m : Nat) : stoppingTime (2 ^ 5 * m + 439) 5 :=
  stoppingTime_of_classCertificate certificate_439 m

/-- Checked base and every prefix for input 441. -/
theorem certificate_441 : classCertificateB 2 441 = true := by
  decide

/-- The same exact first-descent time holds on an infinite dyadic ray. -/
theorem ray_441 (m : Nat) : stoppingTime (2 ^ 2 * m + 441) 2 :=
  stoppingTime_of_classCertificate certificate_441 m

/-- Checked base and every prefix for input 443. -/
theorem certificate_443 : classCertificateB 7 443 = true := by
  decide

/-- The same exact first-descent time holds on an infinite dyadic ray. -/
theorem ray_443 (m : Nat) : stoppingTime (2 ^ 7 * m + 443) 7 :=
  stoppingTime_of_classCertificate certificate_443 m

/-- Checked base and every prefix for input 445. -/
theorem certificate_445 : classCertificateB 2 445 = true := by
  decide

/-- The same exact first-descent time holds on an infinite dyadic ray. -/
theorem ray_445 (m : Nat) : stoppingTime (2 ^ 2 * m + 445) 2 :=
  stoppingTime_of_classCertificate certificate_445 m

/-- Checked base and every prefix for input 447. -/
theorem certificate_447 : classCertificateB 40 447 = true := by
  decide

/-- The same exact first-descent time holds on an infinite dyadic ray. -/
theorem ray_447 (m : Nat) : stoppingTime (2 ^ 40 * m + 447) 40 :=
  stoppingTime_of_classCertificate certificate_447 m

/-- Checked base and every prefix for input 449. -/
theorem certificate_449 : classCertificateB 2 449 = true := by
  decide

/-- The same exact first-descent time holds on an infinite dyadic ray. -/
theorem ray_449 (m : Nat) : stoppingTime (2 ^ 2 * m + 449) 2 :=
  stoppingTime_of_classCertificate certificate_449 m

/-- Checked base and every prefix for input 451. -/
theorem certificate_451 : classCertificateB 4 451 = true := by
  decide

/-- The same exact first-descent time holds on an infinite dyadic ray. -/
theorem ray_451 (m : Nat) : stoppingTime (2 ^ 4 * m + 451) 4 :=
  stoppingTime_of_classCertificate certificate_451 m

/-- Checked base and every prefix for input 453. -/
theorem certificate_453 : classCertificateB 2 453 = true := by
  decide

/-- The same exact first-descent time holds on an infinite dyadic ray. -/
theorem ray_453 (m : Nat) : stoppingTime (2 ^ 2 * m + 453) 2 :=
  stoppingTime_of_classCertificate certificate_453 m

/-- Checked base and every prefix for input 455. -/
theorem certificate_455 : classCertificateB 8 455 = true := by
  decide

/-- The same exact first-descent time holds on an infinite dyadic ray. -/
theorem ray_455 (m : Nat) : stoppingTime (2 ^ 8 * m + 455) 8 :=
  stoppingTime_of_classCertificate certificate_455 m

/-- Checked base and every prefix for input 457. -/
theorem certificate_457 : classCertificateB 2 457 = true := by
  decide

/-- The same exact first-descent time holds on an infinite dyadic ray. -/
theorem ray_457 (m : Nat) : stoppingTime (2 ^ 2 * m + 457) 2 :=
  stoppingTime_of_classCertificate certificate_457 m

/-- Checked base and every prefix for input 459. -/
theorem certificate_459 : classCertificateB 5 459 = true := by
  decide

/-- The same exact first-descent time holds on an infinite dyadic ray. -/
theorem ray_459 (m : Nat) : stoppingTime (2 ^ 5 * m + 459) 5 :=
  stoppingTime_of_classCertificate certificate_459 m

/-- Checked base and every prefix for input 461. -/
theorem certificate_461 : classCertificateB 2 461 = true := by
  decide

/-- The same exact first-descent time holds on an infinite dyadic ray. -/
theorem ray_461 (m : Nat) : stoppingTime (2 ^ 2 * m + 461) 2 :=
  stoppingTime_of_classCertificate certificate_461 m

/-- Checked base and every prefix for input 463. -/
theorem certificate_463 : classCertificateB 12 463 = true := by
  decide

/-- The same exact first-descent time holds on an infinite dyadic ray. -/
theorem ray_463 (m : Nat) : stoppingTime (2 ^ 12 * m + 463) 12 :=
  stoppingTime_of_classCertificate certificate_463 m

/-- Checked base and every prefix for input 465. -/
theorem certificate_465 : classCertificateB 2 465 = true := by
  decide

/-- The same exact first-descent time holds on an infinite dyadic ray. -/
theorem ray_465 (m : Nat) : stoppingTime (2 ^ 2 * m + 465) 2 :=
  stoppingTime_of_classCertificate certificate_465 m

/-- Checked base and every prefix for input 467. -/
theorem certificate_467 : classCertificateB 4 467 = true := by
  decide

/-- The same exact first-descent time holds on an infinite dyadic ray. -/
theorem ray_467 (m : Nat) : stoppingTime (2 ^ 4 * m + 467) 4 :=
  stoppingTime_of_classCertificate certificate_467 m

/-- Checked base and every prefix for input 469. -/
theorem certificate_469 : classCertificateB 2 469 = true := by
  decide

/-- The same exact first-descent time holds on an infinite dyadic ray. -/
theorem ray_469 (m : Nat) : stoppingTime (2 ^ 2 * m + 469) 2 :=
  stoppingTime_of_classCertificate certificate_469 m

/-- Exhaustive coverage of the odd inputs in this batch, with no gaps. -/
theorem coverage : CertifiedRange 403 471 := by
  intro n hlo hhi hodd
  have hn : n = 403 ∨ n = 405 ∨ n = 407 ∨ n = 409 ∨ n = 411 ∨ n = 413 ∨ n = 415 ∨ n = 417 ∨ n = 419 ∨ n = 421 ∨ n = 423 ∨ n = 425 ∨ n = 427 ∨ n = 429 ∨ n = 431 ∨ n = 433 ∨ n = 435 ∨ n = 437 ∨ n = 439 ∨ n = 441 ∨ n = 443 ∨ n = 445 ∨ n = 447 ∨ n = 449 ∨ n = 451 ∨ n = 453 ∨ n = 455 ∨ n = 457 ∨ n = 459 ∨ n = 461 ∨ n = 463 ∨ n = 465 ∨ n = 467 ∨ n = 469 := by omega
  rcases hn with h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h
  · subst n
    exact ⟨4, witness_of_certificate certificate_403⟩
  · subst n
    exact ⟨2, witness_of_certificate certificate_405⟩
  · subst n
    exact ⟨5, witness_of_certificate certificate_407⟩
  · subst n
    exact ⟨2, witness_of_certificate certificate_409⟩
  · subst n
    exact ⟨15, witness_of_certificate certificate_411⟩
  · subst n
    exact ⟨2, witness_of_certificate certificate_413⟩
  · subst n
    exact ⟨15, witness_of_certificate certificate_415⟩
  · subst n
    exact ⟨2, witness_of_certificate certificate_417⟩
  · subst n
    exact ⟨4, witness_of_certificate certificate_419⟩
  · subst n
    exact ⟨2, witness_of_certificate certificate_421⟩
  · subst n
    exact ⟨10, witness_of_certificate certificate_423⟩
  · subst n
    exact ⟨2, witness_of_certificate certificate_425⟩
  · subst n
    exact ⟨5, witness_of_certificate certificate_427⟩
  · subst n
    exact ⟨2, witness_of_certificate certificate_429⟩
  · subst n
    exact ⟨8, witness_of_certificate certificate_431⟩
  · subst n
    exact ⟨2, witness_of_certificate certificate_433⟩
  · subst n
    exact ⟨4, witness_of_certificate certificate_435⟩
  · subst n
    exact ⟨2, witness_of_certificate certificate_437⟩
  · subst n
    exact ⟨5, witness_of_certificate certificate_439⟩
  · subst n
    exact ⟨2, witness_of_certificate certificate_441⟩
  · subst n
    exact ⟨7, witness_of_certificate certificate_443⟩
  · subst n
    exact ⟨2, witness_of_certificate certificate_445⟩
  · subst n
    exact ⟨40, witness_of_certificate certificate_447⟩
  · subst n
    exact ⟨2, witness_of_certificate certificate_449⟩
  · subst n
    exact ⟨4, witness_of_certificate certificate_451⟩
  · subst n
    exact ⟨2, witness_of_certificate certificate_453⟩
  · subst n
    exact ⟨8, witness_of_certificate certificate_455⟩
  · subst n
    exact ⟨2, witness_of_certificate certificate_457⟩
  · subst n
    exact ⟨5, witness_of_certificate certificate_459⟩
  · subst n
    exact ⟨2, witness_of_certificate certificate_461⟩
  · subst n
    exact ⟨12, witness_of_certificate certificate_463⟩
  · subst n
    exact ⟨2, witness_of_certificate certificate_465⟩
  · subst n
    exact ⟨4, witness_of_certificate certificate_467⟩
  · subst n
    exact ⟨2, witness_of_certificate certificate_469⟩

end Collatz.Research.CoefficientDescent.Batch007
