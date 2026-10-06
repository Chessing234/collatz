import Collatz.Research.CoefficientDescent.Basic

namespace Collatz.Research.CoefficientDescent.Batch008

open FirstDescentClass

set_option maxRecDepth 20000
set_option maxHeartbeats 0

/-- Checked base and every prefix for input 471. -/
theorem certificate_471 : classCertificateB 5 471 = true := by
  decide

/-- The same exact first-descent time holds on an infinite dyadic ray. -/
theorem ray_471 (m : Nat) : stoppingTime (2 ^ 5 * m + 471) 5 :=
  stoppingTime_of_classCertificate certificate_471 m

/-- Checked base and every prefix for input 473. -/
theorem certificate_473 : classCertificateB 2 473 = true := by
  decide

/-- The same exact first-descent time holds on an infinite dyadic ray. -/
theorem ray_473 (m : Nat) : stoppingTime (2 ^ 2 * m + 473) 2 :=
  stoppingTime_of_classCertificate certificate_473 m

/-- Checked base and every prefix for input 475. -/
theorem certificate_475 : classCertificateB 8 475 = true := by
  decide

/-- The same exact first-descent time holds on an infinite dyadic ray. -/
theorem ray_475 (m : Nat) : stoppingTime (2 ^ 8 * m + 475) 8 :=
  stoppingTime_of_classCertificate certificate_475 m

/-- Checked base and every prefix for input 477. -/
theorem certificate_477 : classCertificateB 2 477 = true := by
  decide

/-- The same exact first-descent time holds on an infinite dyadic ray. -/
theorem ray_477 (m : Nat) : stoppingTime (2 ^ 2 * m + 477) 2 :=
  stoppingTime_of_classCertificate certificate_477 m

/-- Checked base and every prefix for input 479. -/
theorem certificate_479 : classCertificateB 16 479 = true := by
  decide

/-- The same exact first-descent time holds on an infinite dyadic ray. -/
theorem ray_479 (m : Nat) : stoppingTime (2 ^ 16 * m + 479) 16 :=
  stoppingTime_of_classCertificate certificate_479 m

/-- Checked base and every prefix for input 481. -/
theorem certificate_481 : classCertificateB 2 481 = true := by
  decide

/-- The same exact first-descent time holds on an infinite dyadic ray. -/
theorem ray_481 (m : Nat) : stoppingTime (2 ^ 2 * m + 481) 2 :=
  stoppingTime_of_classCertificate certificate_481 m

/-- Checked base and every prefix for input 483. -/
theorem certificate_483 : classCertificateB 4 483 = true := by
  decide

/-- The same exact first-descent time holds on an infinite dyadic ray. -/
theorem ray_483 (m : Nat) : stoppingTime (2 ^ 4 * m + 483) 4 :=
  stoppingTime_of_classCertificate certificate_483 m

/-- Checked base and every prefix for input 485. -/
theorem certificate_485 : classCertificateB 2 485 = true := by
  decide

/-- The same exact first-descent time holds on an infinite dyadic ray. -/
theorem ray_485 (m : Nat) : stoppingTime (2 ^ 2 * m + 485) 2 :=
  stoppingTime_of_classCertificate certificate_485 m

/-- Checked base and every prefix for input 487. -/
theorem certificate_487 : classCertificateB 20 487 = true := by
  decide

/-- The same exact first-descent time holds on an infinite dyadic ray. -/
theorem ray_487 (m : Nat) : stoppingTime (2 ^ 20 * m + 487) 20 :=
  stoppingTime_of_classCertificate certificate_487 m

/-- Checked base and every prefix for input 489. -/
theorem certificate_489 : classCertificateB 2 489 = true := by
  decide

/-- The same exact first-descent time holds on an infinite dyadic ray. -/
theorem ray_489 (m : Nat) : stoppingTime (2 ^ 2 * m + 489) 2 :=
  stoppingTime_of_classCertificate certificate_489 m

/-- Checked base and every prefix for input 491. -/
theorem certificate_491 : classCertificateB 5 491 = true := by
  decide

/-- The same exact first-descent time holds on an infinite dyadic ray. -/
theorem ray_491 (m : Nat) : stoppingTime (2 ^ 5 * m + 491) 5 :=
  stoppingTime_of_classCertificate certificate_491 m

/-- Checked base and every prefix for input 493. -/
theorem certificate_493 : classCertificateB 2 493 = true := by
  decide

/-- The same exact first-descent time holds on an infinite dyadic ray. -/
theorem ray_493 (m : Nat) : stoppingTime (2 ^ 2 * m + 493) 2 :=
  stoppingTime_of_classCertificate certificate_493 m

/-- Checked base and every prefix for input 495. -/
theorem certificate_495 : classCertificateB 27 495 = true := by
  decide

/-- The same exact first-descent time holds on an infinite dyadic ray. -/
theorem ray_495 (m : Nat) : stoppingTime (2 ^ 27 * m + 495) 27 :=
  stoppingTime_of_classCertificate certificate_495 m

/-- Checked base and every prefix for input 497. -/
theorem certificate_497 : classCertificateB 2 497 = true := by
  decide

/-- The same exact first-descent time holds on an infinite dyadic ray. -/
theorem ray_497 (m : Nat) : stoppingTime (2 ^ 2 * m + 497) 2 :=
  stoppingTime_of_classCertificate certificate_497 m

/-- Checked base and every prefix for input 499. -/
theorem certificate_499 : classCertificateB 4 499 = true := by
  decide

/-- The same exact first-descent time holds on an infinite dyadic ray. -/
theorem ray_499 (m : Nat) : stoppingTime (2 ^ 4 * m + 499) 4 :=
  stoppingTime_of_classCertificate certificate_499 m

/-- Checked base and every prefix for input 501. -/
theorem certificate_501 : classCertificateB 2 501 = true := by
  decide

/-- The same exact first-descent time holds on an infinite dyadic ray. -/
theorem ray_501 (m : Nat) : stoppingTime (2 ^ 2 * m + 501) 2 :=
  stoppingTime_of_classCertificate certificate_501 m

/-- Checked base and every prefix for input 503. -/
theorem certificate_503 : classCertificateB 5 503 = true := by
  decide

/-- The same exact first-descent time holds on an infinite dyadic ray. -/
theorem ray_503 (m : Nat) : stoppingTime (2 ^ 5 * m + 503) 5 :=
  stoppingTime_of_classCertificate certificate_503 m

/-- Checked base and every prefix for input 505. -/
theorem certificate_505 : classCertificateB 2 505 = true := by
  decide

/-- The same exact first-descent time holds on an infinite dyadic ray. -/
theorem ray_505 (m : Nat) : stoppingTime (2 ^ 2 * m + 505) 2 :=
  stoppingTime_of_classCertificate certificate_505 m

/-- Checked base and every prefix for input 507. -/
theorem certificate_507 : classCertificateB 10 507 = true := by
  decide

/-- The same exact first-descent time holds on an infinite dyadic ray. -/
theorem ray_507 (m : Nat) : stoppingTime (2 ^ 10 * m + 507) 10 :=
  stoppingTime_of_classCertificate certificate_507 m

/-- Checked base and every prefix for input 509. -/
theorem certificate_509 : classCertificateB 2 509 = true := by
  decide

/-- The same exact first-descent time holds on an infinite dyadic ray. -/
theorem ray_509 (m : Nat) : stoppingTime (2 ^ 2 * m + 509) 2 :=
  stoppingTime_of_classCertificate certificate_509 m

/-- Checked base and every prefix for input 511. -/
theorem certificate_511 : classCertificateB 18 511 = true := by
  decide

/-- The same exact first-descent time holds on an infinite dyadic ray. -/
theorem ray_511 (m : Nat) : stoppingTime (2 ^ 18 * m + 511) 18 :=
  stoppingTime_of_classCertificate certificate_511 m

/-- Checked base and every prefix for input 513. -/
theorem certificate_513 : classCertificateB 2 513 = true := by
  decide

/-- The same exact first-descent time holds on an infinite dyadic ray. -/
theorem ray_513 (m : Nat) : stoppingTime (2 ^ 2 * m + 513) 2 :=
  stoppingTime_of_classCertificate certificate_513 m

/-- Checked base and every prefix for input 515. -/
theorem certificate_515 : classCertificateB 4 515 = true := by
  decide

/-- The same exact first-descent time holds on an infinite dyadic ray. -/
theorem ray_515 (m : Nat) : stoppingTime (2 ^ 4 * m + 515) 4 :=
  stoppingTime_of_classCertificate certificate_515 m

/-- Checked base and every prefix for input 517. -/
theorem certificate_517 : classCertificateB 2 517 = true := by
  decide

/-- The same exact first-descent time holds on an infinite dyadic ray. -/
theorem ray_517 (m : Nat) : stoppingTime (2 ^ 2 * m + 517) 2 :=
  stoppingTime_of_classCertificate certificate_517 m

/-- Checked base and every prefix for input 519. -/
theorem certificate_519 : classCertificateB 7 519 = true := by
  decide

/-- The same exact first-descent time holds on an infinite dyadic ray. -/
theorem ray_519 (m : Nat) : stoppingTime (2 ^ 7 * m + 519) 7 :=
  stoppingTime_of_classCertificate certificate_519 m

/-- Checked base and every prefix for input 521. -/
theorem certificate_521 : classCertificateB 2 521 = true := by
  decide

/-- The same exact first-descent time holds on an infinite dyadic ray. -/
theorem ray_521 (m : Nat) : stoppingTime (2 ^ 2 * m + 521) 2 :=
  stoppingTime_of_classCertificate certificate_521 m

/-- Checked base and every prefix for input 523. -/
theorem certificate_523 : classCertificateB 5 523 = true := by
  decide

/-- The same exact first-descent time holds on an infinite dyadic ray. -/
theorem ray_523 (m : Nat) : stoppingTime (2 ^ 5 * m + 523) 5 :=
  stoppingTime_of_classCertificate certificate_523 m

/-- Checked base and every prefix for input 525. -/
theorem certificate_525 : classCertificateB 2 525 = true := by
  decide

/-- The same exact first-descent time holds on an infinite dyadic ray. -/
theorem ray_525 (m : Nat) : stoppingTime (2 ^ 2 * m + 525) 2 :=
  stoppingTime_of_classCertificate certificate_525 m

/-- Checked base and every prefix for input 527. -/
theorem certificate_527 : classCertificateB 7 527 = true := by
  decide

/-- The same exact first-descent time holds on an infinite dyadic ray. -/
theorem ray_527 (m : Nat) : stoppingTime (2 ^ 7 * m + 527) 7 :=
  stoppingTime_of_classCertificate certificate_527 m

/-- Checked base and every prefix for input 529. -/
theorem certificate_529 : classCertificateB 2 529 = true := by
  decide

/-- The same exact first-descent time holds on an infinite dyadic ray. -/
theorem ray_529 (m : Nat) : stoppingTime (2 ^ 2 * m + 529) 2 :=
  stoppingTime_of_classCertificate certificate_529 m

/-- Checked base and every prefix for input 531. -/
theorem certificate_531 : classCertificateB 4 531 = true := by
  decide

/-- The same exact first-descent time holds on an infinite dyadic ray. -/
theorem ray_531 (m : Nat) : stoppingTime (2 ^ 4 * m + 531) 4 :=
  stoppingTime_of_classCertificate certificate_531 m

/-- Checked base and every prefix for input 533. -/
theorem certificate_533 : classCertificateB 2 533 = true := by
  decide

/-- The same exact first-descent time holds on an infinite dyadic ray. -/
theorem ray_533 (m : Nat) : stoppingTime (2 ^ 2 * m + 533) 2 :=
  stoppingTime_of_classCertificate certificate_533 m

/-- Checked base and every prefix for input 535. -/
theorem certificate_535 : classCertificateB 5 535 = true := by
  decide

/-- The same exact first-descent time holds on an infinite dyadic ray. -/
theorem ray_535 (m : Nat) : stoppingTime (2 ^ 5 * m + 535) 5 :=
  stoppingTime_of_classCertificate certificate_535 m

/-- Exhaustive coverage of the odd inputs in this batch, with no gaps. -/
theorem coverage : CertifiedRange 471 537 := by
  intro n hlo hhi hodd
  have hn : n = 471 ∨ n = 473 ∨ n = 475 ∨ n = 477 ∨ n = 479 ∨ n = 481 ∨ n = 483 ∨ n = 485 ∨ n = 487 ∨ n = 489 ∨ n = 491 ∨ n = 493 ∨ n = 495 ∨ n = 497 ∨ n = 499 ∨ n = 501 ∨ n = 503 ∨ n = 505 ∨ n = 507 ∨ n = 509 ∨ n = 511 ∨ n = 513 ∨ n = 515 ∨ n = 517 ∨ n = 519 ∨ n = 521 ∨ n = 523 ∨ n = 525 ∨ n = 527 ∨ n = 529 ∨ n = 531 ∨ n = 533 ∨ n = 535 := by omega
  rcases hn with h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h
  · subst n
    exact ⟨5, witness_of_certificate certificate_471⟩
  · subst n
    exact ⟨2, witness_of_certificate certificate_473⟩
  · subst n
    exact ⟨8, witness_of_certificate certificate_475⟩
  · subst n
    exact ⟨2, witness_of_certificate certificate_477⟩
  · subst n
    exact ⟨16, witness_of_certificate certificate_479⟩
  · subst n
    exact ⟨2, witness_of_certificate certificate_481⟩
  · subst n
    exact ⟨4, witness_of_certificate certificate_483⟩
  · subst n
    exact ⟨2, witness_of_certificate certificate_485⟩
  · subst n
    exact ⟨20, witness_of_certificate certificate_487⟩
  · subst n
    exact ⟨2, witness_of_certificate certificate_489⟩
  · subst n
    exact ⟨5, witness_of_certificate certificate_491⟩
  · subst n
    exact ⟨2, witness_of_certificate certificate_493⟩
  · subst n
    exact ⟨27, witness_of_certificate certificate_495⟩
  · subst n
    exact ⟨2, witness_of_certificate certificate_497⟩
  · subst n
    exact ⟨4, witness_of_certificate certificate_499⟩
  · subst n
    exact ⟨2, witness_of_certificate certificate_501⟩
  · subst n
    exact ⟨5, witness_of_certificate certificate_503⟩
  · subst n
    exact ⟨2, witness_of_certificate certificate_505⟩
  · subst n
    exact ⟨10, witness_of_certificate certificate_507⟩
  · subst n
    exact ⟨2, witness_of_certificate certificate_509⟩
  · subst n
    exact ⟨18, witness_of_certificate certificate_511⟩
  · subst n
    exact ⟨2, witness_of_certificate certificate_513⟩
  · subst n
    exact ⟨4, witness_of_certificate certificate_515⟩
  · subst n
    exact ⟨2, witness_of_certificate certificate_517⟩
  · subst n
    exact ⟨7, witness_of_certificate certificate_519⟩
  · subst n
    exact ⟨2, witness_of_certificate certificate_521⟩
  · subst n
    exact ⟨5, witness_of_certificate certificate_523⟩
  · subst n
    exact ⟨2, witness_of_certificate certificate_525⟩
  · subst n
    exact ⟨7, witness_of_certificate certificate_527⟩
  · subst n
    exact ⟨2, witness_of_certificate certificate_529⟩
  · subst n
    exact ⟨4, witness_of_certificate certificate_531⟩
  · subst n
    exact ⟨2, witness_of_certificate certificate_533⟩
  · subst n
    exact ⟨5, witness_of_certificate certificate_535⟩

end Collatz.Research.CoefficientDescent.Batch008
