import Collatz.Research.CoefficientDescent.Basic

namespace Collatz.Research.CoefficientDescent.Batch067

open FirstDescentClass

set_option maxRecDepth 20000
set_option maxHeartbeats 0

/-- Checked base and every prefix for input 4423. -/
theorem certificate_4423 : classCertificateB 21 4423 = true := by
  decide

/-- The same exact first-descent time holds on an infinite dyadic ray. -/
theorem ray_4423 (m : Nat) : stoppingTime (2 ^ 21 * m + 4423) 21 :=
  stoppingTime_of_classCertificate certificate_4423 m

/-- Checked base and every prefix for input 4425. -/
theorem certificate_4425 : classCertificateB 2 4425 = true := by
  decide

/-- The same exact first-descent time holds on an infinite dyadic ray. -/
theorem ray_4425 (m : Nat) : stoppingTime (2 ^ 2 * m + 4425) 2 :=
  stoppingTime_of_classCertificate certificate_4425 m

/-- Checked base and every prefix for input 4427. -/
theorem certificate_4427 : classCertificateB 5 4427 = true := by
  decide

/-- The same exact first-descent time holds on an infinite dyadic ray. -/
theorem ray_4427 (m : Nat) : stoppingTime (2 ^ 5 * m + 4427) 5 :=
  stoppingTime_of_classCertificate certificate_4427 m

/-- Checked base and every prefix for input 4429. -/
theorem certificate_4429 : classCertificateB 2 4429 = true := by
  decide

/-- The same exact first-descent time holds on an infinite dyadic ray. -/
theorem ray_4429 (m : Nat) : stoppingTime (2 ^ 2 * m + 4429) 2 :=
  stoppingTime_of_classCertificate certificate_4429 m

/-- Checked base and every prefix for input 4431. -/
theorem certificate_4431 : classCertificateB 8 4431 = true := by
  decide

/-- The same exact first-descent time holds on an infinite dyadic ray. -/
theorem ray_4431 (m : Nat) : stoppingTime (2 ^ 8 * m + 4431) 8 :=
  stoppingTime_of_classCertificate certificate_4431 m

/-- Checked base and every prefix for input 4433. -/
theorem certificate_4433 : classCertificateB 2 4433 = true := by
  decide

/-- The same exact first-descent time holds on an infinite dyadic ray. -/
theorem ray_4433 (m : Nat) : stoppingTime (2 ^ 2 * m + 4433) 2 :=
  stoppingTime_of_classCertificate certificate_4433 m

/-- Checked base and every prefix for input 4435. -/
theorem certificate_4435 : classCertificateB 4 4435 = true := by
  decide

/-- The same exact first-descent time holds on an infinite dyadic ray. -/
theorem ray_4435 (m : Nat) : stoppingTime (2 ^ 4 * m + 4435) 4 :=
  stoppingTime_of_classCertificate certificate_4435 m

/-- Checked base and every prefix for input 4437. -/
theorem certificate_4437 : classCertificateB 2 4437 = true := by
  decide

/-- The same exact first-descent time holds on an infinite dyadic ray. -/
theorem ray_4437 (m : Nat) : stoppingTime (2 ^ 2 * m + 4437) 2 :=
  stoppingTime_of_classCertificate certificate_4437 m

/-- Checked base and every prefix for input 4439. -/
theorem certificate_4439 : classCertificateB 5 4439 = true := by
  decide

/-- The same exact first-descent time holds on an infinite dyadic ray. -/
theorem ray_4439 (m : Nat) : stoppingTime (2 ^ 5 * m + 4439) 5 :=
  stoppingTime_of_classCertificate certificate_4439 m

/-- Checked base and every prefix for input 4441. -/
theorem certificate_4441 : classCertificateB 2 4441 = true := by
  decide

/-- The same exact first-descent time holds on an infinite dyadic ray. -/
theorem ray_4441 (m : Nat) : stoppingTime (2 ^ 2 * m + 4441) 2 :=
  stoppingTime_of_classCertificate certificate_4441 m

/-- Checked base and every prefix for input 4443. -/
theorem certificate_4443 : classCertificateB 10 4443 = true := by
  decide

/-- The same exact first-descent time holds on an infinite dyadic ray. -/
theorem ray_4443 (m : Nat) : stoppingTime (2 ^ 10 * m + 4443) 10 :=
  stoppingTime_of_classCertificate certificate_4443 m

/-- Checked base and every prefix for input 4445. -/
theorem certificate_4445 : classCertificateB 2 4445 = true := by
  decide

/-- The same exact first-descent time holds on an infinite dyadic ray. -/
theorem ray_4445 (m : Nat) : stoppingTime (2 ^ 2 * m + 4445) 2 :=
  stoppingTime_of_classCertificate certificate_4445 m

/-- Checked base and every prefix for input 4447. -/
theorem certificate_4447 : classCertificateB 8 4447 = true := by
  decide

/-- The same exact first-descent time holds on an infinite dyadic ray. -/
theorem ray_4447 (m : Nat) : stoppingTime (2 ^ 8 * m + 4447) 8 :=
  stoppingTime_of_classCertificate certificate_4447 m

/-- Checked base and every prefix for input 4449. -/
theorem certificate_4449 : classCertificateB 2 4449 = true := by
  decide

/-- The same exact first-descent time holds on an infinite dyadic ray. -/
theorem ray_4449 (m : Nat) : stoppingTime (2 ^ 2 * m + 4449) 2 :=
  stoppingTime_of_classCertificate certificate_4449 m

/-- Checked base and every prefix for input 4451. -/
theorem certificate_4451 : classCertificateB 4 4451 = true := by
  decide

/-- The same exact first-descent time holds on an infinite dyadic ray. -/
theorem ray_4451 (m : Nat) : stoppingTime (2 ^ 4 * m + 4451) 4 :=
  stoppingTime_of_classCertificate certificate_4451 m

/-- Checked base and every prefix for input 4453. -/
theorem certificate_4453 : classCertificateB 2 4453 = true := by
  decide

/-- The same exact first-descent time holds on an infinite dyadic ray. -/
theorem ray_4453 (m : Nat) : stoppingTime (2 ^ 2 * m + 4453) 2 :=
  stoppingTime_of_classCertificate certificate_4453 m

/-- Checked base and every prefix for input 4455. -/
theorem certificate_4455 : classCertificateB 13 4455 = true := by
  decide

/-- The same exact first-descent time holds on an infinite dyadic ray. -/
theorem ray_4455 (m : Nat) : stoppingTime (2 ^ 13 * m + 4455) 13 :=
  stoppingTime_of_classCertificate certificate_4455 m

/-- Checked base and every prefix for input 4457. -/
theorem certificate_4457 : classCertificateB 2 4457 = true := by
  decide

/-- The same exact first-descent time holds on an infinite dyadic ray. -/
theorem ray_4457 (m : Nat) : stoppingTime (2 ^ 2 * m + 4457) 2 :=
  stoppingTime_of_classCertificate certificate_4457 m

/-- Checked base and every prefix for input 4459. -/
theorem certificate_4459 : classCertificateB 5 4459 = true := by
  decide

/-- The same exact first-descent time holds on an infinite dyadic ray. -/
theorem ray_4459 (m : Nat) : stoppingTime (2 ^ 5 * m + 4459) 5 :=
  stoppingTime_of_classCertificate certificate_4459 m

/-- Checked base and every prefix for input 4461. -/
theorem certificate_4461 : classCertificateB 2 4461 = true := by
  decide

/-- The same exact first-descent time holds on an infinite dyadic ray. -/
theorem ray_4461 (m : Nat) : stoppingTime (2 ^ 2 * m + 4461) 2 :=
  stoppingTime_of_classCertificate certificate_4461 m

/-- Checked base and every prefix for input 4463. -/
theorem certificate_4463 : classCertificateB 10 4463 = true := by
  decide

/-- The same exact first-descent time holds on an infinite dyadic ray. -/
theorem ray_4463 (m : Nat) : stoppingTime (2 ^ 10 * m + 4463) 10 :=
  stoppingTime_of_classCertificate certificate_4463 m

/-- Checked base and every prefix for input 4465. -/
theorem certificate_4465 : classCertificateB 2 4465 = true := by
  decide

/-- The same exact first-descent time holds on an infinite dyadic ray. -/
theorem ray_4465 (m : Nat) : stoppingTime (2 ^ 2 * m + 4465) 2 :=
  stoppingTime_of_classCertificate certificate_4465 m

/-- Checked base and every prefix for input 4467. -/
theorem certificate_4467 : classCertificateB 4 4467 = true := by
  decide

/-- The same exact first-descent time holds on an infinite dyadic ray. -/
theorem ray_4467 (m : Nat) : stoppingTime (2 ^ 4 * m + 4467) 4 :=
  stoppingTime_of_classCertificate certificate_4467 m

/-- Checked base and every prefix for input 4469. -/
theorem certificate_4469 : classCertificateB 2 4469 = true := by
  decide

/-- The same exact first-descent time holds on an infinite dyadic ray. -/
theorem ray_4469 (m : Nat) : stoppingTime (2 ^ 2 * m + 4469) 2 :=
  stoppingTime_of_classCertificate certificate_4469 m

/-- Checked base and every prefix for input 4471. -/
theorem certificate_4471 : classCertificateB 5 4471 = true := by
  decide

/-- The same exact first-descent time holds on an infinite dyadic ray. -/
theorem ray_4471 (m : Nat) : stoppingTime (2 ^ 5 * m + 4471) 5 :=
  stoppingTime_of_classCertificate certificate_4471 m

/-- Checked base and every prefix for input 4473. -/
theorem certificate_4473 : classCertificateB 2 4473 = true := by
  decide

/-- The same exact first-descent time holds on an infinite dyadic ray. -/
theorem ray_4473 (m : Nat) : stoppingTime (2 ^ 2 * m + 4473) 2 :=
  stoppingTime_of_classCertificate certificate_4473 m

/-- Checked base and every prefix for input 4475. -/
theorem certificate_4475 : classCertificateB 8 4475 = true := by
  decide

/-- The same exact first-descent time holds on an infinite dyadic ray. -/
theorem ray_4475 (m : Nat) : stoppingTime (2 ^ 8 * m + 4475) 8 :=
  stoppingTime_of_classCertificate certificate_4475 m

/-- Checked base and every prefix for input 4477. -/
theorem certificate_4477 : classCertificateB 2 4477 = true := by
  decide

/-- The same exact first-descent time holds on an infinite dyadic ray. -/
theorem ray_4477 (m : Nat) : stoppingTime (2 ^ 2 * m + 4477) 2 :=
  stoppingTime_of_classCertificate certificate_4477 m

/-- Checked base and every prefix for input 4479. -/
theorem certificate_4479 : classCertificateB 12 4479 = true := by
  decide

/-- The same exact first-descent time holds on an infinite dyadic ray. -/
theorem ray_4479 (m : Nat) : stoppingTime (2 ^ 12 * m + 4479) 12 :=
  stoppingTime_of_classCertificate certificate_4479 m

/-- Checked base and every prefix for input 4481. -/
theorem certificate_4481 : classCertificateB 2 4481 = true := by
  decide

/-- The same exact first-descent time holds on an infinite dyadic ray. -/
theorem ray_4481 (m : Nat) : stoppingTime (2 ^ 2 * m + 4481) 2 :=
  stoppingTime_of_classCertificate certificate_4481 m

/-- Checked base and every prefix for input 4483. -/
theorem certificate_4483 : classCertificateB 4 4483 = true := by
  decide

/-- The same exact first-descent time holds on an infinite dyadic ray. -/
theorem ray_4483 (m : Nat) : stoppingTime (2 ^ 4 * m + 4483) 4 :=
  stoppingTime_of_classCertificate certificate_4483 m

/-- Checked base and every prefix for input 4485. -/
theorem certificate_4485 : classCertificateB 2 4485 = true := by
  decide

/-- The same exact first-descent time holds on an infinite dyadic ray. -/
theorem ray_4485 (m : Nat) : stoppingTime (2 ^ 2 * m + 4485) 2 :=
  stoppingTime_of_classCertificate certificate_4485 m

/-- Checked base and every prefix for input 4487. -/
theorem certificate_4487 : classCertificateB 7 4487 = true := by
  decide

/-- The same exact first-descent time holds on an infinite dyadic ray. -/
theorem ray_4487 (m : Nat) : stoppingTime (2 ^ 7 * m + 4487) 7 :=
  stoppingTime_of_classCertificate certificate_4487 m

/-- Exhaustive coverage of the odd inputs in this batch, with no gaps. -/
theorem coverage : CertifiedRange 4423 4489 := by
  intro n hlo hhi hodd
  have hn : n = 4423 ∨ n = 4425 ∨ n = 4427 ∨ n = 4429 ∨ n = 4431 ∨ n = 4433 ∨ n = 4435 ∨ n = 4437 ∨ n = 4439 ∨ n = 4441 ∨ n = 4443 ∨ n = 4445 ∨ n = 4447 ∨ n = 4449 ∨ n = 4451 ∨ n = 4453 ∨ n = 4455 ∨ n = 4457 ∨ n = 4459 ∨ n = 4461 ∨ n = 4463 ∨ n = 4465 ∨ n = 4467 ∨ n = 4469 ∨ n = 4471 ∨ n = 4473 ∨ n = 4475 ∨ n = 4477 ∨ n = 4479 ∨ n = 4481 ∨ n = 4483 ∨ n = 4485 ∨ n = 4487 := by omega
  rcases hn with h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h
  · subst n
    exact ⟨21, witness_of_certificate certificate_4423⟩
  · subst n
    exact ⟨2, witness_of_certificate certificate_4425⟩
  · subst n
    exact ⟨5, witness_of_certificate certificate_4427⟩
  · subst n
    exact ⟨2, witness_of_certificate certificate_4429⟩
  · subst n
    exact ⟨8, witness_of_certificate certificate_4431⟩
  · subst n
    exact ⟨2, witness_of_certificate certificate_4433⟩
  · subst n
    exact ⟨4, witness_of_certificate certificate_4435⟩
  · subst n
    exact ⟨2, witness_of_certificate certificate_4437⟩
  · subst n
    exact ⟨5, witness_of_certificate certificate_4439⟩
  · subst n
    exact ⟨2, witness_of_certificate certificate_4441⟩
  · subst n
    exact ⟨10, witness_of_certificate certificate_4443⟩
  · subst n
    exact ⟨2, witness_of_certificate certificate_4445⟩
  · subst n
    exact ⟨8, witness_of_certificate certificate_4447⟩
  · subst n
    exact ⟨2, witness_of_certificate certificate_4449⟩
  · subst n
    exact ⟨4, witness_of_certificate certificate_4451⟩
  · subst n
    exact ⟨2, witness_of_certificate certificate_4453⟩
  · subst n
    exact ⟨13, witness_of_certificate certificate_4455⟩
  · subst n
    exact ⟨2, witness_of_certificate certificate_4457⟩
  · subst n
    exact ⟨5, witness_of_certificate certificate_4459⟩
  · subst n
    exact ⟨2, witness_of_certificate certificate_4461⟩
  · subst n
    exact ⟨10, witness_of_certificate certificate_4463⟩
  · subst n
    exact ⟨2, witness_of_certificate certificate_4465⟩
  · subst n
    exact ⟨4, witness_of_certificate certificate_4467⟩
  · subst n
    exact ⟨2, witness_of_certificate certificate_4469⟩
  · subst n
    exact ⟨5, witness_of_certificate certificate_4471⟩
  · subst n
    exact ⟨2, witness_of_certificate certificate_4473⟩
  · subst n
    exact ⟨8, witness_of_certificate certificate_4475⟩
  · subst n
    exact ⟨2, witness_of_certificate certificate_4477⟩
  · subst n
    exact ⟨12, witness_of_certificate certificate_4479⟩
  · subst n
    exact ⟨2, witness_of_certificate certificate_4481⟩
  · subst n
    exact ⟨4, witness_of_certificate certificate_4483⟩
  · subst n
    exact ⟨2, witness_of_certificate certificate_4485⟩
  · subst n
    exact ⟨7, witness_of_certificate certificate_4487⟩

end Collatz.Research.CoefficientDescent.Batch067
