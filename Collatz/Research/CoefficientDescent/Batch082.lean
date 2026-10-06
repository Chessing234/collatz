import Collatz.Research.CoefficientDescent.Basic

namespace Collatz.Research.CoefficientDescent.Batch082

open FirstDescentClass

set_option maxRecDepth 20000
set_option maxHeartbeats 0

/-- Checked base and every prefix for input 5427. -/
theorem certificate_5427 : classCertificateB 4 5427 = true := by
  decide

/-- The same exact first-descent time holds on an infinite dyadic ray. -/
theorem ray_5427 (m : Nat) : stoppingTime (2 ^ 4 * m + 5427) 4 :=
  stoppingTime_of_classCertificate certificate_5427 m

/-- Checked base and every prefix for input 5429. -/
theorem certificate_5429 : classCertificateB 2 5429 = true := by
  decide

/-- The same exact first-descent time holds on an infinite dyadic ray. -/
theorem ray_5429 (m : Nat) : stoppingTime (2 ^ 2 * m + 5429) 2 :=
  stoppingTime_of_classCertificate certificate_5429 m

/-- Checked base and every prefix for input 5431. -/
theorem certificate_5431 : classCertificateB 5 5431 = true := by
  decide

/-- The same exact first-descent time holds on an infinite dyadic ray. -/
theorem ray_5431 (m : Nat) : stoppingTime (2 ^ 5 * m + 5431) 5 :=
  stoppingTime_of_classCertificate certificate_5431 m

/-- Checked base and every prefix for input 5433. -/
theorem certificate_5433 : classCertificateB 2 5433 = true := by
  decide

/-- The same exact first-descent time holds on an infinite dyadic ray. -/
theorem ray_5433 (m : Nat) : stoppingTime (2 ^ 2 * m + 5433) 2 :=
  stoppingTime_of_classCertificate certificate_5433 m

/-- Checked base and every prefix for input 5435. -/
theorem certificate_5435 : classCertificateB 7 5435 = true := by
  decide

/-- The same exact first-descent time holds on an infinite dyadic ray. -/
theorem ray_5435 (m : Nat) : stoppingTime (2 ^ 7 * m + 5435) 7 :=
  stoppingTime_of_classCertificate certificate_5435 m

/-- Checked base and every prefix for input 5437. -/
theorem certificate_5437 : classCertificateB 2 5437 = true := by
  decide

/-- The same exact first-descent time holds on an infinite dyadic ray. -/
theorem ray_5437 (m : Nat) : stoppingTime (2 ^ 2 * m + 5437) 2 :=
  stoppingTime_of_classCertificate certificate_5437 m

/-- Checked base and every prefix for input 5439. -/
theorem certificate_5439 : classCertificateB 13 5439 = true := by
  decide

/-- The same exact first-descent time holds on an infinite dyadic ray. -/
theorem ray_5439 (m : Nat) : stoppingTime (2 ^ 13 * m + 5439) 13 :=
  stoppingTime_of_classCertificate certificate_5439 m

/-- Checked base and every prefix for input 5441. -/
theorem certificate_5441 : classCertificateB 2 5441 = true := by
  decide

/-- The same exact first-descent time holds on an infinite dyadic ray. -/
theorem ray_5441 (m : Nat) : stoppingTime (2 ^ 2 * m + 5441) 2 :=
  stoppingTime_of_classCertificate certificate_5441 m

/-- Checked base and every prefix for input 5443. -/
theorem certificate_5443 : classCertificateB 4 5443 = true := by
  decide

/-- The same exact first-descent time holds on an infinite dyadic ray. -/
theorem ray_5443 (m : Nat) : stoppingTime (2 ^ 4 * m + 5443) 4 :=
  stoppingTime_of_classCertificate certificate_5443 m

/-- Checked base and every prefix for input 5445. -/
theorem certificate_5445 : classCertificateB 2 5445 = true := by
  decide

/-- The same exact first-descent time holds on an infinite dyadic ray. -/
theorem ray_5445 (m : Nat) : stoppingTime (2 ^ 2 * m + 5445) 2 :=
  stoppingTime_of_classCertificate certificate_5445 m

/-- Checked base and every prefix for input 5447. -/
theorem certificate_5447 : classCertificateB 27 5447 = true := by
  decide

/-- The same exact first-descent time holds on an infinite dyadic ray. -/
theorem ray_5447 (m : Nat) : stoppingTime (2 ^ 27 * m + 5447) 27 :=
  stoppingTime_of_classCertificate certificate_5447 m

/-- Checked base and every prefix for input 5449. -/
theorem certificate_5449 : classCertificateB 2 5449 = true := by
  decide

/-- The same exact first-descent time holds on an infinite dyadic ray. -/
theorem ray_5449 (m : Nat) : stoppingTime (2 ^ 2 * m + 5449) 2 :=
  stoppingTime_of_classCertificate certificate_5449 m

/-- Checked base and every prefix for input 5451. -/
theorem certificate_5451 : classCertificateB 5 5451 = true := by
  decide

/-- The same exact first-descent time holds on an infinite dyadic ray. -/
theorem ray_5451 (m : Nat) : stoppingTime (2 ^ 5 * m + 5451) 5 :=
  stoppingTime_of_classCertificate certificate_5451 m

/-- Checked base and every prefix for input 5453. -/
theorem certificate_5453 : classCertificateB 2 5453 = true := by
  decide

/-- The same exact first-descent time holds on an infinite dyadic ray. -/
theorem ray_5453 (m : Nat) : stoppingTime (2 ^ 2 * m + 5453) 2 :=
  stoppingTime_of_classCertificate certificate_5453 m

/-- Checked base and every prefix for input 5455. -/
theorem certificate_5455 : classCertificateB 8 5455 = true := by
  decide

/-- The same exact first-descent time holds on an infinite dyadic ray. -/
theorem ray_5455 (m : Nat) : stoppingTime (2 ^ 8 * m + 5455) 8 :=
  stoppingTime_of_classCertificate certificate_5455 m

/-- Checked base and every prefix for input 5457. -/
theorem certificate_5457 : classCertificateB 2 5457 = true := by
  decide

/-- The same exact first-descent time holds on an infinite dyadic ray. -/
theorem ray_5457 (m : Nat) : stoppingTime (2 ^ 2 * m + 5457) 2 :=
  stoppingTime_of_classCertificate certificate_5457 m

/-- Checked base and every prefix for input 5459. -/
theorem certificate_5459 : classCertificateB 4 5459 = true := by
  decide

/-- The same exact first-descent time holds on an infinite dyadic ray. -/
theorem ray_5459 (m : Nat) : stoppingTime (2 ^ 4 * m + 5459) 4 :=
  stoppingTime_of_classCertificate certificate_5459 m

/-- Checked base and every prefix for input 5461. -/
theorem certificate_5461 : classCertificateB 2 5461 = true := by
  decide

/-- The same exact first-descent time holds on an infinite dyadic ray. -/
theorem ray_5461 (m : Nat) : stoppingTime (2 ^ 2 * m + 5461) 2 :=
  stoppingTime_of_classCertificate certificate_5461 m

/-- Checked base and every prefix for input 5463. -/
theorem certificate_5463 : classCertificateB 5 5463 = true := by
  decide

/-- The same exact first-descent time holds on an infinite dyadic ray. -/
theorem ray_5463 (m : Nat) : stoppingTime (2 ^ 5 * m + 5463) 5 :=
  stoppingTime_of_classCertificate certificate_5463 m

/-- Checked base and every prefix for input 5465. -/
theorem certificate_5465 : classCertificateB 2 5465 = true := by
  decide

/-- The same exact first-descent time holds on an infinite dyadic ray. -/
theorem ray_5465 (m : Nat) : stoppingTime (2 ^ 2 * m + 5465) 2 :=
  stoppingTime_of_classCertificate certificate_5465 m

/-- Checked base and every prefix for input 5467. -/
theorem certificate_5467 : classCertificateB 10 5467 = true := by
  decide

/-- The same exact first-descent time holds on an infinite dyadic ray. -/
theorem ray_5467 (m : Nat) : stoppingTime (2 ^ 10 * m + 5467) 10 :=
  stoppingTime_of_classCertificate certificate_5467 m

/-- Checked base and every prefix for input 5469. -/
theorem certificate_5469 : classCertificateB 2 5469 = true := by
  decide

/-- The same exact first-descent time holds on an infinite dyadic ray. -/
theorem ray_5469 (m : Nat) : stoppingTime (2 ^ 2 * m + 5469) 2 :=
  stoppingTime_of_classCertificate certificate_5469 m

/-- Checked base and every prefix for input 5471. -/
theorem certificate_5471 : classCertificateB 8 5471 = true := by
  decide

/-- The same exact first-descent time holds on an infinite dyadic ray. -/
theorem ray_5471 (m : Nat) : stoppingTime (2 ^ 8 * m + 5471) 8 :=
  stoppingTime_of_classCertificate certificate_5471 m

/-- Checked base and every prefix for input 5473. -/
theorem certificate_5473 : classCertificateB 2 5473 = true := by
  decide

/-- The same exact first-descent time holds on an infinite dyadic ray. -/
theorem ray_5473 (m : Nat) : stoppingTime (2 ^ 2 * m + 5473) 2 :=
  stoppingTime_of_classCertificate certificate_5473 m

/-- Checked base and every prefix for input 5475. -/
theorem certificate_5475 : classCertificateB 4 5475 = true := by
  decide

/-- The same exact first-descent time holds on an infinite dyadic ray. -/
theorem ray_5475 (m : Nat) : stoppingTime (2 ^ 4 * m + 5475) 4 :=
  stoppingTime_of_classCertificate certificate_5475 m

/-- Checked base and every prefix for input 5477. -/
theorem certificate_5477 : classCertificateB 2 5477 = true := by
  decide

/-- The same exact first-descent time holds on an infinite dyadic ray. -/
theorem ray_5477 (m : Nat) : stoppingTime (2 ^ 2 * m + 5477) 2 :=
  stoppingTime_of_classCertificate certificate_5477 m

/-- Checked base and every prefix for input 5479. -/
theorem certificate_5479 : classCertificateB 32 5479 = true := by
  decide

/-- The same exact first-descent time holds on an infinite dyadic ray. -/
theorem ray_5479 (m : Nat) : stoppingTime (2 ^ 32 * m + 5479) 32 :=
  stoppingTime_of_classCertificate certificate_5479 m

/-- Checked base and every prefix for input 5481. -/
theorem certificate_5481 : classCertificateB 2 5481 = true := by
  decide

/-- The same exact first-descent time holds on an infinite dyadic ray. -/
theorem ray_5481 (m : Nat) : stoppingTime (2 ^ 2 * m + 5481) 2 :=
  stoppingTime_of_classCertificate certificate_5481 m

/-- Checked base and every prefix for input 5483. -/
theorem certificate_5483 : classCertificateB 5 5483 = true := by
  decide

/-- The same exact first-descent time holds on an infinite dyadic ray. -/
theorem ray_5483 (m : Nat) : stoppingTime (2 ^ 5 * m + 5483) 5 :=
  stoppingTime_of_classCertificate certificate_5483 m

/-- Checked base and every prefix for input 5485. -/
theorem certificate_5485 : classCertificateB 2 5485 = true := by
  decide

/-- The same exact first-descent time holds on an infinite dyadic ray. -/
theorem ray_5485 (m : Nat) : stoppingTime (2 ^ 2 * m + 5485) 2 :=
  stoppingTime_of_classCertificate certificate_5485 m

/-- Checked base and every prefix for input 5487. -/
theorem certificate_5487 : classCertificateB 10 5487 = true := by
  decide

/-- The same exact first-descent time holds on an infinite dyadic ray. -/
theorem ray_5487 (m : Nat) : stoppingTime (2 ^ 10 * m + 5487) 10 :=
  stoppingTime_of_classCertificate certificate_5487 m

/-- Checked base and every prefix for input 5489. -/
theorem certificate_5489 : classCertificateB 2 5489 = true := by
  decide

/-- The same exact first-descent time holds on an infinite dyadic ray. -/
theorem ray_5489 (m : Nat) : stoppingTime (2 ^ 2 * m + 5489) 2 :=
  stoppingTime_of_classCertificate certificate_5489 m

/-- Checked base and every prefix for input 5491. -/
theorem certificate_5491 : classCertificateB 4 5491 = true := by
  decide

/-- The same exact first-descent time holds on an infinite dyadic ray. -/
theorem ray_5491 (m : Nat) : stoppingTime (2 ^ 4 * m + 5491) 4 :=
  stoppingTime_of_classCertificate certificate_5491 m

/-- Checked base and every prefix for input 5493. -/
theorem certificate_5493 : classCertificateB 2 5493 = true := by
  decide

/-- The same exact first-descent time holds on an infinite dyadic ray. -/
theorem ray_5493 (m : Nat) : stoppingTime (2 ^ 2 * m + 5493) 2 :=
  stoppingTime_of_classCertificate certificate_5493 m

/-- Exhaustive coverage of the odd inputs in this batch, with no gaps. -/
theorem coverage : CertifiedRange 5427 5495 := by
  intro n hlo hhi hodd
  have hn : n = 5427 ∨ n = 5429 ∨ n = 5431 ∨ n = 5433 ∨ n = 5435 ∨ n = 5437 ∨ n = 5439 ∨ n = 5441 ∨ n = 5443 ∨ n = 5445 ∨ n = 5447 ∨ n = 5449 ∨ n = 5451 ∨ n = 5453 ∨ n = 5455 ∨ n = 5457 ∨ n = 5459 ∨ n = 5461 ∨ n = 5463 ∨ n = 5465 ∨ n = 5467 ∨ n = 5469 ∨ n = 5471 ∨ n = 5473 ∨ n = 5475 ∨ n = 5477 ∨ n = 5479 ∨ n = 5481 ∨ n = 5483 ∨ n = 5485 ∨ n = 5487 ∨ n = 5489 ∨ n = 5491 ∨ n = 5493 := by omega
  rcases hn with h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h
  · subst n
    exact ⟨4, witness_of_certificate certificate_5427⟩
  · subst n
    exact ⟨2, witness_of_certificate certificate_5429⟩
  · subst n
    exact ⟨5, witness_of_certificate certificate_5431⟩
  · subst n
    exact ⟨2, witness_of_certificate certificate_5433⟩
  · subst n
    exact ⟨7, witness_of_certificate certificate_5435⟩
  · subst n
    exact ⟨2, witness_of_certificate certificate_5437⟩
  · subst n
    exact ⟨13, witness_of_certificate certificate_5439⟩
  · subst n
    exact ⟨2, witness_of_certificate certificate_5441⟩
  · subst n
    exact ⟨4, witness_of_certificate certificate_5443⟩
  · subst n
    exact ⟨2, witness_of_certificate certificate_5445⟩
  · subst n
    exact ⟨27, witness_of_certificate certificate_5447⟩
  · subst n
    exact ⟨2, witness_of_certificate certificate_5449⟩
  · subst n
    exact ⟨5, witness_of_certificate certificate_5451⟩
  · subst n
    exact ⟨2, witness_of_certificate certificate_5453⟩
  · subst n
    exact ⟨8, witness_of_certificate certificate_5455⟩
  · subst n
    exact ⟨2, witness_of_certificate certificate_5457⟩
  · subst n
    exact ⟨4, witness_of_certificate certificate_5459⟩
  · subst n
    exact ⟨2, witness_of_certificate certificate_5461⟩
  · subst n
    exact ⟨5, witness_of_certificate certificate_5463⟩
  · subst n
    exact ⟨2, witness_of_certificate certificate_5465⟩
  · subst n
    exact ⟨10, witness_of_certificate certificate_5467⟩
  · subst n
    exact ⟨2, witness_of_certificate certificate_5469⟩
  · subst n
    exact ⟨8, witness_of_certificate certificate_5471⟩
  · subst n
    exact ⟨2, witness_of_certificate certificate_5473⟩
  · subst n
    exact ⟨4, witness_of_certificate certificate_5475⟩
  · subst n
    exact ⟨2, witness_of_certificate certificate_5477⟩
  · subst n
    exact ⟨32, witness_of_certificate certificate_5479⟩
  · subst n
    exact ⟨2, witness_of_certificate certificate_5481⟩
  · subst n
    exact ⟨5, witness_of_certificate certificate_5483⟩
  · subst n
    exact ⟨2, witness_of_certificate certificate_5485⟩
  · subst n
    exact ⟨10, witness_of_certificate certificate_5487⟩
  · subst n
    exact ⟨2, witness_of_certificate certificate_5489⟩
  · subst n
    exact ⟨4, witness_of_certificate certificate_5491⟩
  · subst n
    exact ⟨2, witness_of_certificate certificate_5493⟩

end Collatz.Research.CoefficientDescent.Batch082
