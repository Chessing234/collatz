import Collatz.Research.CoefficientDescent.Basic

namespace Collatz.Research.CoefficientDescent.Batch022

open FirstDescentClass

set_option maxRecDepth 20000
set_option maxHeartbeats 0

/-- Checked base and every prefix for input 1409. -/
theorem certificate_1409 : classCertificateB 2 1409 = true := by
  decide

/-- The same exact first-descent time holds on an infinite dyadic ray. -/
theorem ray_1409 (m : Nat) : stoppingTime (2 ^ 2 * m + 1409) 2 :=
  stoppingTime_of_classCertificate certificate_1409 m

/-- Checked base and every prefix for input 1411. -/
theorem certificate_1411 : classCertificateB 4 1411 = true := by
  decide

/-- The same exact first-descent time holds on an infinite dyadic ray. -/
theorem ray_1411 (m : Nat) : stoppingTime (2 ^ 4 * m + 1411) 4 :=
  stoppingTime_of_classCertificate certificate_1411 m

/-- Checked base and every prefix for input 1413. -/
theorem certificate_1413 : classCertificateB 2 1413 = true := by
  decide

/-- The same exact first-descent time holds on an infinite dyadic ray. -/
theorem ray_1413 (m : Nat) : stoppingTime (2 ^ 2 * m + 1413) 2 :=
  stoppingTime_of_classCertificate certificate_1413 m

/-- Checked base and every prefix for input 1415. -/
theorem certificate_1415 : classCertificateB 7 1415 = true := by
  decide

/-- The same exact first-descent time holds on an infinite dyadic ray. -/
theorem ray_1415 (m : Nat) : stoppingTime (2 ^ 7 * m + 1415) 7 :=
  stoppingTime_of_classCertificate certificate_1415 m

/-- Checked base and every prefix for input 1417. -/
theorem certificate_1417 : classCertificateB 2 1417 = true := by
  decide

/-- The same exact first-descent time holds on an infinite dyadic ray. -/
theorem ray_1417 (m : Nat) : stoppingTime (2 ^ 2 * m + 1417) 2 :=
  stoppingTime_of_classCertificate certificate_1417 m

/-- Checked base and every prefix for input 1419. -/
theorem certificate_1419 : classCertificateB 5 1419 = true := by
  decide

/-- The same exact first-descent time holds on an infinite dyadic ray. -/
theorem ray_1419 (m : Nat) : stoppingTime (2 ^ 5 * m + 1419) 5 :=
  stoppingTime_of_classCertificate certificate_1419 m

/-- Checked base and every prefix for input 1421. -/
theorem certificate_1421 : classCertificateB 2 1421 = true := by
  decide

/-- The same exact first-descent time holds on an infinite dyadic ray. -/
theorem ray_1421 (m : Nat) : stoppingTime (2 ^ 2 * m + 1421) 2 :=
  stoppingTime_of_classCertificate certificate_1421 m

/-- Checked base and every prefix for input 1423. -/
theorem certificate_1423 : classCertificateB 7 1423 = true := by
  decide

/-- The same exact first-descent time holds on an infinite dyadic ray. -/
theorem ray_1423 (m : Nat) : stoppingTime (2 ^ 7 * m + 1423) 7 :=
  stoppingTime_of_classCertificate certificate_1423 m

/-- Checked base and every prefix for input 1425. -/
theorem certificate_1425 : classCertificateB 2 1425 = true := by
  decide

/-- The same exact first-descent time holds on an infinite dyadic ray. -/
theorem ray_1425 (m : Nat) : stoppingTime (2 ^ 2 * m + 1425) 2 :=
  stoppingTime_of_classCertificate certificate_1425 m

/-- Checked base and every prefix for input 1427. -/
theorem certificate_1427 : classCertificateB 4 1427 = true := by
  decide

/-- The same exact first-descent time holds on an infinite dyadic ray. -/
theorem ray_1427 (m : Nat) : stoppingTime (2 ^ 4 * m + 1427) 4 :=
  stoppingTime_of_classCertificate certificate_1427 m

/-- Checked base and every prefix for input 1429. -/
theorem certificate_1429 : classCertificateB 2 1429 = true := by
  decide

/-- The same exact first-descent time holds on an infinite dyadic ray. -/
theorem ray_1429 (m : Nat) : stoppingTime (2 ^ 2 * m + 1429) 2 :=
  stoppingTime_of_classCertificate certificate_1429 m

/-- Checked base and every prefix for input 1431. -/
theorem certificate_1431 : classCertificateB 5 1431 = true := by
  decide

/-- The same exact first-descent time holds on an infinite dyadic ray. -/
theorem ray_1431 (m : Nat) : stoppingTime (2 ^ 5 * m + 1431) 5 :=
  stoppingTime_of_classCertificate certificate_1431 m

/-- Checked base and every prefix for input 1433. -/
theorem certificate_1433 : classCertificateB 2 1433 = true := by
  decide

/-- The same exact first-descent time holds on an infinite dyadic ray. -/
theorem ray_1433 (m : Nat) : stoppingTime (2 ^ 2 * m + 1433) 2 :=
  stoppingTime_of_classCertificate certificate_1433 m

/-- Checked base and every prefix for input 1435. -/
theorem certificate_1435 : classCertificateB 12 1435 = true := by
  decide

/-- The same exact first-descent time holds on an infinite dyadic ray. -/
theorem ray_1435 (m : Nat) : stoppingTime (2 ^ 12 * m + 1435) 12 :=
  stoppingTime_of_classCertificate certificate_1435 m

/-- Checked base and every prefix for input 1437. -/
theorem certificate_1437 : classCertificateB 2 1437 = true := by
  decide

/-- The same exact first-descent time holds on an infinite dyadic ray. -/
theorem ray_1437 (m : Nat) : stoppingTime (2 ^ 2 * m + 1437) 2 :=
  stoppingTime_of_classCertificate certificate_1437 m

/-- Checked base and every prefix for input 1439. -/
theorem certificate_1439 : classCertificateB 20 1439 = true := by
  decide

/-- The same exact first-descent time holds on an infinite dyadic ray. -/
theorem ray_1439 (m : Nat) : stoppingTime (2 ^ 20 * m + 1439) 20 :=
  stoppingTime_of_classCertificate certificate_1439 m

/-- Checked base and every prefix for input 1441. -/
theorem certificate_1441 : classCertificateB 2 1441 = true := by
  decide

/-- The same exact first-descent time holds on an infinite dyadic ray. -/
theorem ray_1441 (m : Nat) : stoppingTime (2 ^ 2 * m + 1441) 2 :=
  stoppingTime_of_classCertificate certificate_1441 m

/-- Checked base and every prefix for input 1443. -/
theorem certificate_1443 : classCertificateB 4 1443 = true := by
  decide

/-- The same exact first-descent time holds on an infinite dyadic ray. -/
theorem ray_1443 (m : Nat) : stoppingTime (2 ^ 4 * m + 1443) 4 :=
  stoppingTime_of_classCertificate certificate_1443 m

/-- Checked base and every prefix for input 1445. -/
theorem certificate_1445 : classCertificateB 2 1445 = true := by
  decide

/-- The same exact first-descent time holds on an infinite dyadic ray. -/
theorem ray_1445 (m : Nat) : stoppingTime (2 ^ 2 * m + 1445) 2 :=
  stoppingTime_of_classCertificate certificate_1445 m

/-- Checked base and every prefix for input 1447. -/
theorem certificate_1447 : classCertificateB 10 1447 = true := by
  decide

/-- The same exact first-descent time holds on an infinite dyadic ray. -/
theorem ray_1447 (m : Nat) : stoppingTime (2 ^ 10 * m + 1447) 10 :=
  stoppingTime_of_classCertificate certificate_1447 m

/-- Checked base and every prefix for input 1449. -/
theorem certificate_1449 : classCertificateB 2 1449 = true := by
  decide

/-- The same exact first-descent time holds on an infinite dyadic ray. -/
theorem ray_1449 (m : Nat) : stoppingTime (2 ^ 2 * m + 1449) 2 :=
  stoppingTime_of_classCertificate certificate_1449 m

/-- Checked base and every prefix for input 1451. -/
theorem certificate_1451 : classCertificateB 5 1451 = true := by
  decide

/-- The same exact first-descent time holds on an infinite dyadic ray. -/
theorem ray_1451 (m : Nat) : stoppingTime (2 ^ 5 * m + 1451) 5 :=
  stoppingTime_of_classCertificate certificate_1451 m

/-- Checked base and every prefix for input 1453. -/
theorem certificate_1453 : classCertificateB 2 1453 = true := by
  decide

/-- The same exact first-descent time holds on an infinite dyadic ray. -/
theorem ray_1453 (m : Nat) : stoppingTime (2 ^ 2 * m + 1453) 2 :=
  stoppingTime_of_classCertificate certificate_1453 m

/-- Checked base and every prefix for input 1455. -/
theorem certificate_1455 : classCertificateB 8 1455 = true := by
  decide

/-- The same exact first-descent time holds on an infinite dyadic ray. -/
theorem ray_1455 (m : Nat) : stoppingTime (2 ^ 8 * m + 1455) 8 :=
  stoppingTime_of_classCertificate certificate_1455 m

/-- Checked base and every prefix for input 1457. -/
theorem certificate_1457 : classCertificateB 2 1457 = true := by
  decide

/-- The same exact first-descent time holds on an infinite dyadic ray. -/
theorem ray_1457 (m : Nat) : stoppingTime (2 ^ 2 * m + 1457) 2 :=
  stoppingTime_of_classCertificate certificate_1457 m

/-- Checked base and every prefix for input 1459. -/
theorem certificate_1459 : classCertificateB 4 1459 = true := by
  decide

/-- The same exact first-descent time holds on an infinite dyadic ray. -/
theorem ray_1459 (m : Nat) : stoppingTime (2 ^ 4 * m + 1459) 4 :=
  stoppingTime_of_classCertificate certificate_1459 m

/-- Checked base and every prefix for input 1461. -/
theorem certificate_1461 : classCertificateB 2 1461 = true := by
  decide

/-- The same exact first-descent time holds on an infinite dyadic ray. -/
theorem ray_1461 (m : Nat) : stoppingTime (2 ^ 2 * m + 1461) 2 :=
  stoppingTime_of_classCertificate certificate_1461 m

/-- Checked base and every prefix for input 1463. -/
theorem certificate_1463 : classCertificateB 5 1463 = true := by
  decide

/-- The same exact first-descent time holds on an infinite dyadic ray. -/
theorem ray_1463 (m : Nat) : stoppingTime (2 ^ 5 * m + 1463) 5 :=
  stoppingTime_of_classCertificate certificate_1463 m

/-- Checked base and every prefix for input 1465. -/
theorem certificate_1465 : classCertificateB 2 1465 = true := by
  decide

/-- The same exact first-descent time holds on an infinite dyadic ray. -/
theorem ray_1465 (m : Nat) : stoppingTime (2 ^ 2 * m + 1465) 2 :=
  stoppingTime_of_classCertificate certificate_1465 m

/-- Checked base and every prefix for input 1467. -/
theorem certificate_1467 : classCertificateB 7 1467 = true := by
  decide

/-- The same exact first-descent time holds on an infinite dyadic ray. -/
theorem ray_1467 (m : Nat) : stoppingTime (2 ^ 7 * m + 1467) 7 :=
  stoppingTime_of_classCertificate certificate_1467 m

/-- Checked base and every prefix for input 1469. -/
theorem certificate_1469 : classCertificateB 2 1469 = true := by
  decide

/-- The same exact first-descent time holds on an infinite dyadic ray. -/
theorem ray_1469 (m : Nat) : stoppingTime (2 ^ 2 * m + 1469) 2 :=
  stoppingTime_of_classCertificate certificate_1469 m

/-- Checked base and every prefix for input 1471. -/
theorem certificate_1471 : classCertificateB 31 1471 = true := by
  decide

/-- The same exact first-descent time holds on an infinite dyadic ray. -/
theorem ray_1471 (m : Nat) : stoppingTime (2 ^ 31 * m + 1471) 31 :=
  stoppingTime_of_classCertificate certificate_1471 m

/-- Checked base and every prefix for input 1473. -/
theorem certificate_1473 : classCertificateB 2 1473 = true := by
  decide

/-- The same exact first-descent time holds on an infinite dyadic ray. -/
theorem ray_1473 (m : Nat) : stoppingTime (2 ^ 2 * m + 1473) 2 :=
  stoppingTime_of_classCertificate certificate_1473 m

/-- Exhaustive coverage of the odd inputs in this batch, with no gaps. -/
theorem coverage : CertifiedRange 1409 1475 := by
  intro n hlo hhi hodd
  have hn : n = 1409 ∨ n = 1411 ∨ n = 1413 ∨ n = 1415 ∨ n = 1417 ∨ n = 1419 ∨ n = 1421 ∨ n = 1423 ∨ n = 1425 ∨ n = 1427 ∨ n = 1429 ∨ n = 1431 ∨ n = 1433 ∨ n = 1435 ∨ n = 1437 ∨ n = 1439 ∨ n = 1441 ∨ n = 1443 ∨ n = 1445 ∨ n = 1447 ∨ n = 1449 ∨ n = 1451 ∨ n = 1453 ∨ n = 1455 ∨ n = 1457 ∨ n = 1459 ∨ n = 1461 ∨ n = 1463 ∨ n = 1465 ∨ n = 1467 ∨ n = 1469 ∨ n = 1471 ∨ n = 1473 := by omega
  rcases hn with h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h
  · subst n
    exact ⟨2, witness_of_certificate certificate_1409⟩
  · subst n
    exact ⟨4, witness_of_certificate certificate_1411⟩
  · subst n
    exact ⟨2, witness_of_certificate certificate_1413⟩
  · subst n
    exact ⟨7, witness_of_certificate certificate_1415⟩
  · subst n
    exact ⟨2, witness_of_certificate certificate_1417⟩
  · subst n
    exact ⟨5, witness_of_certificate certificate_1419⟩
  · subst n
    exact ⟨2, witness_of_certificate certificate_1421⟩
  · subst n
    exact ⟨7, witness_of_certificate certificate_1423⟩
  · subst n
    exact ⟨2, witness_of_certificate certificate_1425⟩
  · subst n
    exact ⟨4, witness_of_certificate certificate_1427⟩
  · subst n
    exact ⟨2, witness_of_certificate certificate_1429⟩
  · subst n
    exact ⟨5, witness_of_certificate certificate_1431⟩
  · subst n
    exact ⟨2, witness_of_certificate certificate_1433⟩
  · subst n
    exact ⟨12, witness_of_certificate certificate_1435⟩
  · subst n
    exact ⟨2, witness_of_certificate certificate_1437⟩
  · subst n
    exact ⟨20, witness_of_certificate certificate_1439⟩
  · subst n
    exact ⟨2, witness_of_certificate certificate_1441⟩
  · subst n
    exact ⟨4, witness_of_certificate certificate_1443⟩
  · subst n
    exact ⟨2, witness_of_certificate certificate_1445⟩
  · subst n
    exact ⟨10, witness_of_certificate certificate_1447⟩
  · subst n
    exact ⟨2, witness_of_certificate certificate_1449⟩
  · subst n
    exact ⟨5, witness_of_certificate certificate_1451⟩
  · subst n
    exact ⟨2, witness_of_certificate certificate_1453⟩
  · subst n
    exact ⟨8, witness_of_certificate certificate_1455⟩
  · subst n
    exact ⟨2, witness_of_certificate certificate_1457⟩
  · subst n
    exact ⟨4, witness_of_certificate certificate_1459⟩
  · subst n
    exact ⟨2, witness_of_certificate certificate_1461⟩
  · subst n
    exact ⟨5, witness_of_certificate certificate_1463⟩
  · subst n
    exact ⟨2, witness_of_certificate certificate_1465⟩
  · subst n
    exact ⟨7, witness_of_certificate certificate_1467⟩
  · subst n
    exact ⟨2, witness_of_certificate certificate_1469⟩
  · subst n
    exact ⟨31, witness_of_certificate certificate_1471⟩
  · subst n
    exact ⟨2, witness_of_certificate certificate_1473⟩

end Collatz.Research.CoefficientDescent.Batch022
