import Collatz.Research.CoefficientDescent.Basic

namespace Collatz.Research.CoefficientDescent.Batch023

open FirstDescentClass

set_option maxRecDepth 20000
set_option maxHeartbeats 0

/-- Checked base and every prefix for input 1475. -/
theorem certificate_1475 : classCertificateB 4 1475 = true := by
  decide

/-- The same exact first-descent time holds on an infinite dyadic ray. -/
theorem ray_1475 (m : Nat) : stoppingTime (2 ^ 4 * m + 1475) 4 :=
  stoppingTime_of_classCertificate certificate_1475 m

/-- Checked base and every prefix for input 1477. -/
theorem certificate_1477 : classCertificateB 2 1477 = true := by
  decide

/-- The same exact first-descent time holds on an infinite dyadic ray. -/
theorem ray_1477 (m : Nat) : stoppingTime (2 ^ 2 * m + 1477) 2 :=
  stoppingTime_of_classCertificate certificate_1477 m

/-- Checked base and every prefix for input 1479. -/
theorem certificate_1479 : classCertificateB 8 1479 = true := by
  decide

/-- The same exact first-descent time holds on an infinite dyadic ray. -/
theorem ray_1479 (m : Nat) : stoppingTime (2 ^ 8 * m + 1479) 8 :=
  stoppingTime_of_classCertificate certificate_1479 m

/-- Checked base and every prefix for input 1481. -/
theorem certificate_1481 : classCertificateB 2 1481 = true := by
  decide

/-- The same exact first-descent time holds on an infinite dyadic ray. -/
theorem ray_1481 (m : Nat) : stoppingTime (2 ^ 2 * m + 1481) 2 :=
  stoppingTime_of_classCertificate certificate_1481 m

/-- Checked base and every prefix for input 1483. -/
theorem certificate_1483 : classCertificateB 5 1483 = true := by
  decide

/-- The same exact first-descent time holds on an infinite dyadic ray. -/
theorem ray_1483 (m : Nat) : stoppingTime (2 ^ 5 * m + 1483) 5 :=
  stoppingTime_of_classCertificate certificate_1483 m

/-- Checked base and every prefix for input 1485. -/
theorem certificate_1485 : classCertificateB 2 1485 = true := by
  decide

/-- The same exact first-descent time holds on an infinite dyadic ray. -/
theorem ray_1485 (m : Nat) : stoppingTime (2 ^ 2 * m + 1485) 2 :=
  stoppingTime_of_classCertificate certificate_1485 m

/-- Checked base and every prefix for input 1487. -/
theorem certificate_1487 : classCertificateB 24 1487 = true := by
  decide

/-- The same exact first-descent time holds on an infinite dyadic ray. -/
theorem ray_1487 (m : Nat) : stoppingTime (2 ^ 24 * m + 1487) 24 :=
  stoppingTime_of_classCertificate certificate_1487 m

/-- Checked base and every prefix for input 1489. -/
theorem certificate_1489 : classCertificateB 2 1489 = true := by
  decide

/-- The same exact first-descent time holds on an infinite dyadic ray. -/
theorem ray_1489 (m : Nat) : stoppingTime (2 ^ 2 * m + 1489) 2 :=
  stoppingTime_of_classCertificate certificate_1489 m

/-- Checked base and every prefix for input 1491. -/
theorem certificate_1491 : classCertificateB 4 1491 = true := by
  decide

/-- The same exact first-descent time holds on an infinite dyadic ray. -/
theorem ray_1491 (m : Nat) : stoppingTime (2 ^ 4 * m + 1491) 4 :=
  stoppingTime_of_classCertificate certificate_1491 m

/-- Checked base and every prefix for input 1493. -/
theorem certificate_1493 : classCertificateB 2 1493 = true := by
  decide

/-- The same exact first-descent time holds on an infinite dyadic ray. -/
theorem ray_1493 (m : Nat) : stoppingTime (2 ^ 2 * m + 1493) 2 :=
  stoppingTime_of_classCertificate certificate_1493 m

/-- Checked base and every prefix for input 1495. -/
theorem certificate_1495 : classCertificateB 5 1495 = true := by
  decide

/-- The same exact first-descent time holds on an infinite dyadic ray. -/
theorem ray_1495 (m : Nat) : stoppingTime (2 ^ 5 * m + 1495) 5 :=
  stoppingTime_of_classCertificate certificate_1495 m

/-- Checked base and every prefix for input 1497. -/
theorem certificate_1497 : classCertificateB 2 1497 = true := by
  decide

/-- The same exact first-descent time holds on an infinite dyadic ray. -/
theorem ray_1497 (m : Nat) : stoppingTime (2 ^ 2 * m + 1497) 2 :=
  stoppingTime_of_classCertificate certificate_1497 m

/-- Checked base and every prefix for input 1499. -/
theorem certificate_1499 : classCertificateB 8 1499 = true := by
  decide

/-- The same exact first-descent time holds on an infinite dyadic ray. -/
theorem ray_1499 (m : Nat) : stoppingTime (2 ^ 8 * m + 1499) 8 :=
  stoppingTime_of_classCertificate certificate_1499 m

/-- Checked base and every prefix for input 1501. -/
theorem certificate_1501 : classCertificateB 2 1501 = true := by
  decide

/-- The same exact first-descent time holds on an infinite dyadic ray. -/
theorem ray_1501 (m : Nat) : stoppingTime (2 ^ 2 * m + 1501) 2 :=
  stoppingTime_of_classCertificate certificate_1501 m

/-- Checked base and every prefix for input 1503. -/
theorem certificate_1503 : classCertificateB 21 1503 = true := by
  decide

/-- The same exact first-descent time holds on an infinite dyadic ray. -/
theorem ray_1503 (m : Nat) : stoppingTime (2 ^ 21 * m + 1503) 21 :=
  stoppingTime_of_classCertificate certificate_1503 m

/-- Checked base and every prefix for input 1505. -/
theorem certificate_1505 : classCertificateB 2 1505 = true := by
  decide

/-- The same exact first-descent time holds on an infinite dyadic ray. -/
theorem ray_1505 (m : Nat) : stoppingTime (2 ^ 2 * m + 1505) 2 :=
  stoppingTime_of_classCertificate certificate_1505 m

/-- Checked base and every prefix for input 1507. -/
theorem certificate_1507 : classCertificateB 4 1507 = true := by
  decide

/-- The same exact first-descent time holds on an infinite dyadic ray. -/
theorem ray_1507 (m : Nat) : stoppingTime (2 ^ 4 * m + 1507) 4 :=
  stoppingTime_of_classCertificate certificate_1507 m

/-- Checked base and every prefix for input 1509. -/
theorem certificate_1509 : classCertificateB 2 1509 = true := by
  decide

/-- The same exact first-descent time holds on an infinite dyadic ray. -/
theorem ray_1509 (m : Nat) : stoppingTime (2 ^ 2 * m + 1509) 2 :=
  stoppingTime_of_classCertificate certificate_1509 m

/-- Checked base and every prefix for input 1511. -/
theorem certificate_1511 : classCertificateB 20 1511 = true := by
  decide

/-- The same exact first-descent time holds on an infinite dyadic ray. -/
theorem ray_1511 (m : Nat) : stoppingTime (2 ^ 20 * m + 1511) 20 :=
  stoppingTime_of_classCertificate certificate_1511 m

/-- Checked base and every prefix for input 1513. -/
theorem certificate_1513 : classCertificateB 2 1513 = true := by
  decide

/-- The same exact first-descent time holds on an infinite dyadic ray. -/
theorem ray_1513 (m : Nat) : stoppingTime (2 ^ 2 * m + 1513) 2 :=
  stoppingTime_of_classCertificate certificate_1513 m

/-- Checked base and every prefix for input 1515. -/
theorem certificate_1515 : classCertificateB 5 1515 = true := by
  decide

/-- The same exact first-descent time holds on an infinite dyadic ray. -/
theorem ray_1515 (m : Nat) : stoppingTime (2 ^ 5 * m + 1515) 5 :=
  stoppingTime_of_classCertificate certificate_1515 m

/-- Checked base and every prefix for input 1517. -/
theorem certificate_1517 : classCertificateB 2 1517 = true := by
  decide

/-- The same exact first-descent time holds on an infinite dyadic ray. -/
theorem ray_1517 (m : Nat) : stoppingTime (2 ^ 2 * m + 1517) 2 :=
  stoppingTime_of_classCertificate certificate_1517 m

/-- Checked base and every prefix for input 1519. -/
theorem certificate_1519 : classCertificateB 16 1519 = true := by
  decide

/-- The same exact first-descent time holds on an infinite dyadic ray. -/
theorem ray_1519 (m : Nat) : stoppingTime (2 ^ 16 * m + 1519) 16 :=
  stoppingTime_of_classCertificate certificate_1519 m

/-- Checked base and every prefix for input 1521. -/
theorem certificate_1521 : classCertificateB 2 1521 = true := by
  decide

/-- The same exact first-descent time holds on an infinite dyadic ray. -/
theorem ray_1521 (m : Nat) : stoppingTime (2 ^ 2 * m + 1521) 2 :=
  stoppingTime_of_classCertificate certificate_1521 m

/-- Checked base and every prefix for input 1523. -/
theorem certificate_1523 : classCertificateB 4 1523 = true := by
  decide

/-- The same exact first-descent time holds on an infinite dyadic ray. -/
theorem ray_1523 (m : Nat) : stoppingTime (2 ^ 4 * m + 1523) 4 :=
  stoppingTime_of_classCertificate certificate_1523 m

/-- Checked base and every prefix for input 1525. -/
theorem certificate_1525 : classCertificateB 2 1525 = true := by
  decide

/-- The same exact first-descent time holds on an infinite dyadic ray. -/
theorem ray_1525 (m : Nat) : stoppingTime (2 ^ 2 * m + 1525) 2 :=
  stoppingTime_of_classCertificate certificate_1525 m

/-- Checked base and every prefix for input 1527. -/
theorem certificate_1527 : classCertificateB 5 1527 = true := by
  decide

/-- The same exact first-descent time holds on an infinite dyadic ray. -/
theorem ray_1527 (m : Nat) : stoppingTime (2 ^ 5 * m + 1527) 5 :=
  stoppingTime_of_classCertificate certificate_1527 m

/-- Checked base and every prefix for input 1529. -/
theorem certificate_1529 : classCertificateB 2 1529 = true := by
  decide

/-- The same exact first-descent time holds on an infinite dyadic ray. -/
theorem ray_1529 (m : Nat) : stoppingTime (2 ^ 2 * m + 1529) 2 :=
  stoppingTime_of_classCertificate certificate_1529 m

/-- Checked base and every prefix for input 1531. -/
theorem certificate_1531 : classCertificateB 10 1531 = true := by
  decide

/-- The same exact first-descent time holds on an infinite dyadic ray. -/
theorem ray_1531 (m : Nat) : stoppingTime (2 ^ 10 * m + 1531) 10 :=
  stoppingTime_of_classCertificate certificate_1531 m

/-- Checked base and every prefix for input 1533. -/
theorem certificate_1533 : classCertificateB 2 1533 = true := by
  decide

/-- The same exact first-descent time holds on an infinite dyadic ray. -/
theorem ray_1533 (m : Nat) : stoppingTime (2 ^ 2 * m + 1533) 2 :=
  stoppingTime_of_classCertificate certificate_1533 m

/-- Checked base and every prefix for input 1535. -/
theorem certificate_1535 : classCertificateB 16 1535 = true := by
  decide

/-- The same exact first-descent time holds on an infinite dyadic ray. -/
theorem ray_1535 (m : Nat) : stoppingTime (2 ^ 16 * m + 1535) 16 :=
  stoppingTime_of_classCertificate certificate_1535 m

/-- Checked base and every prefix for input 1537. -/
theorem certificate_1537 : classCertificateB 2 1537 = true := by
  decide

/-- The same exact first-descent time holds on an infinite dyadic ray. -/
theorem ray_1537 (m : Nat) : stoppingTime (2 ^ 2 * m + 1537) 2 :=
  stoppingTime_of_classCertificate certificate_1537 m

/-- Checked base and every prefix for input 1539. -/
theorem certificate_1539 : classCertificateB 4 1539 = true := by
  decide

/-- The same exact first-descent time holds on an infinite dyadic ray. -/
theorem ray_1539 (m : Nat) : stoppingTime (2 ^ 4 * m + 1539) 4 :=
  stoppingTime_of_classCertificate certificate_1539 m

/-- Checked base and every prefix for input 1541. -/
theorem certificate_1541 : classCertificateB 2 1541 = true := by
  decide

/-- The same exact first-descent time holds on an infinite dyadic ray. -/
theorem ray_1541 (m : Nat) : stoppingTime (2 ^ 2 * m + 1541) 2 :=
  stoppingTime_of_classCertificate certificate_1541 m

/-- Exhaustive coverage of the odd inputs in this batch, with no gaps. -/
theorem coverage : CertifiedRange 1475 1543 := by
  intro n hlo hhi hodd
  have hn : n = 1475 ∨ n = 1477 ∨ n = 1479 ∨ n = 1481 ∨ n = 1483 ∨ n = 1485 ∨ n = 1487 ∨ n = 1489 ∨ n = 1491 ∨ n = 1493 ∨ n = 1495 ∨ n = 1497 ∨ n = 1499 ∨ n = 1501 ∨ n = 1503 ∨ n = 1505 ∨ n = 1507 ∨ n = 1509 ∨ n = 1511 ∨ n = 1513 ∨ n = 1515 ∨ n = 1517 ∨ n = 1519 ∨ n = 1521 ∨ n = 1523 ∨ n = 1525 ∨ n = 1527 ∨ n = 1529 ∨ n = 1531 ∨ n = 1533 ∨ n = 1535 ∨ n = 1537 ∨ n = 1539 ∨ n = 1541 := by omega
  rcases hn with h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h
  · subst n
    exact ⟨4, witness_of_certificate certificate_1475⟩
  · subst n
    exact ⟨2, witness_of_certificate certificate_1477⟩
  · subst n
    exact ⟨8, witness_of_certificate certificate_1479⟩
  · subst n
    exact ⟨2, witness_of_certificate certificate_1481⟩
  · subst n
    exact ⟨5, witness_of_certificate certificate_1483⟩
  · subst n
    exact ⟨2, witness_of_certificate certificate_1485⟩
  · subst n
    exact ⟨24, witness_of_certificate certificate_1487⟩
  · subst n
    exact ⟨2, witness_of_certificate certificate_1489⟩
  · subst n
    exact ⟨4, witness_of_certificate certificate_1491⟩
  · subst n
    exact ⟨2, witness_of_certificate certificate_1493⟩
  · subst n
    exact ⟨5, witness_of_certificate certificate_1495⟩
  · subst n
    exact ⟨2, witness_of_certificate certificate_1497⟩
  · subst n
    exact ⟨8, witness_of_certificate certificate_1499⟩
  · subst n
    exact ⟨2, witness_of_certificate certificate_1501⟩
  · subst n
    exact ⟨21, witness_of_certificate certificate_1503⟩
  · subst n
    exact ⟨2, witness_of_certificate certificate_1505⟩
  · subst n
    exact ⟨4, witness_of_certificate certificate_1507⟩
  · subst n
    exact ⟨2, witness_of_certificate certificate_1509⟩
  · subst n
    exact ⟨20, witness_of_certificate certificate_1511⟩
  · subst n
    exact ⟨2, witness_of_certificate certificate_1513⟩
  · subst n
    exact ⟨5, witness_of_certificate certificate_1515⟩
  · subst n
    exact ⟨2, witness_of_certificate certificate_1517⟩
  · subst n
    exact ⟨16, witness_of_certificate certificate_1519⟩
  · subst n
    exact ⟨2, witness_of_certificate certificate_1521⟩
  · subst n
    exact ⟨4, witness_of_certificate certificate_1523⟩
  · subst n
    exact ⟨2, witness_of_certificate certificate_1525⟩
  · subst n
    exact ⟨5, witness_of_certificate certificate_1527⟩
  · subst n
    exact ⟨2, witness_of_certificate certificate_1529⟩
  · subst n
    exact ⟨10, witness_of_certificate certificate_1531⟩
  · subst n
    exact ⟨2, witness_of_certificate certificate_1533⟩
  · subst n
    exact ⟨16, witness_of_certificate certificate_1535⟩
  · subst n
    exact ⟨2, witness_of_certificate certificate_1537⟩
  · subst n
    exact ⟨4, witness_of_certificate certificate_1539⟩
  · subst n
    exact ⟨2, witness_of_certificate certificate_1541⟩

end Collatz.Research.CoefficientDescent.Batch023
