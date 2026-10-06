import Collatz.Research.CoefficientDescent.Basic

namespace Collatz.Research.CoefficientDescent.Batch024

open FirstDescentClass

set_option maxRecDepth 20000
set_option maxHeartbeats 0

/-- Checked base and every prefix for input 1543. -/
theorem certificate_1543 : classCertificateB 7 1543 = true := by
  decide

/-- The same exact first-descent time holds on an infinite dyadic ray. -/
theorem ray_1543 (m : Nat) : stoppingTime (2 ^ 7 * m + 1543) 7 :=
  stoppingTime_of_classCertificate certificate_1543 m

/-- Checked base and every prefix for input 1545. -/
theorem certificate_1545 : classCertificateB 2 1545 = true := by
  decide

/-- The same exact first-descent time holds on an infinite dyadic ray. -/
theorem ray_1545 (m : Nat) : stoppingTime (2 ^ 2 * m + 1545) 2 :=
  stoppingTime_of_classCertificate certificate_1545 m

/-- Checked base and every prefix for input 1547. -/
theorem certificate_1547 : classCertificateB 5 1547 = true := by
  decide

/-- The same exact first-descent time holds on an infinite dyadic ray. -/
theorem ray_1547 (m : Nat) : stoppingTime (2 ^ 5 * m + 1547) 5 :=
  stoppingTime_of_classCertificate certificate_1547 m

/-- Checked base and every prefix for input 1549. -/
theorem certificate_1549 : classCertificateB 2 1549 = true := by
  decide

/-- The same exact first-descent time holds on an infinite dyadic ray. -/
theorem ray_1549 (m : Nat) : stoppingTime (2 ^ 2 * m + 1549) 2 :=
  stoppingTime_of_classCertificate certificate_1549 m

/-- Checked base and every prefix for input 1551. -/
theorem certificate_1551 : classCertificateB 7 1551 = true := by
  decide

/-- The same exact first-descent time holds on an infinite dyadic ray. -/
theorem ray_1551 (m : Nat) : stoppingTime (2 ^ 7 * m + 1551) 7 :=
  stoppingTime_of_classCertificate certificate_1551 m

/-- Checked base and every prefix for input 1553. -/
theorem certificate_1553 : classCertificateB 2 1553 = true := by
  decide

/-- The same exact first-descent time holds on an infinite dyadic ray. -/
theorem ray_1553 (m : Nat) : stoppingTime (2 ^ 2 * m + 1553) 2 :=
  stoppingTime_of_classCertificate certificate_1553 m

/-- Checked base and every prefix for input 1555. -/
theorem certificate_1555 : classCertificateB 4 1555 = true := by
  decide

/-- The same exact first-descent time holds on an infinite dyadic ray. -/
theorem ray_1555 (m : Nat) : stoppingTime (2 ^ 4 * m + 1555) 4 :=
  stoppingTime_of_classCertificate certificate_1555 m

/-- Checked base and every prefix for input 1557. -/
theorem certificate_1557 : classCertificateB 2 1557 = true := by
  decide

/-- The same exact first-descent time holds on an infinite dyadic ray. -/
theorem ray_1557 (m : Nat) : stoppingTime (2 ^ 2 * m + 1557) 2 :=
  stoppingTime_of_classCertificate certificate_1557 m

/-- Checked base and every prefix for input 1559. -/
theorem certificate_1559 : classCertificateB 5 1559 = true := by
  decide

/-- The same exact first-descent time holds on an infinite dyadic ray. -/
theorem ray_1559 (m : Nat) : stoppingTime (2 ^ 5 * m + 1559) 5 :=
  stoppingTime_of_classCertificate certificate_1559 m

/-- Checked base and every prefix for input 1561. -/
theorem certificate_1561 : classCertificateB 2 1561 = true := by
  decide

/-- The same exact first-descent time holds on an infinite dyadic ray. -/
theorem ray_1561 (m : Nat) : stoppingTime (2 ^ 2 * m + 1561) 2 :=
  stoppingTime_of_classCertificate certificate_1561 m

/-- Checked base and every prefix for input 1563. -/
theorem certificate_1563 : classCertificateB 13 1563 = true := by
  decide

/-- The same exact first-descent time holds on an infinite dyadic ray. -/
theorem ray_1563 (m : Nat) : stoppingTime (2 ^ 13 * m + 1563) 13 :=
  stoppingTime_of_classCertificate certificate_1563 m

/-- Checked base and every prefix for input 1565. -/
theorem certificate_1565 : classCertificateB 2 1565 = true := by
  decide

/-- The same exact first-descent time holds on an infinite dyadic ray. -/
theorem ray_1565 (m : Nat) : stoppingTime (2 ^ 2 * m + 1565) 2 :=
  stoppingTime_of_classCertificate certificate_1565 m

/-- Checked base and every prefix for input 1567. -/
theorem certificate_1567 : classCertificateB 13 1567 = true := by
  decide

/-- The same exact first-descent time holds on an infinite dyadic ray. -/
theorem ray_1567 (m : Nat) : stoppingTime (2 ^ 13 * m + 1567) 13 :=
  stoppingTime_of_classCertificate certificate_1567 m

/-- Checked base and every prefix for input 1569. -/
theorem certificate_1569 : classCertificateB 2 1569 = true := by
  decide

/-- The same exact first-descent time holds on an infinite dyadic ray. -/
theorem ray_1569 (m : Nat) : stoppingTime (2 ^ 2 * m + 1569) 2 :=
  stoppingTime_of_classCertificate certificate_1569 m

/-- Checked base and every prefix for input 1571. -/
theorem certificate_1571 : classCertificateB 4 1571 = true := by
  decide

/-- The same exact first-descent time holds on an infinite dyadic ray. -/
theorem ray_1571 (m : Nat) : stoppingTime (2 ^ 4 * m + 1571) 4 :=
  stoppingTime_of_classCertificate certificate_1571 m

/-- Checked base and every prefix for input 1573. -/
theorem certificate_1573 : classCertificateB 2 1573 = true := by
  decide

/-- The same exact first-descent time holds on an infinite dyadic ray. -/
theorem ray_1573 (m : Nat) : stoppingTime (2 ^ 2 * m + 1573) 2 :=
  stoppingTime_of_classCertificate certificate_1573 m

/-- Checked base and every prefix for input 1575. -/
theorem certificate_1575 : classCertificateB 8 1575 = true := by
  decide

/-- The same exact first-descent time holds on an infinite dyadic ray. -/
theorem ray_1575 (m : Nat) : stoppingTime (2 ^ 8 * m + 1575) 8 :=
  stoppingTime_of_classCertificate certificate_1575 m

/-- Checked base and every prefix for input 1577. -/
theorem certificate_1577 : classCertificateB 2 1577 = true := by
  decide

/-- The same exact first-descent time holds on an infinite dyadic ray. -/
theorem ray_1577 (m : Nat) : stoppingTime (2 ^ 2 * m + 1577) 2 :=
  stoppingTime_of_classCertificate certificate_1577 m

/-- Checked base and every prefix for input 1579. -/
theorem certificate_1579 : classCertificateB 5 1579 = true := by
  decide

/-- The same exact first-descent time holds on an infinite dyadic ray. -/
theorem ray_1579 (m : Nat) : stoppingTime (2 ^ 5 * m + 1579) 5 :=
  stoppingTime_of_classCertificate certificate_1579 m

/-- Checked base and every prefix for input 1581. -/
theorem certificate_1581 : classCertificateB 2 1581 = true := by
  decide

/-- The same exact first-descent time holds on an infinite dyadic ray. -/
theorem ray_1581 (m : Nat) : stoppingTime (2 ^ 2 * m + 1581) 2 :=
  stoppingTime_of_classCertificate certificate_1581 m

/-- Checked base and every prefix for input 1583. -/
theorem certificate_1583 : classCertificateB 78 1583 = true := by
  decide

/-- The same exact first-descent time holds on an infinite dyadic ray. -/
theorem ray_1583 (m : Nat) : stoppingTime (2 ^ 78 * m + 1583) 78 :=
  stoppingTime_of_classCertificate certificate_1583 m

/-- Checked base and every prefix for input 1585. -/
theorem certificate_1585 : classCertificateB 2 1585 = true := by
  decide

/-- The same exact first-descent time holds on an infinite dyadic ray. -/
theorem ray_1585 (m : Nat) : stoppingTime (2 ^ 2 * m + 1585) 2 :=
  stoppingTime_of_classCertificate certificate_1585 m

/-- Checked base and every prefix for input 1587. -/
theorem certificate_1587 : classCertificateB 4 1587 = true := by
  decide

/-- The same exact first-descent time holds on an infinite dyadic ray. -/
theorem ray_1587 (m : Nat) : stoppingTime (2 ^ 4 * m + 1587) 4 :=
  stoppingTime_of_classCertificate certificate_1587 m

/-- Checked base and every prefix for input 1589. -/
theorem certificate_1589 : classCertificateB 2 1589 = true := by
  decide

/-- The same exact first-descent time holds on an infinite dyadic ray. -/
theorem ray_1589 (m : Nat) : stoppingTime (2 ^ 2 * m + 1589) 2 :=
  stoppingTime_of_classCertificate certificate_1589 m

/-- Checked base and every prefix for input 1591. -/
theorem certificate_1591 : classCertificateB 5 1591 = true := by
  decide

/-- The same exact first-descent time holds on an infinite dyadic ray. -/
theorem ray_1591 (m : Nat) : stoppingTime (2 ^ 5 * m + 1591) 5 :=
  stoppingTime_of_classCertificate certificate_1591 m

/-- Checked base and every prefix for input 1593. -/
theorem certificate_1593 : classCertificateB 2 1593 = true := by
  decide

/-- The same exact first-descent time holds on an infinite dyadic ray. -/
theorem ray_1593 (m : Nat) : stoppingTime (2 ^ 2 * m + 1593) 2 :=
  stoppingTime_of_classCertificate certificate_1593 m

/-- Checked base and every prefix for input 1595. -/
theorem certificate_1595 : classCertificateB 7 1595 = true := by
  decide

/-- The same exact first-descent time holds on an infinite dyadic ray. -/
theorem ray_1595 (m : Nat) : stoppingTime (2 ^ 7 * m + 1595) 7 :=
  stoppingTime_of_classCertificate certificate_1595 m

/-- Checked base and every prefix for input 1597. -/
theorem certificate_1597 : classCertificateB 2 1597 = true := by
  decide

/-- The same exact first-descent time holds on an infinite dyadic ray. -/
theorem ray_1597 (m : Nat) : stoppingTime (2 ^ 2 * m + 1597) 2 :=
  stoppingTime_of_classCertificate certificate_1597 m

/-- Checked base and every prefix for input 1599. -/
theorem certificate_1599 : classCertificateB 10 1599 = true := by
  decide

/-- The same exact first-descent time holds on an infinite dyadic ray. -/
theorem ray_1599 (m : Nat) : stoppingTime (2 ^ 10 * m + 1599) 10 :=
  stoppingTime_of_classCertificate certificate_1599 m

/-- Checked base and every prefix for input 1601. -/
theorem certificate_1601 : classCertificateB 2 1601 = true := by
  decide

/-- The same exact first-descent time holds on an infinite dyadic ray. -/
theorem ray_1601 (m : Nat) : stoppingTime (2 ^ 2 * m + 1601) 2 :=
  stoppingTime_of_classCertificate certificate_1601 m

/-- Checked base and every prefix for input 1603. -/
theorem certificate_1603 : classCertificateB 4 1603 = true := by
  decide

/-- The same exact first-descent time holds on an infinite dyadic ray. -/
theorem ray_1603 (m : Nat) : stoppingTime (2 ^ 4 * m + 1603) 4 :=
  stoppingTime_of_classCertificate certificate_1603 m

/-- Checked base and every prefix for input 1605. -/
theorem certificate_1605 : classCertificateB 2 1605 = true := by
  decide

/-- The same exact first-descent time holds on an infinite dyadic ray. -/
theorem ray_1605 (m : Nat) : stoppingTime (2 ^ 2 * m + 1605) 2 :=
  stoppingTime_of_classCertificate certificate_1605 m

/-- Checked base and every prefix for input 1607. -/
theorem certificate_1607 : classCertificateB 10 1607 = true := by
  decide

/-- The same exact first-descent time holds on an infinite dyadic ray. -/
theorem ray_1607 (m : Nat) : stoppingTime (2 ^ 10 * m + 1607) 10 :=
  stoppingTime_of_classCertificate certificate_1607 m

/-- Exhaustive coverage of the odd inputs in this batch, with no gaps. -/
theorem coverage : CertifiedRange 1543 1609 := by
  intro n hlo hhi hodd
  have hn : n = 1543 ∨ n = 1545 ∨ n = 1547 ∨ n = 1549 ∨ n = 1551 ∨ n = 1553 ∨ n = 1555 ∨ n = 1557 ∨ n = 1559 ∨ n = 1561 ∨ n = 1563 ∨ n = 1565 ∨ n = 1567 ∨ n = 1569 ∨ n = 1571 ∨ n = 1573 ∨ n = 1575 ∨ n = 1577 ∨ n = 1579 ∨ n = 1581 ∨ n = 1583 ∨ n = 1585 ∨ n = 1587 ∨ n = 1589 ∨ n = 1591 ∨ n = 1593 ∨ n = 1595 ∨ n = 1597 ∨ n = 1599 ∨ n = 1601 ∨ n = 1603 ∨ n = 1605 ∨ n = 1607 := by omega
  rcases hn with h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h
  · subst n
    exact ⟨7, witness_of_certificate certificate_1543⟩
  · subst n
    exact ⟨2, witness_of_certificate certificate_1545⟩
  · subst n
    exact ⟨5, witness_of_certificate certificate_1547⟩
  · subst n
    exact ⟨2, witness_of_certificate certificate_1549⟩
  · subst n
    exact ⟨7, witness_of_certificate certificate_1551⟩
  · subst n
    exact ⟨2, witness_of_certificate certificate_1553⟩
  · subst n
    exact ⟨4, witness_of_certificate certificate_1555⟩
  · subst n
    exact ⟨2, witness_of_certificate certificate_1557⟩
  · subst n
    exact ⟨5, witness_of_certificate certificate_1559⟩
  · subst n
    exact ⟨2, witness_of_certificate certificate_1561⟩
  · subst n
    exact ⟨13, witness_of_certificate certificate_1563⟩
  · subst n
    exact ⟨2, witness_of_certificate certificate_1565⟩
  · subst n
    exact ⟨13, witness_of_certificate certificate_1567⟩
  · subst n
    exact ⟨2, witness_of_certificate certificate_1569⟩
  · subst n
    exact ⟨4, witness_of_certificate certificate_1571⟩
  · subst n
    exact ⟨2, witness_of_certificate certificate_1573⟩
  · subst n
    exact ⟨8, witness_of_certificate certificate_1575⟩
  · subst n
    exact ⟨2, witness_of_certificate certificate_1577⟩
  · subst n
    exact ⟨5, witness_of_certificate certificate_1579⟩
  · subst n
    exact ⟨2, witness_of_certificate certificate_1581⟩
  · subst n
    exact ⟨78, witness_of_certificate certificate_1583⟩
  · subst n
    exact ⟨2, witness_of_certificate certificate_1585⟩
  · subst n
    exact ⟨4, witness_of_certificate certificate_1587⟩
  · subst n
    exact ⟨2, witness_of_certificate certificate_1589⟩
  · subst n
    exact ⟨5, witness_of_certificate certificate_1591⟩
  · subst n
    exact ⟨2, witness_of_certificate certificate_1593⟩
  · subst n
    exact ⟨7, witness_of_certificate certificate_1595⟩
  · subst n
    exact ⟨2, witness_of_certificate certificate_1597⟩
  · subst n
    exact ⟨10, witness_of_certificate certificate_1599⟩
  · subst n
    exact ⟨2, witness_of_certificate certificate_1601⟩
  · subst n
    exact ⟨4, witness_of_certificate certificate_1603⟩
  · subst n
    exact ⟨2, witness_of_certificate certificate_1605⟩
  · subst n
    exact ⟨10, witness_of_certificate certificate_1607⟩

end Collatz.Research.CoefficientDescent.Batch024
