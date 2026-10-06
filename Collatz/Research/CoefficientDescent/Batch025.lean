import Collatz.Research.CoefficientDescent.Basic

namespace Collatz.Research.CoefficientDescent.Batch025

open FirstDescentClass

set_option maxRecDepth 20000
set_option maxHeartbeats 0

/-- Checked base and every prefix for input 1609. -/
theorem certificate_1609 : classCertificateB 2 1609 = true := by
  decide

/-- The same exact first-descent time holds on an infinite dyadic ray. -/
theorem ray_1609 (m : Nat) : stoppingTime (2 ^ 2 * m + 1609) 2 :=
  stoppingTime_of_classCertificate certificate_1609 m

/-- Checked base and every prefix for input 1611. -/
theorem certificate_1611 : classCertificateB 5 1611 = true := by
  decide

/-- The same exact first-descent time holds on an infinite dyadic ray. -/
theorem ray_1611 (m : Nat) : stoppingTime (2 ^ 5 * m + 1611) 5 :=
  stoppingTime_of_classCertificate certificate_1611 m

/-- Checked base and every prefix for input 1613. -/
theorem certificate_1613 : classCertificateB 2 1613 = true := by
  decide

/-- The same exact first-descent time holds on an infinite dyadic ray. -/
theorem ray_1613 (m : Nat) : stoppingTime (2 ^ 2 * m + 1613) 2 :=
  stoppingTime_of_classCertificate certificate_1613 m

/-- Checked base and every prefix for input 1615. -/
theorem certificate_1615 : classCertificateB 8 1615 = true := by
  decide

/-- The same exact first-descent time holds on an infinite dyadic ray. -/
theorem ray_1615 (m : Nat) : stoppingTime (2 ^ 8 * m + 1615) 8 :=
  stoppingTime_of_classCertificate certificate_1615 m

/-- Checked base and every prefix for input 1617. -/
theorem certificate_1617 : classCertificateB 2 1617 = true := by
  decide

/-- The same exact first-descent time holds on an infinite dyadic ray. -/
theorem ray_1617 (m : Nat) : stoppingTime (2 ^ 2 * m + 1617) 2 :=
  stoppingTime_of_classCertificate certificate_1617 m

/-- Checked base and every prefix for input 1619. -/
theorem certificate_1619 : classCertificateB 4 1619 = true := by
  decide

/-- The same exact first-descent time holds on an infinite dyadic ray. -/
theorem ray_1619 (m : Nat) : stoppingTime (2 ^ 4 * m + 1619) 4 :=
  stoppingTime_of_classCertificate certificate_1619 m

/-- Checked base and every prefix for input 1621. -/
theorem certificate_1621 : classCertificateB 2 1621 = true := by
  decide

/-- The same exact first-descent time holds on an infinite dyadic ray. -/
theorem ray_1621 (m : Nat) : stoppingTime (2 ^ 2 * m + 1621) 2 :=
  stoppingTime_of_classCertificate certificate_1621 m

/-- Checked base and every prefix for input 1623. -/
theorem certificate_1623 : classCertificateB 5 1623 = true := by
  decide

/-- The same exact first-descent time holds on an infinite dyadic ray. -/
theorem ray_1623 (m : Nat) : stoppingTime (2 ^ 5 * m + 1623) 5 :=
  stoppingTime_of_classCertificate certificate_1623 m

/-- Checked base and every prefix for input 1625. -/
theorem certificate_1625 : classCertificateB 2 1625 = true := by
  decide

/-- The same exact first-descent time holds on an infinite dyadic ray. -/
theorem ray_1625 (m : Nat) : stoppingTime (2 ^ 2 * m + 1625) 2 :=
  stoppingTime_of_classCertificate certificate_1625 m

/-- Checked base and every prefix for input 1627. -/
theorem certificate_1627 : classCertificateB 16 1627 = true := by
  decide

/-- The same exact first-descent time holds on an infinite dyadic ray. -/
theorem ray_1627 (m : Nat) : stoppingTime (2 ^ 16 * m + 1627) 16 :=
  stoppingTime_of_classCertificate certificate_1627 m

/-- Checked base and every prefix for input 1629. -/
theorem certificate_1629 : classCertificateB 2 1629 = true := by
  decide

/-- The same exact first-descent time holds on an infinite dyadic ray. -/
theorem ray_1629 (m : Nat) : stoppingTime (2 ^ 2 * m + 1629) 2 :=
  stoppingTime_of_classCertificate certificate_1629 m

/-- Checked base and every prefix for input 1631. -/
theorem certificate_1631 : classCertificateB 8 1631 = true := by
  decide

/-- The same exact first-descent time holds on an infinite dyadic ray. -/
theorem ray_1631 (m : Nat) : stoppingTime (2 ^ 8 * m + 1631) 8 :=
  stoppingTime_of_classCertificate certificate_1631 m

/-- Checked base and every prefix for input 1633. -/
theorem certificate_1633 : classCertificateB 2 1633 = true := by
  decide

/-- The same exact first-descent time holds on an infinite dyadic ray. -/
theorem ray_1633 (m : Nat) : stoppingTime (2 ^ 2 * m + 1633) 2 :=
  stoppingTime_of_classCertificate certificate_1633 m

/-- Checked base and every prefix for input 1635. -/
theorem certificate_1635 : classCertificateB 4 1635 = true := by
  decide

/-- The same exact first-descent time holds on an infinite dyadic ray. -/
theorem ray_1635 (m : Nat) : stoppingTime (2 ^ 4 * m + 1635) 4 :=
  stoppingTime_of_classCertificate certificate_1635 m

/-- Checked base and every prefix for input 1637. -/
theorem certificate_1637 : classCertificateB 2 1637 = true := by
  decide

/-- The same exact first-descent time holds on an infinite dyadic ray. -/
theorem ray_1637 (m : Nat) : stoppingTime (2 ^ 2 * m + 1637) 2 :=
  stoppingTime_of_classCertificate certificate_1637 m

/-- Checked base and every prefix for input 1639. -/
theorem certificate_1639 : classCertificateB 43 1639 = true := by
  decide

/-- The same exact first-descent time holds on an infinite dyadic ray. -/
theorem ray_1639 (m : Nat) : stoppingTime (2 ^ 43 * m + 1639) 43 :=
  stoppingTime_of_classCertificate certificate_1639 m

/-- Checked base and every prefix for input 1641. -/
theorem certificate_1641 : classCertificateB 2 1641 = true := by
  decide

/-- The same exact first-descent time holds on an infinite dyadic ray. -/
theorem ray_1641 (m : Nat) : stoppingTime (2 ^ 2 * m + 1641) 2 :=
  stoppingTime_of_classCertificate certificate_1641 m

/-- Checked base and every prefix for input 1643. -/
theorem certificate_1643 : classCertificateB 5 1643 = true := by
  decide

/-- The same exact first-descent time holds on an infinite dyadic ray. -/
theorem ray_1643 (m : Nat) : stoppingTime (2 ^ 5 * m + 1643) 5 :=
  stoppingTime_of_classCertificate certificate_1643 m

/-- Checked base and every prefix for input 1645. -/
theorem certificate_1645 : classCertificateB 2 1645 = true := by
  decide

/-- The same exact first-descent time holds on an infinite dyadic ray. -/
theorem ray_1645 (m : Nat) : stoppingTime (2 ^ 2 * m + 1645) 2 :=
  stoppingTime_of_classCertificate certificate_1645 m

/-- Checked base and every prefix for input 1647. -/
theorem certificate_1647 : classCertificateB 12 1647 = true := by
  decide

/-- The same exact first-descent time holds on an infinite dyadic ray. -/
theorem ray_1647 (m : Nat) : stoppingTime (2 ^ 12 * m + 1647) 12 :=
  stoppingTime_of_classCertificate certificate_1647 m

/-- Checked base and every prefix for input 1649. -/
theorem certificate_1649 : classCertificateB 2 1649 = true := by
  decide

/-- The same exact first-descent time holds on an infinite dyadic ray. -/
theorem ray_1649 (m : Nat) : stoppingTime (2 ^ 2 * m + 1649) 2 :=
  stoppingTime_of_classCertificate certificate_1649 m

/-- Checked base and every prefix for input 1651. -/
theorem certificate_1651 : classCertificateB 4 1651 = true := by
  decide

/-- The same exact first-descent time holds on an infinite dyadic ray. -/
theorem ray_1651 (m : Nat) : stoppingTime (2 ^ 4 * m + 1651) 4 :=
  stoppingTime_of_classCertificate certificate_1651 m

/-- Checked base and every prefix for input 1653. -/
theorem certificate_1653 : classCertificateB 2 1653 = true := by
  decide

/-- The same exact first-descent time holds on an infinite dyadic ray. -/
theorem ray_1653 (m : Nat) : stoppingTime (2 ^ 2 * m + 1653) 2 :=
  stoppingTime_of_classCertificate certificate_1653 m

/-- Checked base and every prefix for input 1655. -/
theorem certificate_1655 : classCertificateB 5 1655 = true := by
  decide

/-- The same exact first-descent time holds on an infinite dyadic ray. -/
theorem ray_1655 (m : Nat) : stoppingTime (2 ^ 5 * m + 1655) 5 :=
  stoppingTime_of_classCertificate certificate_1655 m

/-- Checked base and every prefix for input 1657. -/
theorem certificate_1657 : classCertificateB 2 1657 = true := by
  decide

/-- The same exact first-descent time holds on an infinite dyadic ray. -/
theorem ray_1657 (m : Nat) : stoppingTime (2 ^ 2 * m + 1657) 2 :=
  stoppingTime_of_classCertificate certificate_1657 m

/-- Checked base and every prefix for input 1659. -/
theorem certificate_1659 : classCertificateB 8 1659 = true := by
  decide

/-- The same exact first-descent time holds on an infinite dyadic ray. -/
theorem ray_1659 (m : Nat) : stoppingTime (2 ^ 8 * m + 1659) 8 :=
  stoppingTime_of_classCertificate certificate_1659 m

/-- Checked base and every prefix for input 1661. -/
theorem certificate_1661 : classCertificateB 2 1661 = true := by
  decide

/-- The same exact first-descent time holds on an infinite dyadic ray. -/
theorem ray_1661 (m : Nat) : stoppingTime (2 ^ 2 * m + 1661) 2 :=
  stoppingTime_of_classCertificate certificate_1661 m

/-- Checked base and every prefix for input 1663. -/
theorem certificate_1663 : classCertificateB 24 1663 = true := by
  decide

/-- The same exact first-descent time holds on an infinite dyadic ray. -/
theorem ray_1663 (m : Nat) : stoppingTime (2 ^ 24 * m + 1663) 24 :=
  stoppingTime_of_classCertificate certificate_1663 m

/-- Checked base and every prefix for input 1665. -/
theorem certificate_1665 : classCertificateB 2 1665 = true := by
  decide

/-- The same exact first-descent time holds on an infinite dyadic ray. -/
theorem ray_1665 (m : Nat) : stoppingTime (2 ^ 2 * m + 1665) 2 :=
  stoppingTime_of_classCertificate certificate_1665 m

/-- Checked base and every prefix for input 1667. -/
theorem certificate_1667 : classCertificateB 4 1667 = true := by
  decide

/-- The same exact first-descent time holds on an infinite dyadic ray. -/
theorem ray_1667 (m : Nat) : stoppingTime (2 ^ 4 * m + 1667) 4 :=
  stoppingTime_of_classCertificate certificate_1667 m

/-- Checked base and every prefix for input 1669. -/
theorem certificate_1669 : classCertificateB 2 1669 = true := by
  decide

/-- The same exact first-descent time holds on an infinite dyadic ray. -/
theorem ray_1669 (m : Nat) : stoppingTime (2 ^ 2 * m + 1669) 2 :=
  stoppingTime_of_classCertificate certificate_1669 m

/-- Checked base and every prefix for input 1671. -/
theorem certificate_1671 : classCertificateB 7 1671 = true := by
  decide

/-- The same exact first-descent time holds on an infinite dyadic ray. -/
theorem ray_1671 (m : Nat) : stoppingTime (2 ^ 7 * m + 1671) 7 :=
  stoppingTime_of_classCertificate certificate_1671 m

/-- Checked base and every prefix for input 1673. -/
theorem certificate_1673 : classCertificateB 2 1673 = true := by
  decide

/-- The same exact first-descent time holds on an infinite dyadic ray. -/
theorem ray_1673 (m : Nat) : stoppingTime (2 ^ 2 * m + 1673) 2 :=
  stoppingTime_of_classCertificate certificate_1673 m

/-- Checked base and every prefix for input 1675. -/
theorem certificate_1675 : classCertificateB 5 1675 = true := by
  decide

/-- The same exact first-descent time holds on an infinite dyadic ray. -/
theorem ray_1675 (m : Nat) : stoppingTime (2 ^ 5 * m + 1675) 5 :=
  stoppingTime_of_classCertificate certificate_1675 m

/-- Exhaustive coverage of the odd inputs in this batch, with no gaps. -/
theorem coverage : CertifiedRange 1609 1677 := by
  intro n hlo hhi hodd
  have hn : n = 1609 ∨ n = 1611 ∨ n = 1613 ∨ n = 1615 ∨ n = 1617 ∨ n = 1619 ∨ n = 1621 ∨ n = 1623 ∨ n = 1625 ∨ n = 1627 ∨ n = 1629 ∨ n = 1631 ∨ n = 1633 ∨ n = 1635 ∨ n = 1637 ∨ n = 1639 ∨ n = 1641 ∨ n = 1643 ∨ n = 1645 ∨ n = 1647 ∨ n = 1649 ∨ n = 1651 ∨ n = 1653 ∨ n = 1655 ∨ n = 1657 ∨ n = 1659 ∨ n = 1661 ∨ n = 1663 ∨ n = 1665 ∨ n = 1667 ∨ n = 1669 ∨ n = 1671 ∨ n = 1673 ∨ n = 1675 := by omega
  rcases hn with h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h
  · subst n
    exact ⟨2, witness_of_certificate certificate_1609⟩
  · subst n
    exact ⟨5, witness_of_certificate certificate_1611⟩
  · subst n
    exact ⟨2, witness_of_certificate certificate_1613⟩
  · subst n
    exact ⟨8, witness_of_certificate certificate_1615⟩
  · subst n
    exact ⟨2, witness_of_certificate certificate_1617⟩
  · subst n
    exact ⟨4, witness_of_certificate certificate_1619⟩
  · subst n
    exact ⟨2, witness_of_certificate certificate_1621⟩
  · subst n
    exact ⟨5, witness_of_certificate certificate_1623⟩
  · subst n
    exact ⟨2, witness_of_certificate certificate_1625⟩
  · subst n
    exact ⟨16, witness_of_certificate certificate_1627⟩
  · subst n
    exact ⟨2, witness_of_certificate certificate_1629⟩
  · subst n
    exact ⟨8, witness_of_certificate certificate_1631⟩
  · subst n
    exact ⟨2, witness_of_certificate certificate_1633⟩
  · subst n
    exact ⟨4, witness_of_certificate certificate_1635⟩
  · subst n
    exact ⟨2, witness_of_certificate certificate_1637⟩
  · subst n
    exact ⟨43, witness_of_certificate certificate_1639⟩
  · subst n
    exact ⟨2, witness_of_certificate certificate_1641⟩
  · subst n
    exact ⟨5, witness_of_certificate certificate_1643⟩
  · subst n
    exact ⟨2, witness_of_certificate certificate_1645⟩
  · subst n
    exact ⟨12, witness_of_certificate certificate_1647⟩
  · subst n
    exact ⟨2, witness_of_certificate certificate_1649⟩
  · subst n
    exact ⟨4, witness_of_certificate certificate_1651⟩
  · subst n
    exact ⟨2, witness_of_certificate certificate_1653⟩
  · subst n
    exact ⟨5, witness_of_certificate certificate_1655⟩
  · subst n
    exact ⟨2, witness_of_certificate certificate_1657⟩
  · subst n
    exact ⟨8, witness_of_certificate certificate_1659⟩
  · subst n
    exact ⟨2, witness_of_certificate certificate_1661⟩
  · subst n
    exact ⟨24, witness_of_certificate certificate_1663⟩
  · subst n
    exact ⟨2, witness_of_certificate certificate_1665⟩
  · subst n
    exact ⟨4, witness_of_certificate certificate_1667⟩
  · subst n
    exact ⟨2, witness_of_certificate certificate_1669⟩
  · subst n
    exact ⟨7, witness_of_certificate certificate_1671⟩
  · subst n
    exact ⟨2, witness_of_certificate certificate_1673⟩
  · subst n
    exact ⟨5, witness_of_certificate certificate_1675⟩

end Collatz.Research.CoefficientDescent.Batch025
