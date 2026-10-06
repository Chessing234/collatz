import Collatz.Research.CoefficientDescent.Basic

namespace Collatz.Research.CoefficientDescent.Batch027

open FirstDescentClass

set_option maxRecDepth 20000
set_option maxHeartbeats 0

/-- Checked base and every prefix for input 1743. -/
theorem certificate_1743 : classCertificateB 35 1743 = true := by
  decide

/-- The same exact first-descent time holds on an infinite dyadic ray. -/
theorem ray_1743 (m : Nat) : stoppingTime (2 ^ 35 * m + 1743) 35 :=
  stoppingTime_of_classCertificate certificate_1743 m

/-- Checked base and every prefix for input 1745. -/
theorem certificate_1745 : classCertificateB 2 1745 = true := by
  decide

/-- The same exact first-descent time holds on an infinite dyadic ray. -/
theorem ray_1745 (m : Nat) : stoppingTime (2 ^ 2 * m + 1745) 2 :=
  stoppingTime_of_classCertificate certificate_1745 m

/-- Checked base and every prefix for input 1747. -/
theorem certificate_1747 : classCertificateB 4 1747 = true := by
  decide

/-- The same exact first-descent time holds on an infinite dyadic ray. -/
theorem ray_1747 (m : Nat) : stoppingTime (2 ^ 4 * m + 1747) 4 :=
  stoppingTime_of_classCertificate certificate_1747 m

/-- Checked base and every prefix for input 1749. -/
theorem certificate_1749 : classCertificateB 2 1749 = true := by
  decide

/-- The same exact first-descent time holds on an infinite dyadic ray. -/
theorem ray_1749 (m : Nat) : stoppingTime (2 ^ 2 * m + 1749) 2 :=
  stoppingTime_of_classCertificate certificate_1749 m

/-- Checked base and every prefix for input 1751. -/
theorem certificate_1751 : classCertificateB 5 1751 = true := by
  decide

/-- The same exact first-descent time holds on an infinite dyadic ray. -/
theorem ray_1751 (m : Nat) : stoppingTime (2 ^ 5 * m + 1751) 5 :=
  stoppingTime_of_classCertificate certificate_1751 m

/-- Checked base and every prefix for input 1753. -/
theorem certificate_1753 : classCertificateB 2 1753 = true := by
  decide

/-- The same exact first-descent time holds on an infinite dyadic ray. -/
theorem ray_1753 (m : Nat) : stoppingTime (2 ^ 2 * m + 1753) 2 :=
  stoppingTime_of_classCertificate certificate_1753 m

/-- Checked base and every prefix for input 1755. -/
theorem certificate_1755 : classCertificateB 8 1755 = true := by
  decide

/-- The same exact first-descent time holds on an infinite dyadic ray. -/
theorem ray_1755 (m : Nat) : stoppingTime (2 ^ 8 * m + 1755) 8 :=
  stoppingTime_of_classCertificate certificate_1755 m

/-- Checked base and every prefix for input 1757. -/
theorem certificate_1757 : classCertificateB 2 1757 = true := by
  decide

/-- The same exact first-descent time holds on an infinite dyadic ray. -/
theorem ray_1757 (m : Nat) : stoppingTime (2 ^ 2 * m + 1757) 2 :=
  stoppingTime_of_classCertificate certificate_1757 m

/-- Checked base and every prefix for input 1759. -/
theorem certificate_1759 : classCertificateB 10 1759 = true := by
  decide

/-- The same exact first-descent time holds on an infinite dyadic ray. -/
theorem ray_1759 (m : Nat) : stoppingTime (2 ^ 10 * m + 1759) 10 :=
  stoppingTime_of_classCertificate certificate_1759 m

/-- Checked base and every prefix for input 1761. -/
theorem certificate_1761 : classCertificateB 2 1761 = true := by
  decide

/-- The same exact first-descent time holds on an infinite dyadic ray. -/
theorem ray_1761 (m : Nat) : stoppingTime (2 ^ 2 * m + 1761) 2 :=
  stoppingTime_of_classCertificate certificate_1761 m

/-- Checked base and every prefix for input 1763. -/
theorem certificate_1763 : classCertificateB 4 1763 = true := by
  decide

/-- The same exact first-descent time holds on an infinite dyadic ray. -/
theorem ray_1763 (m : Nat) : stoppingTime (2 ^ 4 * m + 1763) 4 :=
  stoppingTime_of_classCertificate certificate_1763 m

/-- Checked base and every prefix for input 1765. -/
theorem certificate_1765 : classCertificateB 2 1765 = true := by
  decide

/-- The same exact first-descent time holds on an infinite dyadic ray. -/
theorem ray_1765 (m : Nat) : stoppingTime (2 ^ 2 * m + 1765) 2 :=
  stoppingTime_of_classCertificate certificate_1765 m

/-- Checked base and every prefix for input 1767. -/
theorem certificate_1767 : classCertificateB 21 1767 = true := by
  decide

/-- The same exact first-descent time holds on an infinite dyadic ray. -/
theorem ray_1767 (m : Nat) : stoppingTime (2 ^ 21 * m + 1767) 21 :=
  stoppingTime_of_classCertificate certificate_1767 m

/-- Checked base and every prefix for input 1769. -/
theorem certificate_1769 : classCertificateB 2 1769 = true := by
  decide

/-- The same exact first-descent time holds on an infinite dyadic ray. -/
theorem ray_1769 (m : Nat) : stoppingTime (2 ^ 2 * m + 1769) 2 :=
  stoppingTime_of_classCertificate certificate_1769 m

/-- Checked base and every prefix for input 1771. -/
theorem certificate_1771 : classCertificateB 5 1771 = true := by
  decide

/-- The same exact first-descent time holds on an infinite dyadic ray. -/
theorem ray_1771 (m : Nat) : stoppingTime (2 ^ 5 * m + 1771) 5 :=
  stoppingTime_of_classCertificate certificate_1771 m

/-- Checked base and every prefix for input 1773. -/
theorem certificate_1773 : classCertificateB 2 1773 = true := by
  decide

/-- The same exact first-descent time holds on an infinite dyadic ray. -/
theorem ray_1773 (m : Nat) : stoppingTime (2 ^ 2 * m + 1773) 2 :=
  stoppingTime_of_classCertificate certificate_1773 m

/-- Checked base and every prefix for input 1775. -/
theorem certificate_1775 : classCertificateB 15 1775 = true := by
  decide

/-- The same exact first-descent time holds on an infinite dyadic ray. -/
theorem ray_1775 (m : Nat) : stoppingTime (2 ^ 15 * m + 1775) 15 :=
  stoppingTime_of_classCertificate certificate_1775 m

/-- Checked base and every prefix for input 1777. -/
theorem certificate_1777 : classCertificateB 2 1777 = true := by
  decide

/-- The same exact first-descent time holds on an infinite dyadic ray. -/
theorem ray_1777 (m : Nat) : stoppingTime (2 ^ 2 * m + 1777) 2 :=
  stoppingTime_of_classCertificate certificate_1777 m

/-- Checked base and every prefix for input 1779. -/
theorem certificate_1779 : classCertificateB 4 1779 = true := by
  decide

/-- The same exact first-descent time holds on an infinite dyadic ray. -/
theorem ray_1779 (m : Nat) : stoppingTime (2 ^ 4 * m + 1779) 4 :=
  stoppingTime_of_classCertificate certificate_1779 m

/-- Checked base and every prefix for input 1781. -/
theorem certificate_1781 : classCertificateB 2 1781 = true := by
  decide

/-- The same exact first-descent time holds on an infinite dyadic ray. -/
theorem ray_1781 (m : Nat) : stoppingTime (2 ^ 2 * m + 1781) 2 :=
  stoppingTime_of_classCertificate certificate_1781 m

/-- Checked base and every prefix for input 1783. -/
theorem certificate_1783 : classCertificateB 5 1783 = true := by
  decide

/-- The same exact first-descent time holds on an infinite dyadic ray. -/
theorem ray_1783 (m : Nat) : stoppingTime (2 ^ 5 * m + 1783) 5 :=
  stoppingTime_of_classCertificate certificate_1783 m

/-- Checked base and every prefix for input 1785. -/
theorem certificate_1785 : classCertificateB 2 1785 = true := by
  decide

/-- The same exact first-descent time holds on an infinite dyadic ray. -/
theorem ray_1785 (m : Nat) : stoppingTime (2 ^ 2 * m + 1785) 2 :=
  stoppingTime_of_classCertificate certificate_1785 m

/-- Checked base and every prefix for input 1787. -/
theorem certificate_1787 : classCertificateB 12 1787 = true := by
  decide

/-- The same exact first-descent time holds on an infinite dyadic ray. -/
theorem ray_1787 (m : Nat) : stoppingTime (2 ^ 12 * m + 1787) 12 :=
  stoppingTime_of_classCertificate certificate_1787 m

/-- Checked base and every prefix for input 1789. -/
theorem certificate_1789 : classCertificateB 2 1789 = true := by
  decide

/-- The same exact first-descent time holds on an infinite dyadic ray. -/
theorem ray_1789 (m : Nat) : stoppingTime (2 ^ 2 * m + 1789) 2 :=
  stoppingTime_of_classCertificate certificate_1789 m

/-- Checked base and every prefix for input 1791. -/
theorem certificate_1791 : classCertificateB 18 1791 = true := by
  decide

/-- The same exact first-descent time holds on an infinite dyadic ray. -/
theorem ray_1791 (m : Nat) : stoppingTime (2 ^ 18 * m + 1791) 18 :=
  stoppingTime_of_classCertificate certificate_1791 m

/-- Checked base and every prefix for input 1793. -/
theorem certificate_1793 : classCertificateB 2 1793 = true := by
  decide

/-- The same exact first-descent time holds on an infinite dyadic ray. -/
theorem ray_1793 (m : Nat) : stoppingTime (2 ^ 2 * m + 1793) 2 :=
  stoppingTime_of_classCertificate certificate_1793 m

/-- Checked base and every prefix for input 1795. -/
theorem certificate_1795 : classCertificateB 4 1795 = true := by
  decide

/-- The same exact first-descent time holds on an infinite dyadic ray. -/
theorem ray_1795 (m : Nat) : stoppingTime (2 ^ 4 * m + 1795) 4 :=
  stoppingTime_of_classCertificate certificate_1795 m

/-- Checked base and every prefix for input 1797. -/
theorem certificate_1797 : classCertificateB 2 1797 = true := by
  decide

/-- The same exact first-descent time holds on an infinite dyadic ray. -/
theorem ray_1797 (m : Nat) : stoppingTime (2 ^ 2 * m + 1797) 2 :=
  stoppingTime_of_classCertificate certificate_1797 m

/-- Checked base and every prefix for input 1799. -/
theorem certificate_1799 : classCertificateB 7 1799 = true := by
  decide

/-- The same exact first-descent time holds on an infinite dyadic ray. -/
theorem ray_1799 (m : Nat) : stoppingTime (2 ^ 7 * m + 1799) 7 :=
  stoppingTime_of_classCertificate certificate_1799 m

/-- Checked base and every prefix for input 1801. -/
theorem certificate_1801 : classCertificateB 2 1801 = true := by
  decide

/-- The same exact first-descent time holds on an infinite dyadic ray. -/
theorem ray_1801 (m : Nat) : stoppingTime (2 ^ 2 * m + 1801) 2 :=
  stoppingTime_of_classCertificate certificate_1801 m

/-- Checked base and every prefix for input 1803. -/
theorem certificate_1803 : classCertificateB 5 1803 = true := by
  decide

/-- The same exact first-descent time holds on an infinite dyadic ray. -/
theorem ray_1803 (m : Nat) : stoppingTime (2 ^ 5 * m + 1803) 5 :=
  stoppingTime_of_classCertificate certificate_1803 m

/-- Checked base and every prefix for input 1805. -/
theorem certificate_1805 : classCertificateB 2 1805 = true := by
  decide

/-- The same exact first-descent time holds on an infinite dyadic ray. -/
theorem ray_1805 (m : Nat) : stoppingTime (2 ^ 2 * m + 1805) 2 :=
  stoppingTime_of_classCertificate certificate_1805 m

/-- Checked base and every prefix for input 1807. -/
theorem certificate_1807 : classCertificateB 7 1807 = true := by
  decide

/-- The same exact first-descent time holds on an infinite dyadic ray. -/
theorem ray_1807 (m : Nat) : stoppingTime (2 ^ 7 * m + 1807) 7 :=
  stoppingTime_of_classCertificate certificate_1807 m

/-- Checked base and every prefix for input 1809. -/
theorem certificate_1809 : classCertificateB 2 1809 = true := by
  decide

/-- The same exact first-descent time holds on an infinite dyadic ray. -/
theorem ray_1809 (m : Nat) : stoppingTime (2 ^ 2 * m + 1809) 2 :=
  stoppingTime_of_classCertificate certificate_1809 m

/-- Exhaustive coverage of the odd inputs in this batch, with no gaps. -/
theorem coverage : CertifiedRange 1743 1811 := by
  intro n hlo hhi hodd
  have hn : n = 1743 ∨ n = 1745 ∨ n = 1747 ∨ n = 1749 ∨ n = 1751 ∨ n = 1753 ∨ n = 1755 ∨ n = 1757 ∨ n = 1759 ∨ n = 1761 ∨ n = 1763 ∨ n = 1765 ∨ n = 1767 ∨ n = 1769 ∨ n = 1771 ∨ n = 1773 ∨ n = 1775 ∨ n = 1777 ∨ n = 1779 ∨ n = 1781 ∨ n = 1783 ∨ n = 1785 ∨ n = 1787 ∨ n = 1789 ∨ n = 1791 ∨ n = 1793 ∨ n = 1795 ∨ n = 1797 ∨ n = 1799 ∨ n = 1801 ∨ n = 1803 ∨ n = 1805 ∨ n = 1807 ∨ n = 1809 := by omega
  rcases hn with h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h
  · subst n
    exact ⟨35, witness_of_certificate certificate_1743⟩
  · subst n
    exact ⟨2, witness_of_certificate certificate_1745⟩
  · subst n
    exact ⟨4, witness_of_certificate certificate_1747⟩
  · subst n
    exact ⟨2, witness_of_certificate certificate_1749⟩
  · subst n
    exact ⟨5, witness_of_certificate certificate_1751⟩
  · subst n
    exact ⟨2, witness_of_certificate certificate_1753⟩
  · subst n
    exact ⟨8, witness_of_certificate certificate_1755⟩
  · subst n
    exact ⟨2, witness_of_certificate certificate_1757⟩
  · subst n
    exact ⟨10, witness_of_certificate certificate_1759⟩
  · subst n
    exact ⟨2, witness_of_certificate certificate_1761⟩
  · subst n
    exact ⟨4, witness_of_certificate certificate_1763⟩
  · subst n
    exact ⟨2, witness_of_certificate certificate_1765⟩
  · subst n
    exact ⟨21, witness_of_certificate certificate_1767⟩
  · subst n
    exact ⟨2, witness_of_certificate certificate_1769⟩
  · subst n
    exact ⟨5, witness_of_certificate certificate_1771⟩
  · subst n
    exact ⟨2, witness_of_certificate certificate_1773⟩
  · subst n
    exact ⟨15, witness_of_certificate certificate_1775⟩
  · subst n
    exact ⟨2, witness_of_certificate certificate_1777⟩
  · subst n
    exact ⟨4, witness_of_certificate certificate_1779⟩
  · subst n
    exact ⟨2, witness_of_certificate certificate_1781⟩
  · subst n
    exact ⟨5, witness_of_certificate certificate_1783⟩
  · subst n
    exact ⟨2, witness_of_certificate certificate_1785⟩
  · subst n
    exact ⟨12, witness_of_certificate certificate_1787⟩
  · subst n
    exact ⟨2, witness_of_certificate certificate_1789⟩
  · subst n
    exact ⟨18, witness_of_certificate certificate_1791⟩
  · subst n
    exact ⟨2, witness_of_certificate certificate_1793⟩
  · subst n
    exact ⟨4, witness_of_certificate certificate_1795⟩
  · subst n
    exact ⟨2, witness_of_certificate certificate_1797⟩
  · subst n
    exact ⟨7, witness_of_certificate certificate_1799⟩
  · subst n
    exact ⟨2, witness_of_certificate certificate_1801⟩
  · subst n
    exact ⟨5, witness_of_certificate certificate_1803⟩
  · subst n
    exact ⟨2, witness_of_certificate certificate_1805⟩
  · subst n
    exact ⟨7, witness_of_certificate certificate_1807⟩
  · subst n
    exact ⟨2, witness_of_certificate certificate_1809⟩

end Collatz.Research.CoefficientDescent.Batch027
