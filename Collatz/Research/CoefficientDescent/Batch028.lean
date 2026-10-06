import Collatz.Research.CoefficientDescent.Basic

namespace Collatz.Research.CoefficientDescent.Batch028

open FirstDescentClass

set_option maxRecDepth 20000
set_option maxHeartbeats 0

/-- Checked base and every prefix for input 1811. -/
theorem certificate_1811 : classCertificateB 4 1811 = true := by
  decide

/-- The same exact first-descent time holds on an infinite dyadic ray. -/
theorem ray_1811 (m : Nat) : stoppingTime (2 ^ 4 * m + 1811) 4 :=
  stoppingTime_of_classCertificate certificate_1811 m

/-- Checked base and every prefix for input 1813. -/
theorem certificate_1813 : classCertificateB 2 1813 = true := by
  decide

/-- The same exact first-descent time holds on an infinite dyadic ray. -/
theorem ray_1813 (m : Nat) : stoppingTime (2 ^ 2 * m + 1813) 2 :=
  stoppingTime_of_classCertificate certificate_1813 m

/-- Checked base and every prefix for input 1815. -/
theorem certificate_1815 : classCertificateB 5 1815 = true := by
  decide

/-- The same exact first-descent time holds on an infinite dyadic ray. -/
theorem ray_1815 (m : Nat) : stoppingTime (2 ^ 5 * m + 1815) 5 :=
  stoppingTime_of_classCertificate certificate_1815 m

/-- Checked base and every prefix for input 1817. -/
theorem certificate_1817 : classCertificateB 2 1817 = true := by
  decide

/-- The same exact first-descent time holds on an infinite dyadic ray. -/
theorem ray_1817 (m : Nat) : stoppingTime (2 ^ 2 * m + 1817) 2 :=
  stoppingTime_of_classCertificate certificate_1817 m

/-- Checked base and every prefix for input 1819. -/
theorem certificate_1819 : classCertificateB 61 1819 = true := by
  decide

/-- The same exact first-descent time holds on an infinite dyadic ray. -/
theorem ray_1819 (m : Nat) : stoppingTime (2 ^ 61 * m + 1819) 61 :=
  stoppingTime_of_classCertificate certificate_1819 m

/-- Checked base and every prefix for input 1821. -/
theorem certificate_1821 : classCertificateB 2 1821 = true := by
  decide

/-- The same exact first-descent time holds on an infinite dyadic ray. -/
theorem ray_1821 (m : Nat) : stoppingTime (2 ^ 2 * m + 1821) 2 :=
  stoppingTime_of_classCertificate certificate_1821 m

/-- Checked base and every prefix for input 1823. -/
theorem certificate_1823 : classCertificateB 12 1823 = true := by
  decide

/-- The same exact first-descent time holds on an infinite dyadic ray. -/
theorem ray_1823 (m : Nat) : stoppingTime (2 ^ 12 * m + 1823) 12 :=
  stoppingTime_of_classCertificate certificate_1823 m

/-- Checked base and every prefix for input 1825. -/
theorem certificate_1825 : classCertificateB 2 1825 = true := by
  decide

/-- The same exact first-descent time holds on an infinite dyadic ray. -/
theorem ray_1825 (m : Nat) : stoppingTime (2 ^ 2 * m + 1825) 2 :=
  stoppingTime_of_classCertificate certificate_1825 m

/-- Checked base and every prefix for input 1827. -/
theorem certificate_1827 : classCertificateB 4 1827 = true := by
  decide

/-- The same exact first-descent time holds on an infinite dyadic ray. -/
theorem ray_1827 (m : Nat) : stoppingTime (2 ^ 4 * m + 1827) 4 :=
  stoppingTime_of_classCertificate certificate_1827 m

/-- Checked base and every prefix for input 1829. -/
theorem certificate_1829 : classCertificateB 2 1829 = true := by
  decide

/-- The same exact first-descent time holds on an infinite dyadic ray. -/
theorem ray_1829 (m : Nat) : stoppingTime (2 ^ 2 * m + 1829) 2 :=
  stoppingTime_of_classCertificate certificate_1829 m

/-- Checked base and every prefix for input 1831. -/
theorem certificate_1831 : classCertificateB 8 1831 = true := by
  decide

/-- The same exact first-descent time holds on an infinite dyadic ray. -/
theorem ray_1831 (m : Nat) : stoppingTime (2 ^ 8 * m + 1831) 8 :=
  stoppingTime_of_classCertificate certificate_1831 m

/-- Checked base and every prefix for input 1833. -/
theorem certificate_1833 : classCertificateB 2 1833 = true := by
  decide

/-- The same exact first-descent time holds on an infinite dyadic ray. -/
theorem ray_1833 (m : Nat) : stoppingTime (2 ^ 2 * m + 1833) 2 :=
  stoppingTime_of_classCertificate certificate_1833 m

/-- Checked base and every prefix for input 1835. -/
theorem certificate_1835 : classCertificateB 5 1835 = true := by
  decide

/-- The same exact first-descent time holds on an infinite dyadic ray. -/
theorem ray_1835 (m : Nat) : stoppingTime (2 ^ 5 * m + 1835) 5 :=
  stoppingTime_of_classCertificate certificate_1835 m

/-- Checked base and every prefix for input 1837. -/
theorem certificate_1837 : classCertificateB 2 1837 = true := by
  decide

/-- The same exact first-descent time holds on an infinite dyadic ray. -/
theorem ray_1837 (m : Nat) : stoppingTime (2 ^ 2 * m + 1837) 2 :=
  stoppingTime_of_classCertificate certificate_1837 m

/-- Checked base and every prefix for input 1839. -/
theorem certificate_1839 : classCertificateB 10 1839 = true := by
  decide

/-- The same exact first-descent time holds on an infinite dyadic ray. -/
theorem ray_1839 (m : Nat) : stoppingTime (2 ^ 10 * m + 1839) 10 :=
  stoppingTime_of_classCertificate certificate_1839 m

/-- Checked base and every prefix for input 1841. -/
theorem certificate_1841 : classCertificateB 2 1841 = true := by
  decide

/-- The same exact first-descent time holds on an infinite dyadic ray. -/
theorem ray_1841 (m : Nat) : stoppingTime (2 ^ 2 * m + 1841) 2 :=
  stoppingTime_of_classCertificate certificate_1841 m

/-- Checked base and every prefix for input 1843. -/
theorem certificate_1843 : classCertificateB 4 1843 = true := by
  decide

/-- The same exact first-descent time holds on an infinite dyadic ray. -/
theorem ray_1843 (m : Nat) : stoppingTime (2 ^ 4 * m + 1843) 4 :=
  stoppingTime_of_classCertificate certificate_1843 m

/-- Checked base and every prefix for input 1845. -/
theorem certificate_1845 : classCertificateB 2 1845 = true := by
  decide

/-- The same exact first-descent time holds on an infinite dyadic ray. -/
theorem ray_1845 (m : Nat) : stoppingTime (2 ^ 2 * m + 1845) 2 :=
  stoppingTime_of_classCertificate certificate_1845 m

/-- Checked base and every prefix for input 1847. -/
theorem certificate_1847 : classCertificateB 5 1847 = true := by
  decide

/-- The same exact first-descent time holds on an infinite dyadic ray. -/
theorem ray_1847 (m : Nat) : stoppingTime (2 ^ 5 * m + 1847) 5 :=
  stoppingTime_of_classCertificate certificate_1847 m

/-- Checked base and every prefix for input 1849. -/
theorem certificate_1849 : classCertificateB 2 1849 = true := by
  decide

/-- The same exact first-descent time holds on an infinite dyadic ray. -/
theorem ray_1849 (m : Nat) : stoppingTime (2 ^ 2 * m + 1849) 2 :=
  stoppingTime_of_classCertificate certificate_1849 m

/-- Checked base and every prefix for input 1851. -/
theorem certificate_1851 : classCertificateB 7 1851 = true := by
  decide

/-- The same exact first-descent time holds on an infinite dyadic ray. -/
theorem ray_1851 (m : Nat) : stoppingTime (2 ^ 7 * m + 1851) 7 :=
  stoppingTime_of_classCertificate certificate_1851 m

/-- Checked base and every prefix for input 1853. -/
theorem certificate_1853 : classCertificateB 2 1853 = true := by
  decide

/-- The same exact first-descent time holds on an infinite dyadic ray. -/
theorem ray_1853 (m : Nat) : stoppingTime (2 ^ 2 * m + 1853) 2 :=
  stoppingTime_of_classCertificate certificate_1853 m

/-- Checked base and every prefix for input 1855. -/
theorem certificate_1855 : classCertificateB 12 1855 = true := by
  decide

/-- The same exact first-descent time holds on an infinite dyadic ray. -/
theorem ray_1855 (m : Nat) : stoppingTime (2 ^ 12 * m + 1855) 12 :=
  stoppingTime_of_classCertificate certificate_1855 m

/-- Checked base and every prefix for input 1857. -/
theorem certificate_1857 : classCertificateB 2 1857 = true := by
  decide

/-- The same exact first-descent time holds on an infinite dyadic ray. -/
theorem ray_1857 (m : Nat) : stoppingTime (2 ^ 2 * m + 1857) 2 :=
  stoppingTime_of_classCertificate certificate_1857 m

/-- Checked base and every prefix for input 1859. -/
theorem certificate_1859 : classCertificateB 4 1859 = true := by
  decide

/-- The same exact first-descent time holds on an infinite dyadic ray. -/
theorem ray_1859 (m : Nat) : stoppingTime (2 ^ 4 * m + 1859) 4 :=
  stoppingTime_of_classCertificate certificate_1859 m

/-- Checked base and every prefix for input 1861. -/
theorem certificate_1861 : classCertificateB 2 1861 = true := by
  decide

/-- The same exact first-descent time holds on an infinite dyadic ray. -/
theorem ray_1861 (m : Nat) : stoppingTime (2 ^ 2 * m + 1861) 2 :=
  stoppingTime_of_classCertificate certificate_1861 m

/-- Checked base and every prefix for input 1863. -/
theorem certificate_1863 : classCertificateB 23 1863 = true := by
  decide

/-- The same exact first-descent time holds on an infinite dyadic ray. -/
theorem ray_1863 (m : Nat) : stoppingTime (2 ^ 23 * m + 1863) 23 :=
  stoppingTime_of_classCertificate certificate_1863 m

/-- Checked base and every prefix for input 1865. -/
theorem certificate_1865 : classCertificateB 2 1865 = true := by
  decide

/-- The same exact first-descent time holds on an infinite dyadic ray. -/
theorem ray_1865 (m : Nat) : stoppingTime (2 ^ 2 * m + 1865) 2 :=
  stoppingTime_of_classCertificate certificate_1865 m

/-- Checked base and every prefix for input 1867. -/
theorem certificate_1867 : classCertificateB 5 1867 = true := by
  decide

/-- The same exact first-descent time holds on an infinite dyadic ray. -/
theorem ray_1867 (m : Nat) : stoppingTime (2 ^ 5 * m + 1867) 5 :=
  stoppingTime_of_classCertificate certificate_1867 m

/-- Checked base and every prefix for input 1869. -/
theorem certificate_1869 : classCertificateB 2 1869 = true := by
  decide

/-- The same exact first-descent time holds on an infinite dyadic ray. -/
theorem ray_1869 (m : Nat) : stoppingTime (2 ^ 2 * m + 1869) 2 :=
  stoppingTime_of_classCertificate certificate_1869 m

/-- Checked base and every prefix for input 1871. -/
theorem certificate_1871 : classCertificateB 8 1871 = true := by
  decide

/-- The same exact first-descent time holds on an infinite dyadic ray. -/
theorem ray_1871 (m : Nat) : stoppingTime (2 ^ 8 * m + 1871) 8 :=
  stoppingTime_of_classCertificate certificate_1871 m

/-- Checked base and every prefix for input 1873. -/
theorem certificate_1873 : classCertificateB 2 1873 = true := by
  decide

/-- The same exact first-descent time holds on an infinite dyadic ray. -/
theorem ray_1873 (m : Nat) : stoppingTime (2 ^ 2 * m + 1873) 2 :=
  stoppingTime_of_classCertificate certificate_1873 m

/-- Checked base and every prefix for input 1875. -/
theorem certificate_1875 : classCertificateB 4 1875 = true := by
  decide

/-- The same exact first-descent time holds on an infinite dyadic ray. -/
theorem ray_1875 (m : Nat) : stoppingTime (2 ^ 4 * m + 1875) 4 :=
  stoppingTime_of_classCertificate certificate_1875 m

/-- Exhaustive coverage of the odd inputs in this batch, with no gaps. -/
theorem coverage : CertifiedRange 1811 1877 := by
  intro n hlo hhi hodd
  have hn : n = 1811 ∨ n = 1813 ∨ n = 1815 ∨ n = 1817 ∨ n = 1819 ∨ n = 1821 ∨ n = 1823 ∨ n = 1825 ∨ n = 1827 ∨ n = 1829 ∨ n = 1831 ∨ n = 1833 ∨ n = 1835 ∨ n = 1837 ∨ n = 1839 ∨ n = 1841 ∨ n = 1843 ∨ n = 1845 ∨ n = 1847 ∨ n = 1849 ∨ n = 1851 ∨ n = 1853 ∨ n = 1855 ∨ n = 1857 ∨ n = 1859 ∨ n = 1861 ∨ n = 1863 ∨ n = 1865 ∨ n = 1867 ∨ n = 1869 ∨ n = 1871 ∨ n = 1873 ∨ n = 1875 := by omega
  rcases hn with h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h
  · subst n
    exact ⟨4, witness_of_certificate certificate_1811⟩
  · subst n
    exact ⟨2, witness_of_certificate certificate_1813⟩
  · subst n
    exact ⟨5, witness_of_certificate certificate_1815⟩
  · subst n
    exact ⟨2, witness_of_certificate certificate_1817⟩
  · subst n
    exact ⟨61, witness_of_certificate certificate_1819⟩
  · subst n
    exact ⟨2, witness_of_certificate certificate_1821⟩
  · subst n
    exact ⟨12, witness_of_certificate certificate_1823⟩
  · subst n
    exact ⟨2, witness_of_certificate certificate_1825⟩
  · subst n
    exact ⟨4, witness_of_certificate certificate_1827⟩
  · subst n
    exact ⟨2, witness_of_certificate certificate_1829⟩
  · subst n
    exact ⟨8, witness_of_certificate certificate_1831⟩
  · subst n
    exact ⟨2, witness_of_certificate certificate_1833⟩
  · subst n
    exact ⟨5, witness_of_certificate certificate_1835⟩
  · subst n
    exact ⟨2, witness_of_certificate certificate_1837⟩
  · subst n
    exact ⟨10, witness_of_certificate certificate_1839⟩
  · subst n
    exact ⟨2, witness_of_certificate certificate_1841⟩
  · subst n
    exact ⟨4, witness_of_certificate certificate_1843⟩
  · subst n
    exact ⟨2, witness_of_certificate certificate_1845⟩
  · subst n
    exact ⟨5, witness_of_certificate certificate_1847⟩
  · subst n
    exact ⟨2, witness_of_certificate certificate_1849⟩
  · subst n
    exact ⟨7, witness_of_certificate certificate_1851⟩
  · subst n
    exact ⟨2, witness_of_certificate certificate_1853⟩
  · subst n
    exact ⟨12, witness_of_certificate certificate_1855⟩
  · subst n
    exact ⟨2, witness_of_certificate certificate_1857⟩
  · subst n
    exact ⟨4, witness_of_certificate certificate_1859⟩
  · subst n
    exact ⟨2, witness_of_certificate certificate_1861⟩
  · subst n
    exact ⟨23, witness_of_certificate certificate_1863⟩
  · subst n
    exact ⟨2, witness_of_certificate certificate_1865⟩
  · subst n
    exact ⟨5, witness_of_certificate certificate_1867⟩
  · subst n
    exact ⟨2, witness_of_certificate certificate_1869⟩
  · subst n
    exact ⟨8, witness_of_certificate certificate_1871⟩
  · subst n
    exact ⟨2, witness_of_certificate certificate_1873⟩
  · subst n
    exact ⟨4, witness_of_certificate certificate_1875⟩

end Collatz.Research.CoefficientDescent.Batch028
