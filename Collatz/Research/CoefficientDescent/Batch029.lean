import Collatz.Research.CoefficientDescent.Basic

namespace Collatz.Research.CoefficientDescent.Batch029

open FirstDescentClass

set_option maxRecDepth 20000
set_option maxHeartbeats 0

/-- Checked base and every prefix for input 1877. -/
theorem certificate_1877 : classCertificateB 2 1877 = true := by
  decide

/-- The same exact first-descent time holds on an infinite dyadic ray. -/
theorem ray_1877 (m : Nat) : stoppingTime (2 ^ 2 * m + 1877) 2 :=
  stoppingTime_of_classCertificate certificate_1877 m

/-- Checked base and every prefix for input 1879. -/
theorem certificate_1879 : classCertificateB 5 1879 = true := by
  decide

/-- The same exact first-descent time holds on an infinite dyadic ray. -/
theorem ray_1879 (m : Nat) : stoppingTime (2 ^ 5 * m + 1879) 5 :=
  stoppingTime_of_classCertificate certificate_1879 m

/-- Checked base and every prefix for input 1881. -/
theorem certificate_1881 : classCertificateB 2 1881 = true := by
  decide

/-- The same exact first-descent time holds on an infinite dyadic ray. -/
theorem ray_1881 (m : Nat) : stoppingTime (2 ^ 2 * m + 1881) 2 :=
  stoppingTime_of_classCertificate certificate_1881 m

/-- Checked base and every prefix for input 1883. -/
theorem certificate_1883 : classCertificateB 18 1883 = true := by
  decide

/-- The same exact first-descent time holds on an infinite dyadic ray. -/
theorem ray_1883 (m : Nat) : stoppingTime (2 ^ 18 * m + 1883) 18 :=
  stoppingTime_of_classCertificate certificate_1883 m

/-- Checked base and every prefix for input 1885. -/
theorem certificate_1885 : classCertificateB 2 1885 = true := by
  decide

/-- The same exact first-descent time holds on an infinite dyadic ray. -/
theorem ray_1885 (m : Nat) : stoppingTime (2 ^ 2 * m + 1885) 2 :=
  stoppingTime_of_classCertificate certificate_1885 m

/-- Checked base and every prefix for input 1887. -/
theorem certificate_1887 : classCertificateB 8 1887 = true := by
  decide

/-- The same exact first-descent time holds on an infinite dyadic ray. -/
theorem ray_1887 (m : Nat) : stoppingTime (2 ^ 8 * m + 1887) 8 :=
  stoppingTime_of_classCertificate certificate_1887 m

/-- Checked base and every prefix for input 1889. -/
theorem certificate_1889 : classCertificateB 2 1889 = true := by
  decide

/-- The same exact first-descent time holds on an infinite dyadic ray. -/
theorem ray_1889 (m : Nat) : stoppingTime (2 ^ 2 * m + 1889) 2 :=
  stoppingTime_of_classCertificate certificate_1889 m

/-- Checked base and every prefix for input 1891. -/
theorem certificate_1891 : classCertificateB 4 1891 = true := by
  decide

/-- The same exact first-descent time holds on an infinite dyadic ray. -/
theorem ray_1891 (m : Nat) : stoppingTime (2 ^ 4 * m + 1891) 4 :=
  stoppingTime_of_classCertificate certificate_1891 m

/-- Checked base and every prefix for input 1893. -/
theorem certificate_1893 : classCertificateB 2 1893 = true := by
  decide

/-- The same exact first-descent time holds on an infinite dyadic ray. -/
theorem ray_1893 (m : Nat) : stoppingTime (2 ^ 2 * m + 1893) 2 :=
  stoppingTime_of_classCertificate certificate_1893 m

/-- Checked base and every prefix for input 1895. -/
theorem certificate_1895 : classCertificateB 24 1895 = true := by
  decide

/-- The same exact first-descent time holds on an infinite dyadic ray. -/
theorem ray_1895 (m : Nat) : stoppingTime (2 ^ 24 * m + 1895) 24 :=
  stoppingTime_of_classCertificate certificate_1895 m

/-- Checked base and every prefix for input 1897. -/
theorem certificate_1897 : classCertificateB 2 1897 = true := by
  decide

/-- The same exact first-descent time holds on an infinite dyadic ray. -/
theorem ray_1897 (m : Nat) : stoppingTime (2 ^ 2 * m + 1897) 2 :=
  stoppingTime_of_classCertificate certificate_1897 m

/-- Checked base and every prefix for input 1899. -/
theorem certificate_1899 : classCertificateB 5 1899 = true := by
  decide

/-- The same exact first-descent time holds on an infinite dyadic ray. -/
theorem ray_1899 (m : Nat) : stoppingTime (2 ^ 5 * m + 1899) 5 :=
  stoppingTime_of_classCertificate certificate_1899 m

/-- Checked base and every prefix for input 1901. -/
theorem certificate_1901 : classCertificateB 2 1901 = true := by
  decide

/-- The same exact first-descent time holds on an infinite dyadic ray. -/
theorem ray_1901 (m : Nat) : stoppingTime (2 ^ 2 * m + 1901) 2 :=
  stoppingTime_of_classCertificate certificate_1901 m

/-- Checked base and every prefix for input 1903. -/
theorem certificate_1903 : classCertificateB 15 1903 = true := by
  decide

/-- The same exact first-descent time holds on an infinite dyadic ray. -/
theorem ray_1903 (m : Nat) : stoppingTime (2 ^ 15 * m + 1903) 15 :=
  stoppingTime_of_classCertificate certificate_1903 m

/-- Checked base and every prefix for input 1905. -/
theorem certificate_1905 : classCertificateB 2 1905 = true := by
  decide

/-- The same exact first-descent time holds on an infinite dyadic ray. -/
theorem ray_1905 (m : Nat) : stoppingTime (2 ^ 2 * m + 1905) 2 :=
  stoppingTime_of_classCertificate certificate_1905 m

/-- Checked base and every prefix for input 1907. -/
theorem certificate_1907 : classCertificateB 4 1907 = true := by
  decide

/-- The same exact first-descent time holds on an infinite dyadic ray. -/
theorem ray_1907 (m : Nat) : stoppingTime (2 ^ 4 * m + 1907) 4 :=
  stoppingTime_of_classCertificate certificate_1907 m

/-- Checked base and every prefix for input 1909. -/
theorem certificate_1909 : classCertificateB 2 1909 = true := by
  decide

/-- The same exact first-descent time holds on an infinite dyadic ray. -/
theorem ray_1909 (m : Nat) : stoppingTime (2 ^ 2 * m + 1909) 2 :=
  stoppingTime_of_classCertificate certificate_1909 m

/-- Checked base and every prefix for input 1911. -/
theorem certificate_1911 : classCertificateB 5 1911 = true := by
  decide

/-- The same exact first-descent time holds on an infinite dyadic ray. -/
theorem ray_1911 (m : Nat) : stoppingTime (2 ^ 5 * m + 1911) 5 :=
  stoppingTime_of_classCertificate certificate_1911 m

/-- Checked base and every prefix for input 1913. -/
theorem certificate_1913 : classCertificateB 2 1913 = true := by
  decide

/-- The same exact first-descent time holds on an infinite dyadic ray. -/
theorem ray_1913 (m : Nat) : stoppingTime (2 ^ 2 * m + 1913) 2 :=
  stoppingTime_of_classCertificate certificate_1913 m

/-- Checked base and every prefix for input 1915. -/
theorem certificate_1915 : classCertificateB 8 1915 = true := by
  decide

/-- The same exact first-descent time holds on an infinite dyadic ray. -/
theorem ray_1915 (m : Nat) : stoppingTime (2 ^ 8 * m + 1915) 8 :=
  stoppingTime_of_classCertificate certificate_1915 m

/-- Checked base and every prefix for input 1917. -/
theorem certificate_1917 : classCertificateB 2 1917 = true := by
  decide

/-- The same exact first-descent time holds on an infinite dyadic ray. -/
theorem ray_1917 (m : Nat) : stoppingTime (2 ^ 2 * m + 1917) 2 :=
  stoppingTime_of_classCertificate certificate_1917 m

/-- Checked base and every prefix for input 1919. -/
theorem certificate_1919 : classCertificateB 21 1919 = true := by
  decide

/-- The same exact first-descent time holds on an infinite dyadic ray. -/
theorem ray_1919 (m : Nat) : stoppingTime (2 ^ 21 * m + 1919) 21 :=
  stoppingTime_of_classCertificate certificate_1919 m

/-- Checked base and every prefix for input 1921. -/
theorem certificate_1921 : classCertificateB 2 1921 = true := by
  decide

/-- The same exact first-descent time holds on an infinite dyadic ray. -/
theorem ray_1921 (m : Nat) : stoppingTime (2 ^ 2 * m + 1921) 2 :=
  stoppingTime_of_classCertificate certificate_1921 m

/-- Checked base and every prefix for input 1923. -/
theorem certificate_1923 : classCertificateB 4 1923 = true := by
  decide

/-- The same exact first-descent time holds on an infinite dyadic ray. -/
theorem ray_1923 (m : Nat) : stoppingTime (2 ^ 4 * m + 1923) 4 :=
  stoppingTime_of_classCertificate certificate_1923 m

/-- Checked base and every prefix for input 1925. -/
theorem certificate_1925 : classCertificateB 2 1925 = true := by
  decide

/-- The same exact first-descent time holds on an infinite dyadic ray. -/
theorem ray_1925 (m : Nat) : stoppingTime (2 ^ 2 * m + 1925) 2 :=
  stoppingTime_of_classCertificate certificate_1925 m

/-- Checked base and every prefix for input 1927. -/
theorem certificate_1927 : classCertificateB 7 1927 = true := by
  decide

/-- The same exact first-descent time holds on an infinite dyadic ray. -/
theorem ray_1927 (m : Nat) : stoppingTime (2 ^ 7 * m + 1927) 7 :=
  stoppingTime_of_classCertificate certificate_1927 m

/-- Checked base and every prefix for input 1929. -/
theorem certificate_1929 : classCertificateB 2 1929 = true := by
  decide

/-- The same exact first-descent time holds on an infinite dyadic ray. -/
theorem ray_1929 (m : Nat) : stoppingTime (2 ^ 2 * m + 1929) 2 :=
  stoppingTime_of_classCertificate certificate_1929 m

/-- Checked base and every prefix for input 1931. -/
theorem certificate_1931 : classCertificateB 5 1931 = true := by
  decide

/-- The same exact first-descent time holds on an infinite dyadic ray. -/
theorem ray_1931 (m : Nat) : stoppingTime (2 ^ 5 * m + 1931) 5 :=
  stoppingTime_of_classCertificate certificate_1931 m

/-- Checked base and every prefix for input 1933. -/
theorem certificate_1933 : classCertificateB 2 1933 = true := by
  decide

/-- The same exact first-descent time holds on an infinite dyadic ray. -/
theorem ray_1933 (m : Nat) : stoppingTime (2 ^ 2 * m + 1933) 2 :=
  stoppingTime_of_classCertificate certificate_1933 m

/-- Checked base and every prefix for input 1935. -/
theorem certificate_1935 : classCertificateB 7 1935 = true := by
  decide

/-- The same exact first-descent time holds on an infinite dyadic ray. -/
theorem ray_1935 (m : Nat) : stoppingTime (2 ^ 7 * m + 1935) 7 :=
  stoppingTime_of_classCertificate certificate_1935 m

/-- Checked base and every prefix for input 1937. -/
theorem certificate_1937 : classCertificateB 2 1937 = true := by
  decide

/-- The same exact first-descent time holds on an infinite dyadic ray. -/
theorem ray_1937 (m : Nat) : stoppingTime (2 ^ 2 * m + 1937) 2 :=
  stoppingTime_of_classCertificate certificate_1937 m

/-- Checked base and every prefix for input 1939. -/
theorem certificate_1939 : classCertificateB 4 1939 = true := by
  decide

/-- The same exact first-descent time holds on an infinite dyadic ray. -/
theorem ray_1939 (m : Nat) : stoppingTime (2 ^ 4 * m + 1939) 4 :=
  stoppingTime_of_classCertificate certificate_1939 m

/-- Checked base and every prefix for input 1941. -/
theorem certificate_1941 : classCertificateB 2 1941 = true := by
  decide

/-- The same exact first-descent time holds on an infinite dyadic ray. -/
theorem ray_1941 (m : Nat) : stoppingTime (2 ^ 2 * m + 1941) 2 :=
  stoppingTime_of_classCertificate certificate_1941 m

/-- Checked base and every prefix for input 1943. -/
theorem certificate_1943 : classCertificateB 5 1943 = true := by
  decide

/-- The same exact first-descent time holds on an infinite dyadic ray. -/
theorem ray_1943 (m : Nat) : stoppingTime (2 ^ 5 * m + 1943) 5 :=
  stoppingTime_of_classCertificate certificate_1943 m

/-- Exhaustive coverage of the odd inputs in this batch, with no gaps. -/
theorem coverage : CertifiedRange 1877 1945 := by
  intro n hlo hhi hodd
  have hn : n = 1877 ∨ n = 1879 ∨ n = 1881 ∨ n = 1883 ∨ n = 1885 ∨ n = 1887 ∨ n = 1889 ∨ n = 1891 ∨ n = 1893 ∨ n = 1895 ∨ n = 1897 ∨ n = 1899 ∨ n = 1901 ∨ n = 1903 ∨ n = 1905 ∨ n = 1907 ∨ n = 1909 ∨ n = 1911 ∨ n = 1913 ∨ n = 1915 ∨ n = 1917 ∨ n = 1919 ∨ n = 1921 ∨ n = 1923 ∨ n = 1925 ∨ n = 1927 ∨ n = 1929 ∨ n = 1931 ∨ n = 1933 ∨ n = 1935 ∨ n = 1937 ∨ n = 1939 ∨ n = 1941 ∨ n = 1943 := by omega
  rcases hn with h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h
  · subst n
    exact ⟨2, witness_of_certificate certificate_1877⟩
  · subst n
    exact ⟨5, witness_of_certificate certificate_1879⟩
  · subst n
    exact ⟨2, witness_of_certificate certificate_1881⟩
  · subst n
    exact ⟨18, witness_of_certificate certificate_1883⟩
  · subst n
    exact ⟨2, witness_of_certificate certificate_1885⟩
  · subst n
    exact ⟨8, witness_of_certificate certificate_1887⟩
  · subst n
    exact ⟨2, witness_of_certificate certificate_1889⟩
  · subst n
    exact ⟨4, witness_of_certificate certificate_1891⟩
  · subst n
    exact ⟨2, witness_of_certificate certificate_1893⟩
  · subst n
    exact ⟨24, witness_of_certificate certificate_1895⟩
  · subst n
    exact ⟨2, witness_of_certificate certificate_1897⟩
  · subst n
    exact ⟨5, witness_of_certificate certificate_1899⟩
  · subst n
    exact ⟨2, witness_of_certificate certificate_1901⟩
  · subst n
    exact ⟨15, witness_of_certificate certificate_1903⟩
  · subst n
    exact ⟨2, witness_of_certificate certificate_1905⟩
  · subst n
    exact ⟨4, witness_of_certificate certificate_1907⟩
  · subst n
    exact ⟨2, witness_of_certificate certificate_1909⟩
  · subst n
    exact ⟨5, witness_of_certificate certificate_1911⟩
  · subst n
    exact ⟨2, witness_of_certificate certificate_1913⟩
  · subst n
    exact ⟨8, witness_of_certificate certificate_1915⟩
  · subst n
    exact ⟨2, witness_of_certificate certificate_1917⟩
  · subst n
    exact ⟨21, witness_of_certificate certificate_1919⟩
  · subst n
    exact ⟨2, witness_of_certificate certificate_1921⟩
  · subst n
    exact ⟨4, witness_of_certificate certificate_1923⟩
  · subst n
    exact ⟨2, witness_of_certificate certificate_1925⟩
  · subst n
    exact ⟨7, witness_of_certificate certificate_1927⟩
  · subst n
    exact ⟨2, witness_of_certificate certificate_1929⟩
  · subst n
    exact ⟨5, witness_of_certificate certificate_1931⟩
  · subst n
    exact ⟨2, witness_of_certificate certificate_1933⟩
  · subst n
    exact ⟨7, witness_of_certificate certificate_1935⟩
  · subst n
    exact ⟨2, witness_of_certificate certificate_1937⟩
  · subst n
    exact ⟨4, witness_of_certificate certificate_1939⟩
  · subst n
    exact ⟨2, witness_of_certificate certificate_1941⟩
  · subst n
    exact ⟨5, witness_of_certificate certificate_1943⟩

end Collatz.Research.CoefficientDescent.Batch029
