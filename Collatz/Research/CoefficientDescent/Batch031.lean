import Collatz.Research.CoefficientDescent.Basic

namespace Collatz.Research.CoefficientDescent.Batch031

open FirstDescentClass

set_option maxRecDepth 20000
set_option maxHeartbeats 0

/-- Checked base and every prefix for input 2011. -/
theorem certificate_2011 : classCertificateB 8 2011 = true := by
  decide

/-- The same exact first-descent time holds on an infinite dyadic ray. -/
theorem ray_2011 (m : Nat) : stoppingTime (2 ^ 8 * m + 2011) 8 :=
  stoppingTime_of_classCertificate certificate_2011 m

/-- Checked base and every prefix for input 2013. -/
theorem certificate_2013 : classCertificateB 2 2013 = true := by
  decide

/-- The same exact first-descent time holds on an infinite dyadic ray. -/
theorem ray_2013 (m : Nat) : stoppingTime (2 ^ 2 * m + 2013) 2 :=
  stoppingTime_of_classCertificate certificate_2013 m

/-- Checked base and every prefix for input 2015. -/
theorem certificate_2015 : classCertificateB 13 2015 = true := by
  decide

/-- The same exact first-descent time holds on an infinite dyadic ray. -/
theorem ray_2015 (m : Nat) : stoppingTime (2 ^ 13 * m + 2015) 13 :=
  stoppingTime_of_classCertificate certificate_2015 m

/-- Checked base and every prefix for input 2017. -/
theorem certificate_2017 : classCertificateB 2 2017 = true := by
  decide

/-- The same exact first-descent time holds on an infinite dyadic ray. -/
theorem ray_2017 (m : Nat) : stoppingTime (2 ^ 2 * m + 2017) 2 :=
  stoppingTime_of_classCertificate certificate_2017 m

/-- Checked base and every prefix for input 2019. -/
theorem certificate_2019 : classCertificateB 4 2019 = true := by
  decide

/-- The same exact first-descent time holds on an infinite dyadic ray. -/
theorem ray_2019 (m : Nat) : stoppingTime (2 ^ 4 * m + 2019) 4 :=
  stoppingTime_of_classCertificate certificate_2019 m

/-- Checked base and every prefix for input 2021. -/
theorem certificate_2021 : classCertificateB 2 2021 = true := by
  decide

/-- The same exact first-descent time holds on an infinite dyadic ray. -/
theorem ray_2021 (m : Nat) : stoppingTime (2 ^ 2 * m + 2021) 2 :=
  stoppingTime_of_classCertificate certificate_2021 m

/-- Checked base and every prefix for input 2023. -/
theorem certificate_2023 : classCertificateB 10 2023 = true := by
  decide

/-- The same exact first-descent time holds on an infinite dyadic ray. -/
theorem ray_2023 (m : Nat) : stoppingTime (2 ^ 10 * m + 2023) 10 :=
  stoppingTime_of_classCertificate certificate_2023 m

/-- Checked base and every prefix for input 2025. -/
theorem certificate_2025 : classCertificateB 2 2025 = true := by
  decide

/-- The same exact first-descent time holds on an infinite dyadic ray. -/
theorem ray_2025 (m : Nat) : stoppingTime (2 ^ 2 * m + 2025) 2 :=
  stoppingTime_of_classCertificate certificate_2025 m

/-- Checked base and every prefix for input 2027. -/
theorem certificate_2027 : classCertificateB 5 2027 = true := by
  decide

/-- The same exact first-descent time holds on an infinite dyadic ray. -/
theorem ray_2027 (m : Nat) : stoppingTime (2 ^ 5 * m + 2027) 5 :=
  stoppingTime_of_classCertificate certificate_2027 m

/-- Checked base and every prefix for input 2029. -/
theorem certificate_2029 : classCertificateB 2 2029 = true := by
  decide

/-- The same exact first-descent time holds on an infinite dyadic ray. -/
theorem ray_2029 (m : Nat) : stoppingTime (2 ^ 2 * m + 2029) 2 :=
  stoppingTime_of_classCertificate certificate_2029 m

/-- Checked base and every prefix for input 2031. -/
theorem certificate_2031 : classCertificateB 12 2031 = true := by
  decide

/-- The same exact first-descent time holds on an infinite dyadic ray. -/
theorem ray_2031 (m : Nat) : stoppingTime (2 ^ 12 * m + 2031) 12 :=
  stoppingTime_of_classCertificate certificate_2031 m

/-- Checked base and every prefix for input 2033. -/
theorem certificate_2033 : classCertificateB 2 2033 = true := by
  decide

/-- The same exact first-descent time holds on an infinite dyadic ray. -/
theorem ray_2033 (m : Nat) : stoppingTime (2 ^ 2 * m + 2033) 2 :=
  stoppingTime_of_classCertificate certificate_2033 m

/-- Checked base and every prefix for input 2035. -/
theorem certificate_2035 : classCertificateB 4 2035 = true := by
  decide

/-- The same exact first-descent time holds on an infinite dyadic ray. -/
theorem ray_2035 (m : Nat) : stoppingTime (2 ^ 4 * m + 2035) 4 :=
  stoppingTime_of_classCertificate certificate_2035 m

/-- Checked base and every prefix for input 2037. -/
theorem certificate_2037 : classCertificateB 2 2037 = true := by
  decide

/-- The same exact first-descent time holds on an infinite dyadic ray. -/
theorem ray_2037 (m : Nat) : stoppingTime (2 ^ 2 * m + 2037) 2 :=
  stoppingTime_of_classCertificate certificate_2037 m

/-- Checked base and every prefix for input 2039. -/
theorem certificate_2039 : classCertificateB 5 2039 = true := by
  decide

/-- The same exact first-descent time holds on an infinite dyadic ray. -/
theorem ray_2039 (m : Nat) : stoppingTime (2 ^ 5 * m + 2039) 5 :=
  stoppingTime_of_classCertificate certificate_2039 m

/-- Checked base and every prefix for input 2041. -/
theorem certificate_2041 : classCertificateB 2 2041 = true := by
  decide

/-- The same exact first-descent time holds on an infinite dyadic ray. -/
theorem ray_2041 (m : Nat) : stoppingTime (2 ^ 2 * m + 2041) 2 :=
  stoppingTime_of_classCertificate certificate_2041 m

/-- Checked base and every prefix for input 2043. -/
theorem certificate_2043 : classCertificateB 18 2043 = true := by
  decide

/-- The same exact first-descent time holds on an infinite dyadic ray. -/
theorem ray_2043 (m : Nat) : stoppingTime (2 ^ 18 * m + 2043) 18 :=
  stoppingTime_of_classCertificate certificate_2043 m

/-- Checked base and every prefix for input 2045. -/
theorem certificate_2045 : classCertificateB 2 2045 = true := by
  decide

/-- The same exact first-descent time holds on an infinite dyadic ray. -/
theorem ray_2045 (m : Nat) : stoppingTime (2 ^ 2 * m + 2045) 2 :=
  stoppingTime_of_classCertificate certificate_2045 m

/-- Checked base and every prefix for input 2047. -/
theorem certificate_2047 : classCertificateB 58 2047 = true := by
  decide

/-- The same exact first-descent time holds on an infinite dyadic ray. -/
theorem ray_2047 (m : Nat) : stoppingTime (2 ^ 58 * m + 2047) 58 :=
  stoppingTime_of_classCertificate certificate_2047 m

/-- Checked base and every prefix for input 2049. -/
theorem certificate_2049 : classCertificateB 2 2049 = true := by
  decide

/-- The same exact first-descent time holds on an infinite dyadic ray. -/
theorem ray_2049 (m : Nat) : stoppingTime (2 ^ 2 * m + 2049) 2 :=
  stoppingTime_of_classCertificate certificate_2049 m

/-- Checked base and every prefix for input 2051. -/
theorem certificate_2051 : classCertificateB 4 2051 = true := by
  decide

/-- The same exact first-descent time holds on an infinite dyadic ray. -/
theorem ray_2051 (m : Nat) : stoppingTime (2 ^ 4 * m + 2051) 4 :=
  stoppingTime_of_classCertificate certificate_2051 m

/-- Checked base and every prefix for input 2053. -/
theorem certificate_2053 : classCertificateB 2 2053 = true := by
  decide

/-- The same exact first-descent time holds on an infinite dyadic ray. -/
theorem ray_2053 (m : Nat) : stoppingTime (2 ^ 2 * m + 2053) 2 :=
  stoppingTime_of_classCertificate certificate_2053 m

/-- Checked base and every prefix for input 2055. -/
theorem certificate_2055 : classCertificateB 7 2055 = true := by
  decide

/-- The same exact first-descent time holds on an infinite dyadic ray. -/
theorem ray_2055 (m : Nat) : stoppingTime (2 ^ 7 * m + 2055) 7 :=
  stoppingTime_of_classCertificate certificate_2055 m

/-- Checked base and every prefix for input 2057. -/
theorem certificate_2057 : classCertificateB 2 2057 = true := by
  decide

/-- The same exact first-descent time holds on an infinite dyadic ray. -/
theorem ray_2057 (m : Nat) : stoppingTime (2 ^ 2 * m + 2057) 2 :=
  stoppingTime_of_classCertificate certificate_2057 m

/-- Checked base and every prefix for input 2059. -/
theorem certificate_2059 : classCertificateB 5 2059 = true := by
  decide

/-- The same exact first-descent time holds on an infinite dyadic ray. -/
theorem ray_2059 (m : Nat) : stoppingTime (2 ^ 5 * m + 2059) 5 :=
  stoppingTime_of_classCertificate certificate_2059 m

/-- Checked base and every prefix for input 2061. -/
theorem certificate_2061 : classCertificateB 2 2061 = true := by
  decide

/-- The same exact first-descent time holds on an infinite dyadic ray. -/
theorem ray_2061 (m : Nat) : stoppingTime (2 ^ 2 * m + 2061) 2 :=
  stoppingTime_of_classCertificate certificate_2061 m

/-- Checked base and every prefix for input 2063. -/
theorem certificate_2063 : classCertificateB 7 2063 = true := by
  decide

/-- The same exact first-descent time holds on an infinite dyadic ray. -/
theorem ray_2063 (m : Nat) : stoppingTime (2 ^ 7 * m + 2063) 7 :=
  stoppingTime_of_classCertificate certificate_2063 m

/-- Checked base and every prefix for input 2065. -/
theorem certificate_2065 : classCertificateB 2 2065 = true := by
  decide

/-- The same exact first-descent time holds on an infinite dyadic ray. -/
theorem ray_2065 (m : Nat) : stoppingTime (2 ^ 2 * m + 2065) 2 :=
  stoppingTime_of_classCertificate certificate_2065 m

/-- Checked base and every prefix for input 2067. -/
theorem certificate_2067 : classCertificateB 4 2067 = true := by
  decide

/-- The same exact first-descent time holds on an infinite dyadic ray. -/
theorem ray_2067 (m : Nat) : stoppingTime (2 ^ 4 * m + 2067) 4 :=
  stoppingTime_of_classCertificate certificate_2067 m

/-- Checked base and every prefix for input 2069. -/
theorem certificate_2069 : classCertificateB 2 2069 = true := by
  decide

/-- The same exact first-descent time holds on an infinite dyadic ray. -/
theorem ray_2069 (m : Nat) : stoppingTime (2 ^ 2 * m + 2069) 2 :=
  stoppingTime_of_classCertificate certificate_2069 m

/-- Checked base and every prefix for input 2071. -/
theorem certificate_2071 : classCertificateB 5 2071 = true := by
  decide

/-- The same exact first-descent time holds on an infinite dyadic ray. -/
theorem ray_2071 (m : Nat) : stoppingTime (2 ^ 5 * m + 2071) 5 :=
  stoppingTime_of_classCertificate certificate_2071 m

/-- Checked base and every prefix for input 2073. -/
theorem certificate_2073 : classCertificateB 2 2073 = true := by
  decide

/-- The same exact first-descent time holds on an infinite dyadic ray. -/
theorem ray_2073 (m : Nat) : stoppingTime (2 ^ 2 * m + 2073) 2 :=
  stoppingTime_of_classCertificate certificate_2073 m

/-- Checked base and every prefix for input 2075. -/
theorem certificate_2075 : classCertificateB 13 2075 = true := by
  decide

/-- The same exact first-descent time holds on an infinite dyadic ray. -/
theorem ray_2075 (m : Nat) : stoppingTime (2 ^ 13 * m + 2075) 13 :=
  stoppingTime_of_classCertificate certificate_2075 m

/-- Checked base and every prefix for input 2077. -/
theorem certificate_2077 : classCertificateB 2 2077 = true := by
  decide

/-- The same exact first-descent time holds on an infinite dyadic ray. -/
theorem ray_2077 (m : Nat) : stoppingTime (2 ^ 2 * m + 2077) 2 :=
  stoppingTime_of_classCertificate certificate_2077 m

/-- Exhaustive coverage of the odd inputs in this batch, with no gaps. -/
theorem coverage : CertifiedRange 2011 2079 := by
  intro n hlo hhi hodd
  have hn : n = 2011 ∨ n = 2013 ∨ n = 2015 ∨ n = 2017 ∨ n = 2019 ∨ n = 2021 ∨ n = 2023 ∨ n = 2025 ∨ n = 2027 ∨ n = 2029 ∨ n = 2031 ∨ n = 2033 ∨ n = 2035 ∨ n = 2037 ∨ n = 2039 ∨ n = 2041 ∨ n = 2043 ∨ n = 2045 ∨ n = 2047 ∨ n = 2049 ∨ n = 2051 ∨ n = 2053 ∨ n = 2055 ∨ n = 2057 ∨ n = 2059 ∨ n = 2061 ∨ n = 2063 ∨ n = 2065 ∨ n = 2067 ∨ n = 2069 ∨ n = 2071 ∨ n = 2073 ∨ n = 2075 ∨ n = 2077 := by omega
  rcases hn with h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h
  · subst n
    exact ⟨8, witness_of_certificate certificate_2011⟩
  · subst n
    exact ⟨2, witness_of_certificate certificate_2013⟩
  · subst n
    exact ⟨13, witness_of_certificate certificate_2015⟩
  · subst n
    exact ⟨2, witness_of_certificate certificate_2017⟩
  · subst n
    exact ⟨4, witness_of_certificate certificate_2019⟩
  · subst n
    exact ⟨2, witness_of_certificate certificate_2021⟩
  · subst n
    exact ⟨10, witness_of_certificate certificate_2023⟩
  · subst n
    exact ⟨2, witness_of_certificate certificate_2025⟩
  · subst n
    exact ⟨5, witness_of_certificate certificate_2027⟩
  · subst n
    exact ⟨2, witness_of_certificate certificate_2029⟩
  · subst n
    exact ⟨12, witness_of_certificate certificate_2031⟩
  · subst n
    exact ⟨2, witness_of_certificate certificate_2033⟩
  · subst n
    exact ⟨4, witness_of_certificate certificate_2035⟩
  · subst n
    exact ⟨2, witness_of_certificate certificate_2037⟩
  · subst n
    exact ⟨5, witness_of_certificate certificate_2039⟩
  · subst n
    exact ⟨2, witness_of_certificate certificate_2041⟩
  · subst n
    exact ⟨18, witness_of_certificate certificate_2043⟩
  · subst n
    exact ⟨2, witness_of_certificate certificate_2045⟩
  · subst n
    exact ⟨58, witness_of_certificate certificate_2047⟩
  · subst n
    exact ⟨2, witness_of_certificate certificate_2049⟩
  · subst n
    exact ⟨4, witness_of_certificate certificate_2051⟩
  · subst n
    exact ⟨2, witness_of_certificate certificate_2053⟩
  · subst n
    exact ⟨7, witness_of_certificate certificate_2055⟩
  · subst n
    exact ⟨2, witness_of_certificate certificate_2057⟩
  · subst n
    exact ⟨5, witness_of_certificate certificate_2059⟩
  · subst n
    exact ⟨2, witness_of_certificate certificate_2061⟩
  · subst n
    exact ⟨7, witness_of_certificate certificate_2063⟩
  · subst n
    exact ⟨2, witness_of_certificate certificate_2065⟩
  · subst n
    exact ⟨4, witness_of_certificate certificate_2067⟩
  · subst n
    exact ⟨2, witness_of_certificate certificate_2069⟩
  · subst n
    exact ⟨5, witness_of_certificate certificate_2071⟩
  · subst n
    exact ⟨2, witness_of_certificate certificate_2073⟩
  · subst n
    exact ⟨13, witness_of_certificate certificate_2075⟩
  · subst n
    exact ⟨2, witness_of_certificate certificate_2077⟩

end Collatz.Research.CoefficientDescent.Batch031
