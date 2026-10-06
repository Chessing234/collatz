import Collatz.Research.CoefficientDescent.Basic

namespace Collatz.Research.CoefficientDescent.Batch030

open FirstDescentClass

set_option maxRecDepth 20000
set_option maxHeartbeats 0

/-- Checked base and every prefix for input 1945. -/
theorem certificate_1945 : classCertificateB 2 1945 = true := by
  decide

/-- The same exact first-descent time holds on an infinite dyadic ray. -/
theorem ray_1945 (m : Nat) : stoppingTime (2 ^ 2 * m + 1945) 2 :=
  stoppingTime_of_classCertificate certificate_1945 m

/-- Checked base and every prefix for input 1947. -/
theorem certificate_1947 : classCertificateB 10 1947 = true := by
  decide

/-- The same exact first-descent time holds on an infinite dyadic ray. -/
theorem ray_1947 (m : Nat) : stoppingTime (2 ^ 10 * m + 1947) 10 :=
  stoppingTime_of_classCertificate certificate_1947 m

/-- Checked base and every prefix for input 1949. -/
theorem certificate_1949 : classCertificateB 2 1949 = true := by
  decide

/-- The same exact first-descent time holds on an infinite dyadic ray. -/
theorem ray_1949 (m : Nat) : stoppingTime (2 ^ 2 * m + 1949) 2 :=
  stoppingTime_of_classCertificate certificate_1949 m

/-- Checked base and every prefix for input 1951. -/
theorem certificate_1951 : classCertificateB 26 1951 = true := by
  decide

/-- The same exact first-descent time holds on an infinite dyadic ray. -/
theorem ray_1951 (m : Nat) : stoppingTime (2 ^ 26 * m + 1951) 26 :=
  stoppingTime_of_classCertificate certificate_1951 m

/-- Checked base and every prefix for input 1953. -/
theorem certificate_1953 : classCertificateB 2 1953 = true := by
  decide

/-- The same exact first-descent time holds on an infinite dyadic ray. -/
theorem ray_1953 (m : Nat) : stoppingTime (2 ^ 2 * m + 1953) 2 :=
  stoppingTime_of_classCertificate certificate_1953 m

/-- Checked base and every prefix for input 1955. -/
theorem certificate_1955 : classCertificateB 4 1955 = true := by
  decide

/-- The same exact first-descent time holds on an infinite dyadic ray. -/
theorem ray_1955 (m : Nat) : stoppingTime (2 ^ 4 * m + 1955) 4 :=
  stoppingTime_of_classCertificate certificate_1955 m

/-- Checked base and every prefix for input 1957. -/
theorem certificate_1957 : classCertificateB 2 1957 = true := by
  decide

/-- The same exact first-descent time holds on an infinite dyadic ray. -/
theorem ray_1957 (m : Nat) : stoppingTime (2 ^ 2 * m + 1957) 2 :=
  stoppingTime_of_classCertificate certificate_1957 m

/-- Checked base and every prefix for input 1959. -/
theorem certificate_1959 : classCertificateB 26 1959 = true := by
  decide

/-- The same exact first-descent time holds on an infinite dyadic ray. -/
theorem ray_1959 (m : Nat) : stoppingTime (2 ^ 26 * m + 1959) 26 :=
  stoppingTime_of_classCertificate certificate_1959 m

/-- Checked base and every prefix for input 1961. -/
theorem certificate_1961 : classCertificateB 2 1961 = true := by
  decide

/-- The same exact first-descent time holds on an infinite dyadic ray. -/
theorem ray_1961 (m : Nat) : stoppingTime (2 ^ 2 * m + 1961) 2 :=
  stoppingTime_of_classCertificate certificate_1961 m

/-- Checked base and every prefix for input 1963. -/
theorem certificate_1963 : classCertificateB 5 1963 = true := by
  decide

/-- The same exact first-descent time holds on an infinite dyadic ray. -/
theorem ray_1963 (m : Nat) : stoppingTime (2 ^ 5 * m + 1963) 5 :=
  stoppingTime_of_classCertificate certificate_1963 m

/-- Checked base and every prefix for input 1965. -/
theorem certificate_1965 : classCertificateB 2 1965 = true := by
  decide

/-- The same exact first-descent time holds on an infinite dyadic ray. -/
theorem ray_1965 (m : Nat) : stoppingTime (2 ^ 2 * m + 1965) 2 :=
  stoppingTime_of_classCertificate certificate_1965 m

/-- Checked base and every prefix for input 1967. -/
theorem certificate_1967 : classCertificateB 8 1967 = true := by
  decide

/-- The same exact first-descent time holds on an infinite dyadic ray. -/
theorem ray_1967 (m : Nat) : stoppingTime (2 ^ 8 * m + 1967) 8 :=
  stoppingTime_of_classCertificate certificate_1967 m

/-- Checked base and every prefix for input 1969. -/
theorem certificate_1969 : classCertificateB 2 1969 = true := by
  decide

/-- The same exact first-descent time holds on an infinite dyadic ray. -/
theorem ray_1969 (m : Nat) : stoppingTime (2 ^ 2 * m + 1969) 2 :=
  stoppingTime_of_classCertificate certificate_1969 m

/-- Checked base and every prefix for input 1971. -/
theorem certificate_1971 : classCertificateB 4 1971 = true := by
  decide

/-- The same exact first-descent time holds on an infinite dyadic ray. -/
theorem ray_1971 (m : Nat) : stoppingTime (2 ^ 4 * m + 1971) 4 :=
  stoppingTime_of_classCertificate certificate_1971 m

/-- Checked base and every prefix for input 1973. -/
theorem certificate_1973 : classCertificateB 2 1973 = true := by
  decide

/-- The same exact first-descent time holds on an infinite dyadic ray. -/
theorem ray_1973 (m : Nat) : stoppingTime (2 ^ 2 * m + 1973) 2 :=
  stoppingTime_of_classCertificate certificate_1973 m

/-- Checked base and every prefix for input 1975. -/
theorem certificate_1975 : classCertificateB 5 1975 = true := by
  decide

/-- The same exact first-descent time holds on an infinite dyadic ray. -/
theorem ray_1975 (m : Nat) : stoppingTime (2 ^ 5 * m + 1975) 5 :=
  stoppingTime_of_classCertificate certificate_1975 m

/-- Checked base and every prefix for input 1977. -/
theorem certificate_1977 : classCertificateB 2 1977 = true := by
  decide

/-- The same exact first-descent time holds on an infinite dyadic ray. -/
theorem ray_1977 (m : Nat) : stoppingTime (2 ^ 2 * m + 1977) 2 :=
  stoppingTime_of_classCertificate certificate_1977 m

/-- Checked base and every prefix for input 1979. -/
theorem certificate_1979 : classCertificateB 7 1979 = true := by
  decide

/-- The same exact first-descent time holds on an infinite dyadic ray. -/
theorem ray_1979 (m : Nat) : stoppingTime (2 ^ 7 * m + 1979) 7 :=
  stoppingTime_of_classCertificate certificate_1979 m

/-- Checked base and every prefix for input 1981. -/
theorem certificate_1981 : classCertificateB 2 1981 = true := by
  decide

/-- The same exact first-descent time holds on an infinite dyadic ray. -/
theorem ray_1981 (m : Nat) : stoppingTime (2 ^ 2 * m + 1981) 2 :=
  stoppingTime_of_classCertificate certificate_1981 m

/-- Checked base and every prefix for input 1983. -/
theorem certificate_1983 : classCertificateB 13 1983 = true := by
  decide

/-- The same exact first-descent time holds on an infinite dyadic ray. -/
theorem ray_1983 (m : Nat) : stoppingTime (2 ^ 13 * m + 1983) 13 :=
  stoppingTime_of_classCertificate certificate_1983 m

/-- Checked base and every prefix for input 1985. -/
theorem certificate_1985 : classCertificateB 2 1985 = true := by
  decide

/-- The same exact first-descent time holds on an infinite dyadic ray. -/
theorem ray_1985 (m : Nat) : stoppingTime (2 ^ 2 * m + 1985) 2 :=
  stoppingTime_of_classCertificate certificate_1985 m

/-- Checked base and every prefix for input 1987. -/
theorem certificate_1987 : classCertificateB 4 1987 = true := by
  decide

/-- The same exact first-descent time holds on an infinite dyadic ray. -/
theorem ray_1987 (m : Nat) : stoppingTime (2 ^ 4 * m + 1987) 4 :=
  stoppingTime_of_classCertificate certificate_1987 m

/-- Checked base and every prefix for input 1989. -/
theorem certificate_1989 : classCertificateB 2 1989 = true := by
  decide

/-- The same exact first-descent time holds on an infinite dyadic ray. -/
theorem ray_1989 (m : Nat) : stoppingTime (2 ^ 2 * m + 1989) 2 :=
  stoppingTime_of_classCertificate certificate_1989 m

/-- Checked base and every prefix for input 1991. -/
theorem certificate_1991 : classCertificateB 8 1991 = true := by
  decide

/-- The same exact first-descent time holds on an infinite dyadic ray. -/
theorem ray_1991 (m : Nat) : stoppingTime (2 ^ 8 * m + 1991) 8 :=
  stoppingTime_of_classCertificate certificate_1991 m

/-- Checked base and every prefix for input 1993. -/
theorem certificate_1993 : classCertificateB 2 1993 = true := by
  decide

/-- The same exact first-descent time holds on an infinite dyadic ray. -/
theorem ray_1993 (m : Nat) : stoppingTime (2 ^ 2 * m + 1993) 2 :=
  stoppingTime_of_classCertificate certificate_1993 m

/-- Checked base and every prefix for input 1995. -/
theorem certificate_1995 : classCertificateB 5 1995 = true := by
  decide

/-- The same exact first-descent time holds on an infinite dyadic ray. -/
theorem ray_1995 (m : Nat) : stoppingTime (2 ^ 5 * m + 1995) 5 :=
  stoppingTime_of_classCertificate certificate_1995 m

/-- Checked base and every prefix for input 1997. -/
theorem certificate_1997 : classCertificateB 2 1997 = true := by
  decide

/-- The same exact first-descent time holds on an infinite dyadic ray. -/
theorem ray_1997 (m : Nat) : stoppingTime (2 ^ 2 * m + 1997) 2 :=
  stoppingTime_of_classCertificate certificate_1997 m

/-- Checked base and every prefix for input 1999. -/
theorem certificate_1999 : classCertificateB 10 1999 = true := by
  decide

/-- The same exact first-descent time holds on an infinite dyadic ray. -/
theorem ray_1999 (m : Nat) : stoppingTime (2 ^ 10 * m + 1999) 10 :=
  stoppingTime_of_classCertificate certificate_1999 m

/-- Checked base and every prefix for input 2001. -/
theorem certificate_2001 : classCertificateB 2 2001 = true := by
  decide

/-- The same exact first-descent time holds on an infinite dyadic ray. -/
theorem ray_2001 (m : Nat) : stoppingTime (2 ^ 2 * m + 2001) 2 :=
  stoppingTime_of_classCertificate certificate_2001 m

/-- Checked base and every prefix for input 2003. -/
theorem certificate_2003 : classCertificateB 4 2003 = true := by
  decide

/-- The same exact first-descent time holds on an infinite dyadic ray. -/
theorem ray_2003 (m : Nat) : stoppingTime (2 ^ 4 * m + 2003) 4 :=
  stoppingTime_of_classCertificate certificate_2003 m

/-- Checked base and every prefix for input 2005. -/
theorem certificate_2005 : classCertificateB 2 2005 = true := by
  decide

/-- The same exact first-descent time holds on an infinite dyadic ray. -/
theorem ray_2005 (m : Nat) : stoppingTime (2 ^ 2 * m + 2005) 2 :=
  stoppingTime_of_classCertificate certificate_2005 m

/-- Checked base and every prefix for input 2007. -/
theorem certificate_2007 : classCertificateB 5 2007 = true := by
  decide

/-- The same exact first-descent time holds on an infinite dyadic ray. -/
theorem ray_2007 (m : Nat) : stoppingTime (2 ^ 5 * m + 2007) 5 :=
  stoppingTime_of_classCertificate certificate_2007 m

/-- Checked base and every prefix for input 2009. -/
theorem certificate_2009 : classCertificateB 2 2009 = true := by
  decide

/-- The same exact first-descent time holds on an infinite dyadic ray. -/
theorem ray_2009 (m : Nat) : stoppingTime (2 ^ 2 * m + 2009) 2 :=
  stoppingTime_of_classCertificate certificate_2009 m

/-- Exhaustive coverage of the odd inputs in this batch, with no gaps. -/
theorem coverage : CertifiedRange 1945 2011 := by
  intro n hlo hhi hodd
  have hn : n = 1945 ∨ n = 1947 ∨ n = 1949 ∨ n = 1951 ∨ n = 1953 ∨ n = 1955 ∨ n = 1957 ∨ n = 1959 ∨ n = 1961 ∨ n = 1963 ∨ n = 1965 ∨ n = 1967 ∨ n = 1969 ∨ n = 1971 ∨ n = 1973 ∨ n = 1975 ∨ n = 1977 ∨ n = 1979 ∨ n = 1981 ∨ n = 1983 ∨ n = 1985 ∨ n = 1987 ∨ n = 1989 ∨ n = 1991 ∨ n = 1993 ∨ n = 1995 ∨ n = 1997 ∨ n = 1999 ∨ n = 2001 ∨ n = 2003 ∨ n = 2005 ∨ n = 2007 ∨ n = 2009 := by omega
  rcases hn with h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h
  · subst n
    exact ⟨2, witness_of_certificate certificate_1945⟩
  · subst n
    exact ⟨10, witness_of_certificate certificate_1947⟩
  · subst n
    exact ⟨2, witness_of_certificate certificate_1949⟩
  · subst n
    exact ⟨26, witness_of_certificate certificate_1951⟩
  · subst n
    exact ⟨2, witness_of_certificate certificate_1953⟩
  · subst n
    exact ⟨4, witness_of_certificate certificate_1955⟩
  · subst n
    exact ⟨2, witness_of_certificate certificate_1957⟩
  · subst n
    exact ⟨26, witness_of_certificate certificate_1959⟩
  · subst n
    exact ⟨2, witness_of_certificate certificate_1961⟩
  · subst n
    exact ⟨5, witness_of_certificate certificate_1963⟩
  · subst n
    exact ⟨2, witness_of_certificate certificate_1965⟩
  · subst n
    exact ⟨8, witness_of_certificate certificate_1967⟩
  · subst n
    exact ⟨2, witness_of_certificate certificate_1969⟩
  · subst n
    exact ⟨4, witness_of_certificate certificate_1971⟩
  · subst n
    exact ⟨2, witness_of_certificate certificate_1973⟩
  · subst n
    exact ⟨5, witness_of_certificate certificate_1975⟩
  · subst n
    exact ⟨2, witness_of_certificate certificate_1977⟩
  · subst n
    exact ⟨7, witness_of_certificate certificate_1979⟩
  · subst n
    exact ⟨2, witness_of_certificate certificate_1981⟩
  · subst n
    exact ⟨13, witness_of_certificate certificate_1983⟩
  · subst n
    exact ⟨2, witness_of_certificate certificate_1985⟩
  · subst n
    exact ⟨4, witness_of_certificate certificate_1987⟩
  · subst n
    exact ⟨2, witness_of_certificate certificate_1989⟩
  · subst n
    exact ⟨8, witness_of_certificate certificate_1991⟩
  · subst n
    exact ⟨2, witness_of_certificate certificate_1993⟩
  · subst n
    exact ⟨5, witness_of_certificate certificate_1995⟩
  · subst n
    exact ⟨2, witness_of_certificate certificate_1997⟩
  · subst n
    exact ⟨10, witness_of_certificate certificate_1999⟩
  · subst n
    exact ⟨2, witness_of_certificate certificate_2001⟩
  · subst n
    exact ⟨4, witness_of_certificate certificate_2003⟩
  · subst n
    exact ⟨2, witness_of_certificate certificate_2005⟩
  · subst n
    exact ⟨5, witness_of_certificate certificate_2007⟩
  · subst n
    exact ⟨2, witness_of_certificate certificate_2009⟩

end Collatz.Research.CoefficientDescent.Batch030
