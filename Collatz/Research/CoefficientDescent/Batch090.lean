import Collatz.Research.CoefficientDescent.Basic

namespace Collatz.Research.CoefficientDescent.Batch090

open FirstDescentClass

set_option maxRecDepth 20000
set_option maxHeartbeats 0

/-- Checked base and every prefix for input 5963. -/
theorem certificate_5963 : classCertificateB 5 5963 = true := by
  decide

/-- The same exact first-descent time holds on an infinite dyadic ray. -/
theorem ray_5963 (m : Nat) : stoppingTime (2 ^ 5 * m + 5963) 5 :=
  stoppingTime_of_classCertificate certificate_5963 m

/-- Checked base and every prefix for input 5965. -/
theorem certificate_5965 : classCertificateB 2 5965 = true := by
  decide

/-- The same exact first-descent time holds on an infinite dyadic ray. -/
theorem ray_5965 (m : Nat) : stoppingTime (2 ^ 2 * m + 5965) 2 :=
  stoppingTime_of_classCertificate certificate_5965 m

/-- Checked base and every prefix for input 5967. -/
theorem certificate_5967 : classCertificateB 8 5967 = true := by
  decide

/-- The same exact first-descent time holds on an infinite dyadic ray. -/
theorem ray_5967 (m : Nat) : stoppingTime (2 ^ 8 * m + 5967) 8 :=
  stoppingTime_of_classCertificate certificate_5967 m

/-- Checked base and every prefix for input 5969. -/
theorem certificate_5969 : classCertificateB 2 5969 = true := by
  decide

/-- The same exact first-descent time holds on an infinite dyadic ray. -/
theorem ray_5969 (m : Nat) : stoppingTime (2 ^ 2 * m + 5969) 2 :=
  stoppingTime_of_classCertificate certificate_5969 m

/-- Checked base and every prefix for input 5971. -/
theorem certificate_5971 : classCertificateB 4 5971 = true := by
  decide

/-- The same exact first-descent time holds on an infinite dyadic ray. -/
theorem ray_5971 (m : Nat) : stoppingTime (2 ^ 4 * m + 5971) 4 :=
  stoppingTime_of_classCertificate certificate_5971 m

/-- Checked base and every prefix for input 5973. -/
theorem certificate_5973 : classCertificateB 2 5973 = true := by
  decide

/-- The same exact first-descent time holds on an infinite dyadic ray. -/
theorem ray_5973 (m : Nat) : stoppingTime (2 ^ 2 * m + 5973) 2 :=
  stoppingTime_of_classCertificate certificate_5973 m

/-- Checked base and every prefix for input 5975. -/
theorem certificate_5975 : classCertificateB 5 5975 = true := by
  decide

/-- The same exact first-descent time holds on an infinite dyadic ray. -/
theorem ray_5975 (m : Nat) : stoppingTime (2 ^ 5 * m + 5975) 5 :=
  stoppingTime_of_classCertificate certificate_5975 m

/-- Checked base and every prefix for input 5977. -/
theorem certificate_5977 : classCertificateB 2 5977 = true := by
  decide

/-- The same exact first-descent time holds on an infinite dyadic ray. -/
theorem ray_5977 (m : Nat) : stoppingTime (2 ^ 2 * m + 5977) 2 :=
  stoppingTime_of_classCertificate certificate_5977 m

/-- Checked base and every prefix for input 5979. -/
theorem certificate_5979 : classCertificateB 13 5979 = true := by
  decide

/-- The same exact first-descent time holds on an infinite dyadic ray. -/
theorem ray_5979 (m : Nat) : stoppingTime (2 ^ 13 * m + 5979) 13 :=
  stoppingTime_of_classCertificate certificate_5979 m

/-- Checked base and every prefix for input 5981. -/
theorem certificate_5981 : classCertificateB 2 5981 = true := by
  decide

/-- The same exact first-descent time holds on an infinite dyadic ray. -/
theorem ray_5981 (m : Nat) : stoppingTime (2 ^ 2 * m + 5981) 2 :=
  stoppingTime_of_classCertificate certificate_5981 m

/-- Checked base and every prefix for input 5983. -/
theorem certificate_5983 : classCertificateB 8 5983 = true := by
  decide

/-- The same exact first-descent time holds on an infinite dyadic ray. -/
theorem ray_5983 (m : Nat) : stoppingTime (2 ^ 8 * m + 5983) 8 :=
  stoppingTime_of_classCertificate certificate_5983 m

/-- Checked base and every prefix for input 5985. -/
theorem certificate_5985 : classCertificateB 2 5985 = true := by
  decide

/-- The same exact first-descent time holds on an infinite dyadic ray. -/
theorem ray_5985 (m : Nat) : stoppingTime (2 ^ 2 * m + 5985) 2 :=
  stoppingTime_of_classCertificate certificate_5985 m

/-- Checked base and every prefix for input 5987. -/
theorem certificate_5987 : classCertificateB 4 5987 = true := by
  decide

/-- The same exact first-descent time holds on an infinite dyadic ray. -/
theorem ray_5987 (m : Nat) : stoppingTime (2 ^ 4 * m + 5987) 4 :=
  stoppingTime_of_classCertificate certificate_5987 m

/-- Checked base and every prefix for input 5989. -/
theorem certificate_5989 : classCertificateB 2 5989 = true := by
  decide

/-- The same exact first-descent time holds on an infinite dyadic ray. -/
theorem ray_5989 (m : Nat) : stoppingTime (2 ^ 2 * m + 5989) 2 :=
  stoppingTime_of_classCertificate certificate_5989 m

/-- Checked base and every prefix for input 5991. -/
theorem certificate_5991 : classCertificateB 26 5991 = true := by
  decide

/-- The same exact first-descent time holds on an infinite dyadic ray. -/
theorem ray_5991 (m : Nat) : stoppingTime (2 ^ 26 * m + 5991) 26 :=
  stoppingTime_of_classCertificate certificate_5991 m

/-- Checked base and every prefix for input 5993. -/
theorem certificate_5993 : classCertificateB 2 5993 = true := by
  decide

/-- The same exact first-descent time holds on an infinite dyadic ray. -/
theorem ray_5993 (m : Nat) : stoppingTime (2 ^ 2 * m + 5993) 2 :=
  stoppingTime_of_classCertificate certificate_5993 m

/-- Checked base and every prefix for input 5995. -/
theorem certificate_5995 : classCertificateB 5 5995 = true := by
  decide

/-- The same exact first-descent time holds on an infinite dyadic ray. -/
theorem ray_5995 (m : Nat) : stoppingTime (2 ^ 5 * m + 5995) 5 :=
  stoppingTime_of_classCertificate certificate_5995 m

/-- Checked base and every prefix for input 5997. -/
theorem certificate_5997 : classCertificateB 2 5997 = true := by
  decide

/-- The same exact first-descent time holds on an infinite dyadic ray. -/
theorem ray_5997 (m : Nat) : stoppingTime (2 ^ 2 * m + 5997) 2 :=
  stoppingTime_of_classCertificate certificate_5997 m

/-- Checked base and every prefix for input 5999. -/
theorem certificate_5999 : classCertificateB 18 5999 = true := by
  decide

/-- The same exact first-descent time holds on an infinite dyadic ray. -/
theorem ray_5999 (m : Nat) : stoppingTime (2 ^ 18 * m + 5999) 18 :=
  stoppingTime_of_classCertificate certificate_5999 m

/-- Checked base and every prefix for input 6001. -/
theorem certificate_6001 : classCertificateB 2 6001 = true := by
  decide

/-- The same exact first-descent time holds on an infinite dyadic ray. -/
theorem ray_6001 (m : Nat) : stoppingTime (2 ^ 2 * m + 6001) 2 :=
  stoppingTime_of_classCertificate certificate_6001 m

/-- Checked base and every prefix for input 6003. -/
theorem certificate_6003 : classCertificateB 4 6003 = true := by
  decide

/-- The same exact first-descent time holds on an infinite dyadic ray. -/
theorem ray_6003 (m : Nat) : stoppingTime (2 ^ 4 * m + 6003) 4 :=
  stoppingTime_of_classCertificate certificate_6003 m

/-- Checked base and every prefix for input 6005. -/
theorem certificate_6005 : classCertificateB 2 6005 = true := by
  decide

/-- The same exact first-descent time holds on an infinite dyadic ray. -/
theorem ray_6005 (m : Nat) : stoppingTime (2 ^ 2 * m + 6005) 2 :=
  stoppingTime_of_classCertificate certificate_6005 m

/-- Checked base and every prefix for input 6007. -/
theorem certificate_6007 : classCertificateB 5 6007 = true := by
  decide

/-- The same exact first-descent time holds on an infinite dyadic ray. -/
theorem ray_6007 (m : Nat) : stoppingTime (2 ^ 5 * m + 6007) 5 :=
  stoppingTime_of_classCertificate certificate_6007 m

/-- Checked base and every prefix for input 6009. -/
theorem certificate_6009 : classCertificateB 2 6009 = true := by
  decide

/-- The same exact first-descent time holds on an infinite dyadic ray. -/
theorem ray_6009 (m : Nat) : stoppingTime (2 ^ 2 * m + 6009) 2 :=
  stoppingTime_of_classCertificate certificate_6009 m

/-- Checked base and every prefix for input 6011. -/
theorem certificate_6011 : classCertificateB 8 6011 = true := by
  decide

/-- The same exact first-descent time holds on an infinite dyadic ray. -/
theorem ray_6011 (m : Nat) : stoppingTime (2 ^ 8 * m + 6011) 8 :=
  stoppingTime_of_classCertificate certificate_6011 m

/-- Checked base and every prefix for input 6013. -/
theorem certificate_6013 : classCertificateB 2 6013 = true := by
  decide

/-- The same exact first-descent time holds on an infinite dyadic ray. -/
theorem ray_6013 (m : Nat) : stoppingTime (2 ^ 2 * m + 6013) 2 :=
  stoppingTime_of_classCertificate certificate_6013 m

/-- Checked base and every prefix for input 6015. -/
theorem certificate_6015 : classCertificateB 21 6015 = true := by
  decide

/-- The same exact first-descent time holds on an infinite dyadic ray. -/
theorem ray_6015 (m : Nat) : stoppingTime (2 ^ 21 * m + 6015) 21 :=
  stoppingTime_of_classCertificate certificate_6015 m

/-- Checked base and every prefix for input 6017. -/
theorem certificate_6017 : classCertificateB 2 6017 = true := by
  decide

/-- The same exact first-descent time holds on an infinite dyadic ray. -/
theorem ray_6017 (m : Nat) : stoppingTime (2 ^ 2 * m + 6017) 2 :=
  stoppingTime_of_classCertificate certificate_6017 m

/-- Checked base and every prefix for input 6019. -/
theorem certificate_6019 : classCertificateB 4 6019 = true := by
  decide

/-- The same exact first-descent time holds on an infinite dyadic ray. -/
theorem ray_6019 (m : Nat) : stoppingTime (2 ^ 4 * m + 6019) 4 :=
  stoppingTime_of_classCertificate certificate_6019 m

/-- Checked base and every prefix for input 6021. -/
theorem certificate_6021 : classCertificateB 2 6021 = true := by
  decide

/-- The same exact first-descent time holds on an infinite dyadic ray. -/
theorem ray_6021 (m : Nat) : stoppingTime (2 ^ 2 * m + 6021) 2 :=
  stoppingTime_of_classCertificate certificate_6021 m

/-- Checked base and every prefix for input 6023. -/
theorem certificate_6023 : classCertificateB 7 6023 = true := by
  decide

/-- The same exact first-descent time holds on an infinite dyadic ray. -/
theorem ray_6023 (m : Nat) : stoppingTime (2 ^ 7 * m + 6023) 7 :=
  stoppingTime_of_classCertificate certificate_6023 m

/-- Checked base and every prefix for input 6025. -/
theorem certificate_6025 : classCertificateB 2 6025 = true := by
  decide

/-- The same exact first-descent time holds on an infinite dyadic ray. -/
theorem ray_6025 (m : Nat) : stoppingTime (2 ^ 2 * m + 6025) 2 :=
  stoppingTime_of_classCertificate certificate_6025 m

/-- Checked base and every prefix for input 6027. -/
theorem certificate_6027 : classCertificateB 5 6027 = true := by
  decide

/-- The same exact first-descent time holds on an infinite dyadic ray. -/
theorem ray_6027 (m : Nat) : stoppingTime (2 ^ 5 * m + 6027) 5 :=
  stoppingTime_of_classCertificate certificate_6027 m

/-- Checked base and every prefix for input 6029. -/
theorem certificate_6029 : classCertificateB 2 6029 = true := by
  decide

/-- The same exact first-descent time holds on an infinite dyadic ray. -/
theorem ray_6029 (m : Nat) : stoppingTime (2 ^ 2 * m + 6029) 2 :=
  stoppingTime_of_classCertificate certificate_6029 m

/-- Exhaustive coverage of the odd inputs in this batch, with no gaps. -/
theorem coverage : CertifiedRange 5963 6031 := by
  intro n hlo hhi hodd
  have hn : n = 5963 ∨ n = 5965 ∨ n = 5967 ∨ n = 5969 ∨ n = 5971 ∨ n = 5973 ∨ n = 5975 ∨ n = 5977 ∨ n = 5979 ∨ n = 5981 ∨ n = 5983 ∨ n = 5985 ∨ n = 5987 ∨ n = 5989 ∨ n = 5991 ∨ n = 5993 ∨ n = 5995 ∨ n = 5997 ∨ n = 5999 ∨ n = 6001 ∨ n = 6003 ∨ n = 6005 ∨ n = 6007 ∨ n = 6009 ∨ n = 6011 ∨ n = 6013 ∨ n = 6015 ∨ n = 6017 ∨ n = 6019 ∨ n = 6021 ∨ n = 6023 ∨ n = 6025 ∨ n = 6027 ∨ n = 6029 := by omega
  rcases hn with h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h
  · subst n
    exact ⟨5, witness_of_certificate certificate_5963⟩
  · subst n
    exact ⟨2, witness_of_certificate certificate_5965⟩
  · subst n
    exact ⟨8, witness_of_certificate certificate_5967⟩
  · subst n
    exact ⟨2, witness_of_certificate certificate_5969⟩
  · subst n
    exact ⟨4, witness_of_certificate certificate_5971⟩
  · subst n
    exact ⟨2, witness_of_certificate certificate_5973⟩
  · subst n
    exact ⟨5, witness_of_certificate certificate_5975⟩
  · subst n
    exact ⟨2, witness_of_certificate certificate_5977⟩
  · subst n
    exact ⟨13, witness_of_certificate certificate_5979⟩
  · subst n
    exact ⟨2, witness_of_certificate certificate_5981⟩
  · subst n
    exact ⟨8, witness_of_certificate certificate_5983⟩
  · subst n
    exact ⟨2, witness_of_certificate certificate_5985⟩
  · subst n
    exact ⟨4, witness_of_certificate certificate_5987⟩
  · subst n
    exact ⟨2, witness_of_certificate certificate_5989⟩
  · subst n
    exact ⟨26, witness_of_certificate certificate_5991⟩
  · subst n
    exact ⟨2, witness_of_certificate certificate_5993⟩
  · subst n
    exact ⟨5, witness_of_certificate certificate_5995⟩
  · subst n
    exact ⟨2, witness_of_certificate certificate_5997⟩
  · subst n
    exact ⟨18, witness_of_certificate certificate_5999⟩
  · subst n
    exact ⟨2, witness_of_certificate certificate_6001⟩
  · subst n
    exact ⟨4, witness_of_certificate certificate_6003⟩
  · subst n
    exact ⟨2, witness_of_certificate certificate_6005⟩
  · subst n
    exact ⟨5, witness_of_certificate certificate_6007⟩
  · subst n
    exact ⟨2, witness_of_certificate certificate_6009⟩
  · subst n
    exact ⟨8, witness_of_certificate certificate_6011⟩
  · subst n
    exact ⟨2, witness_of_certificate certificate_6013⟩
  · subst n
    exact ⟨21, witness_of_certificate certificate_6015⟩
  · subst n
    exact ⟨2, witness_of_certificate certificate_6017⟩
  · subst n
    exact ⟨4, witness_of_certificate certificate_6019⟩
  · subst n
    exact ⟨2, witness_of_certificate certificate_6021⟩
  · subst n
    exact ⟨7, witness_of_certificate certificate_6023⟩
  · subst n
    exact ⟨2, witness_of_certificate certificate_6025⟩
  · subst n
    exact ⟨5, witness_of_certificate certificate_6027⟩
  · subst n
    exact ⟨2, witness_of_certificate certificate_6029⟩

end Collatz.Research.CoefficientDescent.Batch090
