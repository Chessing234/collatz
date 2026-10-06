import Collatz.Research.CoefficientDescent.Basic

namespace Collatz.Research.CoefficientDescent.Batch076

open FirstDescentClass

set_option maxRecDepth 20000
set_option maxHeartbeats 0

/-- Checked base and every prefix for input 5025. -/
theorem certificate_5025 : classCertificateB 2 5025 = true := by
  decide

/-- The same exact first-descent time holds on an infinite dyadic ray. -/
theorem ray_5025 (m : Nat) : stoppingTime (2 ^ 2 * m + 5025) 2 :=
  stoppingTime_of_classCertificate certificate_5025 m

/-- Checked base and every prefix for input 5027. -/
theorem certificate_5027 : classCertificateB 4 5027 = true := by
  decide

/-- The same exact first-descent time holds on an infinite dyadic ray. -/
theorem ray_5027 (m : Nat) : stoppingTime (2 ^ 4 * m + 5027) 4 :=
  stoppingTime_of_classCertificate certificate_5027 m

/-- Checked base and every prefix for input 5029. -/
theorem certificate_5029 : classCertificateB 2 5029 = true := by
  decide

/-- The same exact first-descent time holds on an infinite dyadic ray. -/
theorem ray_5029 (m : Nat) : stoppingTime (2 ^ 2 * m + 5029) 2 :=
  stoppingTime_of_classCertificate certificate_5029 m

/-- Checked base and every prefix for input 5031. -/
theorem certificate_5031 : classCertificateB 12 5031 = true := by
  decide

/-- The same exact first-descent time holds on an infinite dyadic ray. -/
theorem ray_5031 (m : Nat) : stoppingTime (2 ^ 12 * m + 5031) 12 :=
  stoppingTime_of_classCertificate certificate_5031 m

/-- Checked base and every prefix for input 5033. -/
theorem certificate_5033 : classCertificateB 2 5033 = true := by
  decide

/-- The same exact first-descent time holds on an infinite dyadic ray. -/
theorem ray_5033 (m : Nat) : stoppingTime (2 ^ 2 * m + 5033) 2 :=
  stoppingTime_of_classCertificate certificate_5033 m

/-- Checked base and every prefix for input 5035. -/
theorem certificate_5035 : classCertificateB 5 5035 = true := by
  decide

/-- The same exact first-descent time holds on an infinite dyadic ray. -/
theorem ray_5035 (m : Nat) : stoppingTime (2 ^ 5 * m + 5035) 5 :=
  stoppingTime_of_classCertificate certificate_5035 m

/-- Checked base and every prefix for input 5037. -/
theorem certificate_5037 : classCertificateB 2 5037 = true := by
  decide

/-- The same exact first-descent time holds on an infinite dyadic ray. -/
theorem ray_5037 (m : Nat) : stoppingTime (2 ^ 2 * m + 5037) 2 :=
  stoppingTime_of_classCertificate certificate_5037 m

/-- Checked base and every prefix for input 5039. -/
theorem certificate_5039 : classCertificateB 8 5039 = true := by
  decide

/-- The same exact first-descent time holds on an infinite dyadic ray. -/
theorem ray_5039 (m : Nat) : stoppingTime (2 ^ 8 * m + 5039) 8 :=
  stoppingTime_of_classCertificate certificate_5039 m

/-- Checked base and every prefix for input 5041. -/
theorem certificate_5041 : classCertificateB 2 5041 = true := by
  decide

/-- The same exact first-descent time holds on an infinite dyadic ray. -/
theorem ray_5041 (m : Nat) : stoppingTime (2 ^ 2 * m + 5041) 2 :=
  stoppingTime_of_classCertificate certificate_5041 m

/-- Checked base and every prefix for input 5043. -/
theorem certificate_5043 : classCertificateB 4 5043 = true := by
  decide

/-- The same exact first-descent time holds on an infinite dyadic ray. -/
theorem ray_5043 (m : Nat) : stoppingTime (2 ^ 4 * m + 5043) 4 :=
  stoppingTime_of_classCertificate certificate_5043 m

/-- Checked base and every prefix for input 5045. -/
theorem certificate_5045 : classCertificateB 2 5045 = true := by
  decide

/-- The same exact first-descent time holds on an infinite dyadic ray. -/
theorem ray_5045 (m : Nat) : stoppingTime (2 ^ 2 * m + 5045) 2 :=
  stoppingTime_of_classCertificate certificate_5045 m

/-- Checked base and every prefix for input 5047. -/
theorem certificate_5047 : classCertificateB 5 5047 = true := by
  decide

/-- The same exact first-descent time holds on an infinite dyadic ray. -/
theorem ray_5047 (m : Nat) : stoppingTime (2 ^ 5 * m + 5047) 5 :=
  stoppingTime_of_classCertificate certificate_5047 m

/-- Checked base and every prefix for input 5049. -/
theorem certificate_5049 : classCertificateB 2 5049 = true := by
  decide

/-- The same exact first-descent time holds on an infinite dyadic ray. -/
theorem ray_5049 (m : Nat) : stoppingTime (2 ^ 2 * m + 5049) 2 :=
  stoppingTime_of_classCertificate certificate_5049 m

/-- Checked base and every prefix for input 5051. -/
theorem certificate_5051 : classCertificateB 7 5051 = true := by
  decide

/-- The same exact first-descent time holds on an infinite dyadic ray. -/
theorem ray_5051 (m : Nat) : stoppingTime (2 ^ 7 * m + 5051) 7 :=
  stoppingTime_of_classCertificate certificate_5051 m

/-- Checked base and every prefix for input 5053. -/
theorem certificate_5053 : classCertificateB 2 5053 = true := by
  decide

/-- The same exact first-descent time holds on an infinite dyadic ray. -/
theorem ray_5053 (m : Nat) : stoppingTime (2 ^ 2 * m + 5053) 2 :=
  stoppingTime_of_classCertificate certificate_5053 m

/-- Checked base and every prefix for input 5055. -/
theorem certificate_5055 : classCertificateB 21 5055 = true := by
  decide

/-- The same exact first-descent time holds on an infinite dyadic ray. -/
theorem ray_5055 (m : Nat) : stoppingTime (2 ^ 21 * m + 5055) 21 :=
  stoppingTime_of_classCertificate certificate_5055 m

/-- Checked base and every prefix for input 5057. -/
theorem certificate_5057 : classCertificateB 2 5057 = true := by
  decide

/-- The same exact first-descent time holds on an infinite dyadic ray. -/
theorem ray_5057 (m : Nat) : stoppingTime (2 ^ 2 * m + 5057) 2 :=
  stoppingTime_of_classCertificate certificate_5057 m

/-- Checked base and every prefix for input 5059. -/
theorem certificate_5059 : classCertificateB 4 5059 = true := by
  decide

/-- The same exact first-descent time holds on an infinite dyadic ray. -/
theorem ray_5059 (m : Nat) : stoppingTime (2 ^ 4 * m + 5059) 4 :=
  stoppingTime_of_classCertificate certificate_5059 m

/-- Checked base and every prefix for input 5061. -/
theorem certificate_5061 : classCertificateB 2 5061 = true := by
  decide

/-- The same exact first-descent time holds on an infinite dyadic ray. -/
theorem ray_5061 (m : Nat) : stoppingTime (2 ^ 2 * m + 5061) 2 :=
  stoppingTime_of_classCertificate certificate_5061 m

/-- Checked base and every prefix for input 5063. -/
theorem certificate_5063 : classCertificateB 8 5063 = true := by
  decide

/-- The same exact first-descent time holds on an infinite dyadic ray. -/
theorem ray_5063 (m : Nat) : stoppingTime (2 ^ 8 * m + 5063) 8 :=
  stoppingTime_of_classCertificate certificate_5063 m

/-- Checked base and every prefix for input 5065. -/
theorem certificate_5065 : classCertificateB 2 5065 = true := by
  decide

/-- The same exact first-descent time holds on an infinite dyadic ray. -/
theorem ray_5065 (m : Nat) : stoppingTime (2 ^ 2 * m + 5065) 2 :=
  stoppingTime_of_classCertificate certificate_5065 m

/-- Checked base and every prefix for input 5067. -/
theorem certificate_5067 : classCertificateB 5 5067 = true := by
  decide

/-- The same exact first-descent time holds on an infinite dyadic ray. -/
theorem ray_5067 (m : Nat) : stoppingTime (2 ^ 5 * m + 5067) 5 :=
  stoppingTime_of_classCertificate certificate_5067 m

/-- Checked base and every prefix for input 5069. -/
theorem certificate_5069 : classCertificateB 2 5069 = true := by
  decide

/-- The same exact first-descent time holds on an infinite dyadic ray. -/
theorem ray_5069 (m : Nat) : stoppingTime (2 ^ 2 * m + 5069) 2 :=
  stoppingTime_of_classCertificate certificate_5069 m

/-- Checked base and every prefix for input 5071. -/
theorem certificate_5071 : classCertificateB 10 5071 = true := by
  decide

/-- The same exact first-descent time holds on an infinite dyadic ray. -/
theorem ray_5071 (m : Nat) : stoppingTime (2 ^ 10 * m + 5071) 10 :=
  stoppingTime_of_classCertificate certificate_5071 m

/-- Checked base and every prefix for input 5073. -/
theorem certificate_5073 : classCertificateB 2 5073 = true := by
  decide

/-- The same exact first-descent time holds on an infinite dyadic ray. -/
theorem ray_5073 (m : Nat) : stoppingTime (2 ^ 2 * m + 5073) 2 :=
  stoppingTime_of_classCertificate certificate_5073 m

/-- Checked base and every prefix for input 5075. -/
theorem certificate_5075 : classCertificateB 4 5075 = true := by
  decide

/-- The same exact first-descent time holds on an infinite dyadic ray. -/
theorem ray_5075 (m : Nat) : stoppingTime (2 ^ 4 * m + 5075) 4 :=
  stoppingTime_of_classCertificate certificate_5075 m

/-- Checked base and every prefix for input 5077. -/
theorem certificate_5077 : classCertificateB 2 5077 = true := by
  decide

/-- The same exact first-descent time holds on an infinite dyadic ray. -/
theorem ray_5077 (m : Nat) : stoppingTime (2 ^ 2 * m + 5077) 2 :=
  stoppingTime_of_classCertificate certificate_5077 m

/-- Checked base and every prefix for input 5079. -/
theorem certificate_5079 : classCertificateB 5 5079 = true := by
  decide

/-- The same exact first-descent time holds on an infinite dyadic ray. -/
theorem ray_5079 (m : Nat) : stoppingTime (2 ^ 5 * m + 5079) 5 :=
  stoppingTime_of_classCertificate certificate_5079 m

/-- Checked base and every prefix for input 5081. -/
theorem certificate_5081 : classCertificateB 2 5081 = true := by
  decide

/-- The same exact first-descent time holds on an infinite dyadic ray. -/
theorem ray_5081 (m : Nat) : stoppingTime (2 ^ 2 * m + 5081) 2 :=
  stoppingTime_of_classCertificate certificate_5081 m

/-- Checked base and every prefix for input 5083. -/
theorem certificate_5083 : classCertificateB 8 5083 = true := by
  decide

/-- The same exact first-descent time holds on an infinite dyadic ray. -/
theorem ray_5083 (m : Nat) : stoppingTime (2 ^ 8 * m + 5083) 8 :=
  stoppingTime_of_classCertificate certificate_5083 m

/-- Checked base and every prefix for input 5085. -/
theorem certificate_5085 : classCertificateB 2 5085 = true := by
  decide

/-- The same exact first-descent time holds on an infinite dyadic ray. -/
theorem ray_5085 (m : Nat) : stoppingTime (2 ^ 2 * m + 5085) 2 :=
  stoppingTime_of_classCertificate certificate_5085 m

/-- Checked base and every prefix for input 5087. -/
theorem certificate_5087 : classCertificateB 16 5087 = true := by
  decide

/-- The same exact first-descent time holds on an infinite dyadic ray. -/
theorem ray_5087 (m : Nat) : stoppingTime (2 ^ 16 * m + 5087) 16 :=
  stoppingTime_of_classCertificate certificate_5087 m

/-- Checked base and every prefix for input 5089. -/
theorem certificate_5089 : classCertificateB 2 5089 = true := by
  decide

/-- The same exact first-descent time holds on an infinite dyadic ray. -/
theorem ray_5089 (m : Nat) : stoppingTime (2 ^ 2 * m + 5089) 2 :=
  stoppingTime_of_classCertificate certificate_5089 m

/-- Checked base and every prefix for input 5091. -/
theorem certificate_5091 : classCertificateB 4 5091 = true := by
  decide

/-- The same exact first-descent time holds on an infinite dyadic ray. -/
theorem ray_5091 (m : Nat) : stoppingTime (2 ^ 4 * m + 5091) 4 :=
  stoppingTime_of_classCertificate certificate_5091 m

/-- Exhaustive coverage of the odd inputs in this batch, with no gaps. -/
theorem coverage : CertifiedRange 5025 5093 := by
  intro n hlo hhi hodd
  have hn : n = 5025 ∨ n = 5027 ∨ n = 5029 ∨ n = 5031 ∨ n = 5033 ∨ n = 5035 ∨ n = 5037 ∨ n = 5039 ∨ n = 5041 ∨ n = 5043 ∨ n = 5045 ∨ n = 5047 ∨ n = 5049 ∨ n = 5051 ∨ n = 5053 ∨ n = 5055 ∨ n = 5057 ∨ n = 5059 ∨ n = 5061 ∨ n = 5063 ∨ n = 5065 ∨ n = 5067 ∨ n = 5069 ∨ n = 5071 ∨ n = 5073 ∨ n = 5075 ∨ n = 5077 ∨ n = 5079 ∨ n = 5081 ∨ n = 5083 ∨ n = 5085 ∨ n = 5087 ∨ n = 5089 ∨ n = 5091 := by omega
  rcases hn with h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h
  · subst n
    exact ⟨2, witness_of_certificate certificate_5025⟩
  · subst n
    exact ⟨4, witness_of_certificate certificate_5027⟩
  · subst n
    exact ⟨2, witness_of_certificate certificate_5029⟩
  · subst n
    exact ⟨12, witness_of_certificate certificate_5031⟩
  · subst n
    exact ⟨2, witness_of_certificate certificate_5033⟩
  · subst n
    exact ⟨5, witness_of_certificate certificate_5035⟩
  · subst n
    exact ⟨2, witness_of_certificate certificate_5037⟩
  · subst n
    exact ⟨8, witness_of_certificate certificate_5039⟩
  · subst n
    exact ⟨2, witness_of_certificate certificate_5041⟩
  · subst n
    exact ⟨4, witness_of_certificate certificate_5043⟩
  · subst n
    exact ⟨2, witness_of_certificate certificate_5045⟩
  · subst n
    exact ⟨5, witness_of_certificate certificate_5047⟩
  · subst n
    exact ⟨2, witness_of_certificate certificate_5049⟩
  · subst n
    exact ⟨7, witness_of_certificate certificate_5051⟩
  · subst n
    exact ⟨2, witness_of_certificate certificate_5053⟩
  · subst n
    exact ⟨21, witness_of_certificate certificate_5055⟩
  · subst n
    exact ⟨2, witness_of_certificate certificate_5057⟩
  · subst n
    exact ⟨4, witness_of_certificate certificate_5059⟩
  · subst n
    exact ⟨2, witness_of_certificate certificate_5061⟩
  · subst n
    exact ⟨8, witness_of_certificate certificate_5063⟩
  · subst n
    exact ⟨2, witness_of_certificate certificate_5065⟩
  · subst n
    exact ⟨5, witness_of_certificate certificate_5067⟩
  · subst n
    exact ⟨2, witness_of_certificate certificate_5069⟩
  · subst n
    exact ⟨10, witness_of_certificate certificate_5071⟩
  · subst n
    exact ⟨2, witness_of_certificate certificate_5073⟩
  · subst n
    exact ⟨4, witness_of_certificate certificate_5075⟩
  · subst n
    exact ⟨2, witness_of_certificate certificate_5077⟩
  · subst n
    exact ⟨5, witness_of_certificate certificate_5079⟩
  · subst n
    exact ⟨2, witness_of_certificate certificate_5081⟩
  · subst n
    exact ⟨8, witness_of_certificate certificate_5083⟩
  · subst n
    exact ⟨2, witness_of_certificate certificate_5085⟩
  · subst n
    exact ⟨16, witness_of_certificate certificate_5087⟩
  · subst n
    exact ⟨2, witness_of_certificate certificate_5089⟩
  · subst n
    exact ⟨4, witness_of_certificate certificate_5091⟩

end Collatz.Research.CoefficientDescent.Batch076
