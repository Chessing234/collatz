import Collatz.Research.CoefficientDescent.Basic

namespace Collatz.Research.CoefficientDescent.Batch061

open FirstDescentClass

set_option maxRecDepth 20000
set_option maxHeartbeats 0

/-- Checked base and every prefix for input 4021. -/
theorem certificate_4021 : classCertificateB 2 4021 = true := by
  decide

/-- The same exact first-descent time holds on an infinite dyadic ray. -/
theorem ray_4021 (m : Nat) : stoppingTime (2 ^ 2 * m + 4021) 2 :=
  stoppingTime_of_classCertificate certificate_4021 m

/-- Checked base and every prefix for input 4023. -/
theorem certificate_4023 : classCertificateB 5 4023 = true := by
  decide

/-- The same exact first-descent time holds on an infinite dyadic ray. -/
theorem ray_4023 (m : Nat) : stoppingTime (2 ^ 5 * m + 4023) 5 :=
  stoppingTime_of_classCertificate certificate_4023 m

/-- Checked base and every prefix for input 4025. -/
theorem certificate_4025 : classCertificateB 2 4025 = true := by
  decide

/-- The same exact first-descent time holds on an infinite dyadic ray. -/
theorem ray_4025 (m : Nat) : stoppingTime (2 ^ 2 * m + 4025) 2 :=
  stoppingTime_of_classCertificate certificate_4025 m

/-- Checked base and every prefix for input 4027. -/
theorem certificate_4027 : classCertificateB 7 4027 = true := by
  decide

/-- The same exact first-descent time holds on an infinite dyadic ray. -/
theorem ray_4027 (m : Nat) : stoppingTime (2 ^ 7 * m + 4027) 7 :=
  stoppingTime_of_classCertificate certificate_4027 m

/-- Checked base and every prefix for input 4029. -/
theorem certificate_4029 : classCertificateB 2 4029 = true := by
  decide

/-- The same exact first-descent time holds on an infinite dyadic ray. -/
theorem ray_4029 (m : Nat) : stoppingTime (2 ^ 2 * m + 4029) 2 :=
  stoppingTime_of_classCertificate certificate_4029 m

/-- Checked base and every prefix for input 4031. -/
theorem certificate_4031 : classCertificateB 15 4031 = true := by
  decide

/-- The same exact first-descent time holds on an infinite dyadic ray. -/
theorem ray_4031 (m : Nat) : stoppingTime (2 ^ 15 * m + 4031) 15 :=
  stoppingTime_of_classCertificate certificate_4031 m

/-- Checked base and every prefix for input 4033. -/
theorem certificate_4033 : classCertificateB 2 4033 = true := by
  decide

/-- The same exact first-descent time holds on an infinite dyadic ray. -/
theorem ray_4033 (m : Nat) : stoppingTime (2 ^ 2 * m + 4033) 2 :=
  stoppingTime_of_classCertificate certificate_4033 m

/-- Checked base and every prefix for input 4035. -/
theorem certificate_4035 : classCertificateB 4 4035 = true := by
  decide

/-- The same exact first-descent time holds on an infinite dyadic ray. -/
theorem ray_4035 (m : Nat) : stoppingTime (2 ^ 4 * m + 4035) 4 :=
  stoppingTime_of_classCertificate certificate_4035 m

/-- Checked base and every prefix for input 4037. -/
theorem certificate_4037 : classCertificateB 2 4037 = true := by
  decide

/-- The same exact first-descent time holds on an infinite dyadic ray. -/
theorem ray_4037 (m : Nat) : stoppingTime (2 ^ 2 * m + 4037) 2 :=
  stoppingTime_of_classCertificate certificate_4037 m

/-- Checked base and every prefix for input 4039. -/
theorem certificate_4039 : classCertificateB 8 4039 = true := by
  decide

/-- The same exact first-descent time holds on an infinite dyadic ray. -/
theorem ray_4039 (m : Nat) : stoppingTime (2 ^ 8 * m + 4039) 8 :=
  stoppingTime_of_classCertificate certificate_4039 m

/-- Checked base and every prefix for input 4041. -/
theorem certificate_4041 : classCertificateB 2 4041 = true := by
  decide

/-- The same exact first-descent time holds on an infinite dyadic ray. -/
theorem ray_4041 (m : Nat) : stoppingTime (2 ^ 2 * m + 4041) 2 :=
  stoppingTime_of_classCertificate certificate_4041 m

/-- Checked base and every prefix for input 4043. -/
theorem certificate_4043 : classCertificateB 5 4043 = true := by
  decide

/-- The same exact first-descent time holds on an infinite dyadic ray. -/
theorem ray_4043 (m : Nat) : stoppingTime (2 ^ 5 * m + 4043) 5 :=
  stoppingTime_of_classCertificate certificate_4043 m

/-- Checked base and every prefix for input 4045. -/
theorem certificate_4045 : classCertificateB 2 4045 = true := by
  decide

/-- The same exact first-descent time holds on an infinite dyadic ray. -/
theorem ray_4045 (m : Nat) : stoppingTime (2 ^ 2 * m + 4045) 2 :=
  stoppingTime_of_classCertificate certificate_4045 m

/-- Checked base and every prefix for input 4047. -/
theorem certificate_4047 : classCertificateB 10 4047 = true := by
  decide

/-- The same exact first-descent time holds on an infinite dyadic ray. -/
theorem ray_4047 (m : Nat) : stoppingTime (2 ^ 10 * m + 4047) 10 :=
  stoppingTime_of_classCertificate certificate_4047 m

/-- Checked base and every prefix for input 4049. -/
theorem certificate_4049 : classCertificateB 2 4049 = true := by
  decide

/-- The same exact first-descent time holds on an infinite dyadic ray. -/
theorem ray_4049 (m : Nat) : stoppingTime (2 ^ 2 * m + 4049) 2 :=
  stoppingTime_of_classCertificate certificate_4049 m

/-- Checked base and every prefix for input 4051. -/
theorem certificate_4051 : classCertificateB 4 4051 = true := by
  decide

/-- The same exact first-descent time holds on an infinite dyadic ray. -/
theorem ray_4051 (m : Nat) : stoppingTime (2 ^ 4 * m + 4051) 4 :=
  stoppingTime_of_classCertificate certificate_4051 m

/-- Checked base and every prefix for input 4053. -/
theorem certificate_4053 : classCertificateB 2 4053 = true := by
  decide

/-- The same exact first-descent time holds on an infinite dyadic ray. -/
theorem ray_4053 (m : Nat) : stoppingTime (2 ^ 2 * m + 4053) 2 :=
  stoppingTime_of_classCertificate certificate_4053 m

/-- Checked base and every prefix for input 4055. -/
theorem certificate_4055 : classCertificateB 5 4055 = true := by
  decide

/-- The same exact first-descent time holds on an infinite dyadic ray. -/
theorem ray_4055 (m : Nat) : stoppingTime (2 ^ 5 * m + 4055) 5 :=
  stoppingTime_of_classCertificate certificate_4055 m

/-- Checked base and every prefix for input 4057. -/
theorem certificate_4057 : classCertificateB 2 4057 = true := by
  decide

/-- The same exact first-descent time holds on an infinite dyadic ray. -/
theorem ray_4057 (m : Nat) : stoppingTime (2 ^ 2 * m + 4057) 2 :=
  stoppingTime_of_classCertificate certificate_4057 m

/-- Checked base and every prefix for input 4059. -/
theorem certificate_4059 : classCertificateB 8 4059 = true := by
  decide

/-- The same exact first-descent time holds on an infinite dyadic ray. -/
theorem ray_4059 (m : Nat) : stoppingTime (2 ^ 8 * m + 4059) 8 :=
  stoppingTime_of_classCertificate certificate_4059 m

/-- Checked base and every prefix for input 4061. -/
theorem certificate_4061 : classCertificateB 2 4061 = true := by
  decide

/-- The same exact first-descent time holds on an infinite dyadic ray. -/
theorem ray_4061 (m : Nat) : stoppingTime (2 ^ 2 * m + 4061) 2 :=
  stoppingTime_of_classCertificate certificate_4061 m

/-- Checked base and every prefix for input 4063. -/
theorem certificate_4063 : classCertificateB 12 4063 = true := by
  decide

/-- The same exact first-descent time holds on an infinite dyadic ray. -/
theorem ray_4063 (m : Nat) : stoppingTime (2 ^ 12 * m + 4063) 12 :=
  stoppingTime_of_classCertificate certificate_4063 m

/-- Checked base and every prefix for input 4065. -/
theorem certificate_4065 : classCertificateB 2 4065 = true := by
  decide

/-- The same exact first-descent time holds on an infinite dyadic ray. -/
theorem ray_4065 (m : Nat) : stoppingTime (2 ^ 2 * m + 4065) 2 :=
  stoppingTime_of_classCertificate certificate_4065 m

/-- Checked base and every prefix for input 4067. -/
theorem certificate_4067 : classCertificateB 4 4067 = true := by
  decide

/-- The same exact first-descent time holds on an infinite dyadic ray. -/
theorem ray_4067 (m : Nat) : stoppingTime (2 ^ 4 * m + 4067) 4 :=
  stoppingTime_of_classCertificate certificate_4067 m

/-- Checked base and every prefix for input 4069. -/
theorem certificate_4069 : classCertificateB 2 4069 = true := by
  decide

/-- The same exact first-descent time holds on an infinite dyadic ray. -/
theorem ray_4069 (m : Nat) : stoppingTime (2 ^ 2 * m + 4069) 2 :=
  stoppingTime_of_classCertificate certificate_4069 m

/-- Checked base and every prefix for input 4071. -/
theorem certificate_4071 : classCertificateB 10 4071 = true := by
  decide

/-- The same exact first-descent time holds on an infinite dyadic ray. -/
theorem ray_4071 (m : Nat) : stoppingTime (2 ^ 10 * m + 4071) 10 :=
  stoppingTime_of_classCertificate certificate_4071 m

/-- Checked base and every prefix for input 4073. -/
theorem certificate_4073 : classCertificateB 2 4073 = true := by
  decide

/-- The same exact first-descent time holds on an infinite dyadic ray. -/
theorem ray_4073 (m : Nat) : stoppingTime (2 ^ 2 * m + 4073) 2 :=
  stoppingTime_of_classCertificate certificate_4073 m

/-- Checked base and every prefix for input 4075. -/
theorem certificate_4075 : classCertificateB 5 4075 = true := by
  decide

/-- The same exact first-descent time holds on an infinite dyadic ray. -/
theorem ray_4075 (m : Nat) : stoppingTime (2 ^ 5 * m + 4075) 5 :=
  stoppingTime_of_classCertificate certificate_4075 m

/-- Checked base and every prefix for input 4077. -/
theorem certificate_4077 : classCertificateB 2 4077 = true := by
  decide

/-- The same exact first-descent time holds on an infinite dyadic ray. -/
theorem ray_4077 (m : Nat) : stoppingTime (2 ^ 2 * m + 4077) 2 :=
  stoppingTime_of_classCertificate certificate_4077 m

/-- Checked base and every prefix for input 4079. -/
theorem certificate_4079 : classCertificateB 13 4079 = true := by
  decide

/-- The same exact first-descent time holds on an infinite dyadic ray. -/
theorem ray_4079 (m : Nat) : stoppingTime (2 ^ 13 * m + 4079) 13 :=
  stoppingTime_of_classCertificate certificate_4079 m

/-- Checked base and every prefix for input 4081. -/
theorem certificate_4081 : classCertificateB 2 4081 = true := by
  decide

/-- The same exact first-descent time holds on an infinite dyadic ray. -/
theorem ray_4081 (m : Nat) : stoppingTime (2 ^ 2 * m + 4081) 2 :=
  stoppingTime_of_classCertificate certificate_4081 m

/-- Checked base and every prefix for input 4083. -/
theorem certificate_4083 : classCertificateB 4 4083 = true := by
  decide

/-- The same exact first-descent time holds on an infinite dyadic ray. -/
theorem ray_4083 (m : Nat) : stoppingTime (2 ^ 4 * m + 4083) 4 :=
  stoppingTime_of_classCertificate certificate_4083 m

/-- Checked base and every prefix for input 4085. -/
theorem certificate_4085 : classCertificateB 2 4085 = true := by
  decide

/-- The same exact first-descent time holds on an infinite dyadic ray. -/
theorem ray_4085 (m : Nat) : stoppingTime (2 ^ 2 * m + 4085) 2 :=
  stoppingTime_of_classCertificate certificate_4085 m

/-- Exhaustive coverage of the odd inputs in this batch, with no gaps. -/
theorem coverage : CertifiedRange 4021 4087 := by
  intro n hlo hhi hodd
  have hn : n = 4021 ∨ n = 4023 ∨ n = 4025 ∨ n = 4027 ∨ n = 4029 ∨ n = 4031 ∨ n = 4033 ∨ n = 4035 ∨ n = 4037 ∨ n = 4039 ∨ n = 4041 ∨ n = 4043 ∨ n = 4045 ∨ n = 4047 ∨ n = 4049 ∨ n = 4051 ∨ n = 4053 ∨ n = 4055 ∨ n = 4057 ∨ n = 4059 ∨ n = 4061 ∨ n = 4063 ∨ n = 4065 ∨ n = 4067 ∨ n = 4069 ∨ n = 4071 ∨ n = 4073 ∨ n = 4075 ∨ n = 4077 ∨ n = 4079 ∨ n = 4081 ∨ n = 4083 ∨ n = 4085 := by omega
  rcases hn with h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h
  · subst n
    exact ⟨2, witness_of_certificate certificate_4021⟩
  · subst n
    exact ⟨5, witness_of_certificate certificate_4023⟩
  · subst n
    exact ⟨2, witness_of_certificate certificate_4025⟩
  · subst n
    exact ⟨7, witness_of_certificate certificate_4027⟩
  · subst n
    exact ⟨2, witness_of_certificate certificate_4029⟩
  · subst n
    exact ⟨15, witness_of_certificate certificate_4031⟩
  · subst n
    exact ⟨2, witness_of_certificate certificate_4033⟩
  · subst n
    exact ⟨4, witness_of_certificate certificate_4035⟩
  · subst n
    exact ⟨2, witness_of_certificate certificate_4037⟩
  · subst n
    exact ⟨8, witness_of_certificate certificate_4039⟩
  · subst n
    exact ⟨2, witness_of_certificate certificate_4041⟩
  · subst n
    exact ⟨5, witness_of_certificate certificate_4043⟩
  · subst n
    exact ⟨2, witness_of_certificate certificate_4045⟩
  · subst n
    exact ⟨10, witness_of_certificate certificate_4047⟩
  · subst n
    exact ⟨2, witness_of_certificate certificate_4049⟩
  · subst n
    exact ⟨4, witness_of_certificate certificate_4051⟩
  · subst n
    exact ⟨2, witness_of_certificate certificate_4053⟩
  · subst n
    exact ⟨5, witness_of_certificate certificate_4055⟩
  · subst n
    exact ⟨2, witness_of_certificate certificate_4057⟩
  · subst n
    exact ⟨8, witness_of_certificate certificate_4059⟩
  · subst n
    exact ⟨2, witness_of_certificate certificate_4061⟩
  · subst n
    exact ⟨12, witness_of_certificate certificate_4063⟩
  · subst n
    exact ⟨2, witness_of_certificate certificate_4065⟩
  · subst n
    exact ⟨4, witness_of_certificate certificate_4067⟩
  · subst n
    exact ⟨2, witness_of_certificate certificate_4069⟩
  · subst n
    exact ⟨10, witness_of_certificate certificate_4071⟩
  · subst n
    exact ⟨2, witness_of_certificate certificate_4073⟩
  · subst n
    exact ⟨5, witness_of_certificate certificate_4075⟩
  · subst n
    exact ⟨2, witness_of_certificate certificate_4077⟩
  · subst n
    exact ⟨13, witness_of_certificate certificate_4079⟩
  · subst n
    exact ⟨2, witness_of_certificate certificate_4081⟩
  · subst n
    exact ⟨4, witness_of_certificate certificate_4083⟩
  · subst n
    exact ⟨2, witness_of_certificate certificate_4085⟩

end Collatz.Research.CoefficientDescent.Batch061
