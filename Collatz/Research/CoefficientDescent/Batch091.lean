import Collatz.Research.CoefficientDescent.Basic

namespace Collatz.Research.CoefficientDescent.Batch091

open FirstDescentClass

set_option maxRecDepth 20000
set_option maxHeartbeats 0

/-- Checked base and every prefix for input 6031. -/
theorem certificate_6031 : classCertificateB 7 6031 = true := by
  decide

/-- The same exact first-descent time holds on an infinite dyadic ray. -/
theorem ray_6031 (m : Nat) : stoppingTime (2 ^ 7 * m + 6031) 7 :=
  stoppingTime_of_classCertificate certificate_6031 m

/-- Checked base and every prefix for input 6033. -/
theorem certificate_6033 : classCertificateB 2 6033 = true := by
  decide

/-- The same exact first-descent time holds on an infinite dyadic ray. -/
theorem ray_6033 (m : Nat) : stoppingTime (2 ^ 2 * m + 6033) 2 :=
  stoppingTime_of_classCertificate certificate_6033 m

/-- Checked base and every prefix for input 6035. -/
theorem certificate_6035 : classCertificateB 4 6035 = true := by
  decide

/-- The same exact first-descent time holds on an infinite dyadic ray. -/
theorem ray_6035 (m : Nat) : stoppingTime (2 ^ 4 * m + 6035) 4 :=
  stoppingTime_of_classCertificate certificate_6035 m

/-- Checked base and every prefix for input 6037. -/
theorem certificate_6037 : classCertificateB 2 6037 = true := by
  decide

/-- The same exact first-descent time holds on an infinite dyadic ray. -/
theorem ray_6037 (m : Nat) : stoppingTime (2 ^ 2 * m + 6037) 2 :=
  stoppingTime_of_classCertificate certificate_6037 m

/-- Checked base and every prefix for input 6039. -/
theorem certificate_6039 : classCertificateB 5 6039 = true := by
  decide

/-- The same exact first-descent time holds on an infinite dyadic ray. -/
theorem ray_6039 (m : Nat) : stoppingTime (2 ^ 5 * m + 6039) 5 :=
  stoppingTime_of_classCertificate certificate_6039 m

/-- Checked base and every prefix for input 6041. -/
theorem certificate_6041 : classCertificateB 2 6041 = true := by
  decide

/-- The same exact first-descent time holds on an infinite dyadic ray. -/
theorem ray_6041 (m : Nat) : stoppingTime (2 ^ 2 * m + 6041) 2 :=
  stoppingTime_of_classCertificate certificate_6041 m

/-- Checked base and every prefix for input 6043. -/
theorem certificate_6043 : classCertificateB 10 6043 = true := by
  decide

/-- The same exact first-descent time holds on an infinite dyadic ray. -/
theorem ray_6043 (m : Nat) : stoppingTime (2 ^ 10 * m + 6043) 10 :=
  stoppingTime_of_classCertificate certificate_6043 m

/-- Checked base and every prefix for input 6045. -/
theorem certificate_6045 : classCertificateB 2 6045 = true := by
  decide

/-- The same exact first-descent time holds on an infinite dyadic ray. -/
theorem ray_6045 (m : Nat) : stoppingTime (2 ^ 2 * m + 6045) 2 :=
  stoppingTime_of_classCertificate certificate_6045 m

/-- Checked base and every prefix for input 6047. -/
theorem certificate_6047 : classCertificateB 13 6047 = true := by
  decide

/-- The same exact first-descent time holds on an infinite dyadic ray. -/
theorem ray_6047 (m : Nat) : stoppingTime (2 ^ 13 * m + 6047) 13 :=
  stoppingTime_of_classCertificate certificate_6047 m

/-- Checked base and every prefix for input 6049. -/
theorem certificate_6049 : classCertificateB 2 6049 = true := by
  decide

/-- The same exact first-descent time holds on an infinite dyadic ray. -/
theorem ray_6049 (m : Nat) : stoppingTime (2 ^ 2 * m + 6049) 2 :=
  stoppingTime_of_classCertificate certificate_6049 m

/-- Checked base and every prefix for input 6051. -/
theorem certificate_6051 : classCertificateB 4 6051 = true := by
  decide

/-- The same exact first-descent time holds on an infinite dyadic ray. -/
theorem ray_6051 (m : Nat) : stoppingTime (2 ^ 4 * m + 6051) 4 :=
  stoppingTime_of_classCertificate certificate_6051 m

/-- Checked base and every prefix for input 6053. -/
theorem certificate_6053 : classCertificateB 2 6053 = true := by
  decide

/-- The same exact first-descent time holds on an infinite dyadic ray. -/
theorem ray_6053 (m : Nat) : stoppingTime (2 ^ 2 * m + 6053) 2 :=
  stoppingTime_of_classCertificate certificate_6053 m

/-- Checked base and every prefix for input 6055. -/
theorem certificate_6055 : classCertificateB 18 6055 = true := by
  decide

/-- The same exact first-descent time holds on an infinite dyadic ray. -/
theorem ray_6055 (m : Nat) : stoppingTime (2 ^ 18 * m + 6055) 18 :=
  stoppingTime_of_classCertificate certificate_6055 m

/-- Checked base and every prefix for input 6057. -/
theorem certificate_6057 : classCertificateB 2 6057 = true := by
  decide

/-- The same exact first-descent time holds on an infinite dyadic ray. -/
theorem ray_6057 (m : Nat) : stoppingTime (2 ^ 2 * m + 6057) 2 :=
  stoppingTime_of_classCertificate certificate_6057 m

/-- Checked base and every prefix for input 6059. -/
theorem certificate_6059 : classCertificateB 5 6059 = true := by
  decide

/-- The same exact first-descent time holds on an infinite dyadic ray. -/
theorem ray_6059 (m : Nat) : stoppingTime (2 ^ 5 * m + 6059) 5 :=
  stoppingTime_of_classCertificate certificate_6059 m

/-- Checked base and every prefix for input 6061. -/
theorem certificate_6061 : classCertificateB 2 6061 = true := by
  decide

/-- The same exact first-descent time holds on an infinite dyadic ray. -/
theorem ray_6061 (m : Nat) : stoppingTime (2 ^ 2 * m + 6061) 2 :=
  stoppingTime_of_classCertificate certificate_6061 m

/-- Checked base and every prefix for input 6063. -/
theorem certificate_6063 : classCertificateB 8 6063 = true := by
  decide

/-- The same exact first-descent time holds on an infinite dyadic ray. -/
theorem ray_6063 (m : Nat) : stoppingTime (2 ^ 8 * m + 6063) 8 :=
  stoppingTime_of_classCertificate certificate_6063 m

/-- Checked base and every prefix for input 6065. -/
theorem certificate_6065 : classCertificateB 2 6065 = true := by
  decide

/-- The same exact first-descent time holds on an infinite dyadic ray. -/
theorem ray_6065 (m : Nat) : stoppingTime (2 ^ 2 * m + 6065) 2 :=
  stoppingTime_of_classCertificate certificate_6065 m

/-- Checked base and every prefix for input 6067. -/
theorem certificate_6067 : classCertificateB 4 6067 = true := by
  decide

/-- The same exact first-descent time holds on an infinite dyadic ray. -/
theorem ray_6067 (m : Nat) : stoppingTime (2 ^ 4 * m + 6067) 4 :=
  stoppingTime_of_classCertificate certificate_6067 m

/-- Checked base and every prefix for input 6069. -/
theorem certificate_6069 : classCertificateB 2 6069 = true := by
  decide

/-- The same exact first-descent time holds on an infinite dyadic ray. -/
theorem ray_6069 (m : Nat) : stoppingTime (2 ^ 2 * m + 6069) 2 :=
  stoppingTime_of_classCertificate certificate_6069 m

/-- Checked base and every prefix for input 6071. -/
theorem certificate_6071 : classCertificateB 5 6071 = true := by
  decide

/-- The same exact first-descent time holds on an infinite dyadic ray. -/
theorem ray_6071 (m : Nat) : stoppingTime (2 ^ 5 * m + 6071) 5 :=
  stoppingTime_of_classCertificate certificate_6071 m

/-- Checked base and every prefix for input 6073. -/
theorem certificate_6073 : classCertificateB 2 6073 = true := by
  decide

/-- The same exact first-descent time holds on an infinite dyadic ray. -/
theorem ray_6073 (m : Nat) : stoppingTime (2 ^ 2 * m + 6073) 2 :=
  stoppingTime_of_classCertificate certificate_6073 m

/-- Checked base and every prefix for input 6075. -/
theorem certificate_6075 : classCertificateB 7 6075 = true := by
  decide

/-- The same exact first-descent time holds on an infinite dyadic ray. -/
theorem ray_6075 (m : Nat) : stoppingTime (2 ^ 7 * m + 6075) 7 :=
  stoppingTime_of_classCertificate certificate_6075 m

/-- Checked base and every prefix for input 6077. -/
theorem certificate_6077 : classCertificateB 2 6077 = true := by
  decide

/-- The same exact first-descent time holds on an infinite dyadic ray. -/
theorem ray_6077 (m : Nat) : stoppingTime (2 ^ 2 * m + 6077) 2 :=
  stoppingTime_of_classCertificate certificate_6077 m

/-- Checked base and every prefix for input 6079. -/
theorem certificate_6079 : classCertificateB 18 6079 = true := by
  decide

/-- The same exact first-descent time holds on an infinite dyadic ray. -/
theorem ray_6079 (m : Nat) : stoppingTime (2 ^ 18 * m + 6079) 18 :=
  stoppingTime_of_classCertificate certificate_6079 m

/-- Checked base and every prefix for input 6081. -/
theorem certificate_6081 : classCertificateB 2 6081 = true := by
  decide

/-- The same exact first-descent time holds on an infinite dyadic ray. -/
theorem ray_6081 (m : Nat) : stoppingTime (2 ^ 2 * m + 6081) 2 :=
  stoppingTime_of_classCertificate certificate_6081 m

/-- Checked base and every prefix for input 6083. -/
theorem certificate_6083 : classCertificateB 4 6083 = true := by
  decide

/-- The same exact first-descent time holds on an infinite dyadic ray. -/
theorem ray_6083 (m : Nat) : stoppingTime (2 ^ 4 * m + 6083) 4 :=
  stoppingTime_of_classCertificate certificate_6083 m

/-- Checked base and every prefix for input 6085. -/
theorem certificate_6085 : classCertificateB 2 6085 = true := by
  decide

/-- The same exact first-descent time holds on an infinite dyadic ray. -/
theorem ray_6085 (m : Nat) : stoppingTime (2 ^ 2 * m + 6085) 2 :=
  stoppingTime_of_classCertificate certificate_6085 m

/-- Checked base and every prefix for input 6087. -/
theorem certificate_6087 : classCertificateB 8 6087 = true := by
  decide

/-- The same exact first-descent time holds on an infinite dyadic ray. -/
theorem ray_6087 (m : Nat) : stoppingTime (2 ^ 8 * m + 6087) 8 :=
  stoppingTime_of_classCertificate certificate_6087 m

/-- Checked base and every prefix for input 6089. -/
theorem certificate_6089 : classCertificateB 2 6089 = true := by
  decide

/-- The same exact first-descent time holds on an infinite dyadic ray. -/
theorem ray_6089 (m : Nat) : stoppingTime (2 ^ 2 * m + 6089) 2 :=
  stoppingTime_of_classCertificate certificate_6089 m

/-- Checked base and every prefix for input 6091. -/
theorem certificate_6091 : classCertificateB 5 6091 = true := by
  decide

/-- The same exact first-descent time holds on an infinite dyadic ray. -/
theorem ray_6091 (m : Nat) : stoppingTime (2 ^ 5 * m + 6091) 5 :=
  stoppingTime_of_classCertificate certificate_6091 m

/-- Checked base and every prefix for input 6093. -/
theorem certificate_6093 : classCertificateB 2 6093 = true := by
  decide

/-- The same exact first-descent time holds on an infinite dyadic ray. -/
theorem ray_6093 (m : Nat) : stoppingTime (2 ^ 2 * m + 6093) 2 :=
  stoppingTime_of_classCertificate certificate_6093 m

/-- Checked base and every prefix for input 6095. -/
theorem certificate_6095 : classCertificateB 10 6095 = true := by
  decide

/-- The same exact first-descent time holds on an infinite dyadic ray. -/
theorem ray_6095 (m : Nat) : stoppingTime (2 ^ 10 * m + 6095) 10 :=
  stoppingTime_of_classCertificate certificate_6095 m

/-- Exhaustive coverage of the odd inputs in this batch, with no gaps. -/
theorem coverage : CertifiedRange 6031 6097 := by
  intro n hlo hhi hodd
  have hn : n = 6031 ∨ n = 6033 ∨ n = 6035 ∨ n = 6037 ∨ n = 6039 ∨ n = 6041 ∨ n = 6043 ∨ n = 6045 ∨ n = 6047 ∨ n = 6049 ∨ n = 6051 ∨ n = 6053 ∨ n = 6055 ∨ n = 6057 ∨ n = 6059 ∨ n = 6061 ∨ n = 6063 ∨ n = 6065 ∨ n = 6067 ∨ n = 6069 ∨ n = 6071 ∨ n = 6073 ∨ n = 6075 ∨ n = 6077 ∨ n = 6079 ∨ n = 6081 ∨ n = 6083 ∨ n = 6085 ∨ n = 6087 ∨ n = 6089 ∨ n = 6091 ∨ n = 6093 ∨ n = 6095 := by omega
  rcases hn with h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h
  · subst n
    exact ⟨7, witness_of_certificate certificate_6031⟩
  · subst n
    exact ⟨2, witness_of_certificate certificate_6033⟩
  · subst n
    exact ⟨4, witness_of_certificate certificate_6035⟩
  · subst n
    exact ⟨2, witness_of_certificate certificate_6037⟩
  · subst n
    exact ⟨5, witness_of_certificate certificate_6039⟩
  · subst n
    exact ⟨2, witness_of_certificate certificate_6041⟩
  · subst n
    exact ⟨10, witness_of_certificate certificate_6043⟩
  · subst n
    exact ⟨2, witness_of_certificate certificate_6045⟩
  · subst n
    exact ⟨13, witness_of_certificate certificate_6047⟩
  · subst n
    exact ⟨2, witness_of_certificate certificate_6049⟩
  · subst n
    exact ⟨4, witness_of_certificate certificate_6051⟩
  · subst n
    exact ⟨2, witness_of_certificate certificate_6053⟩
  · subst n
    exact ⟨18, witness_of_certificate certificate_6055⟩
  · subst n
    exact ⟨2, witness_of_certificate certificate_6057⟩
  · subst n
    exact ⟨5, witness_of_certificate certificate_6059⟩
  · subst n
    exact ⟨2, witness_of_certificate certificate_6061⟩
  · subst n
    exact ⟨8, witness_of_certificate certificate_6063⟩
  · subst n
    exact ⟨2, witness_of_certificate certificate_6065⟩
  · subst n
    exact ⟨4, witness_of_certificate certificate_6067⟩
  · subst n
    exact ⟨2, witness_of_certificate certificate_6069⟩
  · subst n
    exact ⟨5, witness_of_certificate certificate_6071⟩
  · subst n
    exact ⟨2, witness_of_certificate certificate_6073⟩
  · subst n
    exact ⟨7, witness_of_certificate certificate_6075⟩
  · subst n
    exact ⟨2, witness_of_certificate certificate_6077⟩
  · subst n
    exact ⟨18, witness_of_certificate certificate_6079⟩
  · subst n
    exact ⟨2, witness_of_certificate certificate_6081⟩
  · subst n
    exact ⟨4, witness_of_certificate certificate_6083⟩
  · subst n
    exact ⟨2, witness_of_certificate certificate_6085⟩
  · subst n
    exact ⟨8, witness_of_certificate certificate_6087⟩
  · subst n
    exact ⟨2, witness_of_certificate certificate_6089⟩
  · subst n
    exact ⟨5, witness_of_certificate certificate_6091⟩
  · subst n
    exact ⟨2, witness_of_certificate certificate_6093⟩
  · subst n
    exact ⟨10, witness_of_certificate certificate_6095⟩

end Collatz.Research.CoefficientDescent.Batch091
