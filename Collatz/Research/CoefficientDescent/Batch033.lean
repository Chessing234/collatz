import Collatz.Research.CoefficientDescent.Basic

namespace Collatz.Research.CoefficientDescent.Batch033

open FirstDescentClass

set_option maxRecDepth 20000
set_option maxHeartbeats 0

/-- Checked base and every prefix for input 2145. -/
theorem certificate_2145 : classCertificateB 2 2145 = true := by
  decide

/-- The same exact first-descent time holds on an infinite dyadic ray. -/
theorem ray_2145 (m : Nat) : stoppingTime (2 ^ 2 * m + 2145) 2 :=
  stoppingTime_of_classCertificate certificate_2145 m

/-- Checked base and every prefix for input 2147. -/
theorem certificate_2147 : classCertificateB 4 2147 = true := by
  decide

/-- The same exact first-descent time holds on an infinite dyadic ray. -/
theorem ray_2147 (m : Nat) : stoppingTime (2 ^ 4 * m + 2147) 4 :=
  stoppingTime_of_classCertificate certificate_2147 m

/-- Checked base and every prefix for input 2149. -/
theorem certificate_2149 : classCertificateB 2 2149 = true := by
  decide

/-- The same exact first-descent time holds on an infinite dyadic ray. -/
theorem ray_2149 (m : Nat) : stoppingTime (2 ^ 2 * m + 2149) 2 :=
  stoppingTime_of_classCertificate certificate_2149 m

/-- Checked base and every prefix for input 2151. -/
theorem certificate_2151 : classCertificateB 43 2151 = true := by
  decide

/-- The same exact first-descent time holds on an infinite dyadic ray. -/
theorem ray_2151 (m : Nat) : stoppingTime (2 ^ 43 * m + 2151) 43 :=
  stoppingTime_of_classCertificate certificate_2151 m

/-- Checked base and every prefix for input 2153. -/
theorem certificate_2153 : classCertificateB 2 2153 = true := by
  decide

/-- The same exact first-descent time holds on an infinite dyadic ray. -/
theorem ray_2153 (m : Nat) : stoppingTime (2 ^ 2 * m + 2153) 2 :=
  stoppingTime_of_classCertificate certificate_2153 m

/-- Checked base and every prefix for input 2155. -/
theorem certificate_2155 : classCertificateB 5 2155 = true := by
  decide

/-- The same exact first-descent time holds on an infinite dyadic ray. -/
theorem ray_2155 (m : Nat) : stoppingTime (2 ^ 5 * m + 2155) 5 :=
  stoppingTime_of_classCertificate certificate_2155 m

/-- Checked base and every prefix for input 2157. -/
theorem certificate_2157 : classCertificateB 2 2157 = true := by
  decide

/-- The same exact first-descent time holds on an infinite dyadic ray. -/
theorem ray_2157 (m : Nat) : stoppingTime (2 ^ 2 * m + 2157) 2 :=
  stoppingTime_of_classCertificate certificate_2157 m

/-- Checked base and every prefix for input 2159. -/
theorem certificate_2159 : classCertificateB 18 2159 = true := by
  decide

/-- The same exact first-descent time holds on an infinite dyadic ray. -/
theorem ray_2159 (m : Nat) : stoppingTime (2 ^ 18 * m + 2159) 18 :=
  stoppingTime_of_classCertificate certificate_2159 m

/-- Checked base and every prefix for input 2161. -/
theorem certificate_2161 : classCertificateB 2 2161 = true := by
  decide

/-- The same exact first-descent time holds on an infinite dyadic ray. -/
theorem ray_2161 (m : Nat) : stoppingTime (2 ^ 2 * m + 2161) 2 :=
  stoppingTime_of_classCertificate certificate_2161 m

/-- Checked base and every prefix for input 2163. -/
theorem certificate_2163 : classCertificateB 4 2163 = true := by
  decide

/-- The same exact first-descent time holds on an infinite dyadic ray. -/
theorem ray_2163 (m : Nat) : stoppingTime (2 ^ 4 * m + 2163) 4 :=
  stoppingTime_of_classCertificate certificate_2163 m

/-- Checked base and every prefix for input 2165. -/
theorem certificate_2165 : classCertificateB 2 2165 = true := by
  decide

/-- The same exact first-descent time holds on an infinite dyadic ray. -/
theorem ray_2165 (m : Nat) : stoppingTime (2 ^ 2 * m + 2165) 2 :=
  stoppingTime_of_classCertificate certificate_2165 m

/-- Checked base and every prefix for input 2167. -/
theorem certificate_2167 : classCertificateB 5 2167 = true := by
  decide

/-- The same exact first-descent time holds on an infinite dyadic ray. -/
theorem ray_2167 (m : Nat) : stoppingTime (2 ^ 5 * m + 2167) 5 :=
  stoppingTime_of_classCertificate certificate_2167 m

/-- Checked base and every prefix for input 2169. -/
theorem certificate_2169 : classCertificateB 2 2169 = true := by
  decide

/-- The same exact first-descent time holds on an infinite dyadic ray. -/
theorem ray_2169 (m : Nat) : stoppingTime (2 ^ 2 * m + 2169) 2 :=
  stoppingTime_of_classCertificate certificate_2169 m

/-- Checked base and every prefix for input 2171. -/
theorem certificate_2171 : classCertificateB 8 2171 = true := by
  decide

/-- The same exact first-descent time holds on an infinite dyadic ray. -/
theorem ray_2171 (m : Nat) : stoppingTime (2 ^ 8 * m + 2171) 8 :=
  stoppingTime_of_classCertificate certificate_2171 m

/-- Checked base and every prefix for input 2173. -/
theorem certificate_2173 : classCertificateB 2 2173 = true := by
  decide

/-- The same exact first-descent time holds on an infinite dyadic ray. -/
theorem ray_2173 (m : Nat) : stoppingTime (2 ^ 2 * m + 2173) 2 :=
  stoppingTime_of_classCertificate certificate_2173 m

/-- Checked base and every prefix for input 2175. -/
theorem certificate_2175 : classCertificateB 20 2175 = true := by
  decide

/-- The same exact first-descent time holds on an infinite dyadic ray. -/
theorem ray_2175 (m : Nat) : stoppingTime (2 ^ 20 * m + 2175) 20 :=
  stoppingTime_of_classCertificate certificate_2175 m

/-- Checked base and every prefix for input 2177. -/
theorem certificate_2177 : classCertificateB 2 2177 = true := by
  decide

/-- The same exact first-descent time holds on an infinite dyadic ray. -/
theorem ray_2177 (m : Nat) : stoppingTime (2 ^ 2 * m + 2177) 2 :=
  stoppingTime_of_classCertificate certificate_2177 m

/-- Checked base and every prefix for input 2179. -/
theorem certificate_2179 : classCertificateB 4 2179 = true := by
  decide

/-- The same exact first-descent time holds on an infinite dyadic ray. -/
theorem ray_2179 (m : Nat) : stoppingTime (2 ^ 4 * m + 2179) 4 :=
  stoppingTime_of_classCertificate certificate_2179 m

/-- Checked base and every prefix for input 2181. -/
theorem certificate_2181 : classCertificateB 2 2181 = true := by
  decide

/-- The same exact first-descent time holds on an infinite dyadic ray. -/
theorem ray_2181 (m : Nat) : stoppingTime (2 ^ 2 * m + 2181) 2 :=
  stoppingTime_of_classCertificate certificate_2181 m

/-- Checked base and every prefix for input 2183. -/
theorem certificate_2183 : classCertificateB 7 2183 = true := by
  decide

/-- The same exact first-descent time holds on an infinite dyadic ray. -/
theorem ray_2183 (m : Nat) : stoppingTime (2 ^ 7 * m + 2183) 7 :=
  stoppingTime_of_classCertificate certificate_2183 m

/-- Checked base and every prefix for input 2185. -/
theorem certificate_2185 : classCertificateB 2 2185 = true := by
  decide

/-- The same exact first-descent time holds on an infinite dyadic ray. -/
theorem ray_2185 (m : Nat) : stoppingTime (2 ^ 2 * m + 2185) 2 :=
  stoppingTime_of_classCertificate certificate_2185 m

/-- Checked base and every prefix for input 2187. -/
theorem certificate_2187 : classCertificateB 5 2187 = true := by
  decide

/-- The same exact first-descent time holds on an infinite dyadic ray. -/
theorem ray_2187 (m : Nat) : stoppingTime (2 ^ 5 * m + 2187) 5 :=
  stoppingTime_of_classCertificate certificate_2187 m

/-- Checked base and every prefix for input 2189. -/
theorem certificate_2189 : classCertificateB 2 2189 = true := by
  decide

/-- The same exact first-descent time holds on an infinite dyadic ray. -/
theorem ray_2189 (m : Nat) : stoppingTime (2 ^ 2 * m + 2189) 2 :=
  stoppingTime_of_classCertificate certificate_2189 m

/-- Checked base and every prefix for input 2191. -/
theorem certificate_2191 : classCertificateB 7 2191 = true := by
  decide

/-- The same exact first-descent time holds on an infinite dyadic ray. -/
theorem ray_2191 (m : Nat) : stoppingTime (2 ^ 7 * m + 2191) 7 :=
  stoppingTime_of_classCertificate certificate_2191 m

/-- Checked base and every prefix for input 2193. -/
theorem certificate_2193 : classCertificateB 2 2193 = true := by
  decide

/-- The same exact first-descent time holds on an infinite dyadic ray. -/
theorem ray_2193 (m : Nat) : stoppingTime (2 ^ 2 * m + 2193) 2 :=
  stoppingTime_of_classCertificate certificate_2193 m

/-- Checked base and every prefix for input 2195. -/
theorem certificate_2195 : classCertificateB 4 2195 = true := by
  decide

/-- The same exact first-descent time holds on an infinite dyadic ray. -/
theorem ray_2195 (m : Nat) : stoppingTime (2 ^ 4 * m + 2195) 4 :=
  stoppingTime_of_classCertificate certificate_2195 m

/-- Checked base and every prefix for input 2197. -/
theorem certificate_2197 : classCertificateB 2 2197 = true := by
  decide

/-- The same exact first-descent time holds on an infinite dyadic ray. -/
theorem ray_2197 (m : Nat) : stoppingTime (2 ^ 2 * m + 2197) 2 :=
  stoppingTime_of_classCertificate certificate_2197 m

/-- Checked base and every prefix for input 2199. -/
theorem certificate_2199 : classCertificateB 5 2199 = true := by
  decide

/-- The same exact first-descent time holds on an infinite dyadic ray. -/
theorem ray_2199 (m : Nat) : stoppingTime (2 ^ 5 * m + 2199) 5 :=
  stoppingTime_of_classCertificate certificate_2199 m

/-- Checked base and every prefix for input 2201. -/
theorem certificate_2201 : classCertificateB 2 2201 = true := by
  decide

/-- The same exact first-descent time holds on an infinite dyadic ray. -/
theorem ray_2201 (m : Nat) : stoppingTime (2 ^ 2 * m + 2201) 2 :=
  stoppingTime_of_classCertificate certificate_2201 m

/-- Checked base and every prefix for input 2203. -/
theorem certificate_2203 : classCertificateB 12 2203 = true := by
  decide

/-- The same exact first-descent time holds on an infinite dyadic ray. -/
theorem ray_2203 (m : Nat) : stoppingTime (2 ^ 12 * m + 2203) 12 :=
  stoppingTime_of_classCertificate certificate_2203 m

/-- Checked base and every prefix for input 2205. -/
theorem certificate_2205 : classCertificateB 2 2205 = true := by
  decide

/-- The same exact first-descent time holds on an infinite dyadic ray. -/
theorem ray_2205 (m : Nat) : stoppingTime (2 ^ 2 * m + 2205) 2 :=
  stoppingTime_of_classCertificate certificate_2205 m

/-- Checked base and every prefix for input 2207. -/
theorem certificate_2207 : classCertificateB 27 2207 = true := by
  decide

/-- The same exact first-descent time holds on an infinite dyadic ray. -/
theorem ray_2207 (m : Nat) : stoppingTime (2 ^ 27 * m + 2207) 27 :=
  stoppingTime_of_classCertificate certificate_2207 m

/-- Checked base and every prefix for input 2209. -/
theorem certificate_2209 : classCertificateB 2 2209 = true := by
  decide

/-- The same exact first-descent time holds on an infinite dyadic ray. -/
theorem ray_2209 (m : Nat) : stoppingTime (2 ^ 2 * m + 2209) 2 :=
  stoppingTime_of_classCertificate certificate_2209 m

/-- Checked base and every prefix for input 2211. -/
theorem certificate_2211 : classCertificateB 4 2211 = true := by
  decide

/-- The same exact first-descent time holds on an infinite dyadic ray. -/
theorem ray_2211 (m : Nat) : stoppingTime (2 ^ 4 * m + 2211) 4 :=
  stoppingTime_of_classCertificate certificate_2211 m

/-- Exhaustive coverage of the odd inputs in this batch, with no gaps. -/
theorem coverage : CertifiedRange 2145 2213 := by
  intro n hlo hhi hodd
  have hn : n = 2145 ∨ n = 2147 ∨ n = 2149 ∨ n = 2151 ∨ n = 2153 ∨ n = 2155 ∨ n = 2157 ∨ n = 2159 ∨ n = 2161 ∨ n = 2163 ∨ n = 2165 ∨ n = 2167 ∨ n = 2169 ∨ n = 2171 ∨ n = 2173 ∨ n = 2175 ∨ n = 2177 ∨ n = 2179 ∨ n = 2181 ∨ n = 2183 ∨ n = 2185 ∨ n = 2187 ∨ n = 2189 ∨ n = 2191 ∨ n = 2193 ∨ n = 2195 ∨ n = 2197 ∨ n = 2199 ∨ n = 2201 ∨ n = 2203 ∨ n = 2205 ∨ n = 2207 ∨ n = 2209 ∨ n = 2211 := by omega
  rcases hn with h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h
  · subst n
    exact ⟨2, witness_of_certificate certificate_2145⟩
  · subst n
    exact ⟨4, witness_of_certificate certificate_2147⟩
  · subst n
    exact ⟨2, witness_of_certificate certificate_2149⟩
  · subst n
    exact ⟨43, witness_of_certificate certificate_2151⟩
  · subst n
    exact ⟨2, witness_of_certificate certificate_2153⟩
  · subst n
    exact ⟨5, witness_of_certificate certificate_2155⟩
  · subst n
    exact ⟨2, witness_of_certificate certificate_2157⟩
  · subst n
    exact ⟨18, witness_of_certificate certificate_2159⟩
  · subst n
    exact ⟨2, witness_of_certificate certificate_2161⟩
  · subst n
    exact ⟨4, witness_of_certificate certificate_2163⟩
  · subst n
    exact ⟨2, witness_of_certificate certificate_2165⟩
  · subst n
    exact ⟨5, witness_of_certificate certificate_2167⟩
  · subst n
    exact ⟨2, witness_of_certificate certificate_2169⟩
  · subst n
    exact ⟨8, witness_of_certificate certificate_2171⟩
  · subst n
    exact ⟨2, witness_of_certificate certificate_2173⟩
  · subst n
    exact ⟨20, witness_of_certificate certificate_2175⟩
  · subst n
    exact ⟨2, witness_of_certificate certificate_2177⟩
  · subst n
    exact ⟨4, witness_of_certificate certificate_2179⟩
  · subst n
    exact ⟨2, witness_of_certificate certificate_2181⟩
  · subst n
    exact ⟨7, witness_of_certificate certificate_2183⟩
  · subst n
    exact ⟨2, witness_of_certificate certificate_2185⟩
  · subst n
    exact ⟨5, witness_of_certificate certificate_2187⟩
  · subst n
    exact ⟨2, witness_of_certificate certificate_2189⟩
  · subst n
    exact ⟨7, witness_of_certificate certificate_2191⟩
  · subst n
    exact ⟨2, witness_of_certificate certificate_2193⟩
  · subst n
    exact ⟨4, witness_of_certificate certificate_2195⟩
  · subst n
    exact ⟨2, witness_of_certificate certificate_2197⟩
  · subst n
    exact ⟨5, witness_of_certificate certificate_2199⟩
  · subst n
    exact ⟨2, witness_of_certificate certificate_2201⟩
  · subst n
    exact ⟨12, witness_of_certificate certificate_2203⟩
  · subst n
    exact ⟨2, witness_of_certificate certificate_2205⟩
  · subst n
    exact ⟨27, witness_of_certificate certificate_2207⟩
  · subst n
    exact ⟨2, witness_of_certificate certificate_2209⟩
  · subst n
    exact ⟨4, witness_of_certificate certificate_2211⟩

end Collatz.Research.CoefficientDescent.Batch033
