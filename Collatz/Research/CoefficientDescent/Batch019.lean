import Collatz.Research.CoefficientDescent.Basic

namespace Collatz.Research.CoefficientDescent.Batch019

open FirstDescentClass

set_option maxRecDepth 20000
set_option maxHeartbeats 0

/-- Checked base and every prefix for input 1207. -/
theorem certificate_1207 : classCertificateB 5 1207 = true := by
  decide

/-- The same exact first-descent time holds on an infinite dyadic ray. -/
theorem ray_1207 (m : Nat) : stoppingTime (2 ^ 5 * m + 1207) 5 :=
  stoppingTime_of_classCertificate certificate_1207 m

/-- Checked base and every prefix for input 1209. -/
theorem certificate_1209 : classCertificateB 2 1209 = true := by
  decide

/-- The same exact first-descent time holds on an infinite dyadic ray. -/
theorem ray_1209 (m : Nat) : stoppingTime (2 ^ 2 * m + 1209) 2 :=
  stoppingTime_of_classCertificate certificate_1209 m

/-- Checked base and every prefix for input 1211. -/
theorem certificate_1211 : classCertificateB 7 1211 = true := by
  decide

/-- The same exact first-descent time holds on an infinite dyadic ray. -/
theorem ray_1211 (m : Nat) : stoppingTime (2 ^ 7 * m + 1211) 7 :=
  stoppingTime_of_classCertificate certificate_1211 m

/-- Checked base and every prefix for input 1213. -/
theorem certificate_1213 : classCertificateB 2 1213 = true := by
  decide

/-- The same exact first-descent time holds on an infinite dyadic ray. -/
theorem ray_1213 (m : Nat) : stoppingTime (2 ^ 2 * m + 1213) 2 :=
  stoppingTime_of_classCertificate certificate_1213 m

/-- Checked base and every prefix for input 1215. -/
theorem certificate_1215 : classCertificateB 13 1215 = true := by
  decide

/-- The same exact first-descent time holds on an infinite dyadic ray. -/
theorem ray_1215 (m : Nat) : stoppingTime (2 ^ 13 * m + 1215) 13 :=
  stoppingTime_of_classCertificate certificate_1215 m

/-- Checked base and every prefix for input 1217. -/
theorem certificate_1217 : classCertificateB 2 1217 = true := by
  decide

/-- The same exact first-descent time holds on an infinite dyadic ray. -/
theorem ray_1217 (m : Nat) : stoppingTime (2 ^ 2 * m + 1217) 2 :=
  stoppingTime_of_classCertificate certificate_1217 m

/-- Checked base and every prefix for input 1219. -/
theorem certificate_1219 : classCertificateB 4 1219 = true := by
  decide

/-- The same exact first-descent time holds on an infinite dyadic ray. -/
theorem ray_1219 (m : Nat) : stoppingTime (2 ^ 4 * m + 1219) 4 :=
  stoppingTime_of_classCertificate certificate_1219 m

/-- Checked base and every prefix for input 1221. -/
theorem certificate_1221 : classCertificateB 2 1221 = true := by
  decide

/-- The same exact first-descent time holds on an infinite dyadic ray. -/
theorem ray_1221 (m : Nat) : stoppingTime (2 ^ 2 * m + 1221) 2 :=
  stoppingTime_of_classCertificate certificate_1221 m

/-- Checked base and every prefix for input 1223. -/
theorem certificate_1223 : classCertificateB 8 1223 = true := by
  decide

/-- The same exact first-descent time holds on an infinite dyadic ray. -/
theorem ray_1223 (m : Nat) : stoppingTime (2 ^ 8 * m + 1223) 8 :=
  stoppingTime_of_classCertificate certificate_1223 m

/-- Checked base and every prefix for input 1225. -/
theorem certificate_1225 : classCertificateB 2 1225 = true := by
  decide

/-- The same exact first-descent time holds on an infinite dyadic ray. -/
theorem ray_1225 (m : Nat) : stoppingTime (2 ^ 2 * m + 1225) 2 :=
  stoppingTime_of_classCertificate certificate_1225 m

/-- Checked base and every prefix for input 1227. -/
theorem certificate_1227 : classCertificateB 5 1227 = true := by
  decide

/-- The same exact first-descent time holds on an infinite dyadic ray. -/
theorem ray_1227 (m : Nat) : stoppingTime (2 ^ 5 * m + 1227) 5 :=
  stoppingTime_of_classCertificate certificate_1227 m

/-- Checked base and every prefix for input 1229. -/
theorem certificate_1229 : classCertificateB 2 1229 = true := by
  decide

/-- The same exact first-descent time holds on an infinite dyadic ray. -/
theorem ray_1229 (m : Nat) : stoppingTime (2 ^ 2 * m + 1229) 2 :=
  stoppingTime_of_classCertificate certificate_1229 m

/-- Checked base and every prefix for input 1231. -/
theorem certificate_1231 : classCertificateB 12 1231 = true := by
  decide

/-- The same exact first-descent time holds on an infinite dyadic ray. -/
theorem ray_1231 (m : Nat) : stoppingTime (2 ^ 12 * m + 1231) 12 :=
  stoppingTime_of_classCertificate certificate_1231 m

/-- Checked base and every prefix for input 1233. -/
theorem certificate_1233 : classCertificateB 2 1233 = true := by
  decide

/-- The same exact first-descent time holds on an infinite dyadic ray. -/
theorem ray_1233 (m : Nat) : stoppingTime (2 ^ 2 * m + 1233) 2 :=
  stoppingTime_of_classCertificate certificate_1233 m

/-- Checked base and every prefix for input 1235. -/
theorem certificate_1235 : classCertificateB 4 1235 = true := by
  decide

/-- The same exact first-descent time holds on an infinite dyadic ray. -/
theorem ray_1235 (m : Nat) : stoppingTime (2 ^ 4 * m + 1235) 4 :=
  stoppingTime_of_classCertificate certificate_1235 m

/-- Checked base and every prefix for input 1237. -/
theorem certificate_1237 : classCertificateB 2 1237 = true := by
  decide

/-- The same exact first-descent time holds on an infinite dyadic ray. -/
theorem ray_1237 (m : Nat) : stoppingTime (2 ^ 2 * m + 1237) 2 :=
  stoppingTime_of_classCertificate certificate_1237 m

/-- Checked base and every prefix for input 1239. -/
theorem certificate_1239 : classCertificateB 5 1239 = true := by
  decide

/-- The same exact first-descent time holds on an infinite dyadic ray. -/
theorem ray_1239 (m : Nat) : stoppingTime (2 ^ 5 * m + 1239) 5 :=
  stoppingTime_of_classCertificate certificate_1239 m

/-- Checked base and every prefix for input 1241. -/
theorem certificate_1241 : classCertificateB 2 1241 = true := by
  decide

/-- The same exact first-descent time holds on an infinite dyadic ray. -/
theorem ray_1241 (m : Nat) : stoppingTime (2 ^ 2 * m + 1241) 2 :=
  stoppingTime_of_classCertificate certificate_1241 m

/-- Checked base and every prefix for input 1243. -/
theorem certificate_1243 : classCertificateB 8 1243 = true := by
  decide

/-- The same exact first-descent time holds on an infinite dyadic ray. -/
theorem ray_1243 (m : Nat) : stoppingTime (2 ^ 8 * m + 1243) 8 :=
  stoppingTime_of_classCertificate certificate_1243 m

/-- Checked base and every prefix for input 1245. -/
theorem certificate_1245 : classCertificateB 2 1245 = true := by
  decide

/-- The same exact first-descent time holds on an infinite dyadic ray. -/
theorem ray_1245 (m : Nat) : stoppingTime (2 ^ 2 * m + 1245) 2 :=
  stoppingTime_of_classCertificate certificate_1245 m

/-- Checked base and every prefix for input 1247. -/
theorem certificate_1247 : classCertificateB 13 1247 = true := by
  decide

/-- The same exact first-descent time holds on an infinite dyadic ray. -/
theorem ray_1247 (m : Nat) : stoppingTime (2 ^ 13 * m + 1247) 13 :=
  stoppingTime_of_classCertificate certificate_1247 m

/-- Checked base and every prefix for input 1249. -/
theorem certificate_1249 : classCertificateB 2 1249 = true := by
  decide

/-- The same exact first-descent time holds on an infinite dyadic ray. -/
theorem ray_1249 (m : Nat) : stoppingTime (2 ^ 2 * m + 1249) 2 :=
  stoppingTime_of_classCertificate certificate_1249 m

/-- Checked base and every prefix for input 1251. -/
theorem certificate_1251 : classCertificateB 4 1251 = true := by
  decide

/-- The same exact first-descent time holds on an infinite dyadic ray. -/
theorem ray_1251 (m : Nat) : stoppingTime (2 ^ 4 * m + 1251) 4 :=
  stoppingTime_of_classCertificate certificate_1251 m

/-- Checked base and every prefix for input 1253. -/
theorem certificate_1253 : classCertificateB 2 1253 = true := by
  decide

/-- The same exact first-descent time holds on an infinite dyadic ray. -/
theorem ray_1253 (m : Nat) : stoppingTime (2 ^ 2 * m + 1253) 2 :=
  stoppingTime_of_classCertificate certificate_1253 m

/-- Checked base and every prefix for input 1255. -/
theorem certificate_1255 : classCertificateB 20 1255 = true := by
  decide

/-- The same exact first-descent time holds on an infinite dyadic ray. -/
theorem ray_1255 (m : Nat) : stoppingTime (2 ^ 20 * m + 1255) 20 :=
  stoppingTime_of_classCertificate certificate_1255 m

/-- Checked base and every prefix for input 1257. -/
theorem certificate_1257 : classCertificateB 2 1257 = true := by
  decide

/-- The same exact first-descent time holds on an infinite dyadic ray. -/
theorem ray_1257 (m : Nat) : stoppingTime (2 ^ 2 * m + 1257) 2 :=
  stoppingTime_of_classCertificate certificate_1257 m

/-- Checked base and every prefix for input 1259. -/
theorem certificate_1259 : classCertificateB 5 1259 = true := by
  decide

/-- The same exact first-descent time holds on an infinite dyadic ray. -/
theorem ray_1259 (m : Nat) : stoppingTime (2 ^ 5 * m + 1259) 5 :=
  stoppingTime_of_classCertificate certificate_1259 m

/-- Checked base and every prefix for input 1261. -/
theorem certificate_1261 : classCertificateB 2 1261 = true := by
  decide

/-- The same exact first-descent time holds on an infinite dyadic ray. -/
theorem ray_1261 (m : Nat) : stoppingTime (2 ^ 2 * m + 1261) 2 :=
  stoppingTime_of_classCertificate certificate_1261 m

/-- Checked base and every prefix for input 1263. -/
theorem certificate_1263 : classCertificateB 26 1263 = true := by
  decide

/-- The same exact first-descent time holds on an infinite dyadic ray. -/
theorem ray_1263 (m : Nat) : stoppingTime (2 ^ 26 * m + 1263) 26 :=
  stoppingTime_of_classCertificate certificate_1263 m

/-- Checked base and every prefix for input 1265. -/
theorem certificate_1265 : classCertificateB 2 1265 = true := by
  decide

/-- The same exact first-descent time holds on an infinite dyadic ray. -/
theorem ray_1265 (m : Nat) : stoppingTime (2 ^ 2 * m + 1265) 2 :=
  stoppingTime_of_classCertificate certificate_1265 m

/-- Checked base and every prefix for input 1267. -/
theorem certificate_1267 : classCertificateB 4 1267 = true := by
  decide

/-- The same exact first-descent time holds on an infinite dyadic ray. -/
theorem ray_1267 (m : Nat) : stoppingTime (2 ^ 4 * m + 1267) 4 :=
  stoppingTime_of_classCertificate certificate_1267 m

/-- Checked base and every prefix for input 1269. -/
theorem certificate_1269 : classCertificateB 2 1269 = true := by
  decide

/-- The same exact first-descent time holds on an infinite dyadic ray. -/
theorem ray_1269 (m : Nat) : stoppingTime (2 ^ 2 * m + 1269) 2 :=
  stoppingTime_of_classCertificate certificate_1269 m

/-- Checked base and every prefix for input 1271. -/
theorem certificate_1271 : classCertificateB 5 1271 = true := by
  decide

/-- The same exact first-descent time holds on an infinite dyadic ray. -/
theorem ray_1271 (m : Nat) : stoppingTime (2 ^ 5 * m + 1271) 5 :=
  stoppingTime_of_classCertificate certificate_1271 m

/-- Checked base and every prefix for input 1273. -/
theorem certificate_1273 : classCertificateB 2 1273 = true := by
  decide

/-- The same exact first-descent time holds on an infinite dyadic ray. -/
theorem ray_1273 (m : Nat) : stoppingTime (2 ^ 2 * m + 1273) 2 :=
  stoppingTime_of_classCertificate certificate_1273 m

/-- Exhaustive coverage of the odd inputs in this batch, with no gaps. -/
theorem coverage : CertifiedRange 1207 1275 := by
  intro n hlo hhi hodd
  have hn : n = 1207 ∨ n = 1209 ∨ n = 1211 ∨ n = 1213 ∨ n = 1215 ∨ n = 1217 ∨ n = 1219 ∨ n = 1221 ∨ n = 1223 ∨ n = 1225 ∨ n = 1227 ∨ n = 1229 ∨ n = 1231 ∨ n = 1233 ∨ n = 1235 ∨ n = 1237 ∨ n = 1239 ∨ n = 1241 ∨ n = 1243 ∨ n = 1245 ∨ n = 1247 ∨ n = 1249 ∨ n = 1251 ∨ n = 1253 ∨ n = 1255 ∨ n = 1257 ∨ n = 1259 ∨ n = 1261 ∨ n = 1263 ∨ n = 1265 ∨ n = 1267 ∨ n = 1269 ∨ n = 1271 ∨ n = 1273 := by omega
  rcases hn with h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h
  · subst n
    exact ⟨5, witness_of_certificate certificate_1207⟩
  · subst n
    exact ⟨2, witness_of_certificate certificate_1209⟩
  · subst n
    exact ⟨7, witness_of_certificate certificate_1211⟩
  · subst n
    exact ⟨2, witness_of_certificate certificate_1213⟩
  · subst n
    exact ⟨13, witness_of_certificate certificate_1215⟩
  · subst n
    exact ⟨2, witness_of_certificate certificate_1217⟩
  · subst n
    exact ⟨4, witness_of_certificate certificate_1219⟩
  · subst n
    exact ⟨2, witness_of_certificate certificate_1221⟩
  · subst n
    exact ⟨8, witness_of_certificate certificate_1223⟩
  · subst n
    exact ⟨2, witness_of_certificate certificate_1225⟩
  · subst n
    exact ⟨5, witness_of_certificate certificate_1227⟩
  · subst n
    exact ⟨2, witness_of_certificate certificate_1229⟩
  · subst n
    exact ⟨12, witness_of_certificate certificate_1231⟩
  · subst n
    exact ⟨2, witness_of_certificate certificate_1233⟩
  · subst n
    exact ⟨4, witness_of_certificate certificate_1235⟩
  · subst n
    exact ⟨2, witness_of_certificate certificate_1237⟩
  · subst n
    exact ⟨5, witness_of_certificate certificate_1239⟩
  · subst n
    exact ⟨2, witness_of_certificate certificate_1241⟩
  · subst n
    exact ⟨8, witness_of_certificate certificate_1243⟩
  · subst n
    exact ⟨2, witness_of_certificate certificate_1245⟩
  · subst n
    exact ⟨13, witness_of_certificate certificate_1247⟩
  · subst n
    exact ⟨2, witness_of_certificate certificate_1249⟩
  · subst n
    exact ⟨4, witness_of_certificate certificate_1251⟩
  · subst n
    exact ⟨2, witness_of_certificate certificate_1253⟩
  · subst n
    exact ⟨20, witness_of_certificate certificate_1255⟩
  · subst n
    exact ⟨2, witness_of_certificate certificate_1257⟩
  · subst n
    exact ⟨5, witness_of_certificate certificate_1259⟩
  · subst n
    exact ⟨2, witness_of_certificate certificate_1261⟩
  · subst n
    exact ⟨26, witness_of_certificate certificate_1263⟩
  · subst n
    exact ⟨2, witness_of_certificate certificate_1265⟩
  · subst n
    exact ⟨4, witness_of_certificate certificate_1267⟩
  · subst n
    exact ⟨2, witness_of_certificate certificate_1269⟩
  · subst n
    exact ⟨5, witness_of_certificate certificate_1271⟩
  · subst n
    exact ⟨2, witness_of_certificate certificate_1273⟩

end Collatz.Research.CoefficientDescent.Batch019
