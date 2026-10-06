import Collatz.Research.CoefficientDescent.Basic

namespace Collatz.Research.CoefficientDescent.Batch020

open FirstDescentClass

set_option maxRecDepth 20000
set_option maxHeartbeats 0

/-- Checked base and every prefix for input 1275. -/
theorem certificate_1275 : classCertificateB 15 1275 = true := by
  decide

/-- The same exact first-descent time holds on an infinite dyadic ray. -/
theorem ray_1275 (m : Nat) : stoppingTime (2 ^ 15 * m + 1275) 15 :=
  stoppingTime_of_classCertificate certificate_1275 m

/-- Checked base and every prefix for input 1277. -/
theorem certificate_1277 : classCertificateB 2 1277 = true := by
  decide

/-- The same exact first-descent time holds on an infinite dyadic ray. -/
theorem ray_1277 (m : Nat) : stoppingTime (2 ^ 2 * m + 1277) 2 :=
  stoppingTime_of_classCertificate certificate_1277 m

/-- Checked base and every prefix for input 1279. -/
theorem certificate_1279 : classCertificateB 23 1279 = true := by
  decide

/-- The same exact first-descent time holds on an infinite dyadic ray. -/
theorem ray_1279 (m : Nat) : stoppingTime (2 ^ 23 * m + 1279) 23 :=
  stoppingTime_of_classCertificate certificate_1279 m

/-- Checked base and every prefix for input 1281. -/
theorem certificate_1281 : classCertificateB 2 1281 = true := by
  decide

/-- The same exact first-descent time holds on an infinite dyadic ray. -/
theorem ray_1281 (m : Nat) : stoppingTime (2 ^ 2 * m + 1281) 2 :=
  stoppingTime_of_classCertificate certificate_1281 m

/-- Checked base and every prefix for input 1283. -/
theorem certificate_1283 : classCertificateB 4 1283 = true := by
  decide

/-- The same exact first-descent time holds on an infinite dyadic ray. -/
theorem ray_1283 (m : Nat) : stoppingTime (2 ^ 4 * m + 1283) 4 :=
  stoppingTime_of_classCertificate certificate_1283 m

/-- Checked base and every prefix for input 1285. -/
theorem certificate_1285 : classCertificateB 2 1285 = true := by
  decide

/-- The same exact first-descent time holds on an infinite dyadic ray. -/
theorem ray_1285 (m : Nat) : stoppingTime (2 ^ 2 * m + 1285) 2 :=
  stoppingTime_of_classCertificate certificate_1285 m

/-- Checked base and every prefix for input 1287. -/
theorem certificate_1287 : classCertificateB 7 1287 = true := by
  decide

/-- The same exact first-descent time holds on an infinite dyadic ray. -/
theorem ray_1287 (m : Nat) : stoppingTime (2 ^ 7 * m + 1287) 7 :=
  stoppingTime_of_classCertificate certificate_1287 m

/-- Checked base and every prefix for input 1289. -/
theorem certificate_1289 : classCertificateB 2 1289 = true := by
  decide

/-- The same exact first-descent time holds on an infinite dyadic ray. -/
theorem ray_1289 (m : Nat) : stoppingTime (2 ^ 2 * m + 1289) 2 :=
  stoppingTime_of_classCertificate certificate_1289 m

/-- Checked base and every prefix for input 1291. -/
theorem certificate_1291 : classCertificateB 5 1291 = true := by
  decide

/-- The same exact first-descent time holds on an infinite dyadic ray. -/
theorem ray_1291 (m : Nat) : stoppingTime (2 ^ 5 * m + 1291) 5 :=
  stoppingTime_of_classCertificate certificate_1291 m

/-- Checked base and every prefix for input 1293. -/
theorem certificate_1293 : classCertificateB 2 1293 = true := by
  decide

/-- The same exact first-descent time holds on an infinite dyadic ray. -/
theorem ray_1293 (m : Nat) : stoppingTime (2 ^ 2 * m + 1293) 2 :=
  stoppingTime_of_classCertificate certificate_1293 m

/-- Checked base and every prefix for input 1295. -/
theorem certificate_1295 : classCertificateB 7 1295 = true := by
  decide

/-- The same exact first-descent time holds on an infinite dyadic ray. -/
theorem ray_1295 (m : Nat) : stoppingTime (2 ^ 7 * m + 1295) 7 :=
  stoppingTime_of_classCertificate certificate_1295 m

/-- Checked base and every prefix for input 1297. -/
theorem certificate_1297 : classCertificateB 2 1297 = true := by
  decide

/-- The same exact first-descent time holds on an infinite dyadic ray. -/
theorem ray_1297 (m : Nat) : stoppingTime (2 ^ 2 * m + 1297) 2 :=
  stoppingTime_of_classCertificate certificate_1297 m

/-- Checked base and every prefix for input 1299. -/
theorem certificate_1299 : classCertificateB 4 1299 = true := by
  decide

/-- The same exact first-descent time holds on an infinite dyadic ray. -/
theorem ray_1299 (m : Nat) : stoppingTime (2 ^ 4 * m + 1299) 4 :=
  stoppingTime_of_classCertificate certificate_1299 m

/-- Checked base and every prefix for input 1301. -/
theorem certificate_1301 : classCertificateB 2 1301 = true := by
  decide

/-- The same exact first-descent time holds on an infinite dyadic ray. -/
theorem ray_1301 (m : Nat) : stoppingTime (2 ^ 2 * m + 1301) 2 :=
  stoppingTime_of_classCertificate certificate_1301 m

/-- Checked base and every prefix for input 1303. -/
theorem certificate_1303 : classCertificateB 5 1303 = true := by
  decide

/-- The same exact first-descent time holds on an infinite dyadic ray. -/
theorem ray_1303 (m : Nat) : stoppingTime (2 ^ 5 * m + 1303) 5 :=
  stoppingTime_of_classCertificate certificate_1303 m

/-- Checked base and every prefix for input 1305. -/
theorem certificate_1305 : classCertificateB 2 1305 = true := by
  decide

/-- The same exact first-descent time holds on an infinite dyadic ray. -/
theorem ray_1305 (m : Nat) : stoppingTime (2 ^ 2 * m + 1305) 2 :=
  stoppingTime_of_classCertificate certificate_1305 m

/-- Checked base and every prefix for input 1307. -/
theorem certificate_1307 : classCertificateB 34 1307 = true := by
  decide

/-- The same exact first-descent time holds on an infinite dyadic ray. -/
theorem ray_1307 (m : Nat) : stoppingTime (2 ^ 34 * m + 1307) 34 :=
  stoppingTime_of_classCertificate certificate_1307 m

/-- Checked base and every prefix for input 1309. -/
theorem certificate_1309 : classCertificateB 2 1309 = true := by
  decide

/-- The same exact first-descent time holds on an infinite dyadic ray. -/
theorem ray_1309 (m : Nat) : stoppingTime (2 ^ 2 * m + 1309) 2 :=
  stoppingTime_of_classCertificate certificate_1309 m

/-- Checked base and every prefix for input 1311. -/
theorem certificate_1311 : classCertificateB 10 1311 = true := by
  decide

/-- The same exact first-descent time holds on an infinite dyadic ray. -/
theorem ray_1311 (m : Nat) : stoppingTime (2 ^ 10 * m + 1311) 10 :=
  stoppingTime_of_classCertificate certificate_1311 m

/-- Checked base and every prefix for input 1313. -/
theorem certificate_1313 : classCertificateB 2 1313 = true := by
  decide

/-- The same exact first-descent time holds on an infinite dyadic ray. -/
theorem ray_1313 (m : Nat) : stoppingTime (2 ^ 2 * m + 1313) 2 :=
  stoppingTime_of_classCertificate certificate_1313 m

/-- Checked base and every prefix for input 1315. -/
theorem certificate_1315 : classCertificateB 4 1315 = true := by
  decide

/-- The same exact first-descent time holds on an infinite dyadic ray. -/
theorem ray_1315 (m : Nat) : stoppingTime (2 ^ 4 * m + 1315) 4 :=
  stoppingTime_of_classCertificate certificate_1315 m

/-- Checked base and every prefix for input 1317. -/
theorem certificate_1317 : classCertificateB 2 1317 = true := by
  decide

/-- The same exact first-descent time holds on an infinite dyadic ray. -/
theorem ray_1317 (m : Nat) : stoppingTime (2 ^ 2 * m + 1317) 2 :=
  stoppingTime_of_classCertificate certificate_1317 m

/-- Checked base and every prefix for input 1319. -/
theorem certificate_1319 : classCertificateB 8 1319 = true := by
  decide

/-- The same exact first-descent time holds on an infinite dyadic ray. -/
theorem ray_1319 (m : Nat) : stoppingTime (2 ^ 8 * m + 1319) 8 :=
  stoppingTime_of_classCertificate certificate_1319 m

/-- Checked base and every prefix for input 1321. -/
theorem certificate_1321 : classCertificateB 2 1321 = true := by
  decide

/-- The same exact first-descent time holds on an infinite dyadic ray. -/
theorem ray_1321 (m : Nat) : stoppingTime (2 ^ 2 * m + 1321) 2 :=
  stoppingTime_of_classCertificate certificate_1321 m

/-- Checked base and every prefix for input 1323. -/
theorem certificate_1323 : classCertificateB 5 1323 = true := by
  decide

/-- The same exact first-descent time holds on an infinite dyadic ray. -/
theorem ray_1323 (m : Nat) : stoppingTime (2 ^ 5 * m + 1323) 5 :=
  stoppingTime_of_classCertificate certificate_1323 m

/-- Checked base and every prefix for input 1325. -/
theorem certificate_1325 : classCertificateB 2 1325 = true := by
  decide

/-- The same exact first-descent time holds on an infinite dyadic ray. -/
theorem ray_1325 (m : Nat) : stoppingTime (2 ^ 2 * m + 1325) 2 :=
  stoppingTime_of_classCertificate certificate_1325 m

/-- Checked base and every prefix for input 1327. -/
theorem certificate_1327 : classCertificateB 13 1327 = true := by
  decide

/-- The same exact first-descent time holds on an infinite dyadic ray. -/
theorem ray_1327 (m : Nat) : stoppingTime (2 ^ 13 * m + 1327) 13 :=
  stoppingTime_of_classCertificate certificate_1327 m

/-- Checked base and every prefix for input 1329. -/
theorem certificate_1329 : classCertificateB 2 1329 = true := by
  decide

/-- The same exact first-descent time holds on an infinite dyadic ray. -/
theorem ray_1329 (m : Nat) : stoppingTime (2 ^ 2 * m + 1329) 2 :=
  stoppingTime_of_classCertificate certificate_1329 m

/-- Checked base and every prefix for input 1331. -/
theorem certificate_1331 : classCertificateB 4 1331 = true := by
  decide

/-- The same exact first-descent time holds on an infinite dyadic ray. -/
theorem ray_1331 (m : Nat) : stoppingTime (2 ^ 4 * m + 1331) 4 :=
  stoppingTime_of_classCertificate certificate_1331 m

/-- Checked base and every prefix for input 1333. -/
theorem certificate_1333 : classCertificateB 2 1333 = true := by
  decide

/-- The same exact first-descent time holds on an infinite dyadic ray. -/
theorem ray_1333 (m : Nat) : stoppingTime (2 ^ 2 * m + 1333) 2 :=
  stoppingTime_of_classCertificate certificate_1333 m

/-- Checked base and every prefix for input 1335. -/
theorem certificate_1335 : classCertificateB 5 1335 = true := by
  decide

/-- The same exact first-descent time holds on an infinite dyadic ray. -/
theorem ray_1335 (m : Nat) : stoppingTime (2 ^ 5 * m + 1335) 5 :=
  stoppingTime_of_classCertificate certificate_1335 m

/-- Checked base and every prefix for input 1337. -/
theorem certificate_1337 : classCertificateB 2 1337 = true := by
  decide

/-- The same exact first-descent time holds on an infinite dyadic ray. -/
theorem ray_1337 (m : Nat) : stoppingTime (2 ^ 2 * m + 1337) 2 :=
  stoppingTime_of_classCertificate certificate_1337 m

/-- Checked base and every prefix for input 1339. -/
theorem certificate_1339 : classCertificateB 7 1339 = true := by
  decide

/-- The same exact first-descent time holds on an infinite dyadic ray. -/
theorem ray_1339 (m : Nat) : stoppingTime (2 ^ 7 * m + 1339) 7 :=
  stoppingTime_of_classCertificate certificate_1339 m

/-- Exhaustive coverage of the odd inputs in this batch, with no gaps. -/
theorem coverage : CertifiedRange 1275 1341 := by
  intro n hlo hhi hodd
  have hn : n = 1275 ∨ n = 1277 ∨ n = 1279 ∨ n = 1281 ∨ n = 1283 ∨ n = 1285 ∨ n = 1287 ∨ n = 1289 ∨ n = 1291 ∨ n = 1293 ∨ n = 1295 ∨ n = 1297 ∨ n = 1299 ∨ n = 1301 ∨ n = 1303 ∨ n = 1305 ∨ n = 1307 ∨ n = 1309 ∨ n = 1311 ∨ n = 1313 ∨ n = 1315 ∨ n = 1317 ∨ n = 1319 ∨ n = 1321 ∨ n = 1323 ∨ n = 1325 ∨ n = 1327 ∨ n = 1329 ∨ n = 1331 ∨ n = 1333 ∨ n = 1335 ∨ n = 1337 ∨ n = 1339 := by omega
  rcases hn with h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h
  · subst n
    exact ⟨15, witness_of_certificate certificate_1275⟩
  · subst n
    exact ⟨2, witness_of_certificate certificate_1277⟩
  · subst n
    exact ⟨23, witness_of_certificate certificate_1279⟩
  · subst n
    exact ⟨2, witness_of_certificate certificate_1281⟩
  · subst n
    exact ⟨4, witness_of_certificate certificate_1283⟩
  · subst n
    exact ⟨2, witness_of_certificate certificate_1285⟩
  · subst n
    exact ⟨7, witness_of_certificate certificate_1287⟩
  · subst n
    exact ⟨2, witness_of_certificate certificate_1289⟩
  · subst n
    exact ⟨5, witness_of_certificate certificate_1291⟩
  · subst n
    exact ⟨2, witness_of_certificate certificate_1293⟩
  · subst n
    exact ⟨7, witness_of_certificate certificate_1295⟩
  · subst n
    exact ⟨2, witness_of_certificate certificate_1297⟩
  · subst n
    exact ⟨4, witness_of_certificate certificate_1299⟩
  · subst n
    exact ⟨2, witness_of_certificate certificate_1301⟩
  · subst n
    exact ⟨5, witness_of_certificate certificate_1303⟩
  · subst n
    exact ⟨2, witness_of_certificate certificate_1305⟩
  · subst n
    exact ⟨34, witness_of_certificate certificate_1307⟩
  · subst n
    exact ⟨2, witness_of_certificate certificate_1309⟩
  · subst n
    exact ⟨10, witness_of_certificate certificate_1311⟩
  · subst n
    exact ⟨2, witness_of_certificate certificate_1313⟩
  · subst n
    exact ⟨4, witness_of_certificate certificate_1315⟩
  · subst n
    exact ⟨2, witness_of_certificate certificate_1317⟩
  · subst n
    exact ⟨8, witness_of_certificate certificate_1319⟩
  · subst n
    exact ⟨2, witness_of_certificate certificate_1321⟩
  · subst n
    exact ⟨5, witness_of_certificate certificate_1323⟩
  · subst n
    exact ⟨2, witness_of_certificate certificate_1325⟩
  · subst n
    exact ⟨13, witness_of_certificate certificate_1327⟩
  · subst n
    exact ⟨2, witness_of_certificate certificate_1329⟩
  · subst n
    exact ⟨4, witness_of_certificate certificate_1331⟩
  · subst n
    exact ⟨2, witness_of_certificate certificate_1333⟩
  · subst n
    exact ⟨5, witness_of_certificate certificate_1335⟩
  · subst n
    exact ⟨2, witness_of_certificate certificate_1337⟩
  · subst n
    exact ⟨7, witness_of_certificate certificate_1339⟩

end Collatz.Research.CoefficientDescent.Batch020
