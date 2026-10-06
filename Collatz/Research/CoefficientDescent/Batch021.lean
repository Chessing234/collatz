import Collatz.Research.CoefficientDescent.Basic

namespace Collatz.Research.CoefficientDescent.Batch021

open FirstDescentClass

set_option maxRecDepth 20000
set_option maxHeartbeats 0

/-- Checked base and every prefix for input 1341. -/
theorem certificate_1341 : classCertificateB 2 1341 = true := by
  decide

/-- The same exact first-descent time holds on an infinite dyadic ray. -/
theorem ray_1341 (m : Nat) : stoppingTime (2 ^ 2 * m + 1341) 2 :=
  stoppingTime_of_classCertificate certificate_1341 m

/-- Checked base and every prefix for input 1343. -/
theorem certificate_1343 : classCertificateB 23 1343 = true := by
  decide

/-- The same exact first-descent time holds on an infinite dyadic ray. -/
theorem ray_1343 (m : Nat) : stoppingTime (2 ^ 23 * m + 1343) 23 :=
  stoppingTime_of_classCertificate certificate_1343 m

/-- Checked base and every prefix for input 1345. -/
theorem certificate_1345 : classCertificateB 2 1345 = true := by
  decide

/-- The same exact first-descent time holds on an infinite dyadic ray. -/
theorem ray_1345 (m : Nat) : stoppingTime (2 ^ 2 * m + 1345) 2 :=
  stoppingTime_of_classCertificate certificate_1345 m

/-- Checked base and every prefix for input 1347. -/
theorem certificate_1347 : classCertificateB 4 1347 = true := by
  decide

/-- The same exact first-descent time holds on an infinite dyadic ray. -/
theorem ray_1347 (m : Nat) : stoppingTime (2 ^ 4 * m + 1347) 4 :=
  stoppingTime_of_classCertificate certificate_1347 m

/-- Checked base and every prefix for input 1349. -/
theorem certificate_1349 : classCertificateB 2 1349 = true := by
  decide

/-- The same exact first-descent time holds on an infinite dyadic ray. -/
theorem ray_1349 (m : Nat) : stoppingTime (2 ^ 2 * m + 1349) 2 :=
  stoppingTime_of_classCertificate certificate_1349 m

/-- Checked base and every prefix for input 1351. -/
theorem certificate_1351 : classCertificateB 16 1351 = true := by
  decide

/-- The same exact first-descent time holds on an infinite dyadic ray. -/
theorem ray_1351 (m : Nat) : stoppingTime (2 ^ 16 * m + 1351) 16 :=
  stoppingTime_of_classCertificate certificate_1351 m

/-- Checked base and every prefix for input 1353. -/
theorem certificate_1353 : classCertificateB 2 1353 = true := by
  decide

/-- The same exact first-descent time holds on an infinite dyadic ray. -/
theorem ray_1353 (m : Nat) : stoppingTime (2 ^ 2 * m + 1353) 2 :=
  stoppingTime_of_classCertificate certificate_1353 m

/-- Checked base and every prefix for input 1355. -/
theorem certificate_1355 : classCertificateB 5 1355 = true := by
  decide

/-- The same exact first-descent time holds on an infinite dyadic ray. -/
theorem ray_1355 (m : Nat) : stoppingTime (2 ^ 5 * m + 1355) 5 :=
  stoppingTime_of_classCertificate certificate_1355 m

/-- Checked base and every prefix for input 1357. -/
theorem certificate_1357 : classCertificateB 2 1357 = true := by
  decide

/-- The same exact first-descent time holds on an infinite dyadic ray. -/
theorem ray_1357 (m : Nat) : stoppingTime (2 ^ 2 * m + 1357) 2 :=
  stoppingTime_of_classCertificate certificate_1357 m

/-- Checked base and every prefix for input 1359. -/
theorem certificate_1359 : classCertificateB 8 1359 = true := by
  decide

/-- The same exact first-descent time holds on an infinite dyadic ray. -/
theorem ray_1359 (m : Nat) : stoppingTime (2 ^ 8 * m + 1359) 8 :=
  stoppingTime_of_classCertificate certificate_1359 m

/-- Checked base and every prefix for input 1361. -/
theorem certificate_1361 : classCertificateB 2 1361 = true := by
  decide

/-- The same exact first-descent time holds on an infinite dyadic ray. -/
theorem ray_1361 (m : Nat) : stoppingTime (2 ^ 2 * m + 1361) 2 :=
  stoppingTime_of_classCertificate certificate_1361 m

/-- Checked base and every prefix for input 1363. -/
theorem certificate_1363 : classCertificateB 4 1363 = true := by
  decide

/-- The same exact first-descent time holds on an infinite dyadic ray. -/
theorem ray_1363 (m : Nat) : stoppingTime (2 ^ 4 * m + 1363) 4 :=
  stoppingTime_of_classCertificate certificate_1363 m

/-- Checked base and every prefix for input 1365. -/
theorem certificate_1365 : classCertificateB 2 1365 = true := by
  decide

/-- The same exact first-descent time holds on an infinite dyadic ray. -/
theorem ray_1365 (m : Nat) : stoppingTime (2 ^ 2 * m + 1365) 2 :=
  stoppingTime_of_classCertificate certificate_1365 m

/-- Checked base and every prefix for input 1367. -/
theorem certificate_1367 : classCertificateB 5 1367 = true := by
  decide

/-- The same exact first-descent time holds on an infinite dyadic ray. -/
theorem ray_1367 (m : Nat) : stoppingTime (2 ^ 5 * m + 1367) 5 :=
  stoppingTime_of_classCertificate certificate_1367 m

/-- Checked base and every prefix for input 1369. -/
theorem certificate_1369 : classCertificateB 2 1369 = true := by
  decide

/-- The same exact first-descent time holds on an infinite dyadic ray. -/
theorem ray_1369 (m : Nat) : stoppingTime (2 ^ 2 * m + 1369) 2 :=
  stoppingTime_of_classCertificate certificate_1369 m

/-- Checked base and every prefix for input 1371. -/
theorem certificate_1371 : classCertificateB 10 1371 = true := by
  decide

/-- The same exact first-descent time holds on an infinite dyadic ray. -/
theorem ray_1371 (m : Nat) : stoppingTime (2 ^ 10 * m + 1371) 10 :=
  stoppingTime_of_classCertificate certificate_1371 m

/-- Checked base and every prefix for input 1373. -/
theorem certificate_1373 : classCertificateB 2 1373 = true := by
  decide

/-- The same exact first-descent time holds on an infinite dyadic ray. -/
theorem ray_1373 (m : Nat) : stoppingTime (2 ^ 2 * m + 1373) 2 :=
  stoppingTime_of_classCertificate certificate_1373 m

/-- Checked base and every prefix for input 1375. -/
theorem certificate_1375 : classCertificateB 8 1375 = true := by
  decide

/-- The same exact first-descent time holds on an infinite dyadic ray. -/
theorem ray_1375 (m : Nat) : stoppingTime (2 ^ 8 * m + 1375) 8 :=
  stoppingTime_of_classCertificate certificate_1375 m

/-- Checked base and every prefix for input 1377. -/
theorem certificate_1377 : classCertificateB 2 1377 = true := by
  decide

/-- The same exact first-descent time holds on an infinite dyadic ray. -/
theorem ray_1377 (m : Nat) : stoppingTime (2 ^ 2 * m + 1377) 2 :=
  stoppingTime_of_classCertificate certificate_1377 m

/-- Checked base and every prefix for input 1379. -/
theorem certificate_1379 : classCertificateB 4 1379 = true := by
  decide

/-- The same exact first-descent time holds on an infinite dyadic ray. -/
theorem ray_1379 (m : Nat) : stoppingTime (2 ^ 4 * m + 1379) 4 :=
  stoppingTime_of_classCertificate certificate_1379 m

/-- Checked base and every prefix for input 1381. -/
theorem certificate_1381 : classCertificateB 2 1381 = true := by
  decide

/-- The same exact first-descent time holds on an infinite dyadic ray. -/
theorem ray_1381 (m : Nat) : stoppingTime (2 ^ 2 * m + 1381) 2 :=
  stoppingTime_of_classCertificate certificate_1381 m

/-- Checked base and every prefix for input 1383. -/
theorem certificate_1383 : classCertificateB 39 1383 = true := by
  decide

/-- The same exact first-descent time holds on an infinite dyadic ray. -/
theorem ray_1383 (m : Nat) : stoppingTime (2 ^ 39 * m + 1383) 39 :=
  stoppingTime_of_classCertificate certificate_1383 m

/-- Checked base and every prefix for input 1385. -/
theorem certificate_1385 : classCertificateB 2 1385 = true := by
  decide

/-- The same exact first-descent time holds on an infinite dyadic ray. -/
theorem ray_1385 (m : Nat) : stoppingTime (2 ^ 2 * m + 1385) 2 :=
  stoppingTime_of_classCertificate certificate_1385 m

/-- Checked base and every prefix for input 1387. -/
theorem certificate_1387 : classCertificateB 5 1387 = true := by
  decide

/-- The same exact first-descent time holds on an infinite dyadic ray. -/
theorem ray_1387 (m : Nat) : stoppingTime (2 ^ 5 * m + 1387) 5 :=
  stoppingTime_of_classCertificate certificate_1387 m

/-- Checked base and every prefix for input 1389. -/
theorem certificate_1389 : classCertificateB 2 1389 = true := by
  decide

/-- The same exact first-descent time holds on an infinite dyadic ray. -/
theorem ray_1389 (m : Nat) : stoppingTime (2 ^ 2 * m + 1389) 2 :=
  stoppingTime_of_classCertificate certificate_1389 m

/-- Checked base and every prefix for input 1391. -/
theorem certificate_1391 : classCertificateB 10 1391 = true := by
  decide

/-- The same exact first-descent time holds on an infinite dyadic ray. -/
theorem ray_1391 (m : Nat) : stoppingTime (2 ^ 10 * m + 1391) 10 :=
  stoppingTime_of_classCertificate certificate_1391 m

/-- Checked base and every prefix for input 1393. -/
theorem certificate_1393 : classCertificateB 2 1393 = true := by
  decide

/-- The same exact first-descent time holds on an infinite dyadic ray. -/
theorem ray_1393 (m : Nat) : stoppingTime (2 ^ 2 * m + 1393) 2 :=
  stoppingTime_of_classCertificate certificate_1393 m

/-- Checked base and every prefix for input 1395. -/
theorem certificate_1395 : classCertificateB 4 1395 = true := by
  decide

/-- The same exact first-descent time holds on an infinite dyadic ray. -/
theorem ray_1395 (m : Nat) : stoppingTime (2 ^ 4 * m + 1395) 4 :=
  stoppingTime_of_classCertificate certificate_1395 m

/-- Checked base and every prefix for input 1397. -/
theorem certificate_1397 : classCertificateB 2 1397 = true := by
  decide

/-- The same exact first-descent time holds on an infinite dyadic ray. -/
theorem ray_1397 (m : Nat) : stoppingTime (2 ^ 2 * m + 1397) 2 :=
  stoppingTime_of_classCertificate certificate_1397 m

/-- Checked base and every prefix for input 1399. -/
theorem certificate_1399 : classCertificateB 5 1399 = true := by
  decide

/-- The same exact first-descent time holds on an infinite dyadic ray. -/
theorem ray_1399 (m : Nat) : stoppingTime (2 ^ 5 * m + 1399) 5 :=
  stoppingTime_of_classCertificate certificate_1399 m

/-- Checked base and every prefix for input 1401. -/
theorem certificate_1401 : classCertificateB 2 1401 = true := by
  decide

/-- The same exact first-descent time holds on an infinite dyadic ray. -/
theorem ray_1401 (m : Nat) : stoppingTime (2 ^ 2 * m + 1401) 2 :=
  stoppingTime_of_classCertificate certificate_1401 m

/-- Checked base and every prefix for input 1403. -/
theorem certificate_1403 : classCertificateB 8 1403 = true := by
  decide

/-- The same exact first-descent time holds on an infinite dyadic ray. -/
theorem ray_1403 (m : Nat) : stoppingTime (2 ^ 8 * m + 1403) 8 :=
  stoppingTime_of_classCertificate certificate_1403 m

/-- Checked base and every prefix for input 1405. -/
theorem certificate_1405 : classCertificateB 2 1405 = true := by
  decide

/-- The same exact first-descent time holds on an infinite dyadic ray. -/
theorem ray_1405 (m : Nat) : stoppingTime (2 ^ 2 * m + 1405) 2 :=
  stoppingTime_of_classCertificate certificate_1405 m

/-- Checked base and every prefix for input 1407. -/
theorem certificate_1407 : classCertificateB 81 1407 = true := by
  decide

/-- The same exact first-descent time holds on an infinite dyadic ray. -/
theorem ray_1407 (m : Nat) : stoppingTime (2 ^ 81 * m + 1407) 81 :=
  stoppingTime_of_classCertificate certificate_1407 m

/-- Exhaustive coverage of the odd inputs in this batch, with no gaps. -/
theorem coverage : CertifiedRange 1341 1409 := by
  intro n hlo hhi hodd
  have hn : n = 1341 ∨ n = 1343 ∨ n = 1345 ∨ n = 1347 ∨ n = 1349 ∨ n = 1351 ∨ n = 1353 ∨ n = 1355 ∨ n = 1357 ∨ n = 1359 ∨ n = 1361 ∨ n = 1363 ∨ n = 1365 ∨ n = 1367 ∨ n = 1369 ∨ n = 1371 ∨ n = 1373 ∨ n = 1375 ∨ n = 1377 ∨ n = 1379 ∨ n = 1381 ∨ n = 1383 ∨ n = 1385 ∨ n = 1387 ∨ n = 1389 ∨ n = 1391 ∨ n = 1393 ∨ n = 1395 ∨ n = 1397 ∨ n = 1399 ∨ n = 1401 ∨ n = 1403 ∨ n = 1405 ∨ n = 1407 := by omega
  rcases hn with h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h
  · subst n
    exact ⟨2, witness_of_certificate certificate_1341⟩
  · subst n
    exact ⟨23, witness_of_certificate certificate_1343⟩
  · subst n
    exact ⟨2, witness_of_certificate certificate_1345⟩
  · subst n
    exact ⟨4, witness_of_certificate certificate_1347⟩
  · subst n
    exact ⟨2, witness_of_certificate certificate_1349⟩
  · subst n
    exact ⟨16, witness_of_certificate certificate_1351⟩
  · subst n
    exact ⟨2, witness_of_certificate certificate_1353⟩
  · subst n
    exact ⟨5, witness_of_certificate certificate_1355⟩
  · subst n
    exact ⟨2, witness_of_certificate certificate_1357⟩
  · subst n
    exact ⟨8, witness_of_certificate certificate_1359⟩
  · subst n
    exact ⟨2, witness_of_certificate certificate_1361⟩
  · subst n
    exact ⟨4, witness_of_certificate certificate_1363⟩
  · subst n
    exact ⟨2, witness_of_certificate certificate_1365⟩
  · subst n
    exact ⟨5, witness_of_certificate certificate_1367⟩
  · subst n
    exact ⟨2, witness_of_certificate certificate_1369⟩
  · subst n
    exact ⟨10, witness_of_certificate certificate_1371⟩
  · subst n
    exact ⟨2, witness_of_certificate certificate_1373⟩
  · subst n
    exact ⟨8, witness_of_certificate certificate_1375⟩
  · subst n
    exact ⟨2, witness_of_certificate certificate_1377⟩
  · subst n
    exact ⟨4, witness_of_certificate certificate_1379⟩
  · subst n
    exact ⟨2, witness_of_certificate certificate_1381⟩
  · subst n
    exact ⟨39, witness_of_certificate certificate_1383⟩
  · subst n
    exact ⟨2, witness_of_certificate certificate_1385⟩
  · subst n
    exact ⟨5, witness_of_certificate certificate_1387⟩
  · subst n
    exact ⟨2, witness_of_certificate certificate_1389⟩
  · subst n
    exact ⟨10, witness_of_certificate certificate_1391⟩
  · subst n
    exact ⟨2, witness_of_certificate certificate_1393⟩
  · subst n
    exact ⟨4, witness_of_certificate certificate_1395⟩
  · subst n
    exact ⟨2, witness_of_certificate certificate_1397⟩
  · subst n
    exact ⟨5, witness_of_certificate certificate_1399⟩
  · subst n
    exact ⟨2, witness_of_certificate certificate_1401⟩
  · subst n
    exact ⟨8, witness_of_certificate certificate_1403⟩
  · subst n
    exact ⟨2, witness_of_certificate certificate_1405⟩
  · subst n
    exact ⟨81, witness_of_certificate certificate_1407⟩

end Collatz.Research.CoefficientDescent.Batch021
