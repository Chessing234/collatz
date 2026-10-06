import Collatz.Research.CoefficientDescent.Basic

namespace Collatz.Research.CoefficientDescent.Batch095

open FirstDescentClass

set_option maxRecDepth 20000
set_option maxHeartbeats 0

/-- Checked base and every prefix for input 6299. -/
theorem certificate_6299 : classCertificateB 12 6299 = true := by
  decide

/-- The same exact first-descent time holds on an infinite dyadic ray. -/
theorem ray_6299 (m : Nat) : stoppingTime (2 ^ 12 * m + 6299) 12 :=
  stoppingTime_of_classCertificate certificate_6299 m

/-- Checked base and every prefix for input 6301. -/
theorem certificate_6301 : classCertificateB 2 6301 = true := by
  decide

/-- The same exact first-descent time holds on an infinite dyadic ray. -/
theorem ray_6301 (m : Nat) : stoppingTime (2 ^ 2 * m + 6301) 2 :=
  stoppingTime_of_classCertificate certificate_6301 m

/-- Checked base and every prefix for input 6303. -/
theorem certificate_6303 : classCertificateB 24 6303 = true := by
  decide

/-- The same exact first-descent time holds on an infinite dyadic ray. -/
theorem ray_6303 (m : Nat) : stoppingTime (2 ^ 24 * m + 6303) 24 :=
  stoppingTime_of_classCertificate certificate_6303 m

/-- Checked base and every prefix for input 6305. -/
theorem certificate_6305 : classCertificateB 2 6305 = true := by
  decide

/-- The same exact first-descent time holds on an infinite dyadic ray. -/
theorem ray_6305 (m : Nat) : stoppingTime (2 ^ 2 * m + 6305) 2 :=
  stoppingTime_of_classCertificate certificate_6305 m

/-- Checked base and every prefix for input 6307. -/
theorem certificate_6307 : classCertificateB 4 6307 = true := by
  decide

/-- The same exact first-descent time holds on an infinite dyadic ray. -/
theorem ray_6307 (m : Nat) : stoppingTime (2 ^ 4 * m + 6307) 4 :=
  stoppingTime_of_classCertificate certificate_6307 m

/-- Checked base and every prefix for input 6309. -/
theorem certificate_6309 : classCertificateB 2 6309 = true := by
  decide

/-- The same exact first-descent time holds on an infinite dyadic ray. -/
theorem ray_6309 (m : Nat) : stoppingTime (2 ^ 2 * m + 6309) 2 :=
  stoppingTime_of_classCertificate certificate_6309 m

/-- Checked base and every prefix for input 6311. -/
theorem certificate_6311 : classCertificateB 34 6311 = true := by
  decide

/-- The same exact first-descent time holds on an infinite dyadic ray. -/
theorem ray_6311 (m : Nat) : stoppingTime (2 ^ 34 * m + 6311) 34 :=
  stoppingTime_of_classCertificate certificate_6311 m

/-- Checked base and every prefix for input 6313. -/
theorem certificate_6313 : classCertificateB 2 6313 = true := by
  decide

/-- The same exact first-descent time holds on an infinite dyadic ray. -/
theorem ray_6313 (m : Nat) : stoppingTime (2 ^ 2 * m + 6313) 2 :=
  stoppingTime_of_classCertificate certificate_6313 m

/-- Checked base and every prefix for input 6315. -/
theorem certificate_6315 : classCertificateB 5 6315 = true := by
  decide

/-- The same exact first-descent time holds on an infinite dyadic ray. -/
theorem ray_6315 (m : Nat) : stoppingTime (2 ^ 5 * m + 6315) 5 :=
  stoppingTime_of_classCertificate certificate_6315 m

/-- Checked base and every prefix for input 6317. -/
theorem certificate_6317 : classCertificateB 2 6317 = true := by
  decide

/-- The same exact first-descent time holds on an infinite dyadic ray. -/
theorem ray_6317 (m : Nat) : stoppingTime (2 ^ 2 * m + 6317) 2 :=
  stoppingTime_of_classCertificate certificate_6317 m

/-- Checked base and every prefix for input 6319. -/
theorem certificate_6319 : classCertificateB 8 6319 = true := by
  decide

/-- The same exact first-descent time holds on an infinite dyadic ray. -/
theorem ray_6319 (m : Nat) : stoppingTime (2 ^ 8 * m + 6319) 8 :=
  stoppingTime_of_classCertificate certificate_6319 m

/-- Checked base and every prefix for input 6321. -/
theorem certificate_6321 : classCertificateB 2 6321 = true := by
  decide

/-- The same exact first-descent time holds on an infinite dyadic ray. -/
theorem ray_6321 (m : Nat) : stoppingTime (2 ^ 2 * m + 6321) 2 :=
  stoppingTime_of_classCertificate certificate_6321 m

/-- Checked base and every prefix for input 6323. -/
theorem certificate_6323 : classCertificateB 4 6323 = true := by
  decide

/-- The same exact first-descent time holds on an infinite dyadic ray. -/
theorem ray_6323 (m : Nat) : stoppingTime (2 ^ 4 * m + 6323) 4 :=
  stoppingTime_of_classCertificate certificate_6323 m

/-- Checked base and every prefix for input 6325. -/
theorem certificate_6325 : classCertificateB 2 6325 = true := by
  decide

/-- The same exact first-descent time holds on an infinite dyadic ray. -/
theorem ray_6325 (m : Nat) : stoppingTime (2 ^ 2 * m + 6325) 2 :=
  stoppingTime_of_classCertificate certificate_6325 m

/-- Checked base and every prefix for input 6327. -/
theorem certificate_6327 : classCertificateB 5 6327 = true := by
  decide

/-- The same exact first-descent time holds on an infinite dyadic ray. -/
theorem ray_6327 (m : Nat) : stoppingTime (2 ^ 5 * m + 6327) 5 :=
  stoppingTime_of_classCertificate certificate_6327 m

/-- Checked base and every prefix for input 6329. -/
theorem certificate_6329 : classCertificateB 2 6329 = true := by
  decide

/-- The same exact first-descent time holds on an infinite dyadic ray. -/
theorem ray_6329 (m : Nat) : stoppingTime (2 ^ 2 * m + 6329) 2 :=
  stoppingTime_of_classCertificate certificate_6329 m

/-- Checked base and every prefix for input 6331. -/
theorem certificate_6331 : classCertificateB 7 6331 = true := by
  decide

/-- The same exact first-descent time holds on an infinite dyadic ray. -/
theorem ray_6331 (m : Nat) : stoppingTime (2 ^ 7 * m + 6331) 7 :=
  stoppingTime_of_classCertificate certificate_6331 m

/-- Checked base and every prefix for input 6333. -/
theorem certificate_6333 : classCertificateB 2 6333 = true := by
  decide

/-- The same exact first-descent time holds on an infinite dyadic ray. -/
theorem ray_6333 (m : Nat) : stoppingTime (2 ^ 2 * m + 6333) 2 :=
  stoppingTime_of_classCertificate certificate_6333 m

/-- Checked base and every prefix for input 6335. -/
theorem certificate_6335 : classCertificateB 12 6335 = true := by
  decide

/-- The same exact first-descent time holds on an infinite dyadic ray. -/
theorem ray_6335 (m : Nat) : stoppingTime (2 ^ 12 * m + 6335) 12 :=
  stoppingTime_of_classCertificate certificate_6335 m

/-- Checked base and every prefix for input 6337. -/
theorem certificate_6337 : classCertificateB 2 6337 = true := by
  decide

/-- The same exact first-descent time holds on an infinite dyadic ray. -/
theorem ray_6337 (m : Nat) : stoppingTime (2 ^ 2 * m + 6337) 2 :=
  stoppingTime_of_classCertificate certificate_6337 m

/-- Checked base and every prefix for input 6339. -/
theorem certificate_6339 : classCertificateB 4 6339 = true := by
  decide

/-- The same exact first-descent time holds on an infinite dyadic ray. -/
theorem ray_6339 (m : Nat) : stoppingTime (2 ^ 4 * m + 6339) 4 :=
  stoppingTime_of_classCertificate certificate_6339 m

/-- Checked base and every prefix for input 6341. -/
theorem certificate_6341 : classCertificateB 2 6341 = true := by
  decide

/-- The same exact first-descent time holds on an infinite dyadic ray. -/
theorem ray_6341 (m : Nat) : stoppingTime (2 ^ 2 * m + 6341) 2 :=
  stoppingTime_of_classCertificate certificate_6341 m

/-- Checked base and every prefix for input 6343. -/
theorem certificate_6343 : classCertificateB 8 6343 = true := by
  decide

/-- The same exact first-descent time holds on an infinite dyadic ray. -/
theorem ray_6343 (m : Nat) : stoppingTime (2 ^ 8 * m + 6343) 8 :=
  stoppingTime_of_classCertificate certificate_6343 m

/-- Checked base and every prefix for input 6345. -/
theorem certificate_6345 : classCertificateB 2 6345 = true := by
  decide

/-- The same exact first-descent time holds on an infinite dyadic ray. -/
theorem ray_6345 (m : Nat) : stoppingTime (2 ^ 2 * m + 6345) 2 :=
  stoppingTime_of_classCertificate certificate_6345 m

/-- Checked base and every prefix for input 6347. -/
theorem certificate_6347 : classCertificateB 5 6347 = true := by
  decide

/-- The same exact first-descent time holds on an infinite dyadic ray. -/
theorem ray_6347 (m : Nat) : stoppingTime (2 ^ 5 * m + 6347) 5 :=
  stoppingTime_of_classCertificate certificate_6347 m

/-- Checked base and every prefix for input 6349. -/
theorem certificate_6349 : classCertificateB 2 6349 = true := by
  decide

/-- The same exact first-descent time holds on an infinite dyadic ray. -/
theorem ray_6349 (m : Nat) : stoppingTime (2 ^ 2 * m + 6349) 2 :=
  stoppingTime_of_classCertificate certificate_6349 m

/-- Checked base and every prefix for input 6351. -/
theorem certificate_6351 : classCertificateB 26 6351 = true := by
  decide

/-- The same exact first-descent time holds on an infinite dyadic ray. -/
theorem ray_6351 (m : Nat) : stoppingTime (2 ^ 26 * m + 6351) 26 :=
  stoppingTime_of_classCertificate certificate_6351 m

/-- Checked base and every prefix for input 6353. -/
theorem certificate_6353 : classCertificateB 2 6353 = true := by
  decide

/-- The same exact first-descent time holds on an infinite dyadic ray. -/
theorem ray_6353 (m : Nat) : stoppingTime (2 ^ 2 * m + 6353) 2 :=
  stoppingTime_of_classCertificate certificate_6353 m

/-- Checked base and every prefix for input 6355. -/
theorem certificate_6355 : classCertificateB 4 6355 = true := by
  decide

/-- The same exact first-descent time holds on an infinite dyadic ray. -/
theorem ray_6355 (m : Nat) : stoppingTime (2 ^ 4 * m + 6355) 4 :=
  stoppingTime_of_classCertificate certificate_6355 m

/-- Checked base and every prefix for input 6357. -/
theorem certificate_6357 : classCertificateB 2 6357 = true := by
  decide

/-- The same exact first-descent time holds on an infinite dyadic ray. -/
theorem ray_6357 (m : Nat) : stoppingTime (2 ^ 2 * m + 6357) 2 :=
  stoppingTime_of_classCertificate certificate_6357 m

/-- Checked base and every prefix for input 6359. -/
theorem certificate_6359 : classCertificateB 5 6359 = true := by
  decide

/-- The same exact first-descent time holds on an infinite dyadic ray. -/
theorem ray_6359 (m : Nat) : stoppingTime (2 ^ 5 * m + 6359) 5 :=
  stoppingTime_of_classCertificate certificate_6359 m

/-- Checked base and every prefix for input 6361. -/
theorem certificate_6361 : classCertificateB 2 6361 = true := by
  decide

/-- The same exact first-descent time holds on an infinite dyadic ray. -/
theorem ray_6361 (m : Nat) : stoppingTime (2 ^ 2 * m + 6361) 2 :=
  stoppingTime_of_classCertificate certificate_6361 m

/-- Checked base and every prefix for input 6363. -/
theorem certificate_6363 : classCertificateB 8 6363 = true := by
  decide

/-- The same exact first-descent time holds on an infinite dyadic ray. -/
theorem ray_6363 (m : Nat) : stoppingTime (2 ^ 8 * m + 6363) 8 :=
  stoppingTime_of_classCertificate certificate_6363 m

/-- Exhaustive coverage of the odd inputs in this batch, with no gaps. -/
theorem coverage : CertifiedRange 6299 6365 := by
  intro n hlo hhi hodd
  have hn : n = 6299 ∨ n = 6301 ∨ n = 6303 ∨ n = 6305 ∨ n = 6307 ∨ n = 6309 ∨ n = 6311 ∨ n = 6313 ∨ n = 6315 ∨ n = 6317 ∨ n = 6319 ∨ n = 6321 ∨ n = 6323 ∨ n = 6325 ∨ n = 6327 ∨ n = 6329 ∨ n = 6331 ∨ n = 6333 ∨ n = 6335 ∨ n = 6337 ∨ n = 6339 ∨ n = 6341 ∨ n = 6343 ∨ n = 6345 ∨ n = 6347 ∨ n = 6349 ∨ n = 6351 ∨ n = 6353 ∨ n = 6355 ∨ n = 6357 ∨ n = 6359 ∨ n = 6361 ∨ n = 6363 := by omega
  rcases hn with h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h
  · subst n
    exact ⟨12, witness_of_certificate certificate_6299⟩
  · subst n
    exact ⟨2, witness_of_certificate certificate_6301⟩
  · subst n
    exact ⟨24, witness_of_certificate certificate_6303⟩
  · subst n
    exact ⟨2, witness_of_certificate certificate_6305⟩
  · subst n
    exact ⟨4, witness_of_certificate certificate_6307⟩
  · subst n
    exact ⟨2, witness_of_certificate certificate_6309⟩
  · subst n
    exact ⟨34, witness_of_certificate certificate_6311⟩
  · subst n
    exact ⟨2, witness_of_certificate certificate_6313⟩
  · subst n
    exact ⟨5, witness_of_certificate certificate_6315⟩
  · subst n
    exact ⟨2, witness_of_certificate certificate_6317⟩
  · subst n
    exact ⟨8, witness_of_certificate certificate_6319⟩
  · subst n
    exact ⟨2, witness_of_certificate certificate_6321⟩
  · subst n
    exact ⟨4, witness_of_certificate certificate_6323⟩
  · subst n
    exact ⟨2, witness_of_certificate certificate_6325⟩
  · subst n
    exact ⟨5, witness_of_certificate certificate_6327⟩
  · subst n
    exact ⟨2, witness_of_certificate certificate_6329⟩
  · subst n
    exact ⟨7, witness_of_certificate certificate_6331⟩
  · subst n
    exact ⟨2, witness_of_certificate certificate_6333⟩
  · subst n
    exact ⟨12, witness_of_certificate certificate_6335⟩
  · subst n
    exact ⟨2, witness_of_certificate certificate_6337⟩
  · subst n
    exact ⟨4, witness_of_certificate certificate_6339⟩
  · subst n
    exact ⟨2, witness_of_certificate certificate_6341⟩
  · subst n
    exact ⟨8, witness_of_certificate certificate_6343⟩
  · subst n
    exact ⟨2, witness_of_certificate certificate_6345⟩
  · subst n
    exact ⟨5, witness_of_certificate certificate_6347⟩
  · subst n
    exact ⟨2, witness_of_certificate certificate_6349⟩
  · subst n
    exact ⟨26, witness_of_certificate certificate_6351⟩
  · subst n
    exact ⟨2, witness_of_certificate certificate_6353⟩
  · subst n
    exact ⟨4, witness_of_certificate certificate_6355⟩
  · subst n
    exact ⟨2, witness_of_certificate certificate_6357⟩
  · subst n
    exact ⟨5, witness_of_certificate certificate_6359⟩
  · subst n
    exact ⟨2, witness_of_certificate certificate_6361⟩
  · subst n
    exact ⟨8, witness_of_certificate certificate_6363⟩

end Collatz.Research.CoefficientDescent.Batch095
