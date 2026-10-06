import Collatz.Research.CoefficientDescent.Basic

namespace Collatz.Research.CoefficientDescent.Batch080

open FirstDescentClass

set_option maxRecDepth 20000
set_option maxHeartbeats 0

/-- Checked base and every prefix for input 5293. -/
theorem certificate_5293 : classCertificateB 2 5293 = true := by
  decide

/-- The same exact first-descent time holds on an infinite dyadic ray. -/
theorem ray_5293 (m : Nat) : stoppingTime (2 ^ 2 * m + 5293) 2 :=
  stoppingTime_of_classCertificate certificate_5293 m

/-- Checked base and every prefix for input 5295. -/
theorem certificate_5295 : classCertificateB 8 5295 = true := by
  decide

/-- The same exact first-descent time holds on an infinite dyadic ray. -/
theorem ray_5295 (m : Nat) : stoppingTime (2 ^ 8 * m + 5295) 8 :=
  stoppingTime_of_classCertificate certificate_5295 m

/-- Checked base and every prefix for input 5297. -/
theorem certificate_5297 : classCertificateB 2 5297 = true := by
  decide

/-- The same exact first-descent time holds on an infinite dyadic ray. -/
theorem ray_5297 (m : Nat) : stoppingTime (2 ^ 2 * m + 5297) 2 :=
  stoppingTime_of_classCertificate certificate_5297 m

/-- Checked base and every prefix for input 5299. -/
theorem certificate_5299 : classCertificateB 4 5299 = true := by
  decide

/-- The same exact first-descent time holds on an infinite dyadic ray. -/
theorem ray_5299 (m : Nat) : stoppingTime (2 ^ 4 * m + 5299) 4 :=
  stoppingTime_of_classCertificate certificate_5299 m

/-- Checked base and every prefix for input 5301. -/
theorem certificate_5301 : classCertificateB 2 5301 = true := by
  decide

/-- The same exact first-descent time holds on an infinite dyadic ray. -/
theorem ray_5301 (m : Nat) : stoppingTime (2 ^ 2 * m + 5301) 2 :=
  stoppingTime_of_classCertificate certificate_5301 m

/-- Checked base and every prefix for input 5303. -/
theorem certificate_5303 : classCertificateB 5 5303 = true := by
  decide

/-- The same exact first-descent time holds on an infinite dyadic ray. -/
theorem ray_5303 (m : Nat) : stoppingTime (2 ^ 5 * m + 5303) 5 :=
  stoppingTime_of_classCertificate certificate_5303 m

/-- Checked base and every prefix for input 5305. -/
theorem certificate_5305 : classCertificateB 2 5305 = true := by
  decide

/-- The same exact first-descent time holds on an infinite dyadic ray. -/
theorem ray_5305 (m : Nat) : stoppingTime (2 ^ 2 * m + 5305) 2 :=
  stoppingTime_of_classCertificate certificate_5305 m

/-- Checked base and every prefix for input 5307. -/
theorem certificate_5307 : classCertificateB 7 5307 = true := by
  decide

/-- The same exact first-descent time holds on an infinite dyadic ray. -/
theorem ray_5307 (m : Nat) : stoppingTime (2 ^ 7 * m + 5307) 7 :=
  stoppingTime_of_classCertificate certificate_5307 m

/-- Checked base and every prefix for input 5309. -/
theorem certificate_5309 : classCertificateB 2 5309 = true := by
  decide

/-- The same exact first-descent time holds on an infinite dyadic ray. -/
theorem ray_5309 (m : Nat) : stoppingTime (2 ^ 2 * m + 5309) 2 :=
  stoppingTime_of_classCertificate certificate_5309 m

/-- Checked base and every prefix for input 5311. -/
theorem certificate_5311 : classCertificateB 15 5311 = true := by
  decide

/-- The same exact first-descent time holds on an infinite dyadic ray. -/
theorem ray_5311 (m : Nat) : stoppingTime (2 ^ 15 * m + 5311) 15 :=
  stoppingTime_of_classCertificate certificate_5311 m

/-- Checked base and every prefix for input 5313. -/
theorem certificate_5313 : classCertificateB 2 5313 = true := by
  decide

/-- The same exact first-descent time holds on an infinite dyadic ray. -/
theorem ray_5313 (m : Nat) : stoppingTime (2 ^ 2 * m + 5313) 2 :=
  stoppingTime_of_classCertificate certificate_5313 m

/-- Checked base and every prefix for input 5315. -/
theorem certificate_5315 : classCertificateB 4 5315 = true := by
  decide

/-- The same exact first-descent time holds on an infinite dyadic ray. -/
theorem ray_5315 (m : Nat) : stoppingTime (2 ^ 4 * m + 5315) 4 :=
  stoppingTime_of_classCertificate certificate_5315 m

/-- Checked base and every prefix for input 5317. -/
theorem certificate_5317 : classCertificateB 2 5317 = true := by
  decide

/-- The same exact first-descent time holds on an infinite dyadic ray. -/
theorem ray_5317 (m : Nat) : stoppingTime (2 ^ 2 * m + 5317) 2 :=
  stoppingTime_of_classCertificate certificate_5317 m

/-- Checked base and every prefix for input 5319. -/
theorem certificate_5319 : classCertificateB 8 5319 = true := by
  decide

/-- The same exact first-descent time holds on an infinite dyadic ray. -/
theorem ray_5319 (m : Nat) : stoppingTime (2 ^ 8 * m + 5319) 8 :=
  stoppingTime_of_classCertificate certificate_5319 m

/-- Checked base and every prefix for input 5321. -/
theorem certificate_5321 : classCertificateB 2 5321 = true := by
  decide

/-- The same exact first-descent time holds on an infinite dyadic ray. -/
theorem ray_5321 (m : Nat) : stoppingTime (2 ^ 2 * m + 5321) 2 :=
  stoppingTime_of_classCertificate certificate_5321 m

/-- Checked base and every prefix for input 5323. -/
theorem certificate_5323 : classCertificateB 5 5323 = true := by
  decide

/-- The same exact first-descent time holds on an infinite dyadic ray. -/
theorem ray_5323 (m : Nat) : stoppingTime (2 ^ 5 * m + 5323) 5 :=
  stoppingTime_of_classCertificate certificate_5323 m

/-- Checked base and every prefix for input 5325. -/
theorem certificate_5325 : classCertificateB 2 5325 = true := by
  decide

/-- The same exact first-descent time holds on an infinite dyadic ray. -/
theorem ray_5325 (m : Nat) : stoppingTime (2 ^ 2 * m + 5325) 2 :=
  stoppingTime_of_classCertificate certificate_5325 m

/-- Checked base and every prefix for input 5327. -/
theorem certificate_5327 : classCertificateB 12 5327 = true := by
  decide

/-- The same exact first-descent time holds on an infinite dyadic ray. -/
theorem ray_5327 (m : Nat) : stoppingTime (2 ^ 12 * m + 5327) 12 :=
  stoppingTime_of_classCertificate certificate_5327 m

/-- Checked base and every prefix for input 5329. -/
theorem certificate_5329 : classCertificateB 2 5329 = true := by
  decide

/-- The same exact first-descent time holds on an infinite dyadic ray. -/
theorem ray_5329 (m : Nat) : stoppingTime (2 ^ 2 * m + 5329) 2 :=
  stoppingTime_of_classCertificate certificate_5329 m

/-- Checked base and every prefix for input 5331. -/
theorem certificate_5331 : classCertificateB 4 5331 = true := by
  decide

/-- The same exact first-descent time holds on an infinite dyadic ray. -/
theorem ray_5331 (m : Nat) : stoppingTime (2 ^ 4 * m + 5331) 4 :=
  stoppingTime_of_classCertificate certificate_5331 m

/-- Checked base and every prefix for input 5333. -/
theorem certificate_5333 : classCertificateB 2 5333 = true := by
  decide

/-- The same exact first-descent time holds on an infinite dyadic ray. -/
theorem ray_5333 (m : Nat) : stoppingTime (2 ^ 2 * m + 5333) 2 :=
  stoppingTime_of_classCertificate certificate_5333 m

/-- Checked base and every prefix for input 5335. -/
theorem certificate_5335 : classCertificateB 5 5335 = true := by
  decide

/-- The same exact first-descent time holds on an infinite dyadic ray. -/
theorem ray_5335 (m : Nat) : stoppingTime (2 ^ 5 * m + 5335) 5 :=
  stoppingTime_of_classCertificate certificate_5335 m

/-- Checked base and every prefix for input 5337. -/
theorem certificate_5337 : classCertificateB 2 5337 = true := by
  decide

/-- The same exact first-descent time holds on an infinite dyadic ray. -/
theorem ray_5337 (m : Nat) : stoppingTime (2 ^ 2 * m + 5337) 2 :=
  stoppingTime_of_classCertificate certificate_5337 m

/-- Checked base and every prefix for input 5339. -/
theorem certificate_5339 : classCertificateB 8 5339 = true := by
  decide

/-- The same exact first-descent time holds on an infinite dyadic ray. -/
theorem ray_5339 (m : Nat) : stoppingTime (2 ^ 8 * m + 5339) 8 :=
  stoppingTime_of_classCertificate certificate_5339 m

/-- Checked base and every prefix for input 5341. -/
theorem certificate_5341 : classCertificateB 2 5341 = true := by
  decide

/-- The same exact first-descent time holds on an infinite dyadic ray. -/
theorem ray_5341 (m : Nat) : stoppingTime (2 ^ 2 * m + 5341) 2 :=
  stoppingTime_of_classCertificate certificate_5341 m

/-- Checked base and every prefix for input 5343. -/
theorem certificate_5343 : classCertificateB 16 5343 = true := by
  decide

/-- The same exact first-descent time holds on an infinite dyadic ray. -/
theorem ray_5343 (m : Nat) : stoppingTime (2 ^ 16 * m + 5343) 16 :=
  stoppingTime_of_classCertificate certificate_5343 m

/-- Checked base and every prefix for input 5345. -/
theorem certificate_5345 : classCertificateB 2 5345 = true := by
  decide

/-- The same exact first-descent time holds on an infinite dyadic ray. -/
theorem ray_5345 (m : Nat) : stoppingTime (2 ^ 2 * m + 5345) 2 :=
  stoppingTime_of_classCertificate certificate_5345 m

/-- Checked base and every prefix for input 5347. -/
theorem certificate_5347 : classCertificateB 4 5347 = true := by
  decide

/-- The same exact first-descent time holds on an infinite dyadic ray. -/
theorem ray_5347 (m : Nat) : stoppingTime (2 ^ 4 * m + 5347) 4 :=
  stoppingTime_of_classCertificate certificate_5347 m

/-- Checked base and every prefix for input 5349. -/
theorem certificate_5349 : classCertificateB 2 5349 = true := by
  decide

/-- The same exact first-descent time holds on an infinite dyadic ray. -/
theorem ray_5349 (m : Nat) : stoppingTime (2 ^ 2 * m + 5349) 2 :=
  stoppingTime_of_classCertificate certificate_5349 m

/-- Checked base and every prefix for input 5351. -/
theorem certificate_5351 : classCertificateB 29 5351 = true := by
  decide

/-- The same exact first-descent time holds on an infinite dyadic ray. -/
theorem ray_5351 (m : Nat) : stoppingTime (2 ^ 29 * m + 5351) 29 :=
  stoppingTime_of_classCertificate certificate_5351 m

/-- Checked base and every prefix for input 5353. -/
theorem certificate_5353 : classCertificateB 2 5353 = true := by
  decide

/-- The same exact first-descent time holds on an infinite dyadic ray. -/
theorem ray_5353 (m : Nat) : stoppingTime (2 ^ 2 * m + 5353) 2 :=
  stoppingTime_of_classCertificate certificate_5353 m

/-- Checked base and every prefix for input 5355. -/
theorem certificate_5355 : classCertificateB 5 5355 = true := by
  decide

/-- The same exact first-descent time holds on an infinite dyadic ray. -/
theorem ray_5355 (m : Nat) : stoppingTime (2 ^ 5 * m + 5355) 5 :=
  stoppingTime_of_classCertificate certificate_5355 m

/-- Checked base and every prefix for input 5357. -/
theorem certificate_5357 : classCertificateB 2 5357 = true := by
  decide

/-- The same exact first-descent time holds on an infinite dyadic ray. -/
theorem ray_5357 (m : Nat) : stoppingTime (2 ^ 2 * m + 5357) 2 :=
  stoppingTime_of_classCertificate certificate_5357 m

/-- Checked base and every prefix for input 5359. -/
theorem certificate_5359 : classCertificateB 21 5359 = true := by
  decide

/-- The same exact first-descent time holds on an infinite dyadic ray. -/
theorem ray_5359 (m : Nat) : stoppingTime (2 ^ 21 * m + 5359) 21 :=
  stoppingTime_of_classCertificate certificate_5359 m

/-- Exhaustive coverage of the odd inputs in this batch, with no gaps. -/
theorem coverage : CertifiedRange 5293 5361 := by
  intro n hlo hhi hodd
  have hn : n = 5293 ∨ n = 5295 ∨ n = 5297 ∨ n = 5299 ∨ n = 5301 ∨ n = 5303 ∨ n = 5305 ∨ n = 5307 ∨ n = 5309 ∨ n = 5311 ∨ n = 5313 ∨ n = 5315 ∨ n = 5317 ∨ n = 5319 ∨ n = 5321 ∨ n = 5323 ∨ n = 5325 ∨ n = 5327 ∨ n = 5329 ∨ n = 5331 ∨ n = 5333 ∨ n = 5335 ∨ n = 5337 ∨ n = 5339 ∨ n = 5341 ∨ n = 5343 ∨ n = 5345 ∨ n = 5347 ∨ n = 5349 ∨ n = 5351 ∨ n = 5353 ∨ n = 5355 ∨ n = 5357 ∨ n = 5359 := by omega
  rcases hn with h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h
  · subst n
    exact ⟨2, witness_of_certificate certificate_5293⟩
  · subst n
    exact ⟨8, witness_of_certificate certificate_5295⟩
  · subst n
    exact ⟨2, witness_of_certificate certificate_5297⟩
  · subst n
    exact ⟨4, witness_of_certificate certificate_5299⟩
  · subst n
    exact ⟨2, witness_of_certificate certificate_5301⟩
  · subst n
    exact ⟨5, witness_of_certificate certificate_5303⟩
  · subst n
    exact ⟨2, witness_of_certificate certificate_5305⟩
  · subst n
    exact ⟨7, witness_of_certificate certificate_5307⟩
  · subst n
    exact ⟨2, witness_of_certificate certificate_5309⟩
  · subst n
    exact ⟨15, witness_of_certificate certificate_5311⟩
  · subst n
    exact ⟨2, witness_of_certificate certificate_5313⟩
  · subst n
    exact ⟨4, witness_of_certificate certificate_5315⟩
  · subst n
    exact ⟨2, witness_of_certificate certificate_5317⟩
  · subst n
    exact ⟨8, witness_of_certificate certificate_5319⟩
  · subst n
    exact ⟨2, witness_of_certificate certificate_5321⟩
  · subst n
    exact ⟨5, witness_of_certificate certificate_5323⟩
  · subst n
    exact ⟨2, witness_of_certificate certificate_5325⟩
  · subst n
    exact ⟨12, witness_of_certificate certificate_5327⟩
  · subst n
    exact ⟨2, witness_of_certificate certificate_5329⟩
  · subst n
    exact ⟨4, witness_of_certificate certificate_5331⟩
  · subst n
    exact ⟨2, witness_of_certificate certificate_5333⟩
  · subst n
    exact ⟨5, witness_of_certificate certificate_5335⟩
  · subst n
    exact ⟨2, witness_of_certificate certificate_5337⟩
  · subst n
    exact ⟨8, witness_of_certificate certificate_5339⟩
  · subst n
    exact ⟨2, witness_of_certificate certificate_5341⟩
  · subst n
    exact ⟨16, witness_of_certificate certificate_5343⟩
  · subst n
    exact ⟨2, witness_of_certificate certificate_5345⟩
  · subst n
    exact ⟨4, witness_of_certificate certificate_5347⟩
  · subst n
    exact ⟨2, witness_of_certificate certificate_5349⟩
  · subst n
    exact ⟨29, witness_of_certificate certificate_5351⟩
  · subst n
    exact ⟨2, witness_of_certificate certificate_5353⟩
  · subst n
    exact ⟨5, witness_of_certificate certificate_5355⟩
  · subst n
    exact ⟨2, witness_of_certificate certificate_5357⟩
  · subst n
    exact ⟨21, witness_of_certificate certificate_5359⟩

end Collatz.Research.CoefficientDescent.Batch080
