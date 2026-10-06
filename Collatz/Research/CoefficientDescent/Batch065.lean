import Collatz.Research.CoefficientDescent.Basic

namespace Collatz.Research.CoefficientDescent.Batch065

open FirstDescentClass

set_option maxRecDepth 20000
set_option maxHeartbeats 0

/-- Checked base and every prefix for input 4289. -/
theorem certificate_4289 : classCertificateB 2 4289 = true := by
  decide

/-- The same exact first-descent time holds on an infinite dyadic ray. -/
theorem ray_4289 (m : Nat) : stoppingTime (2 ^ 2 * m + 4289) 2 :=
  stoppingTime_of_classCertificate certificate_4289 m

/-- Checked base and every prefix for input 4291. -/
theorem certificate_4291 : classCertificateB 4 4291 = true := by
  decide

/-- The same exact first-descent time holds on an infinite dyadic ray. -/
theorem ray_4291 (m : Nat) : stoppingTime (2 ^ 4 * m + 4291) 4 :=
  stoppingTime_of_classCertificate certificate_4291 m

/-- Checked base and every prefix for input 4293. -/
theorem certificate_4293 : classCertificateB 2 4293 = true := by
  decide

/-- The same exact first-descent time holds on an infinite dyadic ray. -/
theorem ray_4293 (m : Nat) : stoppingTime (2 ^ 2 * m + 4293) 2 :=
  stoppingTime_of_classCertificate certificate_4293 m

/-- Checked base and every prefix for input 4295. -/
theorem certificate_4295 : classCertificateB 8 4295 = true := by
  decide

/-- The same exact first-descent time holds on an infinite dyadic ray. -/
theorem ray_4295 (m : Nat) : stoppingTime (2 ^ 8 * m + 4295) 8 :=
  stoppingTime_of_classCertificate certificate_4295 m

/-- Checked base and every prefix for input 4297. -/
theorem certificate_4297 : classCertificateB 2 4297 = true := by
  decide

/-- The same exact first-descent time holds on an infinite dyadic ray. -/
theorem ray_4297 (m : Nat) : stoppingTime (2 ^ 2 * m + 4297) 2 :=
  stoppingTime_of_classCertificate certificate_4297 m

/-- Checked base and every prefix for input 4299. -/
theorem certificate_4299 : classCertificateB 5 4299 = true := by
  decide

/-- The same exact first-descent time holds on an infinite dyadic ray. -/
theorem ray_4299 (m : Nat) : stoppingTime (2 ^ 5 * m + 4299) 5 :=
  stoppingTime_of_classCertificate certificate_4299 m

/-- Checked base and every prefix for input 4301. -/
theorem certificate_4301 : classCertificateB 2 4301 = true := by
  decide

/-- The same exact first-descent time holds on an infinite dyadic ray. -/
theorem ray_4301 (m : Nat) : stoppingTime (2 ^ 2 * m + 4301) 2 :=
  stoppingTime_of_classCertificate certificate_4301 m

/-- Checked base and every prefix for input 4303. -/
theorem certificate_4303 : classCertificateB 42 4303 = true := by
  decide

/-- The same exact first-descent time holds on an infinite dyadic ray. -/
theorem ray_4303 (m : Nat) : stoppingTime (2 ^ 42 * m + 4303) 42 :=
  stoppingTime_of_classCertificate certificate_4303 m

/-- Checked base and every prefix for input 4305. -/
theorem certificate_4305 : classCertificateB 2 4305 = true := by
  decide

/-- The same exact first-descent time holds on an infinite dyadic ray. -/
theorem ray_4305 (m : Nat) : stoppingTime (2 ^ 2 * m + 4305) 2 :=
  stoppingTime_of_classCertificate certificate_4305 m

/-- Checked base and every prefix for input 4307. -/
theorem certificate_4307 : classCertificateB 4 4307 = true := by
  decide

/-- The same exact first-descent time holds on an infinite dyadic ray. -/
theorem ray_4307 (m : Nat) : stoppingTime (2 ^ 4 * m + 4307) 4 :=
  stoppingTime_of_classCertificate certificate_4307 m

/-- Checked base and every prefix for input 4309. -/
theorem certificate_4309 : classCertificateB 2 4309 = true := by
  decide

/-- The same exact first-descent time holds on an infinite dyadic ray. -/
theorem ray_4309 (m : Nat) : stoppingTime (2 ^ 2 * m + 4309) 2 :=
  stoppingTime_of_classCertificate certificate_4309 m

/-- Checked base and every prefix for input 4311. -/
theorem certificate_4311 : classCertificateB 5 4311 = true := by
  decide

/-- The same exact first-descent time holds on an infinite dyadic ray. -/
theorem ray_4311 (m : Nat) : stoppingTime (2 ^ 5 * m + 4311) 5 :=
  stoppingTime_of_classCertificate certificate_4311 m

/-- Checked base and every prefix for input 4313. -/
theorem certificate_4313 : classCertificateB 2 4313 = true := by
  decide

/-- The same exact first-descent time holds on an infinite dyadic ray. -/
theorem ray_4313 (m : Nat) : stoppingTime (2 ^ 2 * m + 4313) 2 :=
  stoppingTime_of_classCertificate certificate_4313 m

/-- Checked base and every prefix for input 4315. -/
theorem certificate_4315 : classCertificateB 8 4315 = true := by
  decide

/-- The same exact first-descent time holds on an infinite dyadic ray. -/
theorem ray_4315 (m : Nat) : stoppingTime (2 ^ 8 * m + 4315) 8 :=
  stoppingTime_of_classCertificate certificate_4315 m

/-- Checked base and every prefix for input 4317. -/
theorem certificate_4317 : classCertificateB 2 4317 = true := by
  decide

/-- The same exact first-descent time holds on an infinite dyadic ray. -/
theorem ray_4317 (m : Nat) : stoppingTime (2 ^ 2 * m + 4317) 2 :=
  stoppingTime_of_classCertificate certificate_4317 m

/-- Checked base and every prefix for input 4319. -/
theorem certificate_4319 : classCertificateB 16 4319 = true := by
  decide

/-- The same exact first-descent time holds on an infinite dyadic ray. -/
theorem ray_4319 (m : Nat) : stoppingTime (2 ^ 16 * m + 4319) 16 :=
  stoppingTime_of_classCertificate certificate_4319 m

/-- Checked base and every prefix for input 4321. -/
theorem certificate_4321 : classCertificateB 2 4321 = true := by
  decide

/-- The same exact first-descent time holds on an infinite dyadic ray. -/
theorem ray_4321 (m : Nat) : stoppingTime (2 ^ 2 * m + 4321) 2 :=
  stoppingTime_of_classCertificate certificate_4321 m

/-- Checked base and every prefix for input 4323. -/
theorem certificate_4323 : classCertificateB 4 4323 = true := by
  decide

/-- The same exact first-descent time holds on an infinite dyadic ray. -/
theorem ray_4323 (m : Nat) : stoppingTime (2 ^ 4 * m + 4323) 4 :=
  stoppingTime_of_classCertificate certificate_4323 m

/-- Checked base and every prefix for input 4325. -/
theorem certificate_4325 : classCertificateB 2 4325 = true := by
  decide

/-- The same exact first-descent time holds on an infinite dyadic ray. -/
theorem ray_4325 (m : Nat) : stoppingTime (2 ^ 2 * m + 4325) 2 :=
  stoppingTime_of_classCertificate certificate_4325 m

/-- Checked base and every prefix for input 4327. -/
theorem certificate_4327 : classCertificateB 12 4327 = true := by
  decide

/-- The same exact first-descent time holds on an infinite dyadic ray. -/
theorem ray_4327 (m : Nat) : stoppingTime (2 ^ 12 * m + 4327) 12 :=
  stoppingTime_of_classCertificate certificate_4327 m

/-- Checked base and every prefix for input 4329. -/
theorem certificate_4329 : classCertificateB 2 4329 = true := by
  decide

/-- The same exact first-descent time holds on an infinite dyadic ray. -/
theorem ray_4329 (m : Nat) : stoppingTime (2 ^ 2 * m + 4329) 2 :=
  stoppingTime_of_classCertificate certificate_4329 m

/-- Checked base and every prefix for input 4331. -/
theorem certificate_4331 : classCertificateB 5 4331 = true := by
  decide

/-- The same exact first-descent time holds on an infinite dyadic ray. -/
theorem ray_4331 (m : Nat) : stoppingTime (2 ^ 5 * m + 4331) 5 :=
  stoppingTime_of_classCertificate certificate_4331 m

/-- Checked base and every prefix for input 4333. -/
theorem certificate_4333 : classCertificateB 2 4333 = true := by
  decide

/-- The same exact first-descent time holds on an infinite dyadic ray. -/
theorem ray_4333 (m : Nat) : stoppingTime (2 ^ 2 * m + 4333) 2 :=
  stoppingTime_of_classCertificate certificate_4333 m

/-- Checked base and every prefix for input 4335. -/
theorem certificate_4335 : classCertificateB 16 4335 = true := by
  decide

/-- The same exact first-descent time holds on an infinite dyadic ray. -/
theorem ray_4335 (m : Nat) : stoppingTime (2 ^ 16 * m + 4335) 16 :=
  stoppingTime_of_classCertificate certificate_4335 m

/-- Checked base and every prefix for input 4337. -/
theorem certificate_4337 : classCertificateB 2 4337 = true := by
  decide

/-- The same exact first-descent time holds on an infinite dyadic ray. -/
theorem ray_4337 (m : Nat) : stoppingTime (2 ^ 2 * m + 4337) 2 :=
  stoppingTime_of_classCertificate certificate_4337 m

/-- Checked base and every prefix for input 4339. -/
theorem certificate_4339 : classCertificateB 4 4339 = true := by
  decide

/-- The same exact first-descent time holds on an infinite dyadic ray. -/
theorem ray_4339 (m : Nat) : stoppingTime (2 ^ 4 * m + 4339) 4 :=
  stoppingTime_of_classCertificate certificate_4339 m

/-- Checked base and every prefix for input 4341. -/
theorem certificate_4341 : classCertificateB 2 4341 = true := by
  decide

/-- The same exact first-descent time holds on an infinite dyadic ray. -/
theorem ray_4341 (m : Nat) : stoppingTime (2 ^ 2 * m + 4341) 2 :=
  stoppingTime_of_classCertificate certificate_4341 m

/-- Checked base and every prefix for input 4343. -/
theorem certificate_4343 : classCertificateB 5 4343 = true := by
  decide

/-- The same exact first-descent time holds on an infinite dyadic ray. -/
theorem ray_4343 (m : Nat) : stoppingTime (2 ^ 5 * m + 4343) 5 :=
  stoppingTime_of_classCertificate certificate_4343 m

/-- Checked base and every prefix for input 4345. -/
theorem certificate_4345 : classCertificateB 2 4345 = true := by
  decide

/-- The same exact first-descent time holds on an infinite dyadic ray. -/
theorem ray_4345 (m : Nat) : stoppingTime (2 ^ 2 * m + 4345) 2 :=
  stoppingTime_of_classCertificate certificate_4345 m

/-- Checked base and every prefix for input 4347. -/
theorem certificate_4347 : classCertificateB 50 4347 = true := by
  decide

/-- The same exact first-descent time holds on an infinite dyadic ray. -/
theorem ray_4347 (m : Nat) : stoppingTime (2 ^ 50 * m + 4347) 50 :=
  stoppingTime_of_classCertificate certificate_4347 m

/-- Checked base and every prefix for input 4349. -/
theorem certificate_4349 : classCertificateB 2 4349 = true := by
  decide

/-- The same exact first-descent time holds on an infinite dyadic ray. -/
theorem ray_4349 (m : Nat) : stoppingTime (2 ^ 2 * m + 4349) 2 :=
  stoppingTime_of_classCertificate certificate_4349 m

/-- Checked base and every prefix for input 4351. -/
theorem certificate_4351 : classCertificateB 20 4351 = true := by
  decide

/-- The same exact first-descent time holds on an infinite dyadic ray. -/
theorem ray_4351 (m : Nat) : stoppingTime (2 ^ 20 * m + 4351) 20 :=
  stoppingTime_of_classCertificate certificate_4351 m

/-- Checked base and every prefix for input 4353. -/
theorem certificate_4353 : classCertificateB 2 4353 = true := by
  decide

/-- The same exact first-descent time holds on an infinite dyadic ray. -/
theorem ray_4353 (m : Nat) : stoppingTime (2 ^ 2 * m + 4353) 2 :=
  stoppingTime_of_classCertificate certificate_4353 m

/-- Exhaustive coverage of the odd inputs in this batch, with no gaps. -/
theorem coverage : CertifiedRange 4289 4355 := by
  intro n hlo hhi hodd
  have hn : n = 4289 ∨ n = 4291 ∨ n = 4293 ∨ n = 4295 ∨ n = 4297 ∨ n = 4299 ∨ n = 4301 ∨ n = 4303 ∨ n = 4305 ∨ n = 4307 ∨ n = 4309 ∨ n = 4311 ∨ n = 4313 ∨ n = 4315 ∨ n = 4317 ∨ n = 4319 ∨ n = 4321 ∨ n = 4323 ∨ n = 4325 ∨ n = 4327 ∨ n = 4329 ∨ n = 4331 ∨ n = 4333 ∨ n = 4335 ∨ n = 4337 ∨ n = 4339 ∨ n = 4341 ∨ n = 4343 ∨ n = 4345 ∨ n = 4347 ∨ n = 4349 ∨ n = 4351 ∨ n = 4353 := by omega
  rcases hn with h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h
  · subst n
    exact ⟨2, witness_of_certificate certificate_4289⟩
  · subst n
    exact ⟨4, witness_of_certificate certificate_4291⟩
  · subst n
    exact ⟨2, witness_of_certificate certificate_4293⟩
  · subst n
    exact ⟨8, witness_of_certificate certificate_4295⟩
  · subst n
    exact ⟨2, witness_of_certificate certificate_4297⟩
  · subst n
    exact ⟨5, witness_of_certificate certificate_4299⟩
  · subst n
    exact ⟨2, witness_of_certificate certificate_4301⟩
  · subst n
    exact ⟨42, witness_of_certificate certificate_4303⟩
  · subst n
    exact ⟨2, witness_of_certificate certificate_4305⟩
  · subst n
    exact ⟨4, witness_of_certificate certificate_4307⟩
  · subst n
    exact ⟨2, witness_of_certificate certificate_4309⟩
  · subst n
    exact ⟨5, witness_of_certificate certificate_4311⟩
  · subst n
    exact ⟨2, witness_of_certificate certificate_4313⟩
  · subst n
    exact ⟨8, witness_of_certificate certificate_4315⟩
  · subst n
    exact ⟨2, witness_of_certificate certificate_4317⟩
  · subst n
    exact ⟨16, witness_of_certificate certificate_4319⟩
  · subst n
    exact ⟨2, witness_of_certificate certificate_4321⟩
  · subst n
    exact ⟨4, witness_of_certificate certificate_4323⟩
  · subst n
    exact ⟨2, witness_of_certificate certificate_4325⟩
  · subst n
    exact ⟨12, witness_of_certificate certificate_4327⟩
  · subst n
    exact ⟨2, witness_of_certificate certificate_4329⟩
  · subst n
    exact ⟨5, witness_of_certificate certificate_4331⟩
  · subst n
    exact ⟨2, witness_of_certificate certificate_4333⟩
  · subst n
    exact ⟨16, witness_of_certificate certificate_4335⟩
  · subst n
    exact ⟨2, witness_of_certificate certificate_4337⟩
  · subst n
    exact ⟨4, witness_of_certificate certificate_4339⟩
  · subst n
    exact ⟨2, witness_of_certificate certificate_4341⟩
  · subst n
    exact ⟨5, witness_of_certificate certificate_4343⟩
  · subst n
    exact ⟨2, witness_of_certificate certificate_4345⟩
  · subst n
    exact ⟨50, witness_of_certificate certificate_4347⟩
  · subst n
    exact ⟨2, witness_of_certificate certificate_4349⟩
  · subst n
    exact ⟨20, witness_of_certificate certificate_4351⟩
  · subst n
    exact ⟨2, witness_of_certificate certificate_4353⟩

end Collatz.Research.CoefficientDescent.Batch065
