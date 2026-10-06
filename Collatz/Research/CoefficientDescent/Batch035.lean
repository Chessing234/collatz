import Collatz.Research.CoefficientDescent.Basic

namespace Collatz.Research.CoefficientDescent.Batch035

open FirstDescentClass

set_option maxRecDepth 20000
set_option maxHeartbeats 0

/-- Checked base and every prefix for input 2279. -/
theorem certificate_2279 : classCertificateB 15 2279 = true := by
  decide

/-- The same exact first-descent time holds on an infinite dyadic ray. -/
theorem ray_2279 (m : Nat) : stoppingTime (2 ^ 15 * m + 2279) 15 :=
  stoppingTime_of_classCertificate certificate_2279 m

/-- Checked base and every prefix for input 2281. -/
theorem certificate_2281 : classCertificateB 2 2281 = true := by
  decide

/-- The same exact first-descent time holds on an infinite dyadic ray. -/
theorem ray_2281 (m : Nat) : stoppingTime (2 ^ 2 * m + 2281) 2 :=
  stoppingTime_of_classCertificate certificate_2281 m

/-- Checked base and every prefix for input 2283. -/
theorem certificate_2283 : classCertificateB 5 2283 = true := by
  decide

/-- The same exact first-descent time holds on an infinite dyadic ray. -/
theorem ray_2283 (m : Nat) : stoppingTime (2 ^ 5 * m + 2283) 5 :=
  stoppingTime_of_classCertificate certificate_2283 m

/-- Checked base and every prefix for input 2285. -/
theorem certificate_2285 : classCertificateB 2 2285 = true := by
  decide

/-- The same exact first-descent time holds on an infinite dyadic ray. -/
theorem ray_2285 (m : Nat) : stoppingTime (2 ^ 2 * m + 2285) 2 :=
  stoppingTime_of_classCertificate certificate_2285 m

/-- Checked base and every prefix for input 2287. -/
theorem certificate_2287 : classCertificateB 50 2287 = true := by
  decide

/-- The same exact first-descent time holds on an infinite dyadic ray. -/
theorem ray_2287 (m : Nat) : stoppingTime (2 ^ 50 * m + 2287) 50 :=
  stoppingTime_of_classCertificate certificate_2287 m

/-- Checked base and every prefix for input 2289. -/
theorem certificate_2289 : classCertificateB 2 2289 = true := by
  decide

/-- The same exact first-descent time holds on an infinite dyadic ray. -/
theorem ray_2289 (m : Nat) : stoppingTime (2 ^ 2 * m + 2289) 2 :=
  stoppingTime_of_classCertificate certificate_2289 m

/-- Checked base and every prefix for input 2291. -/
theorem certificate_2291 : classCertificateB 4 2291 = true := by
  decide

/-- The same exact first-descent time holds on an infinite dyadic ray. -/
theorem ray_2291 (m : Nat) : stoppingTime (2 ^ 4 * m + 2291) 4 :=
  stoppingTime_of_classCertificate certificate_2291 m

/-- Checked base and every prefix for input 2293. -/
theorem certificate_2293 : classCertificateB 2 2293 = true := by
  decide

/-- The same exact first-descent time holds on an infinite dyadic ray. -/
theorem ray_2293 (m : Nat) : stoppingTime (2 ^ 2 * m + 2293) 2 :=
  stoppingTime_of_classCertificate certificate_2293 m

/-- Checked base and every prefix for input 2295. -/
theorem certificate_2295 : classCertificateB 5 2295 = true := by
  decide

/-- The same exact first-descent time holds on an infinite dyadic ray. -/
theorem ray_2295 (m : Nat) : stoppingTime (2 ^ 5 * m + 2295) 5 :=
  stoppingTime_of_classCertificate certificate_2295 m

/-- Checked base and every prefix for input 2297. -/
theorem certificate_2297 : classCertificateB 2 2297 = true := by
  decide

/-- The same exact first-descent time holds on an infinite dyadic ray. -/
theorem ray_2297 (m : Nat) : stoppingTime (2 ^ 2 * m + 2297) 2 :=
  stoppingTime_of_classCertificate certificate_2297 m

/-- Checked base and every prefix for input 2299. -/
theorem certificate_2299 : classCertificateB 15 2299 = true := by
  decide

/-- The same exact first-descent time holds on an infinite dyadic ray. -/
theorem ray_2299 (m : Nat) : stoppingTime (2 ^ 15 * m + 2299) 15 :=
  stoppingTime_of_classCertificate certificate_2299 m

/-- Checked base and every prefix for input 2301. -/
theorem certificate_2301 : classCertificateB 2 2301 = true := by
  decide

/-- The same exact first-descent time holds on an infinite dyadic ray. -/
theorem ray_2301 (m : Nat) : stoppingTime (2 ^ 2 * m + 2301) 2 :=
  stoppingTime_of_classCertificate certificate_2301 m

/-- Checked base and every prefix for input 2303. -/
theorem certificate_2303 : classCertificateB 15 2303 = true := by
  decide

/-- The same exact first-descent time holds on an infinite dyadic ray. -/
theorem ray_2303 (m : Nat) : stoppingTime (2 ^ 15 * m + 2303) 15 :=
  stoppingTime_of_classCertificate certificate_2303 m

/-- Checked base and every prefix for input 2305. -/
theorem certificate_2305 : classCertificateB 2 2305 = true := by
  decide

/-- The same exact first-descent time holds on an infinite dyadic ray. -/
theorem ray_2305 (m : Nat) : stoppingTime (2 ^ 2 * m + 2305) 2 :=
  stoppingTime_of_classCertificate certificate_2305 m

/-- Checked base and every prefix for input 2307. -/
theorem certificate_2307 : classCertificateB 4 2307 = true := by
  decide

/-- The same exact first-descent time holds on an infinite dyadic ray. -/
theorem ray_2307 (m : Nat) : stoppingTime (2 ^ 4 * m + 2307) 4 :=
  stoppingTime_of_classCertificate certificate_2307 m

/-- Checked base and every prefix for input 2309. -/
theorem certificate_2309 : classCertificateB 2 2309 = true := by
  decide

/-- The same exact first-descent time holds on an infinite dyadic ray. -/
theorem ray_2309 (m : Nat) : stoppingTime (2 ^ 2 * m + 2309) 2 :=
  stoppingTime_of_classCertificate certificate_2309 m

/-- Checked base and every prefix for input 2311. -/
theorem certificate_2311 : classCertificateB 7 2311 = true := by
  decide

/-- The same exact first-descent time holds on an infinite dyadic ray. -/
theorem ray_2311 (m : Nat) : stoppingTime (2 ^ 7 * m + 2311) 7 :=
  stoppingTime_of_classCertificate certificate_2311 m

/-- Checked base and every prefix for input 2313. -/
theorem certificate_2313 : classCertificateB 2 2313 = true := by
  decide

/-- The same exact first-descent time holds on an infinite dyadic ray. -/
theorem ray_2313 (m : Nat) : stoppingTime (2 ^ 2 * m + 2313) 2 :=
  stoppingTime_of_classCertificate certificate_2313 m

/-- Checked base and every prefix for input 2315. -/
theorem certificate_2315 : classCertificateB 5 2315 = true := by
  decide

/-- The same exact first-descent time holds on an infinite dyadic ray. -/
theorem ray_2315 (m : Nat) : stoppingTime (2 ^ 5 * m + 2315) 5 :=
  stoppingTime_of_classCertificate certificate_2315 m

/-- Checked base and every prefix for input 2317. -/
theorem certificate_2317 : classCertificateB 2 2317 = true := by
  decide

/-- The same exact first-descent time holds on an infinite dyadic ray. -/
theorem ray_2317 (m : Nat) : stoppingTime (2 ^ 2 * m + 2317) 2 :=
  stoppingTime_of_classCertificate certificate_2317 m

/-- Checked base and every prefix for input 2319. -/
theorem certificate_2319 : classCertificateB 7 2319 = true := by
  decide

/-- The same exact first-descent time holds on an infinite dyadic ray. -/
theorem ray_2319 (m : Nat) : stoppingTime (2 ^ 7 * m + 2319) 7 :=
  stoppingTime_of_classCertificate certificate_2319 m

/-- Checked base and every prefix for input 2321. -/
theorem certificate_2321 : classCertificateB 2 2321 = true := by
  decide

/-- The same exact first-descent time holds on an infinite dyadic ray. -/
theorem ray_2321 (m : Nat) : stoppingTime (2 ^ 2 * m + 2321) 2 :=
  stoppingTime_of_classCertificate certificate_2321 m

/-- Checked base and every prefix for input 2323. -/
theorem certificate_2323 : classCertificateB 4 2323 = true := by
  decide

/-- The same exact first-descent time holds on an infinite dyadic ray. -/
theorem ray_2323 (m : Nat) : stoppingTime (2 ^ 4 * m + 2323) 4 :=
  stoppingTime_of_classCertificate certificate_2323 m

/-- Checked base and every prefix for input 2325. -/
theorem certificate_2325 : classCertificateB 2 2325 = true := by
  decide

/-- The same exact first-descent time holds on an infinite dyadic ray. -/
theorem ray_2325 (m : Nat) : stoppingTime (2 ^ 2 * m + 2325) 2 :=
  stoppingTime_of_classCertificate certificate_2325 m

/-- Checked base and every prefix for input 2327. -/
theorem certificate_2327 : classCertificateB 5 2327 = true := by
  decide

/-- The same exact first-descent time holds on an infinite dyadic ray. -/
theorem ray_2327 (m : Nat) : stoppingTime (2 ^ 5 * m + 2327) 5 :=
  stoppingTime_of_classCertificate certificate_2327 m

/-- Checked base and every prefix for input 2329. -/
theorem certificate_2329 : classCertificateB 2 2329 = true := by
  decide

/-- The same exact first-descent time holds on an infinite dyadic ray. -/
theorem ray_2329 (m : Nat) : stoppingTime (2 ^ 2 * m + 2329) 2 :=
  stoppingTime_of_classCertificate certificate_2329 m

/-- Checked base and every prefix for input 2331. -/
theorem certificate_2331 : classCertificateB 13 2331 = true := by
  decide

/-- The same exact first-descent time holds on an infinite dyadic ray. -/
theorem ray_2331 (m : Nat) : stoppingTime (2 ^ 13 * m + 2331) 13 :=
  stoppingTime_of_classCertificate certificate_2331 m

/-- Checked base and every prefix for input 2333. -/
theorem certificate_2333 : classCertificateB 2 2333 = true := by
  decide

/-- The same exact first-descent time holds on an infinite dyadic ray. -/
theorem ray_2333 (m : Nat) : stoppingTime (2 ^ 2 * m + 2333) 2 :=
  stoppingTime_of_classCertificate certificate_2333 m

/-- Checked base and every prefix for input 2335. -/
theorem certificate_2335 : classCertificateB 10 2335 = true := by
  decide

/-- The same exact first-descent time holds on an infinite dyadic ray. -/
theorem ray_2335 (m : Nat) : stoppingTime (2 ^ 10 * m + 2335) 10 :=
  stoppingTime_of_classCertificate certificate_2335 m

/-- Checked base and every prefix for input 2337. -/
theorem certificate_2337 : classCertificateB 2 2337 = true := by
  decide

/-- The same exact first-descent time holds on an infinite dyadic ray. -/
theorem ray_2337 (m : Nat) : stoppingTime (2 ^ 2 * m + 2337) 2 :=
  stoppingTime_of_classCertificate certificate_2337 m

/-- Checked base and every prefix for input 2339. -/
theorem certificate_2339 : classCertificateB 4 2339 = true := by
  decide

/-- The same exact first-descent time holds on an infinite dyadic ray. -/
theorem ray_2339 (m : Nat) : stoppingTime (2 ^ 4 * m + 2339) 4 :=
  stoppingTime_of_classCertificate certificate_2339 m

/-- Checked base and every prefix for input 2341. -/
theorem certificate_2341 : classCertificateB 2 2341 = true := by
  decide

/-- The same exact first-descent time holds on an infinite dyadic ray. -/
theorem ray_2341 (m : Nat) : stoppingTime (2 ^ 2 * m + 2341) 2 :=
  stoppingTime_of_classCertificate certificate_2341 m

/-- Checked base and every prefix for input 2343. -/
theorem certificate_2343 : classCertificateB 8 2343 = true := by
  decide

/-- The same exact first-descent time holds on an infinite dyadic ray. -/
theorem ray_2343 (m : Nat) : stoppingTime (2 ^ 8 * m + 2343) 8 :=
  stoppingTime_of_classCertificate certificate_2343 m

/-- Checked base and every prefix for input 2345. -/
theorem certificate_2345 : classCertificateB 2 2345 = true := by
  decide

/-- The same exact first-descent time holds on an infinite dyadic ray. -/
theorem ray_2345 (m : Nat) : stoppingTime (2 ^ 2 * m + 2345) 2 :=
  stoppingTime_of_classCertificate certificate_2345 m

/-- Exhaustive coverage of the odd inputs in this batch, with no gaps. -/
theorem coverage : CertifiedRange 2279 2347 := by
  intro n hlo hhi hodd
  have hn : n = 2279 ∨ n = 2281 ∨ n = 2283 ∨ n = 2285 ∨ n = 2287 ∨ n = 2289 ∨ n = 2291 ∨ n = 2293 ∨ n = 2295 ∨ n = 2297 ∨ n = 2299 ∨ n = 2301 ∨ n = 2303 ∨ n = 2305 ∨ n = 2307 ∨ n = 2309 ∨ n = 2311 ∨ n = 2313 ∨ n = 2315 ∨ n = 2317 ∨ n = 2319 ∨ n = 2321 ∨ n = 2323 ∨ n = 2325 ∨ n = 2327 ∨ n = 2329 ∨ n = 2331 ∨ n = 2333 ∨ n = 2335 ∨ n = 2337 ∨ n = 2339 ∨ n = 2341 ∨ n = 2343 ∨ n = 2345 := by omega
  rcases hn with h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h
  · subst n
    exact ⟨15, witness_of_certificate certificate_2279⟩
  · subst n
    exact ⟨2, witness_of_certificate certificate_2281⟩
  · subst n
    exact ⟨5, witness_of_certificate certificate_2283⟩
  · subst n
    exact ⟨2, witness_of_certificate certificate_2285⟩
  · subst n
    exact ⟨50, witness_of_certificate certificate_2287⟩
  · subst n
    exact ⟨2, witness_of_certificate certificate_2289⟩
  · subst n
    exact ⟨4, witness_of_certificate certificate_2291⟩
  · subst n
    exact ⟨2, witness_of_certificate certificate_2293⟩
  · subst n
    exact ⟨5, witness_of_certificate certificate_2295⟩
  · subst n
    exact ⟨2, witness_of_certificate certificate_2297⟩
  · subst n
    exact ⟨15, witness_of_certificate certificate_2299⟩
  · subst n
    exact ⟨2, witness_of_certificate certificate_2301⟩
  · subst n
    exact ⟨15, witness_of_certificate certificate_2303⟩
  · subst n
    exact ⟨2, witness_of_certificate certificate_2305⟩
  · subst n
    exact ⟨4, witness_of_certificate certificate_2307⟩
  · subst n
    exact ⟨2, witness_of_certificate certificate_2309⟩
  · subst n
    exact ⟨7, witness_of_certificate certificate_2311⟩
  · subst n
    exact ⟨2, witness_of_certificate certificate_2313⟩
  · subst n
    exact ⟨5, witness_of_certificate certificate_2315⟩
  · subst n
    exact ⟨2, witness_of_certificate certificate_2317⟩
  · subst n
    exact ⟨7, witness_of_certificate certificate_2319⟩
  · subst n
    exact ⟨2, witness_of_certificate certificate_2321⟩
  · subst n
    exact ⟨4, witness_of_certificate certificate_2323⟩
  · subst n
    exact ⟨2, witness_of_certificate certificate_2325⟩
  · subst n
    exact ⟨5, witness_of_certificate certificate_2327⟩
  · subst n
    exact ⟨2, witness_of_certificate certificate_2329⟩
  · subst n
    exact ⟨13, witness_of_certificate certificate_2331⟩
  · subst n
    exact ⟨2, witness_of_certificate certificate_2333⟩
  · subst n
    exact ⟨10, witness_of_certificate certificate_2335⟩
  · subst n
    exact ⟨2, witness_of_certificate certificate_2337⟩
  · subst n
    exact ⟨4, witness_of_certificate certificate_2339⟩
  · subst n
    exact ⟨2, witness_of_certificate certificate_2341⟩
  · subst n
    exact ⟨8, witness_of_certificate certificate_2343⟩
  · subst n
    exact ⟨2, witness_of_certificate certificate_2345⟩

end Collatz.Research.CoefficientDescent.Batch035
