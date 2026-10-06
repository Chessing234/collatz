import Collatz.Research.DescentIntervals.Classifier

namespace Collatz.Research.PassageAtlas.Batch0375

open Collatz.Research.DescentIntervals

set_option maxRecDepth 20000
set_option maxHeartbeats 0

/-- Complete interval computation for depth 15, residue 12255. -/
theorem bounds_15_12255 : exactInterval 15 12255 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_12255 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 12255) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_12255 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_12255 : oddCount 12255 15 = 7 ∧ acceleratedOrbit 15 12255 = 818 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_12255 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 12255) = 3 ^ 7 * m + 818 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_12255.1, data_15_12255.2]

/-- Complete interval computation for depth 15, residue 12256. -/
theorem bounds_15_12256 : exactInterval 15 12256 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_12256 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 12256) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_12256 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_12256 : oddCount 12256 15 = 7 ∧ acceleratedOrbit 15 12256 = 820 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_12256 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 12256) = 3 ^ 7 * m + 820 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_12256.1, data_15_12256.2]

/-- Complete interval computation for depth 15, residue 12257. -/
theorem bounds_15_12257 : exactInterval 15 12257 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_12257 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 12257) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_12257 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_12257 : oddCount 12257 15 = 11 ∧ acceleratedOrbit 15 12257 = 66278 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_12257 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 12257) = 3 ^ 11 * m + 66278 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_12257.1, data_15_12257.2]

/-- Complete interval computation for depth 15, residue 12258. -/
theorem bounds_15_12258 : exactInterval 15 12258 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_12258 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 12258) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_12258 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_12258 : oddCount 12258 15 = 7 ∧ acceleratedOrbit 15 12258 = 820 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_12258 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 12258) = 3 ^ 7 * m + 820 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_12258.1, data_15_12258.2]

/-- Complete interval computation for depth 15, residue 12259. -/
theorem bounds_15_12259 : exactInterval 15 12259 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_12259 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 12259) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_12259 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_12259 : oddCount 12259 15 = 7 ∧ acceleratedOrbit 15 12259 = 820 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_12259 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 12259) = 3 ^ 7 * m + 820 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_12259.1, data_15_12259.2]

/-- Complete interval computation for depth 15, residue 12260. -/
theorem bounds_15_12260 : exactInterval 15 12260 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_12260 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 12260) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_12260 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_12260 : oddCount 12260 15 = 10 ∧ acceleratedOrbit 15 12260 = 22112 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_12260 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 12260) = 3 ^ 10 * m + 22112 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_12260.1, data_15_12260.2]

/-- Complete interval computation for depth 15, residue 12261. -/
theorem bounds_15_12261 : exactInterval 15 12261 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_12261 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 12261) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_12261 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_12261 : oddCount 12261 15 = 10 ∧ acceleratedOrbit 15 12261 = 22112 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_12261 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 12261) = 3 ^ 10 * m + 22112 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_12261.1, data_15_12261.2]

/-- Complete interval computation for depth 15, residue 12262. -/
theorem bounds_15_12262 : exactInterval 15 12262 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_12262 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 12262) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_12262 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_12262 : oddCount 12262 15 = 10 ∧ acceleratedOrbit 15 12262 = 22112 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_12262 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 12262) = 3 ^ 10 * m + 22112 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_12262.1, data_15_12262.2]

/-- Complete interval computation for depth 15, residue 12263. -/
theorem bounds_15_12263 : exactInterval 15 12263 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_12263 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 12263) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_12263 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_12263 : oddCount 12263 15 = 10 ∧ acceleratedOrbit 15 12263 = 22103 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_12263 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 12263) = 3 ^ 10 * m + 22103 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_12263.1, data_15_12263.2]

/-- Complete interval computation for depth 15, residue 12264. -/
theorem bounds_15_12264 : exactInterval 15 12264 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_12264 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 12264) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_12264 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_12264 : oddCount 12264 15 = 7 ∧ acceleratedOrbit 15 12264 = 820 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_12264 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 12264) = 3 ^ 7 * m + 820 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_12264.1, data_15_12264.2]

/-- Complete interval computation for depth 15, residue 12265. -/
theorem bounds_15_12265 : exactInterval 15 12265 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_12265 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 12265) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_12265 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_12265 : oddCount 12265 15 = 10 ∧ acceleratedOrbit 15 12265 = 22106 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_12265 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 12265) = 3 ^ 10 * m + 22106 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_12265.1, data_15_12265.2]

/-- Complete interval computation for depth 15, residue 12266. -/
theorem bounds_15_12266 : exactInterval 15 12266 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_12266 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 12266) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_12266 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_12266 : oddCount 12266 15 = 7 ∧ acceleratedOrbit 15 12266 = 820 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_12266 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 12266) = 3 ^ 7 * m + 820 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_12266.1, data_15_12266.2]

/-- Complete interval computation for depth 15, residue 12267. -/
theorem bounds_15_12267 : exactInterval 15 12267 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_12267 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 12267) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_12267 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_12267 : oddCount 12267 15 = 11 ∧ acceleratedOrbit 15 12267 = 66329 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_12267 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 12267) = 3 ^ 11 * m + 66329 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_12267.1, data_15_12267.2]

/-- Complete interval computation for depth 15, residue 12268. -/
theorem bounds_15_12268 : exactInterval 15 12268 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_12268 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 12268) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_12268 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_12268 : oddCount 12268 15 = 8 ∧ acceleratedOrbit 15 12268 = 2458 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_12268 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 12268) = 3 ^ 8 * m + 2458 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_12268.1, data_15_12268.2]

/-- Complete interval computation for depth 15, residue 12269. -/
theorem bounds_15_12269 : exactInterval 15 12269 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_12269 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 12269) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_12269 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_12269 : oddCount 12269 15 = 8 ∧ acceleratedOrbit 15 12269 = 2458 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_12269 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 12269) = 3 ^ 8 * m + 2458 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_12269.1, data_15_12269.2]

/-- Complete interval computation for depth 15, residue 12270. -/
theorem bounds_15_12270 : exactInterval 15 12270 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_12270 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 12270) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_12270 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_12270 : oddCount 12270 15 = 8 ∧ acceleratedOrbit 15 12270 = 2458 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_12270 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 12270) = 3 ^ 8 * m + 2458 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_12270.1, data_15_12270.2]

/-- Complete interval computation for depth 15, residue 12271. -/
theorem bounds_15_12271 : exactInterval 15 12271 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_12271 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 12271) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_12271 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_12271 : oddCount 12271 15 = 9 ∧ acceleratedOrbit 15 12271 = 7372 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_12271 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 12271) = 3 ^ 9 * m + 7372 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_12271.1, data_15_12271.2]

/-- Complete interval computation for depth 15, residue 12272. -/
theorem bounds_15_12272 : exactInterval 15 12272 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_12272 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 12272) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_12272 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_12272 : oddCount 12272 15 = 9 ∧ acceleratedOrbit 15 12272 = 7381 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_12272 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 12272) = 3 ^ 9 * m + 7381 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_12272.1, data_15_12272.2]

/-- Complete interval computation for depth 15, residue 12273. -/
theorem bounds_15_12273 : exactInterval 15 12273 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_12273 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 12273) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_12273 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_12273 : oddCount 12273 15 = 7 ∧ acceleratedOrbit 15 12273 = 820 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_12273 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 12273) = 3 ^ 7 * m + 820 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_12273.1, data_15_12273.2]

/-- Complete interval computation for depth 15, residue 12274. -/
theorem bounds_15_12274 : exactInterval 15 12274 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_12274 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 12274) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_12274 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_12274 : oddCount 12274 15 = 8 ∧ acceleratedOrbit 15 12274 = 2459 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_12274 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 12274) = 3 ^ 8 * m + 2459 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_12274.1, data_15_12274.2]

/-- Complete interval computation for depth 15, residue 12275. -/
theorem bounds_15_12275 : exactInterval 15 12275 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_12275 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 12275) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_12275 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_12275 : oddCount 12275 15 = 8 ∧ acceleratedOrbit 15 12275 = 2459 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_12275 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 12275) = 3 ^ 8 * m + 2459 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_12275.1, data_15_12275.2]

/-- Complete interval computation for depth 15, residue 12276. -/
theorem bounds_15_12276 : exactInterval 15 12276 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_12276 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 12276) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_12276 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_12276 : oddCount 12276 15 = 9 ∧ acceleratedOrbit 15 12276 = 7381 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_12276 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 12276) = 3 ^ 9 * m + 7381 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_12276.1, data_15_12276.2]

/-- Complete interval computation for depth 15, residue 12277. -/
theorem bounds_15_12277 : exactInterval 15 12277 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_12277 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 12277) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_12277 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_12277 : oddCount 12277 15 = 9 ∧ acceleratedOrbit 15 12277 = 7381 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_12277 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 12277) = 3 ^ 9 * m + 7381 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_12277.1, data_15_12277.2]

/-- Complete interval computation for depth 15, residue 12278. -/
theorem bounds_15_12278 : exactInterval 15 12278 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_12278 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 12278) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_12278 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_12278 : oddCount 12278 15 = 10 ∧ acceleratedOrbit 15 12278 = 22133 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_12278 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 12278) = 3 ^ 10 * m + 22133 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_12278.1, data_15_12278.2]

/-- Complete interval computation for depth 15, residue 12279. -/
theorem bounds_15_12279 : exactInterval 15 12279 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_12279 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 12279) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_12279 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_12279 : oddCount 12279 15 = 10 ∧ acceleratedOrbit 15 12279 = 22133 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_12279 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 12279) = 3 ^ 10 * m + 22133 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_12279.1, data_15_12279.2]

/-- Complete interval computation for depth 15, residue 12280. -/
theorem bounds_15_12280 : exactInterval 15 12280 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_12280 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 12280) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_12280 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_12280 : oddCount 12280 15 = 9 ∧ acceleratedOrbit 15 12280 = 7381 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_12280 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 12280) = 3 ^ 9 * m + 7381 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_12280.1, data_15_12280.2]

/-- Complete interval computation for depth 15, residue 12281. -/
theorem bounds_15_12281 : exactInterval 15 12281 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_12281 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 12281) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_12281 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_12281 : oddCount 12281 15 = 9 ∧ acceleratedOrbit 15 12281 = 7379 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_12281 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 12281) = 3 ^ 9 * m + 7379 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_12281.1, data_15_12281.2]

/-- Complete interval computation for depth 15, residue 12282. -/
theorem bounds_15_12282 : exactInterval 15 12282 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_12282 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 12282) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_12282 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_12282 : oddCount 12282 15 = 9 ∧ acceleratedOrbit 15 12282 = 7381 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_12282 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 12282) = 3 ^ 9 * m + 7381 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_12282.1, data_15_12282.2]

/-- Complete interval computation for depth 15, residue 12283. -/
theorem bounds_15_12283 : exactInterval 15 12283 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_12283 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 12283) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_12283 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_12283 : oddCount 12283 15 = 10 ∧ acceleratedOrbit 15 12283 = 22139 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_12283 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 12283) = 3 ^ 10 * m + 22139 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_12283.1, data_15_12283.2]

/-- Complete interval computation for depth 15, residue 12284. -/
theorem bounds_15_12284 : exactInterval 15 12284 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_12284 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 12284) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_12284 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_12284 : oddCount 12284 15 = 11 ∧ acceleratedOrbit 15 12284 = 66430 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_12284 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 12284) = 3 ^ 11 * m + 66430 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_12284.1, data_15_12284.2]

/-- Complete interval computation for depth 15, residue 12285. -/
theorem bounds_15_12285 : exactInterval 15 12285 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_12285 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 12285) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_12285 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_12285 : oddCount 12285 15 = 11 ∧ acceleratedOrbit 15 12285 = 66430 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_12285 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 12285) = 3 ^ 11 * m + 66430 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_12285.1, data_15_12285.2]

/-- Complete interval computation for depth 15, residue 12286. -/
theorem bounds_15_12286 : exactInterval 15 12286 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_12286 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 12286) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_12286 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_12286 : oddCount 12286 15 = 11 ∧ acceleratedOrbit 15 12286 = 66430 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_12286 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 12286) = 3 ^ 11 * m + 66430 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_12286.1, data_15_12286.2]

/-- Complete interval computation for depth 15, residue 12287. -/
theorem bounds_15_12287 : exactInterval 15 12287 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_12287 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 12287) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_12287 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_12287 : oddCount 12287 15 = 13 ∧ acceleratedOrbit 15 12287 = 597871 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_12287 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 12287) = 3 ^ 13 * m + 597871 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_12287.1, data_15_12287.2]

end Collatz.Research.PassageAtlas.Batch0375
