import Collatz.Research.DescentIntervals.Classifier

namespace Collatz.Research.PassageAtlas.Batch0558

open Collatz.Research.DescentIntervals

set_option maxRecDepth 20000
set_option maxHeartbeats 0

/-- Complete interval computation for depth 15, residue 18251. -/
theorem bounds_15_18251 : exactInterval 15 18251 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_18251 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 18251) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_18251 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_18251 : oddCount 18251 15 = 6 ∧ acceleratedOrbit 15 18251 = 407 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_18251 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 18251) = 3 ^ 6 * m + 407 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_18251.1, data_15_18251.2]

/-- Complete interval computation for depth 15, residue 18252. -/
theorem bounds_15_18252 : exactInterval 15 18252 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_18252 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 18252) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_18252 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_18252 : oddCount 18252 15 = 7 ∧ acceleratedOrbit 15 18252 = 1219 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_18252 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 18252) = 3 ^ 7 * m + 1219 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_18252.1, data_15_18252.2]

/-- Complete interval computation for depth 15, residue 18253. -/
theorem bounds_15_18253 : exactInterval 15 18253 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_18253 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 18253) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_18253 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_18253 : oddCount 18253 15 = 7 ∧ acceleratedOrbit 15 18253 = 1219 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_18253 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 18253) = 3 ^ 7 * m + 1219 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_18253.1, data_15_18253.2]

/-- Complete interval computation for depth 15, residue 18254. -/
theorem bounds_15_18254 : exactInterval 15 18254 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_18254 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 18254) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_18254 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_18254 : oddCount 18254 15 = 8 ∧ acceleratedOrbit 15 18254 = 3656 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_18254 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 18254) = 3 ^ 8 * m + 3656 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_18254.1, data_15_18254.2]

/-- Complete interval computation for depth 15, residue 18255. -/
theorem bounds_15_18255 : exactInterval 15 18255 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_18255 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 18255) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_18255 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_18255 : oddCount 18255 15 = 8 ∧ acceleratedOrbit 15 18255 = 3656 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_18255 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 18255) = 3 ^ 8 * m + 3656 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_18255.1, data_15_18255.2]

/-- Complete interval computation for depth 15, residue 18256. -/
theorem bounds_15_18256 : exactInterval 15 18256 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_18256 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 18256) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_18256 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_18256 : oddCount 18256 15 = 5 ∧ acceleratedOrbit 15 18256 = 137 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_18256 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 18256) = 3 ^ 5 * m + 137 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_18256.1, data_15_18256.2]

/-- Complete interval computation for depth 15, residue 18257. -/
theorem bounds_15_18257 : exactInterval 15 18257 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_18257 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 18257) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_18257 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_18257 : oddCount 18257 15 = 7 ∧ acceleratedOrbit 15 18257 = 1219 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_18257 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 18257) = 3 ^ 7 * m + 1219 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_18257.1, data_15_18257.2]

/-- Complete interval computation for depth 15, residue 18258. -/
theorem bounds_15_18258 : exactInterval 15 18258 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_18258 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 18258) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_18258 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_18258 : oddCount 18258 15 = 10 ∧ acceleratedOrbit 15 18258 = 32908 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_18258 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 18258) = 3 ^ 10 * m + 32908 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_18258.1, data_15_18258.2]

/-- Complete interval computation for depth 15, residue 18259. -/
theorem bounds_15_18259 : exactInterval 15 18259 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_18259 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 18259) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_18259 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_18259 : oddCount 18259 15 = 10 ∧ acceleratedOrbit 15 18259 = 32908 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_18259 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 18259) = 3 ^ 10 * m + 32908 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_18259.1, data_15_18259.2]

/-- Complete interval computation for depth 15, residue 18260. -/
theorem bounds_15_18260 : exactInterval 15 18260 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_18260 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 18260) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_18260 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_18260 : oddCount 18260 15 = 5 ∧ acceleratedOrbit 15 18260 = 137 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_18260 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 18260) = 3 ^ 5 * m + 137 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_18260.1, data_15_18260.2]

/-- Complete interval computation for depth 15, residue 18261. -/
theorem bounds_15_18261 : exactInterval 15 18261 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_18261 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 18261) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_18261 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_18261 : oddCount 18261 15 = 5 ∧ acceleratedOrbit 15 18261 = 137 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_18261 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 18261) = 3 ^ 5 * m + 137 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_18261.1, data_15_18261.2]

/-- Complete interval computation for depth 15, residue 18262. -/
theorem bounds_15_18262 : exactInterval 15 18262 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_18262 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 18262) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_18262 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_18262 : oddCount 18262 15 = 8 ∧ acceleratedOrbit 15 18262 = 3658 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_18262 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 18262) = 3 ^ 8 * m + 3658 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_18262.1, data_15_18262.2]

/-- Complete interval computation for depth 15, residue 18263. -/
theorem bounds_15_18263 : exactInterval 15 18263 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_18263 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 18263) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_18263 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_18263 : oddCount 18263 15 = 8 ∧ acceleratedOrbit 15 18263 = 3658 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_18263 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 18263) = 3 ^ 8 * m + 3658 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_18263.1, data_15_18263.2]

/-- Complete interval computation for depth 15, residue 18264. -/
theorem bounds_15_18264 : exactInterval 15 18264 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_18264 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 18264) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_18264 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_18264 : oddCount 18264 15 = 7 ∧ acceleratedOrbit 15 18264 = 1220 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_18264 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 18264) = 3 ^ 7 * m + 1220 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_18264.1, data_15_18264.2]

/-- Complete interval computation for depth 15, residue 18265. -/
theorem bounds_15_18265 : exactInterval 15 18265 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_18265 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 18265) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_18265 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_18265 : oddCount 18265 15 = 6 ∧ acceleratedOrbit 15 18265 = 407 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_18265 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 18265) = 3 ^ 6 * m + 407 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_18265.1, data_15_18265.2]

/-- Complete interval computation for depth 15, residue 18266. -/
theorem bounds_15_18266 : exactInterval 15 18266 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_18266 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 18266) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_18266 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_18266 : oddCount 18266 15 = 7 ∧ acceleratedOrbit 15 18266 = 1220 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_18266 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 18266) = 3 ^ 7 * m + 1220 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_18266.1, data_15_18266.2]

/-- Complete interval computation for depth 15, residue 18267. -/
theorem bounds_15_18267 : exactInterval 15 18267 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_18267 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 18267) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_18267 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_18267 : oddCount 18267 15 = 11 ∧ acceleratedOrbit 15 18267 = 98765 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_18267 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 18267) = 3 ^ 11 * m + 98765 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_18267.1, data_15_18267.2]

/-- Complete interval computation for depth 15, residue 18268. -/
theorem bounds_15_18268 : exactInterval 15 18268 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_18268 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 18268) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_18268 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_18268 : oddCount 18268 15 = 7 ∧ acceleratedOrbit 15 18268 = 1220 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_18268 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 18268) = 3 ^ 7 * m + 1220 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_18268.1, data_15_18268.2]

/-- Complete interval computation for depth 15, residue 18269. -/
theorem bounds_15_18269 : exactInterval 15 18269 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_18269 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 18269) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_18269 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_18269 : oddCount 18269 15 = 7 ∧ acceleratedOrbit 15 18269 = 1220 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_18269 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 18269) = 3 ^ 7 * m + 1220 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_18269.1, data_15_18269.2]

/-- Complete interval computation for depth 15, residue 18270. -/
theorem bounds_15_18270 : exactInterval 15 18270 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_18270 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 18270) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_18270 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_18270 : oddCount 18270 15 = 6 ∧ acceleratedOrbit 15 18270 = 407 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_18270 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 18270) = 3 ^ 6 * m + 407 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_18270.1, data_15_18270.2]

/-- Complete interval computation for depth 15, residue 18271. -/
theorem bounds_15_18271 : exactInterval 15 18271 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_18271 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 18271) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_18271 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_18271 : oddCount 18271 15 = 6 ∧ acceleratedOrbit 15 18271 = 407 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_18271 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 18271) = 3 ^ 6 * m + 407 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_18271.1, data_15_18271.2]

/-- Complete interval computation for depth 15, residue 18272. -/
theorem bounds_15_18272 : exactInterval 15 18272 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_18272 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 18272) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_18272 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_18272 : oddCount 18272 15 = 5 ∧ acceleratedOrbit 15 18272 = 136 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_18272 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 18272) = 3 ^ 5 * m + 136 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_18272.1, data_15_18272.2]

/-- Complete interval computation for depth 15, residue 18273. -/
theorem bounds_15_18273 : exactInterval 15 18273 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_18273 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 18273) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_18273 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_18273 : oddCount 18273 15 = 9 ∧ acceleratedOrbit 15 18273 = 10979 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_18273 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 18273) = 3 ^ 9 * m + 10979 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_18273.1, data_15_18273.2]

/-- Complete interval computation for depth 15, residue 18274. -/
theorem bounds_15_18274 : exactInterval 15 18274 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_18274 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 18274) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_18274 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_18274 : oddCount 18274 15 = 5 ∧ acceleratedOrbit 15 18274 = 136 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_18274 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 18274) = 3 ^ 5 * m + 136 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_18274.1, data_15_18274.2]

/-- Complete interval computation for depth 15, residue 18275. -/
theorem bounds_15_18275 : exactInterval 15 18275 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_18275 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 18275) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_18275 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_18275 : oddCount 18275 15 = 5 ∧ acceleratedOrbit 15 18275 = 136 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_18275 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 18275) = 3 ^ 5 * m + 136 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_18275.1, data_15_18275.2]

/-- Complete interval computation for depth 15, residue 18276. -/
theorem bounds_15_18276 : exactInterval 15 18276 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_18276 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 18276) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_18276 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_18276 : oddCount 18276 15 = 5 ∧ acceleratedOrbit 15 18276 = 136 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_18276 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 18276) = 3 ^ 5 * m + 136 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_18276.1, data_15_18276.2]

/-- Complete interval computation for depth 15, residue 18277. -/
theorem bounds_15_18277 : exactInterval 15 18277 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_18277 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 18277) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_18277 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_18277 : oddCount 18277 15 = 5 ∧ acceleratedOrbit 15 18277 = 136 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_18277 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 18277) = 3 ^ 5 * m + 136 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_18277.1, data_15_18277.2]

/-- Complete interval computation for depth 15, residue 18278. -/
theorem bounds_15_18278 : exactInterval 15 18278 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_18278 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 18278) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_18278 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_18278 : oddCount 18278 15 = 5 ∧ acceleratedOrbit 15 18278 = 136 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_18278 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 18278) = 3 ^ 5 * m + 136 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_18278.1, data_15_18278.2]

/-- Complete interval computation for depth 15, residue 18279. -/
theorem bounds_15_18279 : exactInterval 15 18279 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_18279 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 18279) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_18279 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_18279 : oddCount 18279 15 = 11 ∧ acceleratedOrbit 15 18279 = 98825 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_18279 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 18279) = 3 ^ 11 * m + 98825 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_18279.1, data_15_18279.2]

/-- Complete interval computation for depth 15, residue 18280. -/
theorem bounds_15_18280 : exactInterval 15 18280 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_18280 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 18280) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_18280 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_18280 : oddCount 18280 15 = 5 ∧ acceleratedOrbit 15 18280 = 136 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_18280 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 18280) = 3 ^ 5 * m + 136 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_18280.1, data_15_18280.2]

/-- Complete interval computation for depth 15, residue 18281. -/
theorem bounds_15_18281 : exactInterval 15 18281 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_18281 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 18281) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_18281 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_18281 : oddCount 18281 15 = 8 ∧ acceleratedOrbit 15 18281 = 3662 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_18281 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 18281) = 3 ^ 8 * m + 3662 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_18281.1, data_15_18281.2]

/-- Complete interval computation for depth 15, residue 18282. -/
theorem bounds_15_18282 : exactInterval 15 18282 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_18282 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 18282) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_18282 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_18282 : oddCount 18282 15 = 5 ∧ acceleratedOrbit 15 18282 = 136 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_18282 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 18282) = 3 ^ 5 * m + 136 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_18282.1, data_15_18282.2]

/-- Complete interval computation for depth 15, residue 18283. -/
theorem bounds_15_18283 : exactInterval 15 18283 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_18283 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 18283) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_18283 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_18283 : oddCount 18283 15 = 8 ∧ acceleratedOrbit 15 18283 = 3662 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_18283 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 18283) = 3 ^ 8 * m + 3662 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_18283.1, data_15_18283.2]

end Collatz.Research.PassageAtlas.Batch0558
