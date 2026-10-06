import Collatz.Research.DescentIntervals.Classifier

namespace Collatz.Research.PassageAtlas.Batch0924

open Collatz.Research.DescentIntervals

set_option maxRecDepth 20000
set_option maxHeartbeats 0

/-- Complete interval computation for depth 15, residue 30244. -/
theorem bounds_15_30244 : exactInterval 15 30244 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_30244 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 30244) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_30244 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_30244 : oddCount 30244 15 = 6 ∧ acceleratedOrbit 15 30244 = 673 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_30244 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 30244) = 3 ^ 6 * m + 673 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_30244.1, data_15_30244.2]

/-- Complete interval computation for depth 15, residue 30245. -/
theorem bounds_15_30245 : exactInterval 15 30245 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_30245 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 30245) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_30245 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_30245 : oddCount 30245 15 = 6 ∧ acceleratedOrbit 15 30245 = 673 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_30245 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 30245) = 3 ^ 6 * m + 673 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_30245.1, data_15_30245.2]

/-- Complete interval computation for depth 15, residue 30246. -/
theorem bounds_15_30246 : exactInterval 15 30246 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_30246 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 30246) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_30246 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_30246 : oddCount 30246 15 = 6 ∧ acceleratedOrbit 15 30246 = 673 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_30246 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 30246) = 3 ^ 6 * m + 673 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_30246.1, data_15_30246.2]

/-- Complete interval computation for depth 15, residue 30247. -/
theorem bounds_15_30247 : exactInterval 15 30247 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_30247 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 30247) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_30247 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_30247 : oddCount 30247 15 = 6 ∧ acceleratedOrbit 15 30247 = 673 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_30247 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 30247) = 3 ^ 6 * m + 673 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_30247.1, data_15_30247.2]

/-- Complete interval computation for depth 15, residue 30248. -/
theorem bounds_15_30248 : exactInterval 15 30248 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_30248 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 30248) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_30248 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_30248 : oddCount 30248 15 = 3 ∧ acceleratedOrbit 15 30248 = 25 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_30248 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 30248) = 3 ^ 3 * m + 25 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_30248.1, data_15_30248.2]

/-- Complete interval computation for depth 15, residue 30249. -/
theorem bounds_15_30249 : exactInterval 15 30249 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_30249 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 30249) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_30249 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_30249 : oddCount 30249 15 = 13 ∧ acceleratedOrbit 15 30249 = 1471850 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_30249 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 30249) = 3 ^ 13 * m + 1471850 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_30249.1, data_15_30249.2]

/-- Complete interval computation for depth 15, residue 30250. -/
theorem bounds_15_30250 : exactInterval 15 30250 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_30250 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 30250) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_30250 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_30250 : oddCount 30250 15 = 3 ∧ acceleratedOrbit 15 30250 = 25 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_30250 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 30250) = 3 ^ 3 * m + 25 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_30250.1, data_15_30250.2]

/-- Complete interval computation for depth 15, residue 30251. -/
theorem bounds_15_30251 : exactInterval 15 30251 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_30251 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 30251) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_30251 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_30251 : oddCount 30251 15 = 7 ∧ acceleratedOrbit 15 30251 = 2020 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_30251 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 30251) = 3 ^ 7 * m + 2020 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_30251.1, data_15_30251.2]

/-- Complete interval computation for depth 15, residue 30252. -/
theorem bounds_15_30252 : exactInterval 15 30252 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_30252 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 30252) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_30252 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_30252 : oddCount 30252 15 = 7 ∧ acceleratedOrbit 15 30252 = 2020 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_30252 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 30252) = 3 ^ 7 * m + 2020 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_30252.1, data_15_30252.2]

/-- Complete interval computation for depth 15, residue 30253. -/
theorem bounds_15_30253 : exactInterval 15 30253 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_30253 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 30253) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_30253 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_30253 : oddCount 30253 15 = 7 ∧ acceleratedOrbit 15 30253 = 2020 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_30253 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 30253) = 3 ^ 7 * m + 2020 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_30253.1, data_15_30253.2]

/-- Complete interval computation for depth 15, residue 30254. -/
theorem bounds_15_30254 : exactInterval 15 30254 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_30254 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 30254) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_30254 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_30254 : oddCount 30254 15 = 7 ∧ acceleratedOrbit 15 30254 = 2020 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_30254 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 30254) = 3 ^ 7 * m + 2020 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_30254.1, data_15_30254.2]

/-- Complete interval computation for depth 15, residue 30255. -/
theorem bounds_15_30255 : exactInterval 15 30255 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_30255 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 30255) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_30255 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_30255 : oddCount 30255 15 = 10 ∧ acceleratedOrbit 15 30255 = 54523 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_30255 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 30255) = 3 ^ 10 * m + 54523 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_30255.1, data_15_30255.2]

/-- Complete interval computation for depth 15, residue 30256. -/
theorem bounds_15_30256 : exactInterval 15 30256 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_30256 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 30256) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_30256 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_30256 : oddCount 30256 15 = 3 ∧ acceleratedOrbit 15 30256 = 25 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_30256 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 30256) = 3 ^ 3 * m + 25 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_30256.1, data_15_30256.2]

/-- Complete interval computation for depth 15, residue 30257. -/
theorem bounds_15_30257 : exactInterval 15 30257 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_30257 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 30257) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_30257 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_30257 : oddCount 30257 15 = 10 ∧ acceleratedOrbit 15 30257 = 54539 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_30257 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 30257) = 3 ^ 10 * m + 54539 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_30257.1, data_15_30257.2]

/-- Complete interval computation for depth 15, residue 30258. -/
theorem bounds_15_30258 : exactInterval 15 30258 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_30258 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 30258) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_30258 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_30258 : oddCount 30258 15 = 10 ∧ acceleratedOrbit 15 30258 = 54539 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_30258 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 30258) = 3 ^ 10 * m + 54539 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_30258.1, data_15_30258.2]

/-- Complete interval computation for depth 15, residue 30259. -/
theorem bounds_15_30259 : exactInterval 15 30259 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_30259 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 30259) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_30259 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_30259 : oddCount 30259 15 = 10 ∧ acceleratedOrbit 15 30259 = 54539 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_30259 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 30259) = 3 ^ 10 * m + 54539 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_30259.1, data_15_30259.2]

/-- Complete interval computation for depth 15, residue 30260. -/
theorem bounds_15_30260 : exactInterval 15 30260 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_30260 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 30260) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_30260 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_30260 : oddCount 30260 15 = 3 ∧ acceleratedOrbit 15 30260 = 25 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_30260 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 30260) = 3 ^ 3 * m + 25 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_30260.1, data_15_30260.2]

/-- Complete interval computation for depth 15, residue 30261. -/
theorem bounds_15_30261 : exactInterval 15 30261 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_30261 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 30261) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_30261 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_30261 : oddCount 30261 15 = 3 ∧ acceleratedOrbit 15 30261 = 25 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_30261 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 30261) = 3 ^ 3 * m + 25 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_30261.1, data_15_30261.2]

/-- Complete interval computation for depth 15, residue 30262. -/
theorem bounds_15_30262 : exactInterval 15 30262 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_30262 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 30262) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_30262 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_30262 : oddCount 30262 15 = 11 ∧ acceleratedOrbit 15 30262 = 163615 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_30262 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 30262) = 3 ^ 11 * m + 163615 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_30262.1, data_15_30262.2]

/-- Complete interval computation for depth 15, residue 30263. -/
theorem bounds_15_30263 : exactInterval 15 30263 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_30263 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 30263) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_30263 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_30263 : oddCount 30263 15 = 11 ∧ acceleratedOrbit 15 30263 = 163615 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_30263 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 30263) = 3 ^ 11 * m + 163615 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_30263.1, data_15_30263.2]

/-- Complete interval computation for depth 15, residue 30264. -/
theorem bounds_15_30264 : exactInterval 15 30264 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_30264 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 30264) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_30264 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_30264 : oddCount 30264 15 = 6 ∧ acceleratedOrbit 15 30264 = 674 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_30264 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 30264) = 3 ^ 6 * m + 674 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_30264.1, data_15_30264.2]

/-- Complete interval computation for depth 15, residue 30265. -/
theorem bounds_15_30265 : exactInterval 15 30265 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_30265 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 30265) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_30265 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_30265 : oddCount 30265 15 = 8 ∧ acceleratedOrbit 15 30265 = 6061 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_30265 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 30265) = 3 ^ 8 * m + 6061 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_30265.1, data_15_30265.2]

/-- Complete interval computation for depth 15, residue 30266. -/
theorem bounds_15_30266 : exactInterval 15 30266 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_30266 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 30266) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_30266 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_30266 : oddCount 30266 15 = 6 ∧ acceleratedOrbit 15 30266 = 674 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_30266 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 30266) = 3 ^ 6 * m + 674 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_30266.1, data_15_30266.2]

/-- Complete interval computation for depth 15, residue 30267. -/
theorem bounds_15_30267 : exactInterval 15 30267 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_30267 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 30267) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_30267 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_30267 : oddCount 30267 15 = 9 ∧ acceleratedOrbit 15 30267 = 18184 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_30267 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 30267) = 3 ^ 9 * m + 18184 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_30267.1, data_15_30267.2]

/-- Complete interval computation for depth 15, residue 30268. -/
theorem bounds_15_30268 : exactInterval 15 30268 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_30268 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 30268) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_30268 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_30268 : oddCount 30268 15 = 6 ∧ acceleratedOrbit 15 30268 = 674 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_30268 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 30268) = 3 ^ 6 * m + 674 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_30268.1, data_15_30268.2]

/-- Complete interval computation for depth 15, residue 30269. -/
theorem bounds_15_30269 : exactInterval 15 30269 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_30269 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 30269) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_30269 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_30269 : oddCount 30269 15 = 6 ∧ acceleratedOrbit 15 30269 = 674 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_30269 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 30269) = 3 ^ 6 * m + 674 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_30269.1, data_15_30269.2]

/-- Complete interval computation for depth 15, residue 30270. -/
theorem bounds_15_30270 : exactInterval 15 30270 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_30270 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 30270) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_30270 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_30270 : oddCount 30270 15 = 10 ∧ acceleratedOrbit 15 30270 = 54553 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_30270 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 30270) = 3 ^ 10 * m + 54553 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_30270.1, data_15_30270.2]

/-- Complete interval computation for depth 15, residue 30271. -/
theorem bounds_15_30271 : exactInterval 15 30271 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_30271 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 30271) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_30271 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_30271 : oddCount 30271 15 = 10 ∧ acceleratedOrbit 15 30271 = 54553 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_30271 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 30271) = 3 ^ 10 * m + 54553 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_30271.1, data_15_30271.2]

/-- Complete interval computation for depth 15, residue 30272. -/
theorem bounds_15_30272 : exactInterval 15 30272 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_30272 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 30272) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_30272 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_30272 : oddCount 30272 15 = 3 ∧ acceleratedOrbit 15 30272 = 25 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_30272 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 30272) = 3 ^ 3 * m + 25 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_30272.1, data_15_30272.2]

/-- Complete interval computation for depth 15, residue 30273. -/
theorem bounds_15_30273 : exactInterval 15 30273 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_30273 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 30273) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_30273 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_30273 : oddCount 30273 15 = 8 ∧ acceleratedOrbit 15 30273 = 6065 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_30273 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 30273) = 3 ^ 8 * m + 6065 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_30273.1, data_15_30273.2]

/-- Complete interval computation for depth 15, residue 30274. -/
theorem bounds_15_30274 : exactInterval 15 30274 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_30274 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 30274) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_30274 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_30274 : oddCount 30274 15 = 8 ∧ acceleratedOrbit 15 30274 = 6065 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_30274 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 30274) = 3 ^ 8 * m + 6065 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_30274.1, data_15_30274.2]

/-- Complete interval computation for depth 15, residue 30275. -/
theorem bounds_15_30275 : exactInterval 15 30275 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_30275 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 30275) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_30275 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_30275 : oddCount 30275 15 = 8 ∧ acceleratedOrbit 15 30275 = 6065 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_30275 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 30275) = 3 ^ 8 * m + 6065 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_30275.1, data_15_30275.2]

/-- Complete interval computation for depth 15, residue 30276. -/
theorem bounds_15_30276 : exactInterval 15 30276 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_30276 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 30276) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_30276 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_30276 : oddCount 30276 15 = 7 ∧ acceleratedOrbit 15 30276 = 2024 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_30276 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 30276) = 3 ^ 7 * m + 2024 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_30276.1, data_15_30276.2]

end Collatz.Research.PassageAtlas.Batch0924
