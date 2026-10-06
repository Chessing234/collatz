import Collatz.Research.DescentIntervals.Classifier

namespace Collatz.Research.StoppingAtlas.Batch0940

open Collatz.Research.DescentIntervals

set_option maxRecDepth 20000
set_option maxHeartbeats 0

/-- Complete interval computation for depth 13, residue 7255. -/
theorem bounds_13_7255 : exactInterval 13 7255 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_13_7255 (m : Nat) :
    stoppingTime (2 ^ 13 * m + 7255) 13 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_13_7255 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_13_7255 : oddCount 7255 13 = 6 ∧ acceleratedOrbit 13 7255 = 647 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_13_7255 (m : Nat) :
    acceleratedOrbit 13 (2 ^ 13 * m + 7255) = 3 ^ 6 * m + 647 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_13_7255.1, data_13_7255.2]

/-- Complete interval computation for depth 13, residue 7256. -/
theorem bounds_13_7256 : exactInterval 13 7256 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_13_7256 (m : Nat) :
    stoppingTime (2 ^ 13 * m + 7256) 13 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_13_7256 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_13_7256 : oddCount 7256 13 = 7 ∧ acceleratedOrbit 13 7256 = 1943 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_13_7256 (m : Nat) :
    acceleratedOrbit 13 (2 ^ 13 * m + 7256) = 3 ^ 7 * m + 1943 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_13_7256.1, data_13_7256.2]

/-- Complete interval computation for depth 13, residue 7257. -/
theorem bounds_13_7257 : exactInterval 13 7257 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_13_7257 (m : Nat) :
    stoppingTime (2 ^ 13 * m + 7257) 13 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_13_7257 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_13_7257 : oddCount 7257 13 = 7 ∧ acceleratedOrbit 13 7257 = 1939 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_13_7257 (m : Nat) :
    acceleratedOrbit 13 (2 ^ 13 * m + 7257) = 3 ^ 7 * m + 1939 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_13_7257.1, data_13_7257.2]

/-- Complete interval computation for depth 13, residue 7258. -/
theorem bounds_13_7258 : exactInterval 13 7258 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_13_7258 (m : Nat) :
    stoppingTime (2 ^ 13 * m + 7258) 13 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_13_7258 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_13_7258 : oddCount 7258 13 = 7 ∧ acceleratedOrbit 13 7258 = 1943 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_13_7258 (m : Nat) :
    acceleratedOrbit 13 (2 ^ 13 * m + 7258) = 3 ^ 7 * m + 1943 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_13_7258.1, data_13_7258.2]

/-- Complete interval computation for depth 13, residue 7259. -/
theorem bounds_13_7259 : exactInterval 13 7259 = ⟨0, none⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_13_7259 (m : Nat) :
    stoppingTime (2 ^ 13 * m + 7259) 13 ↔ 0 ≤ m := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_13_7259 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_13_7259 : oddCount 7259 13 = 8 ∧ acceleratedOrbit 13 7259 = 5815 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_13_7259 (m : Nat) :
    acceleratedOrbit 13 (2 ^ 13 * m + 7259) = 3 ^ 8 * m + 5815 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_13_7259.1, data_13_7259.2]

/-- Complete interval computation for depth 13, residue 7260. -/
theorem bounds_13_7260 : exactInterval 13 7260 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_13_7260 (m : Nat) :
    stoppingTime (2 ^ 13 * m + 7260) 13 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_13_7260 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_13_7260 : oddCount 7260 13 = 7 ∧ acceleratedOrbit 13 7260 = 1943 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_13_7260 (m : Nat) :
    acceleratedOrbit 13 (2 ^ 13 * m + 7260) = 3 ^ 7 * m + 1943 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_13_7260.1, data_13_7260.2]

/-- Complete interval computation for depth 13, residue 7261. -/
theorem bounds_13_7261 : exactInterval 13 7261 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_13_7261 (m : Nat) :
    stoppingTime (2 ^ 13 * m + 7261) 13 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_13_7261 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_13_7261 : oddCount 7261 13 = 7 ∧ acceleratedOrbit 13 7261 = 1943 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_13_7261 (m : Nat) :
    acceleratedOrbit 13 (2 ^ 13 * m + 7261) = 3 ^ 7 * m + 1943 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_13_7261.1, data_13_7261.2]

/-- Complete interval computation for depth 13, residue 7262. -/
theorem bounds_13_7262 : exactInterval 13 7262 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_13_7262 (m : Nat) :
    stoppingTime (2 ^ 13 * m + 7262) 13 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_13_7262 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_13_7262 : oddCount 7262 13 = 9 ∧ acceleratedOrbit 13 7262 = 17455 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_13_7262 (m : Nat) :
    acceleratedOrbit 13 (2 ^ 13 * m + 7262) = 3 ^ 9 * m + 17455 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_13_7262.1, data_13_7262.2]

/-- Complete interval computation for depth 13, residue 7263. -/
theorem bounds_13_7263 : exactInterval 13 7263 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_13_7263 (m : Nat) :
    stoppingTime (2 ^ 13 * m + 7263) 13 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_13_7263 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_13_7263 : oddCount 7263 13 = 9 ∧ acceleratedOrbit 13 7263 = 17455 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_13_7263 (m : Nat) :
    acceleratedOrbit 13 (2 ^ 13 * m + 7263) = 3 ^ 9 * m + 17455 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_13_7263.1, data_13_7263.2]

/-- Complete interval computation for depth 13, residue 7264. -/
theorem bounds_13_7264 : exactInterval 13 7264 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_13_7264 (m : Nat) :
    stoppingTime (2 ^ 13 * m + 7264) 13 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_13_7264 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_13_7264 : oddCount 7264 13 = 2 ∧ acceleratedOrbit 13 7264 = 8 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_13_7264 (m : Nat) :
    acceleratedOrbit 13 (2 ^ 13 * m + 7264) = 3 ^ 2 * m + 8 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_13_7264.1, data_13_7264.2]

/-- Complete interval computation for depth 13, residue 7265. -/
theorem bounds_13_7265 : exactInterval 13 7265 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_13_7265 (m : Nat) :
    stoppingTime (2 ^ 13 * m + 7265) 13 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_13_7265 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_13_7265 : oddCount 7265 13 = 8 ∧ acceleratedOrbit 13 7265 = 5822 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_13_7265 (m : Nat) :
    acceleratedOrbit 13 (2 ^ 13 * m + 7265) = 3 ^ 8 * m + 5822 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_13_7265.1, data_13_7265.2]

/-- Complete interval computation for depth 13, residue 7266. -/
theorem bounds_13_7266 : exactInterval 13 7266 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_13_7266 (m : Nat) :
    stoppingTime (2 ^ 13 * m + 7266) 13 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_13_7266 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_13_7266 : oddCount 7266 13 = 8 ∧ acceleratedOrbit 13 7266 = 5831 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_13_7266 (m : Nat) :
    acceleratedOrbit 13 (2 ^ 13 * m + 7266) = 3 ^ 8 * m + 5831 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_13_7266.1, data_13_7266.2]

/-- Complete interval computation for depth 13, residue 7267. -/
theorem bounds_13_7267 : exactInterval 13 7267 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_13_7267 (m : Nat) :
    stoppingTime (2 ^ 13 * m + 7267) 13 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_13_7267 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_13_7267 : oddCount 7267 13 = 8 ∧ acceleratedOrbit 13 7267 = 5831 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_13_7267 (m : Nat) :
    acceleratedOrbit 13 (2 ^ 13 * m + 7267) = 3 ^ 8 * m + 5831 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_13_7267.1, data_13_7267.2]

/-- Complete interval computation for depth 13, residue 7268. -/
theorem bounds_13_7268 : exactInterval 13 7268 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_13_7268 (m : Nat) :
    stoppingTime (2 ^ 13 * m + 7268) 13 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_13_7268 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_13_7268 : oddCount 7268 13 = 8 ∧ acceleratedOrbit 13 7268 = 5831 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_13_7268 (m : Nat) :
    acceleratedOrbit 13 (2 ^ 13 * m + 7268) = 3 ^ 8 * m + 5831 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_13_7268.1, data_13_7268.2]

/-- Complete interval computation for depth 13, residue 7269. -/
theorem bounds_13_7269 : exactInterval 13 7269 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_13_7269 (m : Nat) :
    stoppingTime (2 ^ 13 * m + 7269) 13 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_13_7269 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_13_7269 : oddCount 7269 13 = 8 ∧ acceleratedOrbit 13 7269 = 5831 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_13_7269 (m : Nat) :
    acceleratedOrbit 13 (2 ^ 13 * m + 7269) = 3 ^ 8 * m + 5831 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_13_7269.1, data_13_7269.2]

end Collatz.Research.StoppingAtlas.Batch0940
