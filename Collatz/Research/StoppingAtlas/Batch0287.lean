import Collatz.Research.DescentIntervals.Classifier

namespace Collatz.Research.StoppingAtlas.Batch0287

open Collatz.Research.DescentIntervals

set_option maxRecDepth 20000
set_option maxHeartbeats 0

/-- Complete interval computation for depth 12, residue 1320. -/
theorem bounds_12_1320 : exactInterval 12 1320 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_12_1320 (m : Nat) :
    stoppingTime (2 ^ 12 * m + 1320) 12 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_12_1320 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_12_1320 : oddCount 1320 12 = 6 ∧ acceleratedOrbit 12 1320 = 242 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_12_1320 (m : Nat) :
    acceleratedOrbit 12 (2 ^ 12 * m + 1320) = 3 ^ 6 * m + 242 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_12_1320.1, data_12_1320.2]

/-- Complete interval computation for depth 12, residue 1321. -/
theorem bounds_12_1321 : exactInterval 12 1321 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_12_1321 (m : Nat) :
    stoppingTime (2 ^ 12 * m + 1321) 12 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_12_1321 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_12_1321 : oddCount 1321 12 = 8 ∧ acceleratedOrbit 12 1321 = 2119 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_12_1321 (m : Nat) :
    acceleratedOrbit 12 (2 ^ 12 * m + 1321) = 3 ^ 8 * m + 2119 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_12_1321.1, data_12_1321.2]

/-- Complete interval computation for depth 12, residue 1322. -/
theorem bounds_12_1322 : exactInterval 12 1322 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_12_1322 (m : Nat) :
    stoppingTime (2 ^ 12 * m + 1322) 12 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_12_1322 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_12_1322 : oddCount 1322 12 = 6 ∧ acceleratedOrbit 12 1322 = 242 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_12_1322 (m : Nat) :
    acceleratedOrbit 12 (2 ^ 12 * m + 1322) = 3 ^ 6 * m + 242 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_12_1322.1, data_12_1322.2]

/-- Complete interval computation for depth 12, residue 1323. -/
theorem bounds_12_1323 : exactInterval 12 1323 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_12_1323 (m : Nat) :
    stoppingTime (2 ^ 12 * m + 1323) 12 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_12_1323 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_12_1323 : oddCount 1323 12 = 6 ∧ acceleratedOrbit 12 1323 = 236 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_12_1323 (m : Nat) :
    acceleratedOrbit 12 (2 ^ 12 * m + 1323) = 3 ^ 6 * m + 236 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_12_1323.1, data_12_1323.2]

/-- Complete interval computation for depth 12, residue 1324. -/
theorem bounds_12_1324 : exactInterval 12 1324 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_12_1324 (m : Nat) :
    stoppingTime (2 ^ 12 * m + 1324) 12 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_12_1324 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_12_1324 : oddCount 1324 12 = 5 ∧ acceleratedOrbit 12 1324 = 80 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_12_1324 (m : Nat) :
    acceleratedOrbit 12 (2 ^ 12 * m + 1324) = 3 ^ 5 * m + 80 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_12_1324.1, data_12_1324.2]

/-- Complete interval computation for depth 12, residue 1325. -/
theorem bounds_12_1325 : exactInterval 12 1325 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_12_1325 (m : Nat) :
    stoppingTime (2 ^ 12 * m + 1325) 12 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_12_1325 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_12_1325 : oddCount 1325 12 = 5 ∧ acceleratedOrbit 12 1325 = 80 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_12_1325 (m : Nat) :
    acceleratedOrbit 12 (2 ^ 12 * m + 1325) = 3 ^ 5 * m + 80 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_12_1325.1, data_12_1325.2]

/-- Complete interval computation for depth 12, residue 1326. -/
theorem bounds_12_1326 : exactInterval 12 1326 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_12_1326 (m : Nat) :
    stoppingTime (2 ^ 12 * m + 1326) 12 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_12_1326 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_12_1326 : oddCount 1326 12 = 5 ∧ acceleratedOrbit 12 1326 = 80 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_12_1326 (m : Nat) :
    acceleratedOrbit 12 (2 ^ 12 * m + 1326) = 3 ^ 5 * m + 80 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_12_1326.1, data_12_1326.2]

/-- Complete interval computation for depth 12, residue 1327. -/
theorem bounds_12_1327 : exactInterval 12 1327 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_12_1327 (m : Nat) :
    stoppingTime (2 ^ 12 * m + 1327) 12 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_12_1327 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_12_1327 : oddCount 1327 12 = 8 ∧ acceleratedOrbit 12 1327 = 2128 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_12_1327 (m : Nat) :
    acceleratedOrbit 12 (2 ^ 12 * m + 1327) = 3 ^ 8 * m + 2128 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_12_1327.1, data_12_1327.2]

/-- Complete interval computation for depth 12, residue 1328. -/
theorem bounds_12_1328 : exactInterval 12 1328 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_12_1328 (m : Nat) :
    stoppingTime (2 ^ 12 * m + 1328) 12 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_12_1328 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_12_1328 : oddCount 1328 12 = 6 ∧ acceleratedOrbit 12 1328 = 242 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_12_1328 (m : Nat) :
    acceleratedOrbit 12 (2 ^ 12 * m + 1328) = 3 ^ 6 * m + 242 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_12_1328.1, data_12_1328.2]

/-- Complete interval computation for depth 12, residue 1329. -/
theorem bounds_12_1329 : exactInterval 12 1329 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_12_1329 (m : Nat) :
    stoppingTime (2 ^ 12 * m + 1329) 12 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_12_1329 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_12_1329 : oddCount 1329 12 = 6 ∧ acceleratedOrbit 12 1329 = 238 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_12_1329 (m : Nat) :
    acceleratedOrbit 12 (2 ^ 12 * m + 1329) = 3 ^ 6 * m + 238 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_12_1329.1, data_12_1329.2]

/-- Complete interval computation for depth 12, residue 1330. -/
theorem bounds_12_1330 : exactInterval 12 1330 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_12_1330 (m : Nat) :
    stoppingTime (2 ^ 12 * m + 1330) 12 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_12_1330 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_12_1330 : oddCount 1330 12 = 6 ∧ acceleratedOrbit 12 1330 = 238 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_12_1330 (m : Nat) :
    acceleratedOrbit 12 (2 ^ 12 * m + 1330) = 3 ^ 6 * m + 238 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_12_1330.1, data_12_1330.2]

/-- Complete interval computation for depth 12, residue 1331. -/
theorem bounds_12_1331 : exactInterval 12 1331 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_12_1331 (m : Nat) :
    stoppingTime (2 ^ 12 * m + 1331) 12 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_12_1331 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_12_1331 : oddCount 1331 12 = 6 ∧ acceleratedOrbit 12 1331 = 238 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_12_1331 (m : Nat) :
    acceleratedOrbit 12 (2 ^ 12 * m + 1331) = 3 ^ 6 * m + 238 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_12_1331.1, data_12_1331.2]

/-- Complete interval computation for depth 12, residue 1332. -/
theorem bounds_12_1332 : exactInterval 12 1332 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_12_1332 (m : Nat) :
    stoppingTime (2 ^ 12 * m + 1332) 12 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_12_1332 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_12_1332 : oddCount 1332 12 = 6 ∧ acceleratedOrbit 12 1332 = 242 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_12_1332 (m : Nat) :
    acceleratedOrbit 12 (2 ^ 12 * m + 1332) = 3 ^ 6 * m + 242 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_12_1332.1, data_12_1332.2]

/-- Complete interval computation for depth 12, residue 1333. -/
theorem bounds_12_1333 : exactInterval 12 1333 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_12_1333 (m : Nat) :
    stoppingTime (2 ^ 12 * m + 1333) 12 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_12_1333 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_12_1333 : oddCount 1333 12 = 6 ∧ acceleratedOrbit 12 1333 = 242 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_12_1333 (m : Nat) :
    acceleratedOrbit 12 (2 ^ 12 * m + 1333) = 3 ^ 6 * m + 242 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_12_1333.1, data_12_1333.2]

/-- Complete interval computation for depth 12, residue 1334. -/
theorem bounds_12_1334 : exactInterval 12 1334 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_12_1334 (m : Nat) :
    stoppingTime (2 ^ 12 * m + 1334) 12 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_12_1334 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_12_1334 : oddCount 1334 12 = 9 ∧ acceleratedOrbit 12 1334 = 6425 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_12_1334 (m : Nat) :
    acceleratedOrbit 12 (2 ^ 12 * m + 1334) = 3 ^ 9 * m + 6425 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_12_1334.1, data_12_1334.2]

/-- Complete interval computation for depth 12, residue 1335. -/
theorem bounds_12_1335 : exactInterval 12 1335 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_12_1335 (m : Nat) :
    stoppingTime (2 ^ 12 * m + 1335) 12 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_12_1335 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_12_1335 : oddCount 1335 12 = 9 ∧ acceleratedOrbit 12 1335 = 6425 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_12_1335 (m : Nat) :
    acceleratedOrbit 12 (2 ^ 12 * m + 1335) = 3 ^ 9 * m + 6425 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_12_1335.1, data_12_1335.2]

end Collatz.Research.StoppingAtlas.Batch0287
