import Collatz.Research.DescentIntervals.Classifier

namespace Collatz.Research.StoppingAtlas.Batch0154

open Collatz.Research.DescentIntervals

set_option maxRecDepth 20000
set_option maxHeartbeats 0

/-- Complete interval computation for depth 11, residue 1326. -/
theorem bounds_11_1326 : exactInterval 11 1326 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_11_1326 (m : Nat) :
    stoppingTime (2 ^ 11 * m + 1326) 11 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_11_1326 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_11_1326 : oddCount 1326 11 = 4 ∧ acceleratedOrbit 11 1326 = 53 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_11_1326 (m : Nat) :
    acceleratedOrbit 11 (2 ^ 11 * m + 1326) = 3 ^ 4 * m + 53 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_11_1326.1, data_11_1326.2]

/-- Complete interval computation for depth 11, residue 1327. -/
theorem bounds_11_1327 : exactInterval 11 1327 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_11_1327 (m : Nat) :
    stoppingTime (2 ^ 11 * m + 1327) 11 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_11_1327 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_11_1327 : oddCount 1327 11 = 8 ∧ acceleratedOrbit 11 1327 = 4256 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_11_1327 (m : Nat) :
    acceleratedOrbit 11 (2 ^ 11 * m + 1327) = 3 ^ 8 * m + 4256 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_11_1327.1, data_11_1327.2]

/-- Complete interval computation for depth 11, residue 1328. -/
theorem bounds_11_1328 : exactInterval 11 1328 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_11_1328 (m : Nat) :
    stoppingTime (2 ^ 11 * m + 1328) 11 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_11_1328 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_11_1328 : oddCount 1328 11 = 5 ∧ acceleratedOrbit 11 1328 = 161 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_11_1328 (m : Nat) :
    acceleratedOrbit 11 (2 ^ 11 * m + 1328) = 3 ^ 5 * m + 161 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_11_1328.1, data_11_1328.2]

/-- Complete interval computation for depth 11, residue 1329. -/
theorem bounds_11_1329 : exactInterval 11 1329 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_11_1329 (m : Nat) :
    stoppingTime (2 ^ 11 * m + 1329) 11 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_11_1329 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_11_1329 : oddCount 1329 11 = 6 ∧ acceleratedOrbit 11 1329 = 476 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_11_1329 (m : Nat) :
    acceleratedOrbit 11 (2 ^ 11 * m + 1329) = 3 ^ 6 * m + 476 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_11_1329.1, data_11_1329.2]

/-- Complete interval computation for depth 11, residue 1330. -/
theorem bounds_11_1330 : exactInterval 11 1330 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_11_1330 (m : Nat) :
    stoppingTime (2 ^ 11 * m + 1330) 11 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_11_1330 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_11_1330 : oddCount 1330 11 = 6 ∧ acceleratedOrbit 11 1330 = 476 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_11_1330 (m : Nat) :
    acceleratedOrbit 11 (2 ^ 11 * m + 1330) = 3 ^ 6 * m + 476 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_11_1330.1, data_11_1330.2]

/-- Complete interval computation for depth 11, residue 1331. -/
theorem bounds_11_1331 : exactInterval 11 1331 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_11_1331 (m : Nat) :
    stoppingTime (2 ^ 11 * m + 1331) 11 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_11_1331 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_11_1331 : oddCount 1331 11 = 6 ∧ acceleratedOrbit 11 1331 = 476 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_11_1331 (m : Nat) :
    acceleratedOrbit 11 (2 ^ 11 * m + 1331) = 3 ^ 6 * m + 476 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_11_1331.1, data_11_1331.2]

/-- Complete interval computation for depth 11, residue 1332. -/
theorem bounds_11_1332 : exactInterval 11 1332 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_11_1332 (m : Nat) :
    stoppingTime (2 ^ 11 * m + 1332) 11 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_11_1332 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_11_1332 : oddCount 1332 11 = 5 ∧ acceleratedOrbit 11 1332 = 161 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_11_1332 (m : Nat) :
    acceleratedOrbit 11 (2 ^ 11 * m + 1332) = 3 ^ 5 * m + 161 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_11_1332.1, data_11_1332.2]

/-- Complete interval computation for depth 11, residue 1333. -/
theorem bounds_11_1333 : exactInterval 11 1333 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_11_1333 (m : Nat) :
    stoppingTime (2 ^ 11 * m + 1333) 11 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_11_1333 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_11_1333 : oddCount 1333 11 = 5 ∧ acceleratedOrbit 11 1333 = 161 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_11_1333 (m : Nat) :
    acceleratedOrbit 11 (2 ^ 11 * m + 1333) = 3 ^ 5 * m + 161 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_11_1333.1, data_11_1333.2]

/-- Complete interval computation for depth 11, residue 1334. -/
theorem bounds_11_1334 : exactInterval 11 1334 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_11_1334 (m : Nat) :
    stoppingTime (2 ^ 11 * m + 1334) 11 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_11_1334 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_11_1334 : oddCount 1334 11 = 8 ∧ acceleratedOrbit 11 1334 = 4283 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_11_1334 (m : Nat) :
    acceleratedOrbit 11 (2 ^ 11 * m + 1334) = 3 ^ 8 * m + 4283 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_11_1334.1, data_11_1334.2]

/-- Complete interval computation for depth 11, residue 1335. -/
theorem bounds_11_1335 : exactInterval 11 1335 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_11_1335 (m : Nat) :
    stoppingTime (2 ^ 11 * m + 1335) 11 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_11_1335 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_11_1335 : oddCount 1335 11 = 8 ∧ acceleratedOrbit 11 1335 = 4283 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_11_1335 (m : Nat) :
    acceleratedOrbit 11 (2 ^ 11 * m + 1335) = 3 ^ 8 * m + 4283 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_11_1335.1, data_11_1335.2]

/-- Complete interval computation for depth 11, residue 1336. -/
theorem bounds_11_1336 : exactInterval 11 1336 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_11_1336 (m : Nat) :
    stoppingTime (2 ^ 11 * m + 1336) 11 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_11_1336 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_11_1336 : oddCount 1336 11 = 6 ∧ acceleratedOrbit 11 1336 = 479 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_11_1336 (m : Nat) :
    acceleratedOrbit 11 (2 ^ 11 * m + 1336) = 3 ^ 6 * m + 479 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_11_1336.1, data_11_1336.2]

/-- Complete interval computation for depth 11, residue 1337. -/
theorem bounds_11_1337 : exactInterval 11 1337 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_11_1337 (m : Nat) :
    stoppingTime (2 ^ 11 * m + 1337) 11 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_11_1337 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_11_1337 : oddCount 1337 11 = 8 ∧ acceleratedOrbit 11 1337 = 4292 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_11_1337 (m : Nat) :
    acceleratedOrbit 11 (2 ^ 11 * m + 1337) = 3 ^ 8 * m + 4292 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_11_1337.1, data_11_1337.2]

/-- Complete interval computation for depth 11, residue 1338. -/
theorem bounds_11_1338 : exactInterval 11 1338 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_11_1338 (m : Nat) :
    stoppingTime (2 ^ 11 * m + 1338) 11 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_11_1338 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_11_1338 : oddCount 1338 11 = 6 ∧ acceleratedOrbit 11 1338 = 479 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_11_1338 (m : Nat) :
    acceleratedOrbit 11 (2 ^ 11 * m + 1338) = 3 ^ 6 * m + 479 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_11_1338.1, data_11_1338.2]

/-- Complete interval computation for depth 11, residue 1339. -/
theorem bounds_11_1339 : exactInterval 11 1339 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_11_1339 (m : Nat) :
    stoppingTime (2 ^ 11 * m + 1339) 11 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_11_1339 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_11_1339 : oddCount 1339 11 = 4 ∧ acceleratedOrbit 11 1339 = 53 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_11_1339 (m : Nat) :
    acceleratedOrbit 11 (2 ^ 11 * m + 1339) = 3 ^ 4 * m + 53 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_11_1339.1, data_11_1339.2]

/-- Complete interval computation for depth 11, residue 1340. -/
theorem bounds_11_1340 : exactInterval 11 1340 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_11_1340 (m : Nat) :
    stoppingTime (2 ^ 11 * m + 1340) 11 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_11_1340 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_11_1340 : oddCount 1340 11 = 6 ∧ acceleratedOrbit 11 1340 = 479 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_11_1340 (m : Nat) :
    acceleratedOrbit 11 (2 ^ 11 * m + 1340) = 3 ^ 6 * m + 479 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_11_1340.1, data_11_1340.2]

end Collatz.Research.StoppingAtlas.Batch0154
