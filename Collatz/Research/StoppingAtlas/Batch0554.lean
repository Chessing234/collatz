import Collatz.Research.DescentIntervals.Classifier

namespace Collatz.Research.StoppingAtlas.Batch0554

open Collatz.Research.DescentIntervals

set_option maxRecDepth 20000
set_option maxHeartbeats 0

/-- Complete interval computation for depth 13, residue 1326. -/
theorem bounds_13_1326 : exactInterval 13 1326 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_13_1326 (m : Nat) :
    stoppingTime (2 ^ 13 * m + 1326) 13 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_13_1326 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_13_1326 : oddCount 1326 13 = 5 ∧ acceleratedOrbit 13 1326 = 40 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_13_1326 (m : Nat) :
    acceleratedOrbit 13 (2 ^ 13 * m + 1326) = 3 ^ 5 * m + 40 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_13_1326.1, data_13_1326.2]

/-- Complete interval computation for depth 13, residue 1327. -/
theorem bounds_13_1327 : exactInterval 13 1327 = ⟨0, none⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_13_1327 (m : Nat) :
    stoppingTime (2 ^ 13 * m + 1327) 13 ↔ 0 ≤ m := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_13_1327 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_13_1327 : oddCount 1327 13 = 8 ∧ acceleratedOrbit 13 1327 = 1064 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_13_1327 (m : Nat) :
    acceleratedOrbit 13 (2 ^ 13 * m + 1327) = 3 ^ 8 * m + 1064 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_13_1327.1, data_13_1327.2]

/-- Complete interval computation for depth 13, residue 1328. -/
theorem bounds_13_1328 : exactInterval 13 1328 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_13_1328 (m : Nat) :
    stoppingTime (2 ^ 13 * m + 1328) 13 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_13_1328 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_13_1328 : oddCount 1328 13 = 6 ∧ acceleratedOrbit 13 1328 = 121 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_13_1328 (m : Nat) :
    acceleratedOrbit 13 (2 ^ 13 * m + 1328) = 3 ^ 6 * m + 121 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_13_1328.1, data_13_1328.2]

/-- Complete interval computation for depth 13, residue 1329. -/
theorem bounds_13_1329 : exactInterval 13 1329 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_13_1329 (m : Nat) :
    stoppingTime (2 ^ 13 * m + 1329) 13 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_13_1329 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_13_1329 : oddCount 1329 13 = 6 ∧ acceleratedOrbit 13 1329 = 119 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_13_1329 (m : Nat) :
    acceleratedOrbit 13 (2 ^ 13 * m + 1329) = 3 ^ 6 * m + 119 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_13_1329.1, data_13_1329.2]

/-- Complete interval computation for depth 13, residue 1330. -/
theorem bounds_13_1330 : exactInterval 13 1330 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_13_1330 (m : Nat) :
    stoppingTime (2 ^ 13 * m + 1330) 13 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_13_1330 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_13_1330 : oddCount 1330 13 = 6 ∧ acceleratedOrbit 13 1330 = 119 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_13_1330 (m : Nat) :
    acceleratedOrbit 13 (2 ^ 13 * m + 1330) = 3 ^ 6 * m + 119 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_13_1330.1, data_13_1330.2]

/-- Complete interval computation for depth 13, residue 1331. -/
theorem bounds_13_1331 : exactInterval 13 1331 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_13_1331 (m : Nat) :
    stoppingTime (2 ^ 13 * m + 1331) 13 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_13_1331 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_13_1331 : oddCount 1331 13 = 6 ∧ acceleratedOrbit 13 1331 = 119 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_13_1331 (m : Nat) :
    acceleratedOrbit 13 (2 ^ 13 * m + 1331) = 3 ^ 6 * m + 119 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_13_1331.1, data_13_1331.2]

/-- Complete interval computation for depth 13, residue 1332. -/
theorem bounds_13_1332 : exactInterval 13 1332 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_13_1332 (m : Nat) :
    stoppingTime (2 ^ 13 * m + 1332) 13 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_13_1332 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_13_1332 : oddCount 1332 13 = 6 ∧ acceleratedOrbit 13 1332 = 121 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_13_1332 (m : Nat) :
    acceleratedOrbit 13 (2 ^ 13 * m + 1332) = 3 ^ 6 * m + 121 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_13_1332.1, data_13_1332.2]

/-- Complete interval computation for depth 13, residue 1333. -/
theorem bounds_13_1333 : exactInterval 13 1333 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_13_1333 (m : Nat) :
    stoppingTime (2 ^ 13 * m + 1333) 13 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_13_1333 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_13_1333 : oddCount 1333 13 = 6 ∧ acceleratedOrbit 13 1333 = 121 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_13_1333 (m : Nat) :
    acceleratedOrbit 13 (2 ^ 13 * m + 1333) = 3 ^ 6 * m + 121 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_13_1333.1, data_13_1333.2]

/-- Complete interval computation for depth 13, residue 1334. -/
theorem bounds_13_1334 : exactInterval 13 1334 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_13_1334 (m : Nat) :
    stoppingTime (2 ^ 13 * m + 1334) 13 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_13_1334 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_13_1334 : oddCount 1334 13 = 10 ∧ acceleratedOrbit 13 1334 = 9638 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_13_1334 (m : Nat) :
    acceleratedOrbit 13 (2 ^ 13 * m + 1334) = 3 ^ 10 * m + 9638 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_13_1334.1, data_13_1334.2]

/-- Complete interval computation for depth 13, residue 1335. -/
theorem bounds_13_1335 : exactInterval 13 1335 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_13_1335 (m : Nat) :
    stoppingTime (2 ^ 13 * m + 1335) 13 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_13_1335 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_13_1335 : oddCount 1335 13 = 10 ∧ acceleratedOrbit 13 1335 = 9638 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_13_1335 (m : Nat) :
    acceleratedOrbit 13 (2 ^ 13 * m + 1335) = 3 ^ 10 * m + 9638 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_13_1335.1, data_13_1335.2]

/-- Complete interval computation for depth 13, residue 1336. -/
theorem bounds_13_1336 : exactInterval 13 1336 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_13_1336 (m : Nat) :
    stoppingTime (2 ^ 13 * m + 1336) 13 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_13_1336 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_13_1336 : oddCount 1336 13 = 8 ∧ acceleratedOrbit 13 1336 = 1079 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_13_1336 (m : Nat) :
    acceleratedOrbit 13 (2 ^ 13 * m + 1336) = 3 ^ 8 * m + 1079 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_13_1336.1, data_13_1336.2]

/-- Complete interval computation for depth 13, residue 1337. -/
theorem bounds_13_1337 : exactInterval 13 1337 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_13_1337 (m : Nat) :
    stoppingTime (2 ^ 13 * m + 1337) 13 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_13_1337 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_13_1337 : oddCount 1337 13 = 8 ∧ acceleratedOrbit 13 1337 = 1073 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_13_1337 (m : Nat) :
    acceleratedOrbit 13 (2 ^ 13 * m + 1337) = 3 ^ 8 * m + 1073 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_13_1337.1, data_13_1337.2]

/-- Complete interval computation for depth 13, residue 1338. -/
theorem bounds_13_1338 : exactInterval 13 1338 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_13_1338 (m : Nat) :
    stoppingTime (2 ^ 13 * m + 1338) 13 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_13_1338 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_13_1338 : oddCount 1338 13 = 8 ∧ acceleratedOrbit 13 1338 = 1079 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_13_1338 (m : Nat) :
    acceleratedOrbit 13 (2 ^ 13 * m + 1338) = 3 ^ 8 * m + 1079 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_13_1338.1, data_13_1338.2]

/-- Complete interval computation for depth 13, residue 1339. -/
theorem bounds_13_1339 : exactInterval 13 1339 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_13_1339 (m : Nat) :
    stoppingTime (2 ^ 13 * m + 1339) 13 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_13_1339 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_13_1339 : oddCount 1339 13 = 5 ∧ acceleratedOrbit 13 1339 = 40 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_13_1339 (m : Nat) :
    acceleratedOrbit 13 (2 ^ 13 * m + 1339) = 3 ^ 5 * m + 40 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_13_1339.1, data_13_1339.2]

/-- Complete interval computation for depth 13, residue 1340. -/
theorem bounds_13_1340 : exactInterval 13 1340 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_13_1340 (m : Nat) :
    stoppingTime (2 ^ 13 * m + 1340) 13 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_13_1340 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_13_1340 : oddCount 1340 13 = 8 ∧ acceleratedOrbit 13 1340 = 1079 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_13_1340 (m : Nat) :
    acceleratedOrbit 13 (2 ^ 13 * m + 1340) = 3 ^ 8 * m + 1079 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_13_1340.1, data_13_1340.2]

end Collatz.Research.StoppingAtlas.Batch0554
