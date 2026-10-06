import Collatz.Research.DescentIntervals.Classifier

namespace Collatz.Research.StoppingAtlas.Batch0286

open Collatz.Research.DescentIntervals

set_option maxRecDepth 20000
set_option maxHeartbeats 0

/-- Complete interval computation for depth 12, residue 1305. -/
theorem bounds_12_1305 : exactInterval 12 1305 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_12_1305 (m : Nat) :
    stoppingTime (2 ^ 12 * m + 1305) 12 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_12_1305 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_12_1305 : oddCount 1305 12 = 8 ∧ acceleratedOrbit 12 1305 = 2096 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_12_1305 (m : Nat) :
    acceleratedOrbit 12 (2 ^ 12 * m + 1305) = 3 ^ 8 * m + 2096 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_12_1305.1, data_12_1305.2]

/-- Complete interval computation for depth 12, residue 1306. -/
theorem bounds_12_1306 : exactInterval 12 1306 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_12_1306 (m : Nat) :
    stoppingTime (2 ^ 12 * m + 1306) 12 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_12_1306 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_12_1306 : oddCount 1306 12 = 5 ∧ acceleratedOrbit 12 1306 = 80 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_12_1306 (m : Nat) :
    acceleratedOrbit 12 (2 ^ 12 * m + 1306) = 3 ^ 5 * m + 80 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_12_1306.1, data_12_1306.2]

/-- Complete interval computation for depth 12, residue 1307. -/
theorem bounds_12_1307 : exactInterval 12 1307 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_12_1307 (m : Nat) :
    stoppingTime (2 ^ 12 * m + 1307) 12 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_12_1307 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_12_1307 : oddCount 1307 12 = 10 ∧ acceleratedOrbit 12 1307 = 18863 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_12_1307 (m : Nat) :
    acceleratedOrbit 12 (2 ^ 12 * m + 1307) = 3 ^ 10 * m + 18863 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_12_1307.1, data_12_1307.2]

/-- Complete interval computation for depth 12, residue 1308. -/
theorem bounds_12_1308 : exactInterval 12 1308 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_12_1308 (m : Nat) :
    stoppingTime (2 ^ 12 * m + 1308) 12 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_12_1308 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_12_1308 : oddCount 1308 12 = 8 ∧ acceleratedOrbit 12 1308 = 2105 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_12_1308 (m : Nat) :
    acceleratedOrbit 12 (2 ^ 12 * m + 1308) = 3 ^ 8 * m + 2105 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_12_1308.1, data_12_1308.2]

/-- Complete interval computation for depth 12, residue 1309. -/
theorem bounds_12_1309 : exactInterval 12 1309 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_12_1309 (m : Nat) :
    stoppingTime (2 ^ 12 * m + 1309) 12 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_12_1309 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_12_1309 : oddCount 1309 12 = 8 ∧ acceleratedOrbit 12 1309 = 2105 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_12_1309 (m : Nat) :
    acceleratedOrbit 12 (2 ^ 12 * m + 1309) = 3 ^ 8 * m + 2105 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_12_1309.1, data_12_1309.2]

/-- Complete interval computation for depth 12, residue 1310. -/
theorem bounds_12_1310 : exactInterval 12 1310 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_12_1310 (m : Nat) :
    stoppingTime (2 ^ 12 * m + 1310) 12 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_12_1310 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_12_1310 : oddCount 1310 12 = 8 ∧ acceleratedOrbit 12 1310 = 2105 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_12_1310 (m : Nat) :
    acceleratedOrbit 12 (2 ^ 12 * m + 1310) = 3 ^ 8 * m + 2105 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_12_1310.1, data_12_1310.2]

/-- Complete interval computation for depth 12, residue 1311. -/
theorem bounds_12_1311 : exactInterval 12 1311 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_12_1311 (m : Nat) :
    stoppingTime (2 ^ 12 * m + 1311) 12 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_12_1311 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_12_1311 : oddCount 1311 12 = 7 ∧ acceleratedOrbit 12 1311 = 701 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_12_1311 (m : Nat) :
    acceleratedOrbit 12 (2 ^ 12 * m + 1311) = 3 ^ 7 * m + 701 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_12_1311.1, data_12_1311.2]

/-- Complete interval computation for depth 12, residue 1312. -/
theorem bounds_12_1312 : exactInterval 12 1312 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_12_1312 (m : Nat) :
    stoppingTime (2 ^ 12 * m + 1312) 12 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_12_1312 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_12_1312 : oddCount 1312 12 = 6 ∧ acceleratedOrbit 12 1312 = 242 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_12_1312 (m : Nat) :
    acceleratedOrbit 12 (2 ^ 12 * m + 1312) = 3 ^ 6 * m + 242 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_12_1312.1, data_12_1312.2]

/-- Complete interval computation for depth 12, residue 1313. -/
theorem bounds_12_1313 : exactInterval 12 1313 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_12_1313 (m : Nat) :
    stoppingTime (2 ^ 12 * m + 1313) 12 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_12_1313 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_12_1313 : oddCount 1313 12 = 4 ∧ acceleratedOrbit 12 1313 = 26 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_12_1313 (m : Nat) :
    acceleratedOrbit 12 (2 ^ 12 * m + 1313) = 3 ^ 4 * m + 26 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_12_1313.1, data_12_1313.2]

/-- Complete interval computation for depth 12, residue 1314. -/
theorem bounds_12_1314 : exactInterval 12 1314 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_12_1314 (m : Nat) :
    stoppingTime (2 ^ 12 * m + 1314) 12 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_12_1314 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_12_1314 : oddCount 1314 12 = 6 ∧ acceleratedOrbit 12 1314 = 236 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_12_1314 (m : Nat) :
    acceleratedOrbit 12 (2 ^ 12 * m + 1314) = 3 ^ 6 * m + 236 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_12_1314.1, data_12_1314.2]

/-- Complete interval computation for depth 12, residue 1315. -/
theorem bounds_12_1315 : exactInterval 12 1315 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_12_1315 (m : Nat) :
    stoppingTime (2 ^ 12 * m + 1315) 12 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_12_1315 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_12_1315 : oddCount 1315 12 = 6 ∧ acceleratedOrbit 12 1315 = 236 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_12_1315 (m : Nat) :
    acceleratedOrbit 12 (2 ^ 12 * m + 1315) = 3 ^ 6 * m + 236 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_12_1315.1, data_12_1315.2]

/-- Complete interval computation for depth 12, residue 1316. -/
theorem bounds_12_1316 : exactInterval 12 1316 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_12_1316 (m : Nat) :
    stoppingTime (2 ^ 12 * m + 1316) 12 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_12_1316 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_12_1316 : oddCount 1316 12 = 6 ∧ acceleratedOrbit 12 1316 = 236 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_12_1316 (m : Nat) :
    acceleratedOrbit 12 (2 ^ 12 * m + 1316) = 3 ^ 6 * m + 236 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_12_1316.1, data_12_1316.2]

/-- Complete interval computation for depth 12, residue 1317. -/
theorem bounds_12_1317 : exactInterval 12 1317 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_12_1317 (m : Nat) :
    stoppingTime (2 ^ 12 * m + 1317) 12 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_12_1317 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_12_1317 : oddCount 1317 12 = 6 ∧ acceleratedOrbit 12 1317 = 236 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_12_1317 (m : Nat) :
    acceleratedOrbit 12 (2 ^ 12 * m + 1317) = 3 ^ 6 * m + 236 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_12_1317.1, data_12_1317.2]

/-- Complete interval computation for depth 12, residue 1318. -/
theorem bounds_12_1318 : exactInterval 12 1318 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_12_1318 (m : Nat) :
    stoppingTime (2 ^ 12 * m + 1318) 12 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_12_1318 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_12_1318 : oddCount 1318 12 = 6 ∧ acceleratedOrbit 12 1318 = 236 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_12_1318 (m : Nat) :
    acceleratedOrbit 12 (2 ^ 12 * m + 1318) = 3 ^ 6 * m + 236 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_12_1318.1, data_12_1318.2]

/-- Complete interval computation for depth 12, residue 1319. -/
theorem bounds_12_1319 : exactInterval 12 1319 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_12_1319 (m : Nat) :
    stoppingTime (2 ^ 12 * m + 1319) 12 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_12_1319 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_12_1319 : oddCount 1319 12 = 6 ∧ acceleratedOrbit 12 1319 = 235 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_12_1319 (m : Nat) :
    acceleratedOrbit 12 (2 ^ 12 * m + 1319) = 3 ^ 6 * m + 235 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_12_1319.1, data_12_1319.2]

end Collatz.Research.StoppingAtlas.Batch0286
