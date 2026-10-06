import Collatz.Research.DescentIntervals.Classifier

namespace Collatz.Research.StoppingAtlas.Batch0546

open Collatz.Research.DescentIntervals

set_option maxRecDepth 20000
set_option maxHeartbeats 0

/-- Complete interval computation for depth 13, residue 1203. -/
theorem bounds_13_1203 : exactInterval 13 1203 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_13_1203 (m : Nat) :
    stoppingTime (2 ^ 13 * m + 1203) 13 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_13_1203 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_13_1203 : oddCount 1203 13 = 8 ∧ acceleratedOrbit 13 1203 = 971 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_13_1203 (m : Nat) :
    acceleratedOrbit 13 (2 ^ 13 * m + 1203) = 3 ^ 8 * m + 971 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_13_1203.1, data_13_1203.2]

/-- Complete interval computation for depth 13, residue 1204. -/
theorem bounds_13_1204 : exactInterval 13 1204 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_13_1204 (m : Nat) :
    stoppingTime (2 ^ 13 * m + 1204) 13 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_13_1204 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_13_1204 : oddCount 1204 13 = 3 ∧ acceleratedOrbit 13 1204 = 4 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_13_1204 (m : Nat) :
    acceleratedOrbit 13 (2 ^ 13 * m + 1204) = 3 ^ 3 * m + 4 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_13_1204.1, data_13_1204.2]

/-- Complete interval computation for depth 13, residue 1205. -/
theorem bounds_13_1205 : exactInterval 13 1205 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_13_1205 (m : Nat) :
    stoppingTime (2 ^ 13 * m + 1205) 13 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_13_1205 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_13_1205 : oddCount 1205 13 = 3 ∧ acceleratedOrbit 13 1205 = 4 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_13_1205 (m : Nat) :
    acceleratedOrbit 13 (2 ^ 13 * m + 1205) = 3 ^ 3 * m + 4 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_13_1205.1, data_13_1205.2]

/-- Complete interval computation for depth 13, residue 1206. -/
theorem bounds_13_1206 : exactInterval 13 1206 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_13_1206 (m : Nat) :
    stoppingTime (2 ^ 13 * m + 1206) 13 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_13_1206 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_13_1206 : oddCount 1206 13 = 9 ∧ acceleratedOrbit 13 1206 = 2906 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_13_1206 (m : Nat) :
    acceleratedOrbit 13 (2 ^ 13 * m + 1206) = 3 ^ 9 * m + 2906 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_13_1206.1, data_13_1206.2]

/-- Complete interval computation for depth 13, residue 1207. -/
theorem bounds_13_1207 : exactInterval 13 1207 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_13_1207 (m : Nat) :
    stoppingTime (2 ^ 13 * m + 1207) 13 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_13_1207 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_13_1207 : oddCount 1207 13 = 9 ∧ acceleratedOrbit 13 1207 = 2906 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_13_1207 (m : Nat) :
    acceleratedOrbit 13 (2 ^ 13 * m + 1207) = 3 ^ 9 * m + 2906 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_13_1207.1, data_13_1207.2]

/-- Complete interval computation for depth 13, residue 1208. -/
theorem bounds_13_1208 : exactInterval 13 1208 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_13_1208 (m : Nat) :
    stoppingTime (2 ^ 13 * m + 1208) 13 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_13_1208 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_13_1208 : oddCount 1208 13 = 3 ∧ acceleratedOrbit 13 1208 = 4 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_13_1208 (m : Nat) :
    acceleratedOrbit 13 (2 ^ 13 * m + 1208) = 3 ^ 3 * m + 4 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_13_1208.1, data_13_1208.2]

/-- Complete interval computation for depth 13, residue 1209. -/
theorem bounds_13_1209 : exactInterval 13 1209 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_13_1209 (m : Nat) :
    stoppingTime (2 ^ 13 * m + 1209) 13 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_13_1209 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_13_1209 : oddCount 1209 13 = 9 ∧ acceleratedOrbit 13 1209 = 2915 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_13_1209 (m : Nat) :
    acceleratedOrbit 13 (2 ^ 13 * m + 1209) = 3 ^ 9 * m + 2915 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_13_1209.1, data_13_1209.2]

/-- Complete interval computation for depth 13, residue 1210. -/
theorem bounds_13_1210 : exactInterval 13 1210 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_13_1210 (m : Nat) :
    stoppingTime (2 ^ 13 * m + 1210) 13 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_13_1210 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_13_1210 : oddCount 1210 13 = 3 ∧ acceleratedOrbit 13 1210 = 4 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_13_1210 (m : Nat) :
    acceleratedOrbit 13 (2 ^ 13 * m + 1210) = 3 ^ 3 * m + 4 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_13_1210.1, data_13_1210.2]

/-- Complete interval computation for depth 13, residue 1211. -/
theorem bounds_13_1211 : exactInterval 13 1211 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_13_1211 (m : Nat) :
    stoppingTime (2 ^ 13 * m + 1211) 13 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_13_1211 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_13_1211 : oddCount 1211 13 = 10 ∧ acceleratedOrbit 13 1211 = 8747 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_13_1211 (m : Nat) :
    acceleratedOrbit 13 (2 ^ 13 * m + 1211) = 3 ^ 10 * m + 8747 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_13_1211.1, data_13_1211.2]

/-- Complete interval computation for depth 13, residue 1212. -/
theorem bounds_13_1212 : exactInterval 13 1212 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_13_1212 (m : Nat) :
    stoppingTime (2 ^ 13 * m + 1212) 13 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_13_1212 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_13_1212 : oddCount 1212 13 = 7 ∧ acceleratedOrbit 13 1212 = 325 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_13_1212 (m : Nat) :
    acceleratedOrbit 13 (2 ^ 13 * m + 1212) = 3 ^ 7 * m + 325 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_13_1212.1, data_13_1212.2]

/-- Complete interval computation for depth 13, residue 1213. -/
theorem bounds_13_1213 : exactInterval 13 1213 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_13_1213 (m : Nat) :
    stoppingTime (2 ^ 13 * m + 1213) 13 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_13_1213 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_13_1213 : oddCount 1213 13 = 7 ∧ acceleratedOrbit 13 1213 = 325 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_13_1213 (m : Nat) :
    acceleratedOrbit 13 (2 ^ 13 * m + 1213) = 3 ^ 7 * m + 325 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_13_1213.1, data_13_1213.2]

/-- Complete interval computation for depth 13, residue 1214. -/
theorem bounds_13_1214 : exactInterval 13 1214 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_13_1214 (m : Nat) :
    stoppingTime (2 ^ 13 * m + 1214) 13 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_13_1214 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_13_1214 : oddCount 1214 13 = 7 ∧ acceleratedOrbit 13 1214 = 325 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_13_1214 (m : Nat) :
    acceleratedOrbit 13 (2 ^ 13 * m + 1214) = 3 ^ 7 * m + 325 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_13_1214.1, data_13_1214.2]

/-- Complete interval computation for depth 13, residue 1215. -/
theorem bounds_13_1215 : exactInterval 13 1215 = ⟨0, none⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_13_1215 (m : Nat) :
    stoppingTime (2 ^ 13 * m + 1215) 13 ↔ 0 ≤ m := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_13_1215 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_13_1215 : oddCount 1215 13 = 8 ∧ acceleratedOrbit 13 1215 = 974 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_13_1215 (m : Nat) :
    acceleratedOrbit 13 (2 ^ 13 * m + 1215) = 3 ^ 8 * m + 974 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_13_1215.1, data_13_1215.2]

/-- Complete interval computation for depth 13, residue 1216. -/
theorem bounds_13_1216 : exactInterval 13 1216 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_13_1216 (m : Nat) :
    stoppingTime (2 ^ 13 * m + 1216) 13 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_13_1216 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_13_1216 : oddCount 1216 13 = 4 ∧ acceleratedOrbit 13 1216 = 13 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_13_1216 (m : Nat) :
    acceleratedOrbit 13 (2 ^ 13 * m + 1216) = 3 ^ 4 * m + 13 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_13_1216.1, data_13_1216.2]

/-- Complete interval computation for depth 13, residue 1217. -/
theorem bounds_13_1217 : exactInterval 13 1217 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_13_1217 (m : Nat) :
    stoppingTime (2 ^ 13 * m + 1217) 13 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_13_1217 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_13_1217 : oddCount 1217 13 = 6 ∧ acceleratedOrbit 13 1217 = 109 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_13_1217 (m : Nat) :
    acceleratedOrbit 13 (2 ^ 13 * m + 1217) = 3 ^ 6 * m + 109 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_13_1217.1, data_13_1217.2]

end Collatz.Research.StoppingAtlas.Batch0546
