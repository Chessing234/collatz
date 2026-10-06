import Collatz.Research.DescentIntervals.Classifier

namespace Collatz.Research.StoppingAtlas.Batch0146

open Collatz.Research.DescentIntervals

set_option maxRecDepth 20000
set_option maxHeartbeats 0

/-- Complete interval computation for depth 11, residue 1203. -/
theorem bounds_11_1203 : exactInterval 11 1203 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_11_1203 (m : Nat) :
    stoppingTime (2 ^ 11 * m + 1203) 11 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_11_1203 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_11_1203 : oddCount 1203 11 = 6 ∧ acceleratedOrbit 11 1203 = 431 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_11_1203 (m : Nat) :
    acceleratedOrbit 11 (2 ^ 11 * m + 1203) = 3 ^ 6 * m + 431 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_11_1203.1, data_11_1203.2]

/-- Complete interval computation for depth 11, residue 1204. -/
theorem bounds_11_1204 : exactInterval 11 1204 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_11_1204 (m : Nat) :
    stoppingTime (2 ^ 11 * m + 1204) 11 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_11_1204 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_11_1204 : oddCount 1204 11 = 3 ∧ acceleratedOrbit 11 1204 = 16 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_11_1204 (m : Nat) :
    acceleratedOrbit 11 (2 ^ 11 * m + 1204) = 3 ^ 3 * m + 16 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_11_1204.1, data_11_1204.2]

/-- Complete interval computation for depth 11, residue 1205. -/
theorem bounds_11_1205 : exactInterval 11 1205 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_11_1205 (m : Nat) :
    stoppingTime (2 ^ 11 * m + 1205) 11 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_11_1205 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_11_1205 : oddCount 1205 11 = 3 ∧ acceleratedOrbit 11 1205 = 16 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_11_1205 (m : Nat) :
    acceleratedOrbit 11 (2 ^ 11 * m + 1205) = 3 ^ 3 * m + 16 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_11_1205.1, data_11_1205.2]

/-- Complete interval computation for depth 11, residue 1206. -/
theorem bounds_11_1206 : exactInterval 11 1206 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_11_1206 (m : Nat) :
    stoppingTime (2 ^ 11 * m + 1206) 11 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_11_1206 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_11_1206 : oddCount 1206 11 = 7 ∧ acceleratedOrbit 11 1206 = 1291 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_11_1206 (m : Nat) :
    acceleratedOrbit 11 (2 ^ 11 * m + 1206) = 3 ^ 7 * m + 1291 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_11_1206.1, data_11_1206.2]

/-- Complete interval computation for depth 11, residue 1207. -/
theorem bounds_11_1207 : exactInterval 11 1207 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_11_1207 (m : Nat) :
    stoppingTime (2 ^ 11 * m + 1207) 11 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_11_1207 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_11_1207 : oddCount 1207 11 = 7 ∧ acceleratedOrbit 11 1207 = 1291 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_11_1207 (m : Nat) :
    acceleratedOrbit 11 (2 ^ 11 * m + 1207) = 3 ^ 7 * m + 1291 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_11_1207.1, data_11_1207.2]

/-- Complete interval computation for depth 11, residue 1208. -/
theorem bounds_11_1208 : exactInterval 11 1208 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_11_1208 (m : Nat) :
    stoppingTime (2 ^ 11 * m + 1208) 11 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_11_1208 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_11_1208 : oddCount 1208 11 = 3 ∧ acceleratedOrbit 11 1208 = 16 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_11_1208 (m : Nat) :
    acceleratedOrbit 11 (2 ^ 11 * m + 1208) = 3 ^ 3 * m + 16 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_11_1208.1, data_11_1208.2]

/-- Complete interval computation for depth 11, residue 1209. -/
theorem bounds_11_1209 : exactInterval 11 1209 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_11_1209 (m : Nat) :
    stoppingTime (2 ^ 11 * m + 1209) 11 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_11_1209 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_11_1209 : oddCount 1209 11 = 7 ∧ acceleratedOrbit 11 1209 = 1295 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_11_1209 (m : Nat) :
    acceleratedOrbit 11 (2 ^ 11 * m + 1209) = 3 ^ 7 * m + 1295 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_11_1209.1, data_11_1209.2]

/-- Complete interval computation for depth 11, residue 1210. -/
theorem bounds_11_1210 : exactInterval 11 1210 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_11_1210 (m : Nat) :
    stoppingTime (2 ^ 11 * m + 1210) 11 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_11_1210 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_11_1210 : oddCount 1210 11 = 3 ∧ acceleratedOrbit 11 1210 = 16 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_11_1210 (m : Nat) :
    acceleratedOrbit 11 (2 ^ 11 * m + 1210) = 3 ^ 3 * m + 16 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_11_1210.1, data_11_1210.2]

/-- Complete interval computation for depth 11, residue 1211. -/
theorem bounds_11_1211 : exactInterval 11 1211 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_11_1211 (m : Nat) :
    stoppingTime (2 ^ 11 * m + 1211) 11 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_11_1211 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_11_1211 : oddCount 1211 11 = 8 ∧ acceleratedOrbit 11 1211 = 3887 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_11_1211 (m : Nat) :
    acceleratedOrbit 11 (2 ^ 11 * m + 1211) = 3 ^ 8 * m + 3887 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_11_1211.1, data_11_1211.2]

/-- Complete interval computation for depth 11, residue 1212. -/
theorem bounds_11_1212 : exactInterval 11 1212 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_11_1212 (m : Nat) :
    stoppingTime (2 ^ 11 * m + 1212) 11 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_11_1212 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_11_1212 : oddCount 1212 11 = 6 ∧ acceleratedOrbit 11 1212 = 433 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_11_1212 (m : Nat) :
    acceleratedOrbit 11 (2 ^ 11 * m + 1212) = 3 ^ 6 * m + 433 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_11_1212.1, data_11_1212.2]

/-- Complete interval computation for depth 11, residue 1213. -/
theorem bounds_11_1213 : exactInterval 11 1213 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_11_1213 (m : Nat) :
    stoppingTime (2 ^ 11 * m + 1213) 11 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_11_1213 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_11_1213 : oddCount 1213 11 = 6 ∧ acceleratedOrbit 11 1213 = 433 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_11_1213 (m : Nat) :
    acceleratedOrbit 11 (2 ^ 11 * m + 1213) = 3 ^ 6 * m + 433 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_11_1213.1, data_11_1213.2]

/-- Complete interval computation for depth 11, residue 1214. -/
theorem bounds_11_1214 : exactInterval 11 1214 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_11_1214 (m : Nat) :
    stoppingTime (2 ^ 11 * m + 1214) 11 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_11_1214 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_11_1214 : oddCount 1214 11 = 6 ∧ acceleratedOrbit 11 1214 = 433 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_11_1214 (m : Nat) :
    acceleratedOrbit 11 (2 ^ 11 * m + 1214) = 3 ^ 6 * m + 433 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_11_1214.1, data_11_1214.2]

/-- Complete interval computation for depth 11, residue 1215. -/
theorem bounds_11_1215 : exactInterval 11 1215 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_11_1215 (m : Nat) :
    stoppingTime (2 ^ 11 * m + 1215) 11 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_11_1215 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_11_1215 : oddCount 1215 11 = 8 ∧ acceleratedOrbit 11 1215 = 3896 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_11_1215 (m : Nat) :
    acceleratedOrbit 11 (2 ^ 11 * m + 1215) = 3 ^ 8 * m + 3896 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_11_1215.1, data_11_1215.2]

/-- Complete interval computation for depth 11, residue 1216. -/
theorem bounds_11_1216 : exactInterval 11 1216 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_11_1216 (m : Nat) :
    stoppingTime (2 ^ 11 * m + 1216) 11 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_11_1216 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_11_1216 : oddCount 1216 11 = 3 ∧ acceleratedOrbit 11 1216 = 17 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_11_1216 (m : Nat) :
    acceleratedOrbit 11 (2 ^ 11 * m + 1216) = 3 ^ 3 * m + 17 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_11_1216.1, data_11_1216.2]

/-- Complete interval computation for depth 11, residue 1217. -/
theorem bounds_11_1217 : exactInterval 11 1217 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_11_1217 (m : Nat) :
    stoppingTime (2 ^ 11 * m + 1217) 11 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_11_1217 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_11_1217 : oddCount 1217 11 = 5 ∧ acceleratedOrbit 11 1217 = 145 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_11_1217 (m : Nat) :
    acceleratedOrbit 11 (2 ^ 11 * m + 1217) = 3 ^ 5 * m + 145 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_11_1217.1, data_11_1217.2]

end Collatz.Research.StoppingAtlas.Batch0146
