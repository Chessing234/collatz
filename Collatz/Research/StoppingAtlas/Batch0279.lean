import Collatz.Research.DescentIntervals.Classifier

namespace Collatz.Research.StoppingAtlas.Batch0279

open Collatz.Research.DescentIntervals

set_option maxRecDepth 20000
set_option maxHeartbeats 0

/-- Complete interval computation for depth 12, residue 1198. -/
theorem bounds_12_1198 : exactInterval 12 1198 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_12_1198 (m : Nat) :
    stoppingTime (2 ^ 12 * m + 1198) 12 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_12_1198 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_12_1198 : oddCount 1198 12 = 6 ∧ acceleratedOrbit 12 1198 = 215 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_12_1198 (m : Nat) :
    acceleratedOrbit 12 (2 ^ 12 * m + 1198) = 3 ^ 6 * m + 215 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_12_1198.1, data_12_1198.2]

/-- Complete interval computation for depth 12, residue 1199. -/
theorem bounds_12_1199 : exactInterval 12 1199 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_12_1199 (m : Nat) :
    stoppingTime (2 ^ 12 * m + 1199) 12 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_12_1199 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_12_1199 : oddCount 1199 12 = 7 ∧ acceleratedOrbit 12 1199 = 641 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_12_1199 (m : Nat) :
    acceleratedOrbit 12 (2 ^ 12 * m + 1199) = 3 ^ 7 * m + 641 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_12_1199.1, data_12_1199.2]

/-- Complete interval computation for depth 12, residue 1200. -/
theorem bounds_12_1200 : exactInterval 12 1200 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_12_1200 (m : Nat) :
    stoppingTime (2 ^ 12 * m + 1200) 12 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_12_1200 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_12_1200 : oddCount 1200 12 = 3 ∧ acceleratedOrbit 12 1200 = 8 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_12_1200 (m : Nat) :
    acceleratedOrbit 12 (2 ^ 12 * m + 1200) = 3 ^ 3 * m + 8 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_12_1200.1, data_12_1200.2]

/-- Complete interval computation for depth 12, residue 1201. -/
theorem bounds_12_1201 : exactInterval 12 1201 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_12_1201 (m : Nat) :
    stoppingTime (2 ^ 12 * m + 1201) 12 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_12_1201 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_12_1201 : oddCount 1201 12 = 7 ∧ acceleratedOrbit 12 1201 = 647 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_12_1201 (m : Nat) :
    acceleratedOrbit 12 (2 ^ 12 * m + 1201) = 3 ^ 7 * m + 647 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_12_1201.1, data_12_1201.2]

/-- Complete interval computation for depth 12, residue 1202. -/
theorem bounds_12_1202 : exactInterval 12 1202 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_12_1202 (m : Nat) :
    stoppingTime (2 ^ 12 * m + 1202) 12 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_12_1202 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_12_1202 : oddCount 1202 12 = 7 ∧ acceleratedOrbit 12 1202 = 647 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_12_1202 (m : Nat) :
    acceleratedOrbit 12 (2 ^ 12 * m + 1202) = 3 ^ 7 * m + 647 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_12_1202.1, data_12_1202.2]

/-- Complete interval computation for depth 12, residue 1203. -/
theorem bounds_12_1203 : exactInterval 12 1203 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_12_1203 (m : Nat) :
    stoppingTime (2 ^ 12 * m + 1203) 12 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_12_1203 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_12_1203 : oddCount 1203 12 = 7 ∧ acceleratedOrbit 12 1203 = 647 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_12_1203 (m : Nat) :
    acceleratedOrbit 12 (2 ^ 12 * m + 1203) = 3 ^ 7 * m + 647 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_12_1203.1, data_12_1203.2]

/-- Complete interval computation for depth 12, residue 1204. -/
theorem bounds_12_1204 : exactInterval 12 1204 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_12_1204 (m : Nat) :
    stoppingTime (2 ^ 12 * m + 1204) 12 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_12_1204 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_12_1204 : oddCount 1204 12 = 3 ∧ acceleratedOrbit 12 1204 = 8 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_12_1204 (m : Nat) :
    acceleratedOrbit 12 (2 ^ 12 * m + 1204) = 3 ^ 3 * m + 8 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_12_1204.1, data_12_1204.2]

/-- Complete interval computation for depth 12, residue 1205. -/
theorem bounds_12_1205 : exactInterval 12 1205 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_12_1205 (m : Nat) :
    stoppingTime (2 ^ 12 * m + 1205) 12 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_12_1205 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_12_1205 : oddCount 1205 12 = 3 ∧ acceleratedOrbit 12 1205 = 8 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_12_1205 (m : Nat) :
    acceleratedOrbit 12 (2 ^ 12 * m + 1205) = 3 ^ 3 * m + 8 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_12_1205.1, data_12_1205.2]

/-- Complete interval computation for depth 12, residue 1206. -/
theorem bounds_12_1206 : exactInterval 12 1206 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_12_1206 (m : Nat) :
    stoppingTime (2 ^ 12 * m + 1206) 12 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_12_1206 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_12_1206 : oddCount 1206 12 = 8 ∧ acceleratedOrbit 12 1206 = 1937 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_12_1206 (m : Nat) :
    acceleratedOrbit 12 (2 ^ 12 * m + 1206) = 3 ^ 8 * m + 1937 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_12_1206.1, data_12_1206.2]

/-- Complete interval computation for depth 12, residue 1207. -/
theorem bounds_12_1207 : exactInterval 12 1207 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_12_1207 (m : Nat) :
    stoppingTime (2 ^ 12 * m + 1207) 12 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_12_1207 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_12_1207 : oddCount 1207 12 = 8 ∧ acceleratedOrbit 12 1207 = 1937 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_12_1207 (m : Nat) :
    acceleratedOrbit 12 (2 ^ 12 * m + 1207) = 3 ^ 8 * m + 1937 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_12_1207.1, data_12_1207.2]

/-- Complete interval computation for depth 12, residue 1208. -/
theorem bounds_12_1208 : exactInterval 12 1208 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_12_1208 (m : Nat) :
    stoppingTime (2 ^ 12 * m + 1208) 12 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_12_1208 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_12_1208 : oddCount 1208 12 = 3 ∧ acceleratedOrbit 12 1208 = 8 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_12_1208 (m : Nat) :
    acceleratedOrbit 12 (2 ^ 12 * m + 1208) = 3 ^ 3 * m + 8 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_12_1208.1, data_12_1208.2]

/-- Complete interval computation for depth 12, residue 1209. -/
theorem bounds_12_1209 : exactInterval 12 1209 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_12_1209 (m : Nat) :
    stoppingTime (2 ^ 12 * m + 1209) 12 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_12_1209 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_12_1209 : oddCount 1209 12 = 8 ∧ acceleratedOrbit 12 1209 = 1943 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_12_1209 (m : Nat) :
    acceleratedOrbit 12 (2 ^ 12 * m + 1209) = 3 ^ 8 * m + 1943 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_12_1209.1, data_12_1209.2]

/-- Complete interval computation for depth 12, residue 1210. -/
theorem bounds_12_1210 : exactInterval 12 1210 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_12_1210 (m : Nat) :
    stoppingTime (2 ^ 12 * m + 1210) 12 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_12_1210 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_12_1210 : oddCount 1210 12 = 3 ∧ acceleratedOrbit 12 1210 = 8 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_12_1210 (m : Nat) :
    acceleratedOrbit 12 (2 ^ 12 * m + 1210) = 3 ^ 3 * m + 8 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_12_1210.1, data_12_1210.2]

/-- Complete interval computation for depth 12, residue 1211. -/
theorem bounds_12_1211 : exactInterval 12 1211 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_12_1211 (m : Nat) :
    stoppingTime (2 ^ 12 * m + 1211) 12 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_12_1211 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_12_1211 : oddCount 1211 12 = 9 ∧ acceleratedOrbit 12 1211 = 5831 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_12_1211 (m : Nat) :
    acceleratedOrbit 12 (2 ^ 12 * m + 1211) = 3 ^ 9 * m + 5831 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_12_1211.1, data_12_1211.2]

/-- Complete interval computation for depth 12, residue 1212. -/
theorem bounds_12_1212 : exactInterval 12 1212 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_12_1212 (m : Nat) :
    stoppingTime (2 ^ 12 * m + 1212) 12 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_12_1212 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_12_1212 : oddCount 1212 12 = 7 ∧ acceleratedOrbit 12 1212 = 650 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_12_1212 (m : Nat) :
    acceleratedOrbit 12 (2 ^ 12 * m + 1212) = 3 ^ 7 * m + 650 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_12_1212.1, data_12_1212.2]

end Collatz.Research.StoppingAtlas.Batch0279
