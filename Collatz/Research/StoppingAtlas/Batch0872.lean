import Collatz.Research.DescentIntervals.Classifier

namespace Collatz.Research.StoppingAtlas.Batch0872

open Collatz.Research.DescentIntervals

set_option maxRecDepth 20000
set_option maxHeartbeats 0

/-- Complete interval computation for depth 13, residue 6210. -/
theorem bounds_13_6210 : exactInterval 13 6210 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_13_6210 (m : Nat) :
    stoppingTime (2 ^ 13 * m + 6210) 13 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_13_6210 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_13_6210 : oddCount 6210 13 = 7 ∧ acceleratedOrbit 13 6210 = 1660 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_13_6210 (m : Nat) :
    acceleratedOrbit 13 (2 ^ 13 * m + 6210) = 3 ^ 7 * m + 1660 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_13_6210.1, data_13_6210.2]

/-- Complete interval computation for depth 13, residue 6211. -/
theorem bounds_13_6211 : exactInterval 13 6211 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_13_6211 (m : Nat) :
    stoppingTime (2 ^ 13 * m + 6211) 13 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_13_6211 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_13_6211 : oddCount 6211 13 = 7 ∧ acceleratedOrbit 13 6211 = 1660 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_13_6211 (m : Nat) :
    acceleratedOrbit 13 (2 ^ 13 * m + 6211) = 3 ^ 7 * m + 1660 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_13_6211.1, data_13_6211.2]

/-- Complete interval computation for depth 13, residue 6212. -/
theorem bounds_13_6212 : exactInterval 13 6212 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_13_6212 (m : Nat) :
    stoppingTime (2 ^ 13 * m + 6212) 13 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_13_6212 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_13_6212 : oddCount 6212 13 = 4 ∧ acceleratedOrbit 13 6212 = 62 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_13_6212 (m : Nat) :
    acceleratedOrbit 13 (2 ^ 13 * m + 6212) = 3 ^ 4 * m + 62 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_13_6212.1, data_13_6212.2]

/-- Complete interval computation for depth 13, residue 6213. -/
theorem bounds_13_6213 : exactInterval 13 6213 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_13_6213 (m : Nat) :
    stoppingTime (2 ^ 13 * m + 6213) 13 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_13_6213 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_13_6213 : oddCount 6213 13 = 4 ∧ acceleratedOrbit 13 6213 = 62 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_13_6213 (m : Nat) :
    acceleratedOrbit 13 (2 ^ 13 * m + 6213) = 3 ^ 4 * m + 62 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_13_6213.1, data_13_6213.2]

/-- Complete interval computation for depth 13, residue 6214. -/
theorem bounds_13_6214 : exactInterval 13 6214 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_13_6214 (m : Nat) :
    stoppingTime (2 ^ 13 * m + 6214) 13 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_13_6214 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_13_6214 : oddCount 6214 13 = 4 ∧ acceleratedOrbit 13 6214 = 62 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_13_6214 (m : Nat) :
    acceleratedOrbit 13 (2 ^ 13 * m + 6214) = 3 ^ 4 * m + 62 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_13_6214.1, data_13_6214.2]

/-- Complete interval computation for depth 13, residue 6215. -/
theorem bounds_13_6215 : exactInterval 13 6215 = ⟨0, none⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_13_6215 (m : Nat) :
    stoppingTime (2 ^ 13 * m + 6215) 13 ↔ 0 ≤ m := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_13_6215 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_13_6215 : oddCount 6215 13 = 8 ∧ acceleratedOrbit 13 6215 = 4979 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_13_6215 (m : Nat) :
    acceleratedOrbit 13 (2 ^ 13 * m + 6215) = 3 ^ 8 * m + 4979 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_13_6215.1, data_13_6215.2]

/-- Complete interval computation for depth 13, residue 6216. -/
theorem bounds_13_6216 : exactInterval 13 6216 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_13_6216 (m : Nat) :
    stoppingTime (2 ^ 13 * m + 6216) 13 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_13_6216 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_13_6216 : oddCount 6216 13 = 7 ∧ acceleratedOrbit 13 6216 = 1664 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_13_6216 (m : Nat) :
    acceleratedOrbit 13 (2 ^ 13 * m + 6216) = 3 ^ 7 * m + 1664 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_13_6216.1, data_13_6216.2]

/-- Complete interval computation for depth 13, residue 6217. -/
theorem bounds_13_6217 : exactInterval 13 6217 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_13_6217 (m : Nat) :
    stoppingTime (2 ^ 13 * m + 6217) 13 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_13_6217 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_13_6217 : oddCount 6217 13 = 9 ∧ acceleratedOrbit 13 6217 = 14944 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_13_6217 (m : Nat) :
    acceleratedOrbit 13 (2 ^ 13 * m + 6217) = 3 ^ 9 * m + 14944 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_13_6217.1, data_13_6217.2]

/-- Complete interval computation for depth 13, residue 6218. -/
theorem bounds_13_6218 : exactInterval 13 6218 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_13_6218 (m : Nat) :
    stoppingTime (2 ^ 13 * m + 6218) 13 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_13_6218 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_13_6218 : oddCount 6218 13 = 7 ∧ acceleratedOrbit 13 6218 = 1664 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_13_6218 (m : Nat) :
    acceleratedOrbit 13 (2 ^ 13 * m + 6218) = 3 ^ 7 * m + 1664 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_13_6218.1, data_13_6218.2]

/-- Complete interval computation for depth 13, residue 6219. -/
theorem bounds_13_6219 : exactInterval 13 6219 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_13_6219 (m : Nat) :
    stoppingTime (2 ^ 13 * m + 6219) 13 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_13_6219 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_13_6219 : oddCount 6219 13 = 4 ∧ acceleratedOrbit 13 6219 = 62 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_13_6219 (m : Nat) :
    acceleratedOrbit 13 (2 ^ 13 * m + 6219) = 3 ^ 4 * m + 62 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_13_6219.1, data_13_6219.2]

/-- Complete interval computation for depth 13, residue 6220. -/
theorem bounds_13_6220 : exactInterval 13 6220 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_13_6220 (m : Nat) :
    stoppingTime (2 ^ 13 * m + 6220) 13 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_13_6220 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_13_6220 : oddCount 6220 13 = 7 ∧ acceleratedOrbit 13 6220 = 1664 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_13_6220 (m : Nat) :
    acceleratedOrbit 13 (2 ^ 13 * m + 6220) = 3 ^ 7 * m + 1664 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_13_6220.1, data_13_6220.2]

/-- Complete interval computation for depth 13, residue 6221. -/
theorem bounds_13_6221 : exactInterval 13 6221 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_13_6221 (m : Nat) :
    stoppingTime (2 ^ 13 * m + 6221) 13 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_13_6221 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_13_6221 : oddCount 6221 13 = 7 ∧ acceleratedOrbit 13 6221 = 1664 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_13_6221 (m : Nat) :
    acceleratedOrbit 13 (2 ^ 13 * m + 6221) = 3 ^ 7 * m + 1664 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_13_6221.1, data_13_6221.2]

/-- Complete interval computation for depth 13, residue 6222. -/
theorem bounds_13_6222 : exactInterval 13 6222 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_13_6222 (m : Nat) :
    stoppingTime (2 ^ 13 * m + 6222) 13 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_13_6222 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_13_6222 : oddCount 6222 13 = 6 ∧ acceleratedOrbit 13 6222 = 554 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_13_6222 (m : Nat) :
    acceleratedOrbit 13 (2 ^ 13 * m + 6222) = 3 ^ 6 * m + 554 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_13_6222.1, data_13_6222.2]

/-- Complete interval computation for depth 13, residue 6223. -/
theorem bounds_13_6223 : exactInterval 13 6223 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_13_6223 (m : Nat) :
    stoppingTime (2 ^ 13 * m + 6223) 13 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_13_6223 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_13_6223 : oddCount 6223 13 = 6 ∧ acceleratedOrbit 13 6223 = 554 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_13_6223 (m : Nat) :
    acceleratedOrbit 13 (2 ^ 13 * m + 6223) = 3 ^ 6 * m + 554 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_13_6223.1, data_13_6223.2]

/-- Complete interval computation for depth 13, residue 6224. -/
theorem bounds_13_6224 : exactInterval 13 6224 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_13_6224 (m : Nat) :
    stoppingTime (2 ^ 13 * m + 6224) 13 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_13_6224 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_13_6224 : oddCount 6224 13 = 5 ∧ acceleratedOrbit 13 6224 = 188 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_13_6224 (m : Nat) :
    acceleratedOrbit 13 (2 ^ 13 * m + 6224) = 3 ^ 5 * m + 188 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_13_6224.1, data_13_6224.2]

end Collatz.Research.StoppingAtlas.Batch0872
