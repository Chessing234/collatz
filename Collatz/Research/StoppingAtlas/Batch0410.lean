import Collatz.Research.DescentIntervals.Classifier

namespace Collatz.Research.StoppingAtlas.Batch0410

open Collatz.Research.DescentIntervals

set_option maxRecDepth 20000
set_option maxHeartbeats 0

/-- Complete interval computation for depth 12, residue 3210. -/
theorem bounds_12_3210 : exactInterval 12 3210 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_12_3210 (m : Nat) :
    stoppingTime (2 ^ 12 * m + 3210) 12 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_12_3210 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_12_3210 : oddCount 3210 12 = 4 ∧ acceleratedOrbit 12 3210 = 64 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_12_3210 (m : Nat) :
    acceleratedOrbit 12 (2 ^ 12 * m + 3210) = 3 ^ 4 * m + 64 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_12_3210.1, data_12_3210.2]

/-- Complete interval computation for depth 12, residue 3211. -/
theorem bounds_12_3211 : exactInterval 12 3211 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_12_3211 (m : Nat) :
    stoppingTime (2 ^ 12 * m + 3211) 12 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_12_3211 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_12_3211 : oddCount 3211 12 = 6 ∧ acceleratedOrbit 12 3211 = 572 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_12_3211 (m : Nat) :
    acceleratedOrbit 12 (2 ^ 12 * m + 3211) = 3 ^ 6 * m + 572 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_12_3211.1, data_12_3211.2]

/-- Complete interval computation for depth 12, residue 3212. -/
theorem bounds_12_3212 : exactInterval 12 3212 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_12_3212 (m : Nat) :
    stoppingTime (2 ^ 12 * m + 3212) 12 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_12_3212 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_12_3212 : oddCount 3212 12 = 4 ∧ acceleratedOrbit 12 3212 = 64 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_12_3212 (m : Nat) :
    acceleratedOrbit 12 (2 ^ 12 * m + 3212) = 3 ^ 4 * m + 64 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_12_3212.1, data_12_3212.2]

/-- Complete interval computation for depth 12, residue 3213. -/
theorem bounds_12_3213 : exactInterval 12 3213 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_12_3213 (m : Nat) :
    stoppingTime (2 ^ 12 * m + 3213) 12 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_12_3213 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_12_3213 : oddCount 3213 12 = 4 ∧ acceleratedOrbit 12 3213 = 64 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_12_3213 (m : Nat) :
    acceleratedOrbit 12 (2 ^ 12 * m + 3213) = 3 ^ 4 * m + 64 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_12_3213.1, data_12_3213.2]

/-- Complete interval computation for depth 12, residue 3214. -/
theorem bounds_12_3214 : exactInterval 12 3214 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_12_3214 (m : Nat) :
    stoppingTime (2 ^ 12 * m + 3214) 12 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_12_3214 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_12_3214 : oddCount 3214 12 = 7 ∧ acceleratedOrbit 12 3214 = 1718 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_12_3214 (m : Nat) :
    acceleratedOrbit 12 (2 ^ 12 * m + 3214) = 3 ^ 7 * m + 1718 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_12_3214.1, data_12_3214.2]

/-- Complete interval computation for depth 12, residue 3215. -/
theorem bounds_12_3215 : exactInterval 12 3215 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_12_3215 (m : Nat) :
    stoppingTime (2 ^ 12 * m + 3215) 12 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_12_3215 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_12_3215 : oddCount 3215 12 = 7 ∧ acceleratedOrbit 12 3215 = 1718 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_12_3215 (m : Nat) :
    acceleratedOrbit 12 (2 ^ 12 * m + 3215) = 3 ^ 7 * m + 1718 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_12_3215.1, data_12_3215.2]

/-- Complete interval computation for depth 12, residue 3216. -/
theorem bounds_12_3216 : exactInterval 12 3216 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_12_3216 (m : Nat) :
    stoppingTime (2 ^ 12 * m + 3216) 12 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_12_3216 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_12_3216 : oddCount 3216 12 = 4 ∧ acceleratedOrbit 12 3216 = 64 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_12_3216 (m : Nat) :
    acceleratedOrbit 12 (2 ^ 12 * m + 3216) = 3 ^ 4 * m + 64 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_12_3216.1, data_12_3216.2]

/-- Complete interval computation for depth 12, residue 3217. -/
theorem bounds_12_3217 : exactInterval 12 3217 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_12_3217 (m : Nat) :
    stoppingTime (2 ^ 12 * m + 3217) 12 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_12_3217 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_12_3217 : oddCount 3217 12 = 7 ∧ acceleratedOrbit 12 3217 = 1721 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_12_3217 (m : Nat) :
    acceleratedOrbit 12 (2 ^ 12 * m + 3217) = 3 ^ 7 * m + 1721 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_12_3217.1, data_12_3217.2]

/-- Complete interval computation for depth 12, residue 3218. -/
theorem bounds_12_3218 : exactInterval 12 3218 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_12_3218 (m : Nat) :
    stoppingTime (2 ^ 12 * m + 3218) 12 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_12_3218 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_12_3218 : oddCount 3218 12 = 7 ∧ acceleratedOrbit 12 3218 = 1721 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_12_3218 (m : Nat) :
    acceleratedOrbit 12 (2 ^ 12 * m + 3218) = 3 ^ 7 * m + 1721 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_12_3218.1, data_12_3218.2]

/-- Complete interval computation for depth 12, residue 3219. -/
theorem bounds_12_3219 : exactInterval 12 3219 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_12_3219 (m : Nat) :
    stoppingTime (2 ^ 12 * m + 3219) 12 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_12_3219 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_12_3219 : oddCount 3219 12 = 7 ∧ acceleratedOrbit 12 3219 = 1721 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_12_3219 (m : Nat) :
    acceleratedOrbit 12 (2 ^ 12 * m + 3219) = 3 ^ 7 * m + 1721 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_12_3219.1, data_12_3219.2]

/-- Complete interval computation for depth 12, residue 3220. -/
theorem bounds_12_3220 : exactInterval 12 3220 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_12_3220 (m : Nat) :
    stoppingTime (2 ^ 12 * m + 3220) 12 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_12_3220 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_12_3220 : oddCount 3220 12 = 4 ∧ acceleratedOrbit 12 3220 = 64 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_12_3220 (m : Nat) :
    acceleratedOrbit 12 (2 ^ 12 * m + 3220) = 3 ^ 4 * m + 64 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_12_3220.1, data_12_3220.2]

/-- Complete interval computation for depth 12, residue 3221. -/
theorem bounds_12_3221 : exactInterval 12 3221 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_12_3221 (m : Nat) :
    stoppingTime (2 ^ 12 * m + 3221) 12 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_12_3221 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_12_3221 : oddCount 3221 12 = 4 ∧ acceleratedOrbit 12 3221 = 64 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_12_3221 (m : Nat) :
    acceleratedOrbit 12 (2 ^ 12 * m + 3221) = 3 ^ 4 * m + 64 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_12_3221.1, data_12_3221.2]

/-- Complete interval computation for depth 12, residue 3222. -/
theorem bounds_12_3222 : exactInterval 12 3222 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_12_3222 (m : Nat) :
    stoppingTime (2 ^ 12 * m + 3222) 12 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_12_3222 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_12_3222 : oddCount 3222 12 = 4 ∧ acceleratedOrbit 12 3222 = 64 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_12_3222 (m : Nat) :
    acceleratedOrbit 12 (2 ^ 12 * m + 3222) = 3 ^ 4 * m + 64 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_12_3222.1, data_12_3222.2]

/-- Complete interval computation for depth 12, residue 3223. -/
theorem bounds_12_3223 : exactInterval 12 3223 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_12_3223 (m : Nat) :
    stoppingTime (2 ^ 12 * m + 3223) 12 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_12_3223 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_12_3223 : oddCount 3223 12 = 4 ∧ acceleratedOrbit 12 3223 = 64 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_12_3223 (m : Nat) :
    acceleratedOrbit 12 (2 ^ 12 * m + 3223) = 3 ^ 4 * m + 64 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_12_3223.1, data_12_3223.2]

/-- Complete interval computation for depth 12, residue 3224. -/
theorem bounds_12_3224 : exactInterval 12 3224 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_12_3224 (m : Nat) :
    stoppingTime (2 ^ 12 * m + 3224) 12 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_12_3224 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_12_3224 : oddCount 3224 12 = 4 ∧ acceleratedOrbit 12 3224 = 64 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_12_3224 (m : Nat) :
    acceleratedOrbit 12 (2 ^ 12 * m + 3224) = 3 ^ 4 * m + 64 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_12_3224.1, data_12_3224.2]

end Collatz.Research.StoppingAtlas.Batch0410
