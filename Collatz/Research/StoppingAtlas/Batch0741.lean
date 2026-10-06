import Collatz.Research.DescentIntervals.Classifier

namespace Collatz.Research.StoppingAtlas.Batch0741

open Collatz.Research.DescentIntervals

set_option maxRecDepth 20000
set_option maxHeartbeats 0

/-- Complete interval computation for depth 13, residue 4198. -/
theorem bounds_13_4198 : exactInterval 13 4198 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_13_4198 (m : Nat) :
    stoppingTime (2 ^ 13 * m + 4198) 13 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_13_4198 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_13_4198 : oddCount 4198 13 = 7 ∧ acceleratedOrbit 13 4198 = 1124 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_13_4198 (m : Nat) :
    acceleratedOrbit 13 (2 ^ 13 * m + 4198) = 3 ^ 7 * m + 1124 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_13_4198.1, data_13_4198.2]

/-- Complete interval computation for depth 13, residue 4199. -/
theorem bounds_13_4199 : exactInterval 13 4199 = ⟨0, none⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_13_4199 (m : Nat) :
    stoppingTime (2 ^ 13 * m + 4199) 13 ↔ 0 ≤ m := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_13_4199 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_13_4199 : oddCount 4199 13 = 8 ∧ acceleratedOrbit 13 4199 = 3364 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_13_4199 (m : Nat) :
    acceleratedOrbit 13 (2 ^ 13 * m + 4199) = 3 ^ 8 * m + 3364 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_13_4199.1, data_13_4199.2]

/-- Complete interval computation for depth 13, residue 4200. -/
theorem bounds_13_4200 : exactInterval 13 4200 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_13_4200 (m : Nat) :
    stoppingTime (2 ^ 13 * m + 4200) 13 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_13_4200 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_13_4200 : oddCount 4200 13 = 3 ∧ acceleratedOrbit 13 4200 = 14 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_13_4200 (m : Nat) :
    acceleratedOrbit 13 (2 ^ 13 * m + 4200) = 3 ^ 3 * m + 14 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_13_4200.1, data_13_4200.2]

/-- Complete interval computation for depth 13, residue 4201. -/
theorem bounds_13_4201 : exactInterval 13 4201 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_13_4201 (m : Nat) :
    stoppingTime (2 ^ 13 * m + 4201) 13 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_13_4201 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_13_4201 : oddCount 4201 13 = 6 ∧ acceleratedOrbit 13 4201 = 374 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_13_4201 (m : Nat) :
    acceleratedOrbit 13 (2 ^ 13 * m + 4201) = 3 ^ 6 * m + 374 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_13_4201.1, data_13_4201.2]

/-- Complete interval computation for depth 13, residue 4202. -/
theorem bounds_13_4202 : exactInterval 13 4202 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_13_4202 (m : Nat) :
    stoppingTime (2 ^ 13 * m + 4202) 13 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_13_4202 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_13_4202 : oddCount 4202 13 = 3 ∧ acceleratedOrbit 13 4202 = 14 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_13_4202 (m : Nat) :
    acceleratedOrbit 13 (2 ^ 13 * m + 4202) = 3 ^ 3 * m + 14 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_13_4202.1, data_13_4202.2]

/-- Complete interval computation for depth 13, residue 4203. -/
theorem bounds_13_4203 : exactInterval 13 4203 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_13_4203 (m : Nat) :
    stoppingTime (2 ^ 13 * m + 4203) 13 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_13_4203 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_13_4203 : oddCount 4203 13 = 8 ∧ acceleratedOrbit 13 4203 = 3368 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_13_4203 (m : Nat) :
    acceleratedOrbit 13 (2 ^ 13 * m + 4203) = 3 ^ 8 * m + 3368 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_13_4203.1, data_13_4203.2]

/-- Complete interval computation for depth 13, residue 4204. -/
theorem bounds_13_4204 : exactInterval 13 4204 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_13_4204 (m : Nat) :
    stoppingTime (2 ^ 13 * m + 4204) 13 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_13_4204 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_13_4204 : oddCount 4204 13 = 9 ∧ acceleratedOrbit 13 4204 = 10115 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_13_4204 (m : Nat) :
    acceleratedOrbit 13 (2 ^ 13 * m + 4204) = 3 ^ 9 * m + 10115 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_13_4204.1, data_13_4204.2]

/-- Complete interval computation for depth 13, residue 4205. -/
theorem bounds_13_4205 : exactInterval 13 4205 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_13_4205 (m : Nat) :
    stoppingTime (2 ^ 13 * m + 4205) 13 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_13_4205 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_13_4205 : oddCount 4205 13 = 9 ∧ acceleratedOrbit 13 4205 = 10115 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_13_4205 (m : Nat) :
    acceleratedOrbit 13 (2 ^ 13 * m + 4205) = 3 ^ 9 * m + 10115 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_13_4205.1, data_13_4205.2]

/-- Complete interval computation for depth 13, residue 4206. -/
theorem bounds_13_4206 : exactInterval 13 4206 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_13_4206 (m : Nat) :
    stoppingTime (2 ^ 13 * m + 4206) 13 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_13_4206 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_13_4206 : oddCount 4206 13 = 9 ∧ acceleratedOrbit 13 4206 = 10115 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_13_4206 (m : Nat) :
    acceleratedOrbit 13 (2 ^ 13 * m + 4206) = 3 ^ 9 * m + 10115 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_13_4206.1, data_13_4206.2]

/-- Complete interval computation for depth 13, residue 4207. -/
theorem bounds_13_4207 : exactInterval 13 4207 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_13_4207 (m : Nat) :
    stoppingTime (2 ^ 13 * m + 4207) 13 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_13_4207 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_13_4207 : oddCount 4207 13 = 10 ∧ acceleratedOrbit 13 4207 = 30334 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_13_4207 (m : Nat) :
    acceleratedOrbit 13 (2 ^ 13 * m + 4207) = 3 ^ 10 * m + 30334 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_13_4207.1, data_13_4207.2]

/-- Complete interval computation for depth 13, residue 4208. -/
theorem bounds_13_4208 : exactInterval 13 4208 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_13_4208 (m : Nat) :
    stoppingTime (2 ^ 13 * m + 4208) 13 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_13_4208 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_13_4208 : oddCount 4208 13 = 6 ∧ acceleratedOrbit 13 4208 = 377 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_13_4208 (m : Nat) :
    acceleratedOrbit 13 (2 ^ 13 * m + 4208) = 3 ^ 6 * m + 377 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_13_4208.1, data_13_4208.2]

/-- Complete interval computation for depth 13, residue 4209. -/
theorem bounds_13_4209 : exactInterval 13 4209 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_13_4209 (m : Nat) :
    stoppingTime (2 ^ 13 * m + 4209) 13 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_13_4209 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_13_4209 : oddCount 4209 13 = 3 ∧ acceleratedOrbit 13 4209 = 14 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_13_4209 (m : Nat) :
    acceleratedOrbit 13 (2 ^ 13 * m + 4209) = 3 ^ 3 * m + 14 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_13_4209.1, data_13_4209.2]

/-- Complete interval computation for depth 13, residue 4210. -/
theorem bounds_13_4210 : exactInterval 13 4210 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_13_4210 (m : Nat) :
    stoppingTime (2 ^ 13 * m + 4210) 13 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_13_4210 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_13_4210 : oddCount 4210 13 = 5 ∧ acceleratedOrbit 13 4210 = 125 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_13_4210 (m : Nat) :
    acceleratedOrbit 13 (2 ^ 13 * m + 4210) = 3 ^ 5 * m + 125 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_13_4210.1, data_13_4210.2]

/-- Complete interval computation for depth 13, residue 4211. -/
theorem bounds_13_4211 : exactInterval 13 4211 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_13_4211 (m : Nat) :
    stoppingTime (2 ^ 13 * m + 4211) 13 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_13_4211 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_13_4211 : oddCount 4211 13 = 5 ∧ acceleratedOrbit 13 4211 = 125 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_13_4211 (m : Nat) :
    acceleratedOrbit 13 (2 ^ 13 * m + 4211) = 3 ^ 5 * m + 125 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_13_4211.1, data_13_4211.2]

/-- Complete interval computation for depth 13, residue 4212. -/
theorem bounds_13_4212 : exactInterval 13 4212 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_13_4212 (m : Nat) :
    stoppingTime (2 ^ 13 * m + 4212) 13 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_13_4212 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_13_4212 : oddCount 4212 13 = 6 ∧ acceleratedOrbit 13 4212 = 377 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_13_4212 (m : Nat) :
    acceleratedOrbit 13 (2 ^ 13 * m + 4212) = 3 ^ 6 * m + 377 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_13_4212.1, data_13_4212.2]

end Collatz.Research.StoppingAtlas.Batch0741
