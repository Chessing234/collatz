import Collatz.Research.DescentIntervals.Classifier

namespace Collatz.Research.StoppingAtlas.Batch0871

open Collatz.Research.DescentIntervals

set_option maxRecDepth 20000
set_option maxHeartbeats 0

/-- Complete interval computation for depth 13, residue 6195. -/
theorem bounds_13_6195 : exactInterval 13 6195 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_13_6195 (m : Nat) :
    stoppingTime (2 ^ 13 * m + 6195) 13 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_13_6195 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_13_6195 : oddCount 6195 13 = 8 ∧ acceleratedOrbit 13 6195 = 4967 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_13_6195 (m : Nat) :
    acceleratedOrbit 13 (2 ^ 13 * m + 6195) = 3 ^ 8 * m + 4967 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_13_6195.1, data_13_6195.2]

/-- Complete interval computation for depth 13, residue 6196. -/
theorem bounds_13_6196 : exactInterval 13 6196 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_13_6196 (m : Nat) :
    stoppingTime (2 ^ 13 * m + 6196) 13 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_13_6196 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_13_6196 : oddCount 6196 13 = 4 ∧ acceleratedOrbit 13 6196 = 62 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_13_6196 (m : Nat) :
    acceleratedOrbit 13 (2 ^ 13 * m + 6196) = 3 ^ 4 * m + 62 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_13_6196.1, data_13_6196.2]

/-- Complete interval computation for depth 13, residue 6197. -/
theorem bounds_13_6197 : exactInterval 13 6197 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_13_6197 (m : Nat) :
    stoppingTime (2 ^ 13 * m + 6197) 13 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_13_6197 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_13_6197 : oddCount 6197 13 = 4 ∧ acceleratedOrbit 13 6197 = 62 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_13_6197 (m : Nat) :
    acceleratedOrbit 13 (2 ^ 13 * m + 6197) = 3 ^ 4 * m + 62 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_13_6197.1, data_13_6197.2]

/-- Complete interval computation for depth 13, residue 6198. -/
theorem bounds_13_6198 : exactInterval 13 6198 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_13_6198 (m : Nat) :
    stoppingTime (2 ^ 13 * m + 6198) 13 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_13_6198 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_13_6198 : oddCount 6198 13 = 9 ∧ acceleratedOrbit 13 6198 = 14899 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_13_6198 (m : Nat) :
    acceleratedOrbit 13 (2 ^ 13 * m + 6198) = 3 ^ 9 * m + 14899 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_13_6198.1, data_13_6198.2]

/-- Complete interval computation for depth 13, residue 6199. -/
theorem bounds_13_6199 : exactInterval 13 6199 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_13_6199 (m : Nat) :
    stoppingTime (2 ^ 13 * m + 6199) 13 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_13_6199 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_13_6199 : oddCount 6199 13 = 9 ∧ acceleratedOrbit 13 6199 = 14899 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_13_6199 (m : Nat) :
    acceleratedOrbit 13 (2 ^ 13 * m + 6199) = 3 ^ 9 * m + 14899 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_13_6199.1, data_13_6199.2]

/-- Complete interval computation for depth 13, residue 6200. -/
theorem bounds_13_6200 : exactInterval 13 6200 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_13_6200 (m : Nat) :
    stoppingTime (2 ^ 13 * m + 6200) 13 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_13_6200 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_13_6200 : oddCount 6200 13 = 6 ∧ acceleratedOrbit 13 6200 = 553 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_13_6200 (m : Nat) :
    acceleratedOrbit 13 (2 ^ 13 * m + 6200) = 3 ^ 6 * m + 553 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_13_6200.1, data_13_6200.2]

/-- Complete interval computation for depth 13, residue 6201. -/
theorem bounds_13_6201 : exactInterval 13 6201 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_13_6201 (m : Nat) :
    stoppingTime (2 ^ 13 * m + 6201) 13 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_13_6201 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_13_6201 : oddCount 6201 13 = 5 ∧ acceleratedOrbit 13 6201 = 184 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_13_6201 (m : Nat) :
    acceleratedOrbit 13 (2 ^ 13 * m + 6201) = 3 ^ 5 * m + 184 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_13_6201.1, data_13_6201.2]

/-- Complete interval computation for depth 13, residue 6202. -/
theorem bounds_13_6202 : exactInterval 13 6202 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_13_6202 (m : Nat) :
    stoppingTime (2 ^ 13 * m + 6202) 13 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_13_6202 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_13_6202 : oddCount 6202 13 = 6 ∧ acceleratedOrbit 13 6202 = 553 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_13_6202 (m : Nat) :
    acceleratedOrbit 13 (2 ^ 13 * m + 6202) = 3 ^ 6 * m + 553 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_13_6202.1, data_13_6202.2]

/-- Complete interval computation for depth 13, residue 6203. -/
theorem bounds_13_6203 : exactInterval 13 6203 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_13_6203 (m : Nat) :
    stoppingTime (2 ^ 13 * m + 6203) 13 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_13_6203 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_13_6203 : oddCount 6203 13 = 7 ∧ acceleratedOrbit 13 6203 = 1657 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_13_6203 (m : Nat) :
    acceleratedOrbit 13 (2 ^ 13 * m + 6203) = 3 ^ 7 * m + 1657 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_13_6203.1, data_13_6203.2]

/-- Complete interval computation for depth 13, residue 6204. -/
theorem bounds_13_6204 : exactInterval 13 6204 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_13_6204 (m : Nat) :
    stoppingTime (2 ^ 13 * m + 6204) 13 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_13_6204 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_13_6204 : oddCount 6204 13 = 6 ∧ acceleratedOrbit 13 6204 = 553 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_13_6204 (m : Nat) :
    acceleratedOrbit 13 (2 ^ 13 * m + 6204) = 3 ^ 6 * m + 553 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_13_6204.1, data_13_6204.2]

/-- Complete interval computation for depth 13, residue 6205. -/
theorem bounds_13_6205 : exactInterval 13 6205 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_13_6205 (m : Nat) :
    stoppingTime (2 ^ 13 * m + 6205) 13 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_13_6205 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_13_6205 : oddCount 6205 13 = 6 ∧ acceleratedOrbit 13 6205 = 553 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_13_6205 (m : Nat) :
    acceleratedOrbit 13 (2 ^ 13 * m + 6205) = 3 ^ 6 * m + 553 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_13_6205.1, data_13_6205.2]

/-- Complete interval computation for depth 13, residue 6206. -/
theorem bounds_13_6206 : exactInterval 13 6206 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_13_6206 (m : Nat) :
    stoppingTime (2 ^ 13 * m + 6206) 13 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_13_6206 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_13_6206 : oddCount 6206 13 = 9 ∧ acceleratedOrbit 13 6206 = 14917 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_13_6206 (m : Nat) :
    acceleratedOrbit 13 (2 ^ 13 * m + 6206) = 3 ^ 9 * m + 14917 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_13_6206.1, data_13_6206.2]

/-- Complete interval computation for depth 13, residue 6207. -/
theorem bounds_13_6207 : exactInterval 13 6207 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_13_6207 (m : Nat) :
    stoppingTime (2 ^ 13 * m + 6207) 13 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_13_6207 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_13_6207 : oddCount 6207 13 = 9 ∧ acceleratedOrbit 13 6207 = 14917 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_13_6207 (m : Nat) :
    acceleratedOrbit 13 (2 ^ 13 * m + 6207) = 3 ^ 9 * m + 14917 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_13_6207.1, data_13_6207.2]

/-- Complete interval computation for depth 13, residue 6208. -/
theorem bounds_13_6208 : exactInterval 13 6208 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_13_6208 (m : Nat) :
    stoppingTime (2 ^ 13 * m + 6208) 13 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_13_6208 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_13_6208 : oddCount 6208 13 = 5 ∧ acceleratedOrbit 13 6208 = 188 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_13_6208 (m : Nat) :
    acceleratedOrbit 13 (2 ^ 13 * m + 6208) = 3 ^ 5 * m + 188 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_13_6208.1, data_13_6208.2]

/-- Complete interval computation for depth 13, residue 6209. -/
theorem bounds_13_6209 : exactInterval 13 6209 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_13_6209 (m : Nat) :
    stoppingTime (2 ^ 13 * m + 6209) 13 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_13_6209 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_13_6209 : oddCount 6209 13 = 7 ∧ acceleratedOrbit 13 6209 = 1660 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_13_6209 (m : Nat) :
    acceleratedOrbit 13 (2 ^ 13 * m + 6209) = 3 ^ 7 * m + 1660 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_13_6209.1, data_13_6209.2]

end Collatz.Research.StoppingAtlas.Batch0871
