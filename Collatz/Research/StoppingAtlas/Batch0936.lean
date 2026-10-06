import Collatz.Research.DescentIntervals.Classifier

namespace Collatz.Research.StoppingAtlas.Batch0936

open Collatz.Research.DescentIntervals

set_option maxRecDepth 20000
set_option maxHeartbeats 0

/-- Complete interval computation for depth 13, residue 7193. -/
theorem bounds_13_7193 : exactInterval 13 7193 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_13_7193 (m : Nat) :
    stoppingTime (2 ^ 13 * m + 7193) 13 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_13_7193 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_13_7193 : oddCount 7193 13 = 8 ∧ acceleratedOrbit 13 7193 = 5764 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_13_7193 (m : Nat) :
    acceleratedOrbit 13 (2 ^ 13 * m + 7193) = 3 ^ 8 * m + 5764 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_13_7193.1, data_13_7193.2]

/-- Complete interval computation for depth 13, residue 7194. -/
theorem bounds_13_7194 : exactInterval 13 7194 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_13_7194 (m : Nat) :
    stoppingTime (2 ^ 13 * m + 7194) 13 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_13_7194 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_13_7194 : oddCount 7194 13 = 5 ∧ acceleratedOrbit 13 7194 = 215 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_13_7194 (m : Nat) :
    acceleratedOrbit 13 (2 ^ 13 * m + 7194) = 3 ^ 5 * m + 215 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_13_7194.1, data_13_7194.2]

/-- Complete interval computation for depth 13, residue 7195. -/
theorem bounds_13_7195 : exactInterval 13 7195 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_13_7195 (m : Nat) :
    stoppingTime (2 ^ 13 * m + 7195) 13 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_13_7195 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_13_7195 : oddCount 7195 13 = 9 ∧ acceleratedOrbit 13 7195 = 17291 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_13_7195 (m : Nat) :
    acceleratedOrbit 13 (2 ^ 13 * m + 7195) = 3 ^ 9 * m + 17291 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_13_7195.1, data_13_7195.2]

/-- Complete interval computation for depth 13, residue 7196. -/
theorem bounds_13_7196 : exactInterval 13 7196 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_13_7196 (m : Nat) :
    stoppingTime (2 ^ 13 * m + 7196) 13 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_13_7196 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_13_7196 : oddCount 7196 13 = 6 ∧ acceleratedOrbit 13 7196 = 641 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_13_7196 (m : Nat) :
    acceleratedOrbit 13 (2 ^ 13 * m + 7196) = 3 ^ 6 * m + 641 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_13_7196.1, data_13_7196.2]

/-- Complete interval computation for depth 13, residue 7197. -/
theorem bounds_13_7197 : exactInterval 13 7197 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_13_7197 (m : Nat) :
    stoppingTime (2 ^ 13 * m + 7197) 13 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_13_7197 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_13_7197 : oddCount 7197 13 = 6 ∧ acceleratedOrbit 13 7197 = 641 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_13_7197 (m : Nat) :
    acceleratedOrbit 13 (2 ^ 13 * m + 7197) = 3 ^ 6 * m + 641 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_13_7197.1, data_13_7197.2]

/-- Complete interval computation for depth 13, residue 7198. -/
theorem bounds_13_7198 : exactInterval 13 7198 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_13_7198 (m : Nat) :
    stoppingTime (2 ^ 13 * m + 7198) 13 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_13_7198 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_13_7198 : oddCount 7198 13 = 6 ∧ acceleratedOrbit 13 7198 = 641 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_13_7198 (m : Nat) :
    acceleratedOrbit 13 (2 ^ 13 * m + 7198) = 3 ^ 6 * m + 641 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_13_7198.1, data_13_7198.2]

/-- Complete interval computation for depth 13, residue 7199. -/
theorem bounds_13_7199 : exactInterval 13 7199 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_13_7199 (m : Nat) :
    stoppingTime (2 ^ 13 * m + 7199) 13 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_13_7199 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_13_7199 : oddCount 7199 13 = 9 ∧ acceleratedOrbit 13 7199 = 17300 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_13_7199 (m : Nat) :
    acceleratedOrbit 13 (2 ^ 13 * m + 7199) = 3 ^ 9 * m + 17300 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_13_7199.1, data_13_7199.2]

/-- Complete interval computation for depth 13, residue 7200. -/
theorem bounds_13_7200 : exactInterval 13 7200 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_13_7200 (m : Nat) :
    stoppingTime (2 ^ 13 * m + 7200) 13 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_13_7200 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_13_7200 : oddCount 7200 13 = 6 ∧ acceleratedOrbit 13 7200 = 647 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_13_7200 (m : Nat) :
    acceleratedOrbit 13 (2 ^ 13 * m + 7200) = 3 ^ 6 * m + 647 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_13_7200.1, data_13_7200.2]

/-- Complete interval computation for depth 13, residue 7201. -/
theorem bounds_13_7201 : exactInterval 13 7201 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_13_7201 (m : Nat) :
    stoppingTime (2 ^ 13 * m + 7201) 13 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_13_7201 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_13_7201 : oddCount 7201 13 = 8 ∧ acceleratedOrbit 13 7201 = 5771 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_13_7201 (m : Nat) :
    acceleratedOrbit 13 (2 ^ 13 * m + 7201) = 3 ^ 8 * m + 5771 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_13_7201.1, data_13_7201.2]

/-- Complete interval computation for depth 13, residue 7202. -/
theorem bounds_13_7202 : exactInterval 13 7202 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_13_7202 (m : Nat) :
    stoppingTime (2 ^ 13 * m + 7202) 13 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_13_7202 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_13_7202 : oddCount 7202 13 = 5 ∧ acceleratedOrbit 13 7202 = 215 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_13_7202 (m : Nat) :
    acceleratedOrbit 13 (2 ^ 13 * m + 7202) = 3 ^ 5 * m + 215 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_13_7202.1, data_13_7202.2]

/-- Complete interval computation for depth 13, residue 7203. -/
theorem bounds_13_7203 : exactInterval 13 7203 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_13_7203 (m : Nat) :
    stoppingTime (2 ^ 13 * m + 7203) 13 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_13_7203 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_13_7203 : oddCount 7203 13 = 5 ∧ acceleratedOrbit 13 7203 = 215 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_13_7203 (m : Nat) :
    acceleratedOrbit 13 (2 ^ 13 * m + 7203) = 3 ^ 5 * m + 215 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_13_7203.1, data_13_7203.2]

/-- Complete interval computation for depth 13, residue 7204. -/
theorem bounds_13_7204 : exactInterval 13 7204 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_13_7204 (m : Nat) :
    stoppingTime (2 ^ 13 * m + 7204) 13 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_13_7204 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_13_7204 : oddCount 7204 13 = 8 ∧ acceleratedOrbit 13 7204 = 5777 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_13_7204 (m : Nat) :
    acceleratedOrbit 13 (2 ^ 13 * m + 7204) = 3 ^ 8 * m + 5777 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_13_7204.1, data_13_7204.2]

/-- Complete interval computation for depth 13, residue 7205. -/
theorem bounds_13_7205 : exactInterval 13 7205 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_13_7205 (m : Nat) :
    stoppingTime (2 ^ 13 * m + 7205) 13 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_13_7205 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_13_7205 : oddCount 7205 13 = 8 ∧ acceleratedOrbit 13 7205 = 5777 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_13_7205 (m : Nat) :
    acceleratedOrbit 13 (2 ^ 13 * m + 7205) = 3 ^ 8 * m + 5777 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_13_7205.1, data_13_7205.2]

/-- Complete interval computation for depth 13, residue 7206. -/
theorem bounds_13_7206 : exactInterval 13 7206 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_13_7206 (m : Nat) :
    stoppingTime (2 ^ 13 * m + 7206) 13 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_13_7206 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_13_7206 : oddCount 7206 13 = 8 ∧ acceleratedOrbit 13 7206 = 5777 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_13_7206 (m : Nat) :
    acceleratedOrbit 13 (2 ^ 13 * m + 7206) = 3 ^ 8 * m + 5777 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_13_7206.1, data_13_7206.2]

/-- Complete interval computation for depth 13, residue 7207. -/
theorem bounds_13_7207 : exactInterval 13 7207 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_13_7207 (m : Nat) :
    stoppingTime (2 ^ 13 * m + 7207) 13 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_13_7207 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_13_7207 : oddCount 7207 13 = 7 ∧ acceleratedOrbit 13 7207 = 1925 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_13_7207 (m : Nat) :
    acceleratedOrbit 13 (2 ^ 13 * m + 7207) = 3 ^ 7 * m + 1925 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_13_7207.1, data_13_7207.2]

end Collatz.Research.StoppingAtlas.Batch0936
