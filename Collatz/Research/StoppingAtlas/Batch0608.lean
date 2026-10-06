import Collatz.Research.DescentIntervals.Classifier

namespace Collatz.Research.StoppingAtlas.Batch0608

open Collatz.Research.DescentIntervals

set_option maxRecDepth 20000
set_option maxHeartbeats 0

/-- Complete interval computation for depth 13, residue 2155. -/
theorem bounds_13_2155 : exactInterval 13 2155 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_13_2155 (m : Nat) :
    stoppingTime (2 ^ 13 * m + 2155) 13 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_13_2155 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_13_2155 : oddCount 2155 13 = 10 ∧ acceleratedOrbit 13 2155 = 15551 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_13_2155 (m : Nat) :
    acceleratedOrbit 13 (2 ^ 13 * m + 2155) = 3 ^ 10 * m + 15551 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_13_2155.1, data_13_2155.2]

/-- Complete interval computation for depth 13, residue 2156. -/
theorem bounds_13_2156 : exactInterval 13 2156 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_13_2156 (m : Nat) :
    stoppingTime (2 ^ 13 * m + 2156) 13 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_13_2156 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_13_2156 : oddCount 2156 13 = 7 ∧ acceleratedOrbit 13 2156 = 577 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_13_2156 (m : Nat) :
    acceleratedOrbit 13 (2 ^ 13 * m + 2156) = 3 ^ 7 * m + 577 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_13_2156.1, data_13_2156.2]

/-- Complete interval computation for depth 13, residue 2157. -/
theorem bounds_13_2157 : exactInterval 13 2157 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_13_2157 (m : Nat) :
    stoppingTime (2 ^ 13 * m + 2157) 13 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_13_2157 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_13_2157 : oddCount 2157 13 = 7 ∧ acceleratedOrbit 13 2157 = 577 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_13_2157 (m : Nat) :
    acceleratedOrbit 13 (2 ^ 13 * m + 2157) = 3 ^ 7 * m + 577 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_13_2157.1, data_13_2157.2]

/-- Complete interval computation for depth 13, residue 2158. -/
theorem bounds_13_2158 : exactInterval 13 2158 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_13_2158 (m : Nat) :
    stoppingTime (2 ^ 13 * m + 2158) 13 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_13_2158 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_13_2158 : oddCount 2158 13 = 7 ∧ acceleratedOrbit 13 2158 = 577 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_13_2158 (m : Nat) :
    acceleratedOrbit 13 (2 ^ 13 * m + 2158) = 3 ^ 7 * m + 577 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_13_2158.1, data_13_2158.2]

/-- Complete interval computation for depth 13, residue 2159. -/
theorem bounds_13_2159 : exactInterval 13 2159 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_13_2159 (m : Nat) :
    stoppingTime (2 ^ 13 * m + 2159) 13 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_13_2159 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_13_2159 : oddCount 2159 13 = 10 ∧ acceleratedOrbit 13 2159 = 15572 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_13_2159 (m : Nat) :
    acceleratedOrbit 13 (2 ^ 13 * m + 2159) = 3 ^ 10 * m + 15572 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_13_2159.1, data_13_2159.2]

/-- Complete interval computation for depth 13, residue 2160. -/
theorem bounds_13_2160 : exactInterval 13 2160 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_13_2160 (m : Nat) :
    stoppingTime (2 ^ 13 * m + 2160) 13 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_13_2160 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_13_2160 : oddCount 2160 13 = 5 ∧ acceleratedOrbit 13 2160 = 65 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_13_2160 (m : Nat) :
    acceleratedOrbit 13 (2 ^ 13 * m + 2160) = 3 ^ 5 * m + 65 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_13_2160.1, data_13_2160.2]

/-- Complete interval computation for depth 13, residue 2161. -/
theorem bounds_13_2161 : exactInterval 13 2161 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_13_2161 (m : Nat) :
    stoppingTime (2 ^ 13 * m + 2161) 13 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_13_2161 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_13_2161 : oddCount 2161 13 = 4 ∧ acceleratedOrbit 13 2161 = 22 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_13_2161 (m : Nat) :
    acceleratedOrbit 13 (2 ^ 13 * m + 2161) = 3 ^ 4 * m + 22 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_13_2161.1, data_13_2161.2]

/-- Complete interval computation for depth 13, residue 2162. -/
theorem bounds_13_2162 : exactInterval 13 2162 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_13_2162 (m : Nat) :
    stoppingTime (2 ^ 13 * m + 2162) 13 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_13_2162 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_13_2162 : oddCount 2162 13 = 6 ∧ acceleratedOrbit 13 2162 = 193 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_13_2162 (m : Nat) :
    acceleratedOrbit 13 (2 ^ 13 * m + 2162) = 3 ^ 6 * m + 193 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_13_2162.1, data_13_2162.2]

/-- Complete interval computation for depth 13, residue 2163. -/
theorem bounds_13_2163 : exactInterval 13 2163 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_13_2163 (m : Nat) :
    stoppingTime (2 ^ 13 * m + 2163) 13 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_13_2163 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_13_2163 : oddCount 2163 13 = 6 ∧ acceleratedOrbit 13 2163 = 193 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_13_2163 (m : Nat) :
    acceleratedOrbit 13 (2 ^ 13 * m + 2163) = 3 ^ 6 * m + 193 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_13_2163.1, data_13_2163.2]

/-- Complete interval computation for depth 13, residue 2164. -/
theorem bounds_13_2164 : exactInterval 13 2164 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_13_2164 (m : Nat) :
    stoppingTime (2 ^ 13 * m + 2164) 13 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_13_2164 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_13_2164 : oddCount 2164 13 = 5 ∧ acceleratedOrbit 13 2164 = 65 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_13_2164 (m : Nat) :
    acceleratedOrbit 13 (2 ^ 13 * m + 2164) = 3 ^ 5 * m + 65 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_13_2164.1, data_13_2164.2]

/-- Complete interval computation for depth 13, residue 2165. -/
theorem bounds_13_2165 : exactInterval 13 2165 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_13_2165 (m : Nat) :
    stoppingTime (2 ^ 13 * m + 2165) 13 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_13_2165 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_13_2165 : oddCount 2165 13 = 5 ∧ acceleratedOrbit 13 2165 = 65 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_13_2165 (m : Nat) :
    acceleratedOrbit 13 (2 ^ 13 * m + 2165) = 3 ^ 5 * m + 65 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_13_2165.1, data_13_2165.2]

/-- Complete interval computation for depth 13, residue 2166. -/
theorem bounds_13_2166 : exactInterval 13 2166 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_13_2166 (m : Nat) :
    stoppingTime (2 ^ 13 * m + 2166) 13 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_13_2166 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_13_2166 : oddCount 2166 13 = 7 ∧ acceleratedOrbit 13 2166 = 580 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_13_2166 (m : Nat) :
    acceleratedOrbit 13 (2 ^ 13 * m + 2166) = 3 ^ 7 * m + 580 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_13_2166.1, data_13_2166.2]

/-- Complete interval computation for depth 13, residue 2167. -/
theorem bounds_13_2167 : exactInterval 13 2167 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_13_2167 (m : Nat) :
    stoppingTime (2 ^ 13 * m + 2167) 13 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_13_2167 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_13_2167 : oddCount 2167 13 = 7 ∧ acceleratedOrbit 13 2167 = 580 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_13_2167 (m : Nat) :
    acceleratedOrbit 13 (2 ^ 13 * m + 2167) = 3 ^ 7 * m + 580 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_13_2167.1, data_13_2167.2]

/-- Complete interval computation for depth 13, residue 2168. -/
theorem bounds_13_2168 : exactInterval 13 2168 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_13_2168 (m : Nat) :
    stoppingTime (2 ^ 13 * m + 2168) 13 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_13_2168 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_13_2168 : oddCount 2168 13 = 5 ∧ acceleratedOrbit 13 2168 = 65 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_13_2168 (m : Nat) :
    acceleratedOrbit 13 (2 ^ 13 * m + 2168) = 3 ^ 5 * m + 65 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_13_2168.1, data_13_2168.2]

/-- Complete interval computation for depth 13, residue 2169. -/
theorem bounds_13_2169 : exactInterval 13 2169 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_13_2169 (m : Nat) :
    stoppingTime (2 ^ 13 * m + 2169) 13 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_13_2169 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_13_2169 : oddCount 2169 13 = 8 ∧ acceleratedOrbit 13 2169 = 1739 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_13_2169 (m : Nat) :
    acceleratedOrbit 13 (2 ^ 13 * m + 2169) = 3 ^ 8 * m + 1739 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_13_2169.1, data_13_2169.2]

end Collatz.Research.StoppingAtlas.Batch0608
