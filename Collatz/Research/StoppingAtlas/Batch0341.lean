import Collatz.Research.DescentIntervals.Classifier

namespace Collatz.Research.StoppingAtlas.Batch0341

open Collatz.Research.DescentIntervals

set_option maxRecDepth 20000
set_option maxHeartbeats 0

/-- Complete interval computation for depth 12, residue 2150. -/
theorem bounds_12_2150 : exactInterval 12 2150 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_12_2150 (m : Nat) :
    stoppingTime (2 ^ 12 * m + 2150) 12 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_12_2150 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_12_2150 : oddCount 2150 12 = 5 ∧ acceleratedOrbit 12 2150 = 128 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_12_2150 (m : Nat) :
    acceleratedOrbit 12 (2 ^ 12 * m + 2150) = 3 ^ 5 * m + 128 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_12_2150.1, data_12_2150.2]

/-- Complete interval computation for depth 12, residue 2151. -/
theorem bounds_12_2151 : exactInterval 12 2151 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_12_2151 (m : Nat) :
    stoppingTime (2 ^ 12 * m + 2151) 12 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_12_2151 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_12_2151 : oddCount 2151 12 = 9 ∧ acceleratedOrbit 12 2151 = 10343 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_12_2151 (m : Nat) :
    acceleratedOrbit 12 (2 ^ 12 * m + 2151) = 3 ^ 9 * m + 10343 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_12_2151.1, data_12_2151.2]

/-- Complete interval computation for depth 12, residue 2152. -/
theorem bounds_12_2152 : exactInterval 12 2152 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_12_2152 (m : Nat) :
    stoppingTime (2 ^ 12 * m + 2152) 12 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_12_2152 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_12_2152 : oddCount 2152 12 = 4 ∧ acceleratedOrbit 12 2152 = 44 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_12_2152 (m : Nat) :
    acceleratedOrbit 12 (2 ^ 12 * m + 2152) = 3 ^ 4 * m + 44 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_12_2152.1, data_12_2152.2]

/-- Complete interval computation for depth 12, residue 2153. -/
theorem bounds_12_2153 : exactInterval 12 2153 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_12_2153 (m : Nat) :
    stoppingTime (2 ^ 12 * m + 2153) 12 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_12_2153 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_12_2153 : oddCount 2153 12 = 7 ∧ acceleratedOrbit 12 2153 = 1151 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_12_2153 (m : Nat) :
    acceleratedOrbit 12 (2 ^ 12 * m + 2153) = 3 ^ 7 * m + 1151 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_12_2153.1, data_12_2153.2]

/-- Complete interval computation for depth 12, residue 2154. -/
theorem bounds_12_2154 : exactInterval 12 2154 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_12_2154 (m : Nat) :
    stoppingTime (2 ^ 12 * m + 2154) 12 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_12_2154 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_12_2154 : oddCount 2154 12 = 4 ∧ acceleratedOrbit 12 2154 = 44 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_12_2154 (m : Nat) :
    acceleratedOrbit 12 (2 ^ 12 * m + 2154) = 3 ^ 4 * m + 44 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_12_2154.1, data_12_2154.2]

/-- Complete interval computation for depth 12, residue 2155. -/
theorem bounds_12_2155 : exactInterval 12 2155 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_12_2155 (m : Nat) :
    stoppingTime (2 ^ 12 * m + 2155) 12 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_12_2155 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_12_2155 : oddCount 2155 12 = 9 ∧ acceleratedOrbit 12 2155 = 10367 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_12_2155 (m : Nat) :
    acceleratedOrbit 12 (2 ^ 12 * m + 2155) = 3 ^ 9 * m + 10367 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_12_2155.1, data_12_2155.2]

/-- Complete interval computation for depth 12, residue 2156. -/
theorem bounds_12_2156 : exactInterval 12 2156 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_12_2156 (m : Nat) :
    stoppingTime (2 ^ 12 * m + 2156) 12 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_12_2156 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_12_2156 : oddCount 2156 12 = 7 ∧ acceleratedOrbit 12 2156 = 1154 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_12_2156 (m : Nat) :
    acceleratedOrbit 12 (2 ^ 12 * m + 2156) = 3 ^ 7 * m + 1154 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_12_2156.1, data_12_2156.2]

/-- Complete interval computation for depth 12, residue 2157. -/
theorem bounds_12_2157 : exactInterval 12 2157 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_12_2157 (m : Nat) :
    stoppingTime (2 ^ 12 * m + 2157) 12 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_12_2157 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_12_2157 : oddCount 2157 12 = 7 ∧ acceleratedOrbit 12 2157 = 1154 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_12_2157 (m : Nat) :
    acceleratedOrbit 12 (2 ^ 12 * m + 2157) = 3 ^ 7 * m + 1154 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_12_2157.1, data_12_2157.2]

/-- Complete interval computation for depth 12, residue 2158. -/
theorem bounds_12_2158 : exactInterval 12 2158 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_12_2158 (m : Nat) :
    stoppingTime (2 ^ 12 * m + 2158) 12 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_12_2158 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_12_2158 : oddCount 2158 12 = 7 ∧ acceleratedOrbit 12 2158 = 1154 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_12_2158 (m : Nat) :
    acceleratedOrbit 12 (2 ^ 12 * m + 2158) = 3 ^ 7 * m + 1154 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_12_2158.1, data_12_2158.2]

/-- Complete interval computation for depth 12, residue 2159. -/
theorem bounds_12_2159 : exactInterval 12 2159 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_12_2159 (m : Nat) :
    stoppingTime (2 ^ 12 * m + 2159) 12 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_12_2159 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_12_2159 : oddCount 2159 12 = 9 ∧ acceleratedOrbit 12 2159 = 10381 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_12_2159 (m : Nat) :
    acceleratedOrbit 12 (2 ^ 12 * m + 2159) = 3 ^ 9 * m + 10381 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_12_2159.1, data_12_2159.2]

/-- Complete interval computation for depth 12, residue 2160. -/
theorem bounds_12_2160 : exactInterval 12 2160 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_12_2160 (m : Nat) :
    stoppingTime (2 ^ 12 * m + 2160) 12 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_12_2160 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_12_2160 : oddCount 2160 12 = 4 ∧ acceleratedOrbit 12 2160 = 43 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_12_2160 (m : Nat) :
    acceleratedOrbit 12 (2 ^ 12 * m + 2160) = 3 ^ 4 * m + 43 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_12_2160.1, data_12_2160.2]

/-- Complete interval computation for depth 12, residue 2161. -/
theorem bounds_12_2161 : exactInterval 12 2161 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_12_2161 (m : Nat) :
    stoppingTime (2 ^ 12 * m + 2161) 12 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_12_2161 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_12_2161 : oddCount 2161 12 = 4 ∧ acceleratedOrbit 12 2161 = 44 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_12_2161 (m : Nat) :
    acceleratedOrbit 12 (2 ^ 12 * m + 2161) = 3 ^ 4 * m + 44 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_12_2161.1, data_12_2161.2]

/-- Complete interval computation for depth 12, residue 2162. -/
theorem bounds_12_2162 : exactInterval 12 2162 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_12_2162 (m : Nat) :
    stoppingTime (2 ^ 12 * m + 2162) 12 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_12_2162 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_12_2162 : oddCount 2162 12 = 6 ∧ acceleratedOrbit 12 2162 = 386 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_12_2162 (m : Nat) :
    acceleratedOrbit 12 (2 ^ 12 * m + 2162) = 3 ^ 6 * m + 386 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_12_2162.1, data_12_2162.2]

/-- Complete interval computation for depth 12, residue 2163. -/
theorem bounds_12_2163 : exactInterval 12 2163 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_12_2163 (m : Nat) :
    stoppingTime (2 ^ 12 * m + 2163) 12 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_12_2163 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_12_2163 : oddCount 2163 12 = 6 ∧ acceleratedOrbit 12 2163 = 386 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_12_2163 (m : Nat) :
    acceleratedOrbit 12 (2 ^ 12 * m + 2163) = 3 ^ 6 * m + 386 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_12_2163.1, data_12_2163.2]

/-- Complete interval computation for depth 12, residue 2164. -/
theorem bounds_12_2164 : exactInterval 12 2164 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_12_2164 (m : Nat) :
    stoppingTime (2 ^ 12 * m + 2164) 12 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_12_2164 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_12_2164 : oddCount 2164 12 = 4 ∧ acceleratedOrbit 12 2164 = 43 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_12_2164 (m : Nat) :
    acceleratedOrbit 12 (2 ^ 12 * m + 2164) = 3 ^ 4 * m + 43 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_12_2164.1, data_12_2164.2]

end Collatz.Research.StoppingAtlas.Batch0341
