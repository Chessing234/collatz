import Collatz.Research.DescentIntervals.Classifier

namespace Collatz.Research.StoppingAtlas.Batch0607

open Collatz.Research.DescentIntervals

set_option maxRecDepth 20000
set_option maxHeartbeats 0

/-- Complete interval computation for depth 13, residue 2140. -/
theorem bounds_13_2140 : exactInterval 13 2140 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_13_2140 (m : Nat) :
    stoppingTime (2 ^ 13 * m + 2140) 13 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_13_2140 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_13_2140 : oddCount 2140 13 = 5 ∧ acceleratedOrbit 13 2140 = 64 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_13_2140 (m : Nat) :
    acceleratedOrbit 13 (2 ^ 13 * m + 2140) = 3 ^ 5 * m + 64 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_13_2140.1, data_13_2140.2]

/-- Complete interval computation for depth 13, residue 2141. -/
theorem bounds_13_2141 : exactInterval 13 2141 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_13_2141 (m : Nat) :
    stoppingTime (2 ^ 13 * m + 2141) 13 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_13_2141 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_13_2141 : oddCount 2141 13 = 5 ∧ acceleratedOrbit 13 2141 = 64 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_13_2141 (m : Nat) :
    acceleratedOrbit 13 (2 ^ 13 * m + 2141) = 3 ^ 5 * m + 64 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_13_2141.1, data_13_2141.2]

/-- Complete interval computation for depth 13, residue 2142. -/
theorem bounds_13_2142 : exactInterval 13 2142 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_13_2142 (m : Nat) :
    stoppingTime (2 ^ 13 * m + 2142) 13 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_13_2142 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_13_2142 : oddCount 2142 13 = 8 ∧ acceleratedOrbit 13 2142 = 1718 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_13_2142 (m : Nat) :
    acceleratedOrbit 13 (2 ^ 13 * m + 2142) = 3 ^ 8 * m + 1718 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_13_2142.1, data_13_2142.2]

/-- Complete interval computation for depth 13, residue 2143. -/
theorem bounds_13_2143 : exactInterval 13 2143 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_13_2143 (m : Nat) :
    stoppingTime (2 ^ 13 * m + 2143) 13 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_13_2143 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_13_2143 : oddCount 2143 13 = 8 ∧ acceleratedOrbit 13 2143 = 1718 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_13_2143 (m : Nat) :
    acceleratedOrbit 13 (2 ^ 13 * m + 2143) = 3 ^ 8 * m + 1718 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_13_2143.1, data_13_2143.2]

/-- Complete interval computation for depth 13, residue 2144. -/
theorem bounds_13_2144 : exactInterval 13 2144 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_13_2144 (m : Nat) :
    stoppingTime (2 ^ 13 * m + 2144) 13 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_13_2144 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_13_2144 : oddCount 2144 13 = 4 ∧ acceleratedOrbit 13 2144 = 22 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_13_2144 (m : Nat) :
    acceleratedOrbit 13 (2 ^ 13 * m + 2144) = 3 ^ 4 * m + 22 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_13_2144.1, data_13_2144.2]

/-- Complete interval computation for depth 13, residue 2145. -/
theorem bounds_13_2145 : exactInterval 13 2145 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_13_2145 (m : Nat) :
    stoppingTime (2 ^ 13 * m + 2145) 13 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_13_2145 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_13_2145 : oddCount 2145 13 = 8 ∧ acceleratedOrbit 13 2145 = 1721 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_13_2145 (m : Nat) :
    acceleratedOrbit 13 (2 ^ 13 * m + 2145) = 3 ^ 8 * m + 1721 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_13_2145.1, data_13_2145.2]

/-- Complete interval computation for depth 13, residue 2146. -/
theorem bounds_13_2146 : exactInterval 13 2146 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_13_2146 (m : Nat) :
    stoppingTime (2 ^ 13 * m + 2146) 13 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_13_2146 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_13_2146 : oddCount 2146 13 = 5 ∧ acceleratedOrbit 13 2146 = 64 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_13_2146 (m : Nat) :
    acceleratedOrbit 13 (2 ^ 13 * m + 2146) = 3 ^ 5 * m + 64 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_13_2146.1, data_13_2146.2]

/-- Complete interval computation for depth 13, residue 2147. -/
theorem bounds_13_2147 : exactInterval 13 2147 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_13_2147 (m : Nat) :
    stoppingTime (2 ^ 13 * m + 2147) 13 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_13_2147 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_13_2147 : oddCount 2147 13 = 5 ∧ acceleratedOrbit 13 2147 = 64 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_13_2147 (m : Nat) :
    acceleratedOrbit 13 (2 ^ 13 * m + 2147) = 3 ^ 5 * m + 64 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_13_2147.1, data_13_2147.2]

/-- Complete interval computation for depth 13, residue 2148. -/
theorem bounds_13_2148 : exactInterval 13 2148 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_13_2148 (m : Nat) :
    stoppingTime (2 ^ 13 * m + 2148) 13 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_13_2148 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_13_2148 : oddCount 2148 13 = 5 ∧ acceleratedOrbit 13 2148 = 64 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_13_2148 (m : Nat) :
    acceleratedOrbit 13 (2 ^ 13 * m + 2148) = 3 ^ 5 * m + 64 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_13_2148.1, data_13_2148.2]

/-- Complete interval computation for depth 13, residue 2149. -/
theorem bounds_13_2149 : exactInterval 13 2149 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_13_2149 (m : Nat) :
    stoppingTime (2 ^ 13 * m + 2149) 13 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_13_2149 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_13_2149 : oddCount 2149 13 = 5 ∧ acceleratedOrbit 13 2149 = 64 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_13_2149 (m : Nat) :
    acceleratedOrbit 13 (2 ^ 13 * m + 2149) = 3 ^ 5 * m + 64 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_13_2149.1, data_13_2149.2]

/-- Complete interval computation for depth 13, residue 2150. -/
theorem bounds_13_2150 : exactInterval 13 2150 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_13_2150 (m : Nat) :
    stoppingTime (2 ^ 13 * m + 2150) 13 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_13_2150 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_13_2150 : oddCount 2150 13 = 5 ∧ acceleratedOrbit 13 2150 = 64 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_13_2150 (m : Nat) :
    acceleratedOrbit 13 (2 ^ 13 * m + 2150) = 3 ^ 5 * m + 64 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_13_2150.1, data_13_2150.2]

/-- Complete interval computation for depth 13, residue 2151. -/
theorem bounds_13_2151 : exactInterval 13 2151 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_13_2151 (m : Nat) :
    stoppingTime (2 ^ 13 * m + 2151) 13 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_13_2151 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_13_2151 : oddCount 2151 13 = 10 ∧ acceleratedOrbit 13 2151 = 15515 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_13_2151 (m : Nat) :
    acceleratedOrbit 13 (2 ^ 13 * m + 2151) = 3 ^ 10 * m + 15515 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_13_2151.1, data_13_2151.2]

/-- Complete interval computation for depth 13, residue 2152. -/
theorem bounds_13_2152 : exactInterval 13 2152 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_13_2152 (m : Nat) :
    stoppingTime (2 ^ 13 * m + 2152) 13 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_13_2152 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_13_2152 : oddCount 2152 13 = 4 ∧ acceleratedOrbit 13 2152 = 22 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_13_2152 (m : Nat) :
    acceleratedOrbit 13 (2 ^ 13 * m + 2152) = 3 ^ 4 * m + 22 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_13_2152.1, data_13_2152.2]

/-- Complete interval computation for depth 13, residue 2153. -/
theorem bounds_13_2153 : exactInterval 13 2153 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_13_2153 (m : Nat) :
    stoppingTime (2 ^ 13 * m + 2153) 13 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_13_2153 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_13_2153 : oddCount 2153 13 = 8 ∧ acceleratedOrbit 13 2153 = 1727 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_13_2153 (m : Nat) :
    acceleratedOrbit 13 (2 ^ 13 * m + 2153) = 3 ^ 8 * m + 1727 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_13_2153.1, data_13_2153.2]

/-- Complete interval computation for depth 13, residue 2154. -/
theorem bounds_13_2154 : exactInterval 13 2154 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_13_2154 (m : Nat) :
    stoppingTime (2 ^ 13 * m + 2154) 13 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_13_2154 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_13_2154 : oddCount 2154 13 = 4 ∧ acceleratedOrbit 13 2154 = 22 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_13_2154 (m : Nat) :
    acceleratedOrbit 13 (2 ^ 13 * m + 2154) = 3 ^ 4 * m + 22 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_13_2154.1, data_13_2154.2]

end Collatz.Research.StoppingAtlas.Batch0607
