import Collatz.Research.DescentIntervals.Classifier

namespace Collatz.Research.StoppingAtlas.Batch0477

open Collatz.Research.DescentIntervals

set_option maxRecDepth 20000
set_option maxHeartbeats 0

/-- Complete interval computation for depth 13, residue 143. -/
theorem bounds_13_143 : exactInterval 13 143 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_13_143 (m : Nat) :
    stoppingTime (2 ^ 13 * m + 143) 13 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_13_143 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_13_143 : oddCount 143 13 = 9 ∧ acceleratedOrbit 13 143 = 350 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_13_143 (m : Nat) :
    acceleratedOrbit 13 (2 ^ 13 * m + 143) = 3 ^ 9 * m + 350 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_13_143.1, data_13_143.2]

/-- Complete interval computation for depth 13, residue 144. -/
theorem bounds_13_144 : exactInterval 13 144 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_13_144 (m : Nat) :
    stoppingTime (2 ^ 13 * m + 144) 13 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_13_144 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_13_144 : oddCount 144 13 = 5 ∧ acceleratedOrbit 13 144 = 5 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_13_144 (m : Nat) :
    acceleratedOrbit 13 (2 ^ 13 * m + 144) = 3 ^ 5 * m + 5 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_13_144.1, data_13_144.2]

/-- Complete interval computation for depth 13, residue 145. -/
theorem bounds_13_145 : exactInterval 13 145 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_13_145 (m : Nat) :
    stoppingTime (2 ^ 13 * m + 145) 13 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_13_145 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_13_145 : oddCount 145 13 = 8 ∧ acceleratedOrbit 13 145 = 121 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_13_145 (m : Nat) :
    acceleratedOrbit 13 (2 ^ 13 * m + 145) = 3 ^ 8 * m + 121 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_13_145.1, data_13_145.2]

/-- Complete interval computation for depth 13, residue 146. -/
theorem bounds_13_146 : exactInterval 13 146 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_13_146 (m : Nat) :
    stoppingTime (2 ^ 13 * m + 146) 13 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_13_146 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_13_146 : oddCount 146 13 = 8 ∧ acceleratedOrbit 13 146 = 121 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_13_146 (m : Nat) :
    acceleratedOrbit 13 (2 ^ 13 * m + 146) = 3 ^ 8 * m + 121 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_13_146.1, data_13_146.2]

/-- Complete interval computation for depth 13, residue 147. -/
theorem bounds_13_147 : exactInterval 13 147 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_13_147 (m : Nat) :
    stoppingTime (2 ^ 13 * m + 147) 13 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_13_147 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_13_147 : oddCount 147 13 = 8 ∧ acceleratedOrbit 13 147 = 121 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_13_147 (m : Nat) :
    acceleratedOrbit 13 (2 ^ 13 * m + 147) = 3 ^ 8 * m + 121 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_13_147.1, data_13_147.2]

/-- Complete interval computation for depth 13, residue 148. -/
theorem bounds_13_148 : exactInterval 13 148 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_13_148 (m : Nat) :
    stoppingTime (2 ^ 13 * m + 148) 13 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_13_148 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_13_148 : oddCount 148 13 = 5 ∧ acceleratedOrbit 13 148 = 5 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_13_148 (m : Nat) :
    acceleratedOrbit 13 (2 ^ 13 * m + 148) = 3 ^ 5 * m + 5 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_13_148.1, data_13_148.2]

/-- Complete interval computation for depth 13, residue 149. -/
theorem bounds_13_149 : exactInterval 13 149 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_13_149 (m : Nat) :
    stoppingTime (2 ^ 13 * m + 149) 13 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_13_149 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_13_149 : oddCount 149 13 = 5 ∧ acceleratedOrbit 13 149 = 5 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_13_149 (m : Nat) :
    acceleratedOrbit 13 (2 ^ 13 * m + 149) = 3 ^ 5 * m + 5 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_13_149.1, data_13_149.2]

/-- Complete interval computation for depth 13, residue 150. -/
theorem bounds_13_150 : exactInterval 13 150 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_13_150 (m : Nat) :
    stoppingTime (2 ^ 13 * m + 150) 13 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_13_150 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_13_150 : oddCount 150 13 = 4 ∧ acceleratedOrbit 13 150 = 2 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_13_150 (m : Nat) :
    acceleratedOrbit 13 (2 ^ 13 * m + 150) = 3 ^ 4 * m + 2 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_13_150.1, data_13_150.2]

/-- Complete interval computation for depth 13, residue 151. -/
theorem bounds_13_151 : exactInterval 13 151 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_13_151 (m : Nat) :
    stoppingTime (2 ^ 13 * m + 151) 13 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_13_151 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_13_151 : oddCount 151 13 = 4 ∧ acceleratedOrbit 13 151 = 2 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_13_151 (m : Nat) :
    acceleratedOrbit 13 (2 ^ 13 * m + 151) = 3 ^ 4 * m + 2 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_13_151.1, data_13_151.2]

/-- Complete interval computation for depth 13, residue 152. -/
theorem bounds_13_152 : exactInterval 13 152 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_13_152 (m : Nat) :
    stoppingTime (2 ^ 13 * m + 152) 13 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_13_152 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_13_152 : oddCount 152 13 = 5 ∧ acceleratedOrbit 13 152 = 5 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_13_152 (m : Nat) :
    acceleratedOrbit 13 (2 ^ 13 * m + 152) = 3 ^ 5 * m + 5 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_13_152.1, data_13_152.2]

/-- Complete interval computation for depth 13, residue 153. -/
theorem bounds_13_153 : exactInterval 13 153 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_13_153 (m : Nat) :
    stoppingTime (2 ^ 13 * m + 153) 13 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_13_153 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_13_153 : oddCount 153 13 = 6 ∧ acceleratedOrbit 13 153 = 14 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_13_153 (m : Nat) :
    acceleratedOrbit 13 (2 ^ 13 * m + 153) = 3 ^ 6 * m + 14 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_13_153.1, data_13_153.2]

/-- Complete interval computation for depth 13, residue 154. -/
theorem bounds_13_154 : exactInterval 13 154 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_13_154 (m : Nat) :
    stoppingTime (2 ^ 13 * m + 154) 13 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_13_154 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_13_154 : oddCount 154 13 = 5 ∧ acceleratedOrbit 13 154 = 5 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_13_154 (m : Nat) :
    acceleratedOrbit 13 (2 ^ 13 * m + 154) = 3 ^ 5 * m + 5 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_13_154.1, data_13_154.2]

/-- Complete interval computation for depth 13, residue 155. -/
theorem bounds_13_155 : exactInterval 13 155 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_13_155 (m : Nat) :
    stoppingTime (2 ^ 13 * m + 155) 13 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_13_155 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_13_155 : oddCount 155 13 = 9 ∧ acceleratedOrbit 13 155 = 377 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_13_155 (m : Nat) :
    acceleratedOrbit 13 (2 ^ 13 * m + 155) = 3 ^ 9 * m + 377 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_13_155.1, data_13_155.2]

/-- Complete interval computation for depth 13, residue 156. -/
theorem bounds_13_156 : exactInterval 13 156 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_13_156 (m : Nat) :
    stoppingTime (2 ^ 13 * m + 156) 13 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_13_156 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_13_156 : oddCount 156 13 = 7 ∧ acceleratedOrbit 13 156 = 44 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_13_156 (m : Nat) :
    acceleratedOrbit 13 (2 ^ 13 * m + 156) = 3 ^ 7 * m + 44 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_13_156.1, data_13_156.2]

/-- Complete interval computation for depth 13, residue 157. -/
theorem bounds_13_157 : exactInterval 13 157 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_13_157 (m : Nat) :
    stoppingTime (2 ^ 13 * m + 157) 13 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_13_157 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_13_157 : oddCount 157 13 = 7 ∧ acceleratedOrbit 13 157 = 44 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_13_157 (m : Nat) :
    acceleratedOrbit 13 (2 ^ 13 * m + 157) = 3 ^ 7 * m + 44 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_13_157.1, data_13_157.2]

end Collatz.Research.StoppingAtlas.Batch0477
