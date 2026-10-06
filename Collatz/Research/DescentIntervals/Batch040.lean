import Collatz.Research.DescentIntervals.Classifier

namespace Collatz.Research.DescentIntervals.Batch040

/-- Complete interval computation for depth 8, residue 144. -/
theorem bounds_8_144 : exactInterval 8 144 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_8_144 (m : Nat) :
    stoppingTime (2 ^ 8 * m + 144) 8 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_8_144 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_8_144 : oddCount 144 8 = 3 ∧ acceleratedOrbit 8 144 = 17 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_8_144 (m : Nat) :
    acceleratedOrbit 8 (2 ^ 8 * m + 144) = 3 ^ 3 * m + 17 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_8_144.1, data_8_144.2]

/-- Complete interval computation for depth 8, residue 145. -/
theorem bounds_8_145 : exactInterval 8 145 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_8_145 (m : Nat) :
    stoppingTime (2 ^ 8 * m + 145) 8 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_8_145 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_8_145 : oddCount 145 8 = 4 ∧ acceleratedOrbit 8 145 = 47 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_8_145 (m : Nat) :
    acceleratedOrbit 8 (2 ^ 8 * m + 145) = 3 ^ 4 * m + 47 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_8_145.1, data_8_145.2]

/-- Complete interval computation for depth 8, residue 146. -/
theorem bounds_8_146 : exactInterval 8 146 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_8_146 (m : Nat) :
    stoppingTime (2 ^ 8 * m + 146) 8 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_8_146 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_8_146 : oddCount 146 8 = 4 ∧ acceleratedOrbit 8 146 = 47 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_8_146 (m : Nat) :
    acceleratedOrbit 8 (2 ^ 8 * m + 146) = 3 ^ 4 * m + 47 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_8_146.1, data_8_146.2]

/-- Complete interval computation for depth 8, residue 147. -/
theorem bounds_8_147 : exactInterval 8 147 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_8_147 (m : Nat) :
    stoppingTime (2 ^ 8 * m + 147) 8 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_8_147 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_8_147 : oddCount 147 8 = 4 ∧ acceleratedOrbit 8 147 = 47 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_8_147 (m : Nat) :
    acceleratedOrbit 8 (2 ^ 8 * m + 147) = 3 ^ 4 * m + 47 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_8_147.1, data_8_147.2]

/-- Complete interval computation for depth 8, residue 148. -/
theorem bounds_8_148 : exactInterval 8 148 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_8_148 (m : Nat) :
    stoppingTime (2 ^ 8 * m + 148) 8 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_8_148 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_8_148 : oddCount 148 8 = 3 ∧ acceleratedOrbit 8 148 = 17 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_8_148 (m : Nat) :
    acceleratedOrbit 8 (2 ^ 8 * m + 148) = 3 ^ 3 * m + 17 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_8_148.1, data_8_148.2]

/-- Complete interval computation for depth 8, residue 149. -/
theorem bounds_8_149 : exactInterval 8 149 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_8_149 (m : Nat) :
    stoppingTime (2 ^ 8 * m + 149) 8 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_8_149 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_8_149 : oddCount 149 8 = 3 ∧ acceleratedOrbit 8 149 = 17 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_8_149 (m : Nat) :
    acceleratedOrbit 8 (2 ^ 8 * m + 149) = 3 ^ 3 * m + 17 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_8_149.1, data_8_149.2]

/-- Complete interval computation for depth 8, residue 150. -/
theorem bounds_8_150 : exactInterval 8 150 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_8_150 (m : Nat) :
    stoppingTime (2 ^ 8 * m + 150) 8 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_8_150 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_8_150 : oddCount 150 8 = 3 ∧ acceleratedOrbit 8 150 = 16 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_8_150 (m : Nat) :
    acceleratedOrbit 8 (2 ^ 8 * m + 150) = 3 ^ 3 * m + 16 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_8_150.1, data_8_150.2]

/-- Complete interval computation for depth 8, residue 151. -/
theorem bounds_8_151 : exactInterval 8 151 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_8_151 (m : Nat) :
    stoppingTime (2 ^ 8 * m + 151) 8 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_8_151 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_8_151 : oddCount 151 8 = 3 ∧ acceleratedOrbit 8 151 = 16 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_8_151 (m : Nat) :
    acceleratedOrbit 8 (2 ^ 8 * m + 151) = 3 ^ 3 * m + 16 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_8_151.1, data_8_151.2]

/-- Complete interval computation for depth 8, residue 152. -/
theorem bounds_8_152 : exactInterval 8 152 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_8_152 (m : Nat) :
    stoppingTime (2 ^ 8 * m + 152) 8 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_8_152 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_8_152 : oddCount 152 8 = 3 ∧ acceleratedOrbit 8 152 = 17 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_8_152 (m : Nat) :
    acceleratedOrbit 8 (2 ^ 8 * m + 152) = 3 ^ 3 * m + 17 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_8_152.1, data_8_152.2]

/-- Complete interval computation for depth 8, residue 153. -/
theorem bounds_8_153 : exactInterval 8 153 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_8_153 (m : Nat) :
    stoppingTime (2 ^ 8 * m + 153) 8 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_8_153 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_8_153 : oddCount 153 8 = 4 ∧ acceleratedOrbit 8 153 = 49 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_8_153 (m : Nat) :
    acceleratedOrbit 8 (2 ^ 8 * m + 153) = 3 ^ 4 * m + 49 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_8_153.1, data_8_153.2]

end Collatz.Research.DescentIntervals.Batch040
