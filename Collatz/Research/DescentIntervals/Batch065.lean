import Collatz.Research.DescentIntervals.Classifier

namespace Collatz.Research.DescentIntervals.Batch065

/-- Complete interval computation for depth 9, residue 144. -/
theorem bounds_9_144 : exactInterval 9 144 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_9_144 (m : Nat) :
    stoppingTime (2 ^ 9 * m + 144) 9 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_9_144 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_9_144 : oddCount 144 9 = 4 ∧ acceleratedOrbit 9 144 = 26 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_9_144 (m : Nat) :
    acceleratedOrbit 9 (2 ^ 9 * m + 144) = 3 ^ 4 * m + 26 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_9_144.1, data_9_144.2]

/-- Complete interval computation for depth 9, residue 145. -/
theorem bounds_9_145 : exactInterval 9 145 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_9_145 (m : Nat) :
    stoppingTime (2 ^ 9 * m + 145) 9 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_9_145 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_9_145 : oddCount 145 9 = 5 ∧ acceleratedOrbit 9 145 = 71 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_9_145 (m : Nat) :
    acceleratedOrbit 9 (2 ^ 9 * m + 145) = 3 ^ 5 * m + 71 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_9_145.1, data_9_145.2]

/-- Complete interval computation for depth 9, residue 146. -/
theorem bounds_9_146 : exactInterval 9 146 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_9_146 (m : Nat) :
    stoppingTime (2 ^ 9 * m + 146) 9 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_9_146 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_9_146 : oddCount 146 9 = 5 ∧ acceleratedOrbit 9 146 = 71 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_9_146 (m : Nat) :
    acceleratedOrbit 9 (2 ^ 9 * m + 146) = 3 ^ 5 * m + 71 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_9_146.1, data_9_146.2]

/-- Complete interval computation for depth 9, residue 147. -/
theorem bounds_9_147 : exactInterval 9 147 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_9_147 (m : Nat) :
    stoppingTime (2 ^ 9 * m + 147) 9 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_9_147 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_9_147 : oddCount 147 9 = 5 ∧ acceleratedOrbit 9 147 = 71 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_9_147 (m : Nat) :
    acceleratedOrbit 9 (2 ^ 9 * m + 147) = 3 ^ 5 * m + 71 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_9_147.1, data_9_147.2]

/-- Complete interval computation for depth 9, residue 148. -/
theorem bounds_9_148 : exactInterval 9 148 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_9_148 (m : Nat) :
    stoppingTime (2 ^ 9 * m + 148) 9 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_9_148 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_9_148 : oddCount 148 9 = 4 ∧ acceleratedOrbit 9 148 = 26 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_9_148 (m : Nat) :
    acceleratedOrbit 9 (2 ^ 9 * m + 148) = 3 ^ 4 * m + 26 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_9_148.1, data_9_148.2]

/-- Complete interval computation for depth 9, residue 149. -/
theorem bounds_9_149 : exactInterval 9 149 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_9_149 (m : Nat) :
    stoppingTime (2 ^ 9 * m + 149) 9 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_9_149 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_9_149 : oddCount 149 9 = 4 ∧ acceleratedOrbit 9 149 = 26 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_9_149 (m : Nat) :
    acceleratedOrbit 9 (2 ^ 9 * m + 149) = 3 ^ 4 * m + 26 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_9_149.1, data_9_149.2]

/-- Complete interval computation for depth 9, residue 150. -/
theorem bounds_9_150 : exactInterval 9 150 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_9_150 (m : Nat) :
    stoppingTime (2 ^ 9 * m + 150) 9 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_9_150 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_9_150 : oddCount 150 9 = 3 ∧ acceleratedOrbit 9 150 = 8 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_9_150 (m : Nat) :
    acceleratedOrbit 9 (2 ^ 9 * m + 150) = 3 ^ 3 * m + 8 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_9_150.1, data_9_150.2]

/-- Complete interval computation for depth 9, residue 151. -/
theorem bounds_9_151 : exactInterval 9 151 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_9_151 (m : Nat) :
    stoppingTime (2 ^ 9 * m + 151) 9 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_9_151 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_9_151 : oddCount 151 9 = 3 ∧ acceleratedOrbit 9 151 = 8 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_9_151 (m : Nat) :
    acceleratedOrbit 9 (2 ^ 9 * m + 151) = 3 ^ 3 * m + 8 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_9_151.1, data_9_151.2]

/-- Complete interval computation for depth 9, residue 152. -/
theorem bounds_9_152 : exactInterval 9 152 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_9_152 (m : Nat) :
    stoppingTime (2 ^ 9 * m + 152) 9 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_9_152 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_9_152 : oddCount 152 9 = 4 ∧ acceleratedOrbit 9 152 = 26 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_9_152 (m : Nat) :
    acceleratedOrbit 9 (2 ^ 9 * m + 152) = 3 ^ 4 * m + 26 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_9_152.1, data_9_152.2]

/-- Complete interval computation for depth 9, residue 153. -/
theorem bounds_9_153 : exactInterval 9 153 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_9_153 (m : Nat) :
    stoppingTime (2 ^ 9 * m + 153) 9 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_9_153 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_9_153 : oddCount 153 9 = 5 ∧ acceleratedOrbit 9 153 = 74 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_9_153 (m : Nat) :
    acceleratedOrbit 9 (2 ^ 9 * m + 153) = 3 ^ 5 * m + 74 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_9_153.1, data_9_153.2]

end Collatz.Research.DescentIntervals.Batch065
