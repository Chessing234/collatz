import Collatz.Research.DescentIntervals.Classifier

namespace Collatz.Research.StoppingAtlas.Batch0210

open Collatz.Research.DescentIntervals

set_option maxRecDepth 20000
set_option maxHeartbeats 0

/-- Complete interval computation for depth 12, residue 138. -/
theorem bounds_12_138 : exactInterval 12 138 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_12_138 (m : Nat) :
    stoppingTime (2 ^ 12 * m + 138) 12 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_12_138 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_12_138 : oddCount 138 12 = 3 ∧ acceleratedOrbit 12 138 = 1 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_12_138 (m : Nat) :
    acceleratedOrbit 12 (2 ^ 12 * m + 138) = 3 ^ 3 * m + 1 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_12_138.1, data_12_138.2]

/-- Complete interval computation for depth 12, residue 139. -/
theorem bounds_12_139 : exactInterval 12 139 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_12_139 (m : Nat) :
    stoppingTime (2 ^ 12 * m + 139) 12 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_12_139 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_12_139 : oddCount 139 12 = 7 ∧ acceleratedOrbit 12 139 = 76 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_12_139 (m : Nat) :
    acceleratedOrbit 12 (2 ^ 12 * m + 139) = 3 ^ 7 * m + 76 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_12_139.1, data_12_139.2]

/-- Complete interval computation for depth 12, residue 140. -/
theorem bounds_12_140 : exactInterval 12 140 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_12_140 (m : Nat) :
    stoppingTime (2 ^ 12 * m + 140) 12 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_12_140 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_12_140 : oddCount 140 12 = 3 ∧ acceleratedOrbit 12 140 = 1 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_12_140 (m : Nat) :
    acceleratedOrbit 12 (2 ^ 12 * m + 140) = 3 ^ 3 * m + 1 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_12_140.1, data_12_140.2]

/-- Complete interval computation for depth 12, residue 141. -/
theorem bounds_12_141 : exactInterval 12 141 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_12_141 (m : Nat) :
    stoppingTime (2 ^ 12 * m + 141) 12 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_12_141 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_12_141 : oddCount 141 12 = 3 ∧ acceleratedOrbit 12 141 = 1 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_12_141 (m : Nat) :
    acceleratedOrbit 12 (2 ^ 12 * m + 141) = 3 ^ 3 * m + 1 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_12_141.1, data_12_141.2]

/-- Complete interval computation for depth 12, residue 142. -/
theorem bounds_12_142 : exactInterval 12 142 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_12_142 (m : Nat) :
    stoppingTime (2 ^ 12 * m + 142) 12 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_12_142 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_12_142 : oddCount 142 12 = 8 ∧ acceleratedOrbit 12 142 = 233 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_12_142 (m : Nat) :
    acceleratedOrbit 12 (2 ^ 12 * m + 142) = 3 ^ 8 * m + 233 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_12_142.1, data_12_142.2]

/-- Complete interval computation for depth 12, residue 143. -/
theorem bounds_12_143 : exactInterval 12 143 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_12_143 (m : Nat) :
    stoppingTime (2 ^ 12 * m + 143) 12 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_12_143 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_12_143 : oddCount 143 12 = 8 ∧ acceleratedOrbit 12 143 = 233 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_12_143 (m : Nat) :
    acceleratedOrbit 12 (2 ^ 12 * m + 143) = 3 ^ 8 * m + 233 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_12_143.1, data_12_143.2]

/-- Complete interval computation for depth 12, residue 144. -/
theorem bounds_12_144 : exactInterval 12 144 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_12_144 (m : Nat) :
    stoppingTime (2 ^ 12 * m + 144) 12 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_12_144 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_12_144 : oddCount 144 12 = 5 ∧ acceleratedOrbit 12 144 = 10 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_12_144 (m : Nat) :
    acceleratedOrbit 12 (2 ^ 12 * m + 144) = 3 ^ 5 * m + 10 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_12_144.1, data_12_144.2]

/-- Complete interval computation for depth 12, residue 145. -/
theorem bounds_12_145 : exactInterval 12 145 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_12_145 (m : Nat) :
    stoppingTime (2 ^ 12 * m + 145) 12 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_12_145 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_12_145 : oddCount 145 12 = 8 ∧ acceleratedOrbit 12 145 = 242 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_12_145 (m : Nat) :
    acceleratedOrbit 12 (2 ^ 12 * m + 145) = 3 ^ 8 * m + 242 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_12_145.1, data_12_145.2]

/-- Complete interval computation for depth 12, residue 146. -/
theorem bounds_12_146 : exactInterval 12 146 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_12_146 (m : Nat) :
    stoppingTime (2 ^ 12 * m + 146) 12 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_12_146 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_12_146 : oddCount 146 12 = 8 ∧ acceleratedOrbit 12 146 = 242 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_12_146 (m : Nat) :
    acceleratedOrbit 12 (2 ^ 12 * m + 146) = 3 ^ 8 * m + 242 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_12_146.1, data_12_146.2]

/-- Complete interval computation for depth 12, residue 147. -/
theorem bounds_12_147 : exactInterval 12 147 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_12_147 (m : Nat) :
    stoppingTime (2 ^ 12 * m + 147) 12 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_12_147 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_12_147 : oddCount 147 12 = 8 ∧ acceleratedOrbit 12 147 = 242 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_12_147 (m : Nat) :
    acceleratedOrbit 12 (2 ^ 12 * m + 147) = 3 ^ 8 * m + 242 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_12_147.1, data_12_147.2]

/-- Complete interval computation for depth 12, residue 148. -/
theorem bounds_12_148 : exactInterval 12 148 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_12_148 (m : Nat) :
    stoppingTime (2 ^ 12 * m + 148) 12 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_12_148 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_12_148 : oddCount 148 12 = 5 ∧ acceleratedOrbit 12 148 = 10 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_12_148 (m : Nat) :
    acceleratedOrbit 12 (2 ^ 12 * m + 148) = 3 ^ 5 * m + 10 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_12_148.1, data_12_148.2]

/-- Complete interval computation for depth 12, residue 149. -/
theorem bounds_12_149 : exactInterval 12 149 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_12_149 (m : Nat) :
    stoppingTime (2 ^ 12 * m + 149) 12 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_12_149 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_12_149 : oddCount 149 12 = 5 ∧ acceleratedOrbit 12 149 = 10 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_12_149 (m : Nat) :
    acceleratedOrbit 12 (2 ^ 12 * m + 149) = 3 ^ 5 * m + 10 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_12_149.1, data_12_149.2]

/-- Complete interval computation for depth 12, residue 150. -/
theorem bounds_12_150 : exactInterval 12 150 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_12_150 (m : Nat) :
    stoppingTime (2 ^ 12 * m + 150) 12 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_12_150 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_12_150 : oddCount 150 12 = 3 ∧ acceleratedOrbit 12 150 = 1 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_12_150 (m : Nat) :
    acceleratedOrbit 12 (2 ^ 12 * m + 150) = 3 ^ 3 * m + 1 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_12_150.1, data_12_150.2]

/-- Complete interval computation for depth 12, residue 151. -/
theorem bounds_12_151 : exactInterval 12 151 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_12_151 (m : Nat) :
    stoppingTime (2 ^ 12 * m + 151) 12 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_12_151 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_12_151 : oddCount 151 12 = 3 ∧ acceleratedOrbit 12 151 = 1 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_12_151 (m : Nat) :
    acceleratedOrbit 12 (2 ^ 12 * m + 151) = 3 ^ 3 * m + 1 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_12_151.1, data_12_151.2]

/-- Complete interval computation for depth 12, residue 152. -/
theorem bounds_12_152 : exactInterval 12 152 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_12_152 (m : Nat) :
    stoppingTime (2 ^ 12 * m + 152) 12 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_12_152 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_12_152 : oddCount 152 12 = 5 ∧ acceleratedOrbit 12 152 = 10 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_12_152 (m : Nat) :
    acceleratedOrbit 12 (2 ^ 12 * m + 152) = 3 ^ 5 * m + 10 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_12_152.1, data_12_152.2]

end Collatz.Research.StoppingAtlas.Batch0210
