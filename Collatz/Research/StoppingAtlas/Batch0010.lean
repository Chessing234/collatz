import Collatz.Research.DescentIntervals.Classifier

namespace Collatz.Research.StoppingAtlas.Batch0010

open Collatz.Research.DescentIntervals

set_option maxRecDepth 20000
set_option maxHeartbeats 0

/-- Complete interval computation for depth 10, residue 138. -/
theorem bounds_10_138 : exactInterval 10 138 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_10_138 (m : Nat) :
    stoppingTime (2 ^ 10 * m + 138) 10 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_10_138 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_10_138 : oddCount 138 10 = 3 ∧ acceleratedOrbit 10 138 = 4 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_10_138 (m : Nat) :
    acceleratedOrbit 10 (2 ^ 10 * m + 138) = 3 ^ 3 * m + 4 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_10_138.1, data_10_138.2]

/-- Complete interval computation for depth 10, residue 139. -/
theorem bounds_10_139 : exactInterval 10 139 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_10_139 (m : Nat) :
    stoppingTime (2 ^ 10 * m + 139) 10 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_10_139 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_10_139 : oddCount 139 10 = 6 ∧ acceleratedOrbit 10 139 = 101 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_10_139 (m : Nat) :
    acceleratedOrbit 10 (2 ^ 10 * m + 139) = 3 ^ 6 * m + 101 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_10_139.1, data_10_139.2]

/-- Complete interval computation for depth 10, residue 140. -/
theorem bounds_10_140 : exactInterval 10 140 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_10_140 (m : Nat) :
    stoppingTime (2 ^ 10 * m + 140) 10 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_10_140 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_10_140 : oddCount 140 10 = 3 ∧ acceleratedOrbit 10 140 = 4 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_10_140 (m : Nat) :
    acceleratedOrbit 10 (2 ^ 10 * m + 140) = 3 ^ 3 * m + 4 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_10_140.1, data_10_140.2]

/-- Complete interval computation for depth 10, residue 141. -/
theorem bounds_10_141 : exactInterval 10 141 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_10_141 (m : Nat) :
    stoppingTime (2 ^ 10 * m + 141) 10 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_10_141 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_10_141 : oddCount 141 10 = 3 ∧ acceleratedOrbit 10 141 = 4 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_10_141 (m : Nat) :
    acceleratedOrbit 10 (2 ^ 10 * m + 141) = 3 ^ 3 * m + 4 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_10_141.1, data_10_141.2]

/-- Complete interval computation for depth 10, residue 142. -/
theorem bounds_10_142 : exactInterval 10 142 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_10_142 (m : Nat) :
    stoppingTime (2 ^ 10 * m + 142) 10 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_10_142 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_10_142 : oddCount 142 10 = 6 ∧ acceleratedOrbit 10 142 = 103 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_10_142 (m : Nat) :
    acceleratedOrbit 10 (2 ^ 10 * m + 142) = 3 ^ 6 * m + 103 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_10_142.1, data_10_142.2]

/-- Complete interval computation for depth 10, residue 143. -/
theorem bounds_10_143 : exactInterval 10 143 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_10_143 (m : Nat) :
    stoppingTime (2 ^ 10 * m + 143) 10 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_10_143 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_10_143 : oddCount 143 10 = 6 ∧ acceleratedOrbit 10 143 = 103 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_10_143 (m : Nat) :
    acceleratedOrbit 10 (2 ^ 10 * m + 143) = 3 ^ 6 * m + 103 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_10_143.1, data_10_143.2]

/-- Complete interval computation for depth 10, residue 144. -/
theorem bounds_10_144 : exactInterval 10 144 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_10_144 (m : Nat) :
    stoppingTime (2 ^ 10 * m + 144) 10 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_10_144 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_10_144 : oddCount 144 10 = 4 ∧ acceleratedOrbit 10 144 = 13 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_10_144 (m : Nat) :
    acceleratedOrbit 10 (2 ^ 10 * m + 144) = 3 ^ 4 * m + 13 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_10_144.1, data_10_144.2]

/-- Complete interval computation for depth 10, residue 145. -/
theorem bounds_10_145 : exactInterval 10 145 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_10_145 (m : Nat) :
    stoppingTime (2 ^ 10 * m + 145) 10 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_10_145 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_10_145 : oddCount 145 10 = 6 ∧ acceleratedOrbit 10 145 = 107 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_10_145 (m : Nat) :
    acceleratedOrbit 10 (2 ^ 10 * m + 145) = 3 ^ 6 * m + 107 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_10_145.1, data_10_145.2]

/-- Complete interval computation for depth 10, residue 146. -/
theorem bounds_10_146 : exactInterval 10 146 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_10_146 (m : Nat) :
    stoppingTime (2 ^ 10 * m + 146) 10 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_10_146 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_10_146 : oddCount 146 10 = 6 ∧ acceleratedOrbit 10 146 = 107 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_10_146 (m : Nat) :
    acceleratedOrbit 10 (2 ^ 10 * m + 146) = 3 ^ 6 * m + 107 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_10_146.1, data_10_146.2]

/-- Complete interval computation for depth 10, residue 147. -/
theorem bounds_10_147 : exactInterval 10 147 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_10_147 (m : Nat) :
    stoppingTime (2 ^ 10 * m + 147) 10 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_10_147 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_10_147 : oddCount 147 10 = 6 ∧ acceleratedOrbit 10 147 = 107 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_10_147 (m : Nat) :
    acceleratedOrbit 10 (2 ^ 10 * m + 147) = 3 ^ 6 * m + 107 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_10_147.1, data_10_147.2]

/-- Complete interval computation for depth 10, residue 148. -/
theorem bounds_10_148 : exactInterval 10 148 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_10_148 (m : Nat) :
    stoppingTime (2 ^ 10 * m + 148) 10 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_10_148 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_10_148 : oddCount 148 10 = 4 ∧ acceleratedOrbit 10 148 = 13 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_10_148 (m : Nat) :
    acceleratedOrbit 10 (2 ^ 10 * m + 148) = 3 ^ 4 * m + 13 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_10_148.1, data_10_148.2]

/-- Complete interval computation for depth 10, residue 149. -/
theorem bounds_10_149 : exactInterval 10 149 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_10_149 (m : Nat) :
    stoppingTime (2 ^ 10 * m + 149) 10 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_10_149 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_10_149 : oddCount 149 10 = 4 ∧ acceleratedOrbit 10 149 = 13 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_10_149 (m : Nat) :
    acceleratedOrbit 10 (2 ^ 10 * m + 149) = 3 ^ 4 * m + 13 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_10_149.1, data_10_149.2]

/-- Complete interval computation for depth 10, residue 150. -/
theorem bounds_10_150 : exactInterval 10 150 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_10_150 (m : Nat) :
    stoppingTime (2 ^ 10 * m + 150) 10 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_10_150 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_10_150 : oddCount 150 10 = 3 ∧ acceleratedOrbit 10 150 = 4 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_10_150 (m : Nat) :
    acceleratedOrbit 10 (2 ^ 10 * m + 150) = 3 ^ 3 * m + 4 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_10_150.1, data_10_150.2]

/-- Complete interval computation for depth 10, residue 151. -/
theorem bounds_10_151 : exactInterval 10 151 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_10_151 (m : Nat) :
    stoppingTime (2 ^ 10 * m + 151) 10 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_10_151 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_10_151 : oddCount 151 10 = 3 ∧ acceleratedOrbit 10 151 = 4 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_10_151 (m : Nat) :
    acceleratedOrbit 10 (2 ^ 10 * m + 151) = 3 ^ 3 * m + 4 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_10_151.1, data_10_151.2]

/-- Complete interval computation for depth 10, residue 152. -/
theorem bounds_10_152 : exactInterval 10 152 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_10_152 (m : Nat) :
    stoppingTime (2 ^ 10 * m + 152) 10 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_10_152 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_10_152 : oddCount 152 10 = 4 ∧ acceleratedOrbit 10 152 = 13 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_10_152 (m : Nat) :
    acceleratedOrbit 10 (2 ^ 10 * m + 152) = 3 ^ 4 * m + 13 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_10_152.1, data_10_152.2]

end Collatz.Research.StoppingAtlas.Batch0010
