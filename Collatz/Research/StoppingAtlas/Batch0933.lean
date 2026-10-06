import Collatz.Research.DescentIntervals.Classifier

namespace Collatz.Research.StoppingAtlas.Batch0933

open Collatz.Research.DescentIntervals

set_option maxRecDepth 20000
set_option maxHeartbeats 0

/-- Complete interval computation for depth 13, residue 7147. -/
theorem bounds_13_7147 : exactInterval 13 7147 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_13_7147 (m : Nat) :
    stoppingTime (2 ^ 13 * m + 7147) 13 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_13_7147 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_13_7147 : oddCount 7147 13 = 8 ∧ acceleratedOrbit 13 7147 = 5726 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_13_7147 (m : Nat) :
    acceleratedOrbit 13 (2 ^ 13 * m + 7147) = 3 ^ 8 * m + 5726 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_13_7147.1, data_13_7147.2]

/-- Complete interval computation for depth 13, residue 7148. -/
theorem bounds_13_7148 : exactInterval 13 7148 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_13_7148 (m : Nat) :
    stoppingTime (2 ^ 13 * m + 7148) 13 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_13_7148 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_13_7148 : oddCount 7148 13 = 7 ∧ acceleratedOrbit 13 7148 = 1910 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_13_7148 (m : Nat) :
    acceleratedOrbit 13 (2 ^ 13 * m + 7148) = 3 ^ 7 * m + 1910 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_13_7148.1, data_13_7148.2]

/-- Complete interval computation for depth 13, residue 7149. -/
theorem bounds_13_7149 : exactInterval 13 7149 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_13_7149 (m : Nat) :
    stoppingTime (2 ^ 13 * m + 7149) 13 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_13_7149 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_13_7149 : oddCount 7149 13 = 7 ∧ acceleratedOrbit 13 7149 = 1910 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_13_7149 (m : Nat) :
    acceleratedOrbit 13 (2 ^ 13 * m + 7149) = 3 ^ 7 * m + 1910 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_13_7149.1, data_13_7149.2]

/-- Complete interval computation for depth 13, residue 7150. -/
theorem bounds_13_7150 : exactInterval 13 7150 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_13_7150 (m : Nat) :
    stoppingTime (2 ^ 13 * m + 7150) 13 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_13_7150 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_13_7150 : oddCount 7150 13 = 7 ∧ acceleratedOrbit 13 7150 = 1910 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_13_7150 (m : Nat) :
    acceleratedOrbit 13 (2 ^ 13 * m + 7150) = 3 ^ 7 * m + 1910 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_13_7150.1, data_13_7150.2]

/-- Complete interval computation for depth 13, residue 7151. -/
theorem bounds_13_7151 : exactInterval 13 7151 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_13_7151 (m : Nat) :
    stoppingTime (2 ^ 13 * m + 7151) 13 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_13_7151 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_13_7151 : oddCount 7151 13 = 9 ∧ acceleratedOrbit 13 7151 = 17185 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_13_7151 (m : Nat) :
    acceleratedOrbit 13 (2 ^ 13 * m + 7151) = 3 ^ 9 * m + 17185 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_13_7151.1, data_13_7151.2]

/-- Complete interval computation for depth 13, residue 7152. -/
theorem bounds_13_7152 : exactInterval 13 7152 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_13_7152 (m : Nat) :
    stoppingTime (2 ^ 13 * m + 7152) 13 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_13_7152 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_13_7152 : oddCount 7152 13 = 8 ∧ acceleratedOrbit 13 7152 = 5741 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_13_7152 (m : Nat) :
    acceleratedOrbit 13 (2 ^ 13 * m + 7152) = 3 ^ 8 * m + 5741 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_13_7152.1, data_13_7152.2]

/-- Complete interval computation for depth 13, residue 7153. -/
theorem bounds_13_7153 : exactInterval 13 7153 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_13_7153 (m : Nat) :
    stoppingTime (2 ^ 13 * m + 7153) 13 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_13_7153 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_13_7153 : oddCount 7153 13 = 6 ∧ acceleratedOrbit 13 7153 = 638 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_13_7153 (m : Nat) :
    acceleratedOrbit 13 (2 ^ 13 * m + 7153) = 3 ^ 6 * m + 638 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_13_7153.1, data_13_7153.2]

/-- Complete interval computation for depth 13, residue 7154. -/
theorem bounds_13_7154 : exactInterval 13 7154 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_13_7154 (m : Nat) :
    stoppingTime (2 ^ 13 * m + 7154) 13 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_13_7154 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_13_7154 : oddCount 7154 13 = 6 ∧ acceleratedOrbit 13 7154 = 637 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_13_7154 (m : Nat) :
    acceleratedOrbit 13 (2 ^ 13 * m + 7154) = 3 ^ 6 * m + 637 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_13_7154.1, data_13_7154.2]

/-- Complete interval computation for depth 13, residue 7155. -/
theorem bounds_13_7155 : exactInterval 13 7155 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_13_7155 (m : Nat) :
    stoppingTime (2 ^ 13 * m + 7155) 13 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_13_7155 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_13_7155 : oddCount 7155 13 = 6 ∧ acceleratedOrbit 13 7155 = 637 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_13_7155 (m : Nat) :
    acceleratedOrbit 13 (2 ^ 13 * m + 7155) = 3 ^ 6 * m + 637 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_13_7155.1, data_13_7155.2]

/-- Complete interval computation for depth 13, residue 7156. -/
theorem bounds_13_7156 : exactInterval 13 7156 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_13_7156 (m : Nat) :
    stoppingTime (2 ^ 13 * m + 7156) 13 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_13_7156 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_13_7156 : oddCount 7156 13 = 8 ∧ acceleratedOrbit 13 7156 = 5741 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_13_7156 (m : Nat) :
    acceleratedOrbit 13 (2 ^ 13 * m + 7156) = 3 ^ 8 * m + 5741 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_13_7156.1, data_13_7156.2]

/-- Complete interval computation for depth 13, residue 7157. -/
theorem bounds_13_7157 : exactInterval 13 7157 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_13_7157 (m : Nat) :
    stoppingTime (2 ^ 13 * m + 7157) 13 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_13_7157 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_13_7157 : oddCount 7157 13 = 8 ∧ acceleratedOrbit 13 7157 = 5741 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_13_7157 (m : Nat) :
    acceleratedOrbit 13 (2 ^ 13 * m + 7157) = 3 ^ 8 * m + 5741 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_13_7157.1, data_13_7157.2]

/-- Complete interval computation for depth 13, residue 7158. -/
theorem bounds_13_7158 : exactInterval 13 7158 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_13_7158 (m : Nat) :
    stoppingTime (2 ^ 13 * m + 7158) 13 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_13_7158 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_13_7158 : oddCount 7158 13 = 7 ∧ acceleratedOrbit 13 7158 = 1912 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_13_7158 (m : Nat) :
    acceleratedOrbit 13 (2 ^ 13 * m + 7158) = 3 ^ 7 * m + 1912 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_13_7158.1, data_13_7158.2]

/-- Complete interval computation for depth 13, residue 7159. -/
theorem bounds_13_7159 : exactInterval 13 7159 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_13_7159 (m : Nat) :
    stoppingTime (2 ^ 13 * m + 7159) 13 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_13_7159 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_13_7159 : oddCount 7159 13 = 7 ∧ acceleratedOrbit 13 7159 = 1912 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_13_7159 (m : Nat) :
    acceleratedOrbit 13 (2 ^ 13 * m + 7159) = 3 ^ 7 * m + 1912 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_13_7159.1, data_13_7159.2]

/-- Complete interval computation for depth 13, residue 7160. -/
theorem bounds_13_7160 : exactInterval 13 7160 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_13_7160 (m : Nat) :
    stoppingTime (2 ^ 13 * m + 7160) 13 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_13_7160 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_13_7160 : oddCount 7160 13 = 8 ∧ acceleratedOrbit 13 7160 = 5741 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_13_7160 (m : Nat) :
    acceleratedOrbit 13 (2 ^ 13 * m + 7160) = 3 ^ 8 * m + 5741 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_13_7160.1, data_13_7160.2]

/-- Complete interval computation for depth 13, residue 7161. -/
theorem bounds_13_7161 : exactInterval 13 7161 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_13_7161 (m : Nat) :
    stoppingTime (2 ^ 13 * m + 7161) 13 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_13_7161 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_13_7161 : oddCount 7161 13 = 9 ∧ acceleratedOrbit 13 7161 = 17212 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_13_7161 (m : Nat) :
    acceleratedOrbit 13 (2 ^ 13 * m + 7161) = 3 ^ 9 * m + 17212 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_13_7161.1, data_13_7161.2]

end Collatz.Research.StoppingAtlas.Batch0933
