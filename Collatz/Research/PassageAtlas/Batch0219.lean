import Collatz.Research.DescentIntervals.Classifier

namespace Collatz.Research.PassageAtlas.Batch0219

open Collatz.Research.DescentIntervals

set_option maxRecDepth 20000
set_option maxHeartbeats 0

/-- Complete interval computation for depth 15, residue 7143. -/
theorem bounds_15_7143 : exactInterval 15 7143 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_7143 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 7143) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_7143 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_7143 : oddCount 7143 15 = 10 ∧ acceleratedOrbit 15 7143 = 12878 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_7143 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 7143) = 3 ^ 10 * m + 12878 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_7143.1, data_15_7143.2]

/-- Complete interval computation for depth 15, residue 7144. -/
theorem bounds_15_7144 : exactInterval 15 7144 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_7144 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 7144) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_7144 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_7144 : oddCount 7144 15 = 7 ∧ acceleratedOrbit 15 7144 = 479 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_7144 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 7144) = 3 ^ 7 * m + 479 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_7144.1, data_15_7144.2]

/-- Complete interval computation for depth 15, residue 7145. -/
theorem bounds_15_7145 : exactInterval 15 7145 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_7145 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 7145) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_7145 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_7145 : oddCount 7145 15 = 13 ∧ acceleratedOrbit 15 7145 = 347732 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_7145 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 7145) = 3 ^ 13 * m + 347732 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_7145.1, data_15_7145.2]

/-- Complete interval computation for depth 15, residue 7146. -/
theorem bounds_15_7146 : exactInterval 15 7146 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_7146 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 7146) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_7146 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_7146 : oddCount 7146 15 = 7 ∧ acceleratedOrbit 15 7146 = 479 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_7146 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 7146) = 3 ^ 7 * m + 479 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_7146.1, data_15_7146.2]

/-- Complete interval computation for depth 15, residue 7147. -/
theorem bounds_15_7147 : exactInterval 15 7147 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_7147 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 7147) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_7147 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_7147 : oddCount 7147 15 = 9 ∧ acceleratedOrbit 15 7147 = 4295 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_7147 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 7147) = 3 ^ 9 * m + 4295 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_7147.1, data_15_7147.2]

/-- Complete interval computation for depth 15, residue 7148. -/
theorem bounds_15_7148 : exactInterval 15 7148 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_7148 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 7148) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_7148 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_7148 : oddCount 7148 15 = 8 ∧ acceleratedOrbit 15 7148 = 1433 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_7148 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 7148) = 3 ^ 8 * m + 1433 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_7148.1, data_15_7148.2]

/-- Complete interval computation for depth 15, residue 7149. -/
theorem bounds_15_7149 : exactInterval 15 7149 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_7149 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 7149) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_7149 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_7149 : oddCount 7149 15 = 8 ∧ acceleratedOrbit 15 7149 = 1433 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_7149 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 7149) = 3 ^ 8 * m + 1433 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_7149.1, data_15_7149.2]

/-- Complete interval computation for depth 15, residue 7150. -/
theorem bounds_15_7150 : exactInterval 15 7150 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_7150 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 7150) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_7150 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_7150 : oddCount 7150 15 = 8 ∧ acceleratedOrbit 15 7150 = 1433 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_7150 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 7150) = 3 ^ 8 * m + 1433 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_7150.1, data_15_7150.2]

/-- Complete interval computation for depth 15, residue 7151. -/
theorem bounds_15_7151 : exactInterval 15 7151 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_7151 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 7151) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_7151 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_7151 : oddCount 7151 15 = 10 ∧ acceleratedOrbit 15 7151 = 12889 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_7151 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 7151) = 3 ^ 10 * m + 12889 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_7151.1, data_15_7151.2]

/-- Complete interval computation for depth 15, residue 7152. -/
theorem bounds_15_7152 : exactInterval 15 7152 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_7152 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 7152) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_7152 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_7152 : oddCount 7152 15 = 9 ∧ acceleratedOrbit 15 7152 = 4306 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_7152 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 7152) = 3 ^ 9 * m + 4306 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_7152.1, data_15_7152.2]

/-- Complete interval computation for depth 15, residue 7153. -/
theorem bounds_15_7153 : exactInterval 15 7153 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_7153 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 7153) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_7153 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_7153 : oddCount 7153 15 = 7 ∧ acceleratedOrbit 15 7153 = 479 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_7153 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 7153) = 3 ^ 7 * m + 479 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_7153.1, data_15_7153.2]

/-- Complete interval computation for depth 15, residue 7154. -/
theorem bounds_15_7154 : exactInterval 15 7154 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_7154 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 7154) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_7154 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_7154 : oddCount 7154 15 = 7 ∧ acceleratedOrbit 15 7154 = 478 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_7154 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 7154) = 3 ^ 7 * m + 478 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_7154.1, data_15_7154.2]

/-- Complete interval computation for depth 15, residue 7155. -/
theorem bounds_15_7155 : exactInterval 15 7155 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_7155 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 7155) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_7155 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_7155 : oddCount 7155 15 = 7 ∧ acceleratedOrbit 15 7155 = 478 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_7155 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 7155) = 3 ^ 7 * m + 478 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_7155.1, data_15_7155.2]

/-- Complete interval computation for depth 15, residue 7156. -/
theorem bounds_15_7156 : exactInterval 15 7156 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_7156 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 7156) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_7156 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_7156 : oddCount 7156 15 = 9 ∧ acceleratedOrbit 15 7156 = 4306 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_7156 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 7156) = 3 ^ 9 * m + 4306 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_7156.1, data_15_7156.2]

/-- Complete interval computation for depth 15, residue 7157. -/
theorem bounds_15_7157 : exactInterval 15 7157 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_7157 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 7157) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_7157 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_7157 : oddCount 7157 15 = 9 ∧ acceleratedOrbit 15 7157 = 4306 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_7157 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 7157) = 3 ^ 9 * m + 4306 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_7157.1, data_15_7157.2]

/-- Complete interval computation for depth 15, residue 7158. -/
theorem bounds_15_7158 : exactInterval 15 7158 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_7158 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 7158) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_7158 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_7158 : oddCount 7158 15 = 7 ∧ acceleratedOrbit 15 7158 = 478 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_7158 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 7158) = 3 ^ 7 * m + 478 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_7158.1, data_15_7158.2]

/-- Complete interval computation for depth 15, residue 7159. -/
theorem bounds_15_7159 : exactInterval 15 7159 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_7159 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 7159) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_7159 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_7159 : oddCount 7159 15 = 7 ∧ acceleratedOrbit 15 7159 = 478 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_7159 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 7159) = 3 ^ 7 * m + 478 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_7159.1, data_15_7159.2]

/-- Complete interval computation for depth 15, residue 7160. -/
theorem bounds_15_7160 : exactInterval 15 7160 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_7160 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 7160) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_7160 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_7160 : oddCount 7160 15 = 9 ∧ acceleratedOrbit 15 7160 = 4306 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_7160 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 7160) = 3 ^ 9 * m + 4306 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_7160.1, data_15_7160.2]

/-- Complete interval computation for depth 15, residue 7161. -/
theorem bounds_15_7161 : exactInterval 15 7161 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_7161 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 7161) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_7161 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_7161 : oddCount 7161 15 = 9 ∧ acceleratedOrbit 15 7161 = 4303 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_7161 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 7161) = 3 ^ 9 * m + 4303 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_7161.1, data_15_7161.2]

/-- Complete interval computation for depth 15, residue 7162. -/
theorem bounds_15_7162 : exactInterval 15 7162 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_7162 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 7162) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_7162 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_7162 : oddCount 7162 15 = 9 ∧ acceleratedOrbit 15 7162 = 4306 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_7162 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 7162) = 3 ^ 9 * m + 4306 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_7162.1, data_15_7162.2]

/-- Complete interval computation for depth 15, residue 7163. -/
theorem bounds_15_7163 : exactInterval 15 7163 = ⟨0, none⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_7163 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 7163) 15 ↔ 0 ≤ m := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_7163 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_7163 : oddCount 7163 15 = 9 ∧ acceleratedOrbit 15 7163 = 4304 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_7163 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 7163) = 3 ^ 9 * m + 4304 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_7163.1, data_15_7163.2]

/-- Complete interval computation for depth 15, residue 7164. -/
theorem bounds_15_7164 : exactInterval 15 7164 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_7164 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 7164) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_7164 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_7164 : oddCount 7164 15 = 10 ∧ acceleratedOrbit 15 7164 = 12917 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_7164 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 7164) = 3 ^ 10 * m + 12917 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_7164.1, data_15_7164.2]

/-- Complete interval computation for depth 15, residue 7165. -/
theorem bounds_15_7165 : exactInterval 15 7165 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_7165 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 7165) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_7165 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_7165 : oddCount 7165 15 = 10 ∧ acceleratedOrbit 15 7165 = 12917 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_7165 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 7165) = 3 ^ 10 * m + 12917 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_7165.1, data_15_7165.2]

/-- Complete interval computation for depth 15, residue 7166. -/
theorem bounds_15_7166 : exactInterval 15 7166 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_7166 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 7166) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_7166 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_7166 : oddCount 7166 15 = 10 ∧ acceleratedOrbit 15 7166 = 12917 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_7166 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 7166) = 3 ^ 10 * m + 12917 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_7166.1, data_15_7166.2]

/-- Complete interval computation for depth 15, residue 7167. -/
theorem bounds_15_7167 : exactInterval 15 7167 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_7167 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 7167) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_7167 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_7167 : oddCount 7167 15 = 14 ∧ acceleratedOrbit 15 7167 = 1046276 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_7167 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 7167) = 3 ^ 14 * m + 1046276 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_7167.1, data_15_7167.2]

/-- Complete interval computation for depth 15, residue 7168. -/
theorem bounds_15_7168 : exactInterval 15 7168 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_7168 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 7168) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_7168 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_7168 : oddCount 7168 15 = 4 ∧ acceleratedOrbit 15 7168 = 20 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_7168 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 7168) = 3 ^ 4 * m + 20 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_7168.1, data_15_7168.2]

/-- Complete interval computation for depth 15, residue 7169. -/
theorem bounds_15_7169 : exactInterval 15 7169 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_7169 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 7169) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_7169 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_7169 : oddCount 7169 15 = 7 ∧ acceleratedOrbit 15 7169 = 479 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_7169 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 7169) = 3 ^ 7 * m + 479 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_7169.1, data_15_7169.2]

/-- Complete interval computation for depth 15, residue 7170. -/
theorem bounds_15_7170 : exactInterval 15 7170 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_7170 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 7170) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_7170 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_7170 : oddCount 7170 15 = 9 ∧ acceleratedOrbit 15 7170 = 4313 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_7170 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 7170) = 3 ^ 9 * m + 4313 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_7170.1, data_15_7170.2]

/-- Complete interval computation for depth 15, residue 7171. -/
theorem bounds_15_7171 : exactInterval 15 7171 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_7171 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 7171) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_7171 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_7171 : oddCount 7171 15 = 9 ∧ acceleratedOrbit 15 7171 = 4313 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_7171 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 7171) = 3 ^ 9 * m + 4313 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_7171.1, data_15_7171.2]

/-- Complete interval computation for depth 15, residue 7172. -/
theorem bounds_15_7172 : exactInterval 15 7172 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_7172 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 7172) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_7172 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_7172 : oddCount 7172 15 = 6 ∧ acceleratedOrbit 15 7172 = 161 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_7172 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 7172) = 3 ^ 6 * m + 161 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_7172.1, data_15_7172.2]

/-- Complete interval computation for depth 15, residue 7173. -/
theorem bounds_15_7173 : exactInterval 15 7173 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_7173 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 7173) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_7173 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_7173 : oddCount 7173 15 = 6 ∧ acceleratedOrbit 15 7173 = 161 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_7173 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 7173) = 3 ^ 6 * m + 161 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_7173.1, data_15_7173.2]

/-- Complete interval computation for depth 15, residue 7174. -/
theorem bounds_15_7174 : exactInterval 15 7174 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_7174 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 7174) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_7174 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_7174 : oddCount 7174 15 = 6 ∧ acceleratedOrbit 15 7174 = 161 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_7174 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 7174) = 3 ^ 6 * m + 161 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_7174.1, data_15_7174.2]

/-- Complete interval computation for depth 15, residue 7175. -/
theorem bounds_15_7175 : exactInterval 15 7175 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_7175 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 7175) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_7175 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_7175 : oddCount 7175 15 = 9 ∧ acceleratedOrbit 15 7175 = 4313 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_7175 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 7175) = 3 ^ 9 * m + 4313 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_7175.1, data_15_7175.2]

end Collatz.Research.PassageAtlas.Batch0219
