import Collatz.Research.DescentIntervals.Classifier

namespace Collatz.Research.PassageAtlas.Batch0799

open Collatz.Research.DescentIntervals

set_option maxRecDepth 20000
set_option maxHeartbeats 0

/-- Complete interval computation for depth 15, residue 26148. -/
theorem bounds_15_26148 : exactInterval 15 26148 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_26148 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 26148) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_26148 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_26148 : oddCount 26148 15 = 9 ∧ acceleratedOrbit 15 26148 = 15713 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_26148 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 26148) = 3 ^ 9 * m + 15713 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_26148.1, data_15_26148.2]

/-- Complete interval computation for depth 15, residue 26149. -/
theorem bounds_15_26149 : exactInterval 15 26149 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_26149 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 26149) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_26149 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_26149 : oddCount 26149 15 = 9 ∧ acceleratedOrbit 15 26149 = 15713 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_26149 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 26149) = 3 ^ 9 * m + 15713 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_26149.1, data_15_26149.2]

/-- Complete interval computation for depth 15, residue 26150. -/
theorem bounds_15_26150 : exactInterval 15 26150 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_26150 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 26150) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_26150 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_26150 : oddCount 26150 15 = 9 ∧ acceleratedOrbit 15 26150 = 15713 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_26150 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 26150) = 3 ^ 9 * m + 15713 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_26150.1, data_15_26150.2]

/-- Complete interval computation for depth 15, residue 26151. -/
theorem bounds_15_26151 : exactInterval 15 26151 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_26151 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 26151) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_26151 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_26151 : oddCount 26151 15 = 9 ∧ acceleratedOrbit 15 26151 = 15713 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_26151 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 26151) = 3 ^ 9 * m + 15713 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_26151.1, data_15_26151.2]

/-- Complete interval computation for depth 15, residue 26152. -/
theorem bounds_15_26152 : exactInterval 15 26152 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_26152 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 26152) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_26152 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_26152 : oddCount 26152 15 = 4 ∧ acceleratedOrbit 15 26152 = 65 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_26152 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 26152) = 3 ^ 4 * m + 65 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_26152.1, data_15_26152.2]

/-- Complete interval computation for depth 15, residue 26153. -/
theorem bounds_15_26153 : exactInterval 15 26153 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_26153 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 26153) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_26153 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_26153 : oddCount 26153 15 = 12 ∧ acceleratedOrbit 15 26153 = 424187 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_26153 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 26153) = 3 ^ 12 * m + 424187 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_26153.1, data_15_26153.2]

/-- Complete interval computation for depth 15, residue 26154. -/
theorem bounds_15_26154 : exactInterval 15 26154 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_26154 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 26154) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_26154 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_26154 : oddCount 26154 15 = 4 ∧ acceleratedOrbit 15 26154 = 65 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_26154 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 26154) = 3 ^ 4 * m + 65 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_26154.1, data_15_26154.2]

/-- Complete interval computation for depth 15, residue 26155. -/
theorem bounds_15_26155 : exactInterval 15 26155 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_26155 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 26155) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_26155 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_26155 : oddCount 26155 15 = 5 ∧ acceleratedOrbit 15 26155 = 194 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_26155 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 26155) = 3 ^ 5 * m + 194 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_26155.1, data_15_26155.2]

/-- Complete interval computation for depth 15, residue 26156. -/
theorem bounds_15_26156 : exactInterval 15 26156 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_26156 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 26156) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_26156 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_26156 : oddCount 26156 15 = 8 ∧ acceleratedOrbit 15 26156 = 5240 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_26156 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 26156) = 3 ^ 8 * m + 5240 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_26156.1, data_15_26156.2]

/-- Complete interval computation for depth 15, residue 26157. -/
theorem bounds_15_26157 : exactInterval 15 26157 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_26157 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 26157) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_26157 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_26157 : oddCount 26157 15 = 8 ∧ acceleratedOrbit 15 26157 = 5240 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_26157 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 26157) = 3 ^ 8 * m + 5240 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_26157.1, data_15_26157.2]

/-- Complete interval computation for depth 15, residue 26158. -/
theorem bounds_15_26158 : exactInterval 15 26158 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_26158 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 26158) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_26158 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_26158 : oddCount 26158 15 = 8 ∧ acceleratedOrbit 15 26158 = 5240 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_26158 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 26158) = 3 ^ 8 * m + 5240 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_26158.1, data_15_26158.2]

/-- Complete interval computation for depth 15, residue 26159. -/
theorem bounds_15_26159 : exactInterval 15 26159 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_26159 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 26159) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_26159 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_26159 : oddCount 26159 15 = 13 ∧ acceleratedOrbit 15 26159 = 1272833 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_26159 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 26159) = 3 ^ 13 * m + 1272833 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_26159.1, data_15_26159.2]

/-- Complete interval computation for depth 15, residue 26160. -/
theorem bounds_15_26160 : exactInterval 15 26160 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_26160 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 26160) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_26160 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_26160 : oddCount 26160 15 = 4 ∧ acceleratedOrbit 15 26160 = 65 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_26160 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 26160) = 3 ^ 4 * m + 65 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_26160.1, data_15_26160.2]

/-- Complete interval computation for depth 15, residue 26161. -/
theorem bounds_15_26161 : exactInterval 15 26161 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_26161 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 26161) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_26161 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_26161 : oddCount 26161 15 = 8 ∧ acceleratedOrbit 15 26161 = 5240 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_26161 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 26161) = 3 ^ 8 * m + 5240 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_26161.1, data_15_26161.2]

/-- Complete interval computation for depth 15, residue 26162. -/
theorem bounds_15_26162 : exactInterval 15 26162 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_26162 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 26162) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_26162 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_26162 : oddCount 26162 15 = 8 ∧ acceleratedOrbit 15 26162 = 5240 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_26162 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 26162) = 3 ^ 8 * m + 5240 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_26162.1, data_15_26162.2]

/-- Complete interval computation for depth 15, residue 26163. -/
theorem bounds_15_26163 : exactInterval 15 26163 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_26163 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 26163) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_26163 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_26163 : oddCount 26163 15 = 8 ∧ acceleratedOrbit 15 26163 = 5240 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_26163 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 26163) = 3 ^ 8 * m + 5240 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_26163.1, data_15_26163.2]

/-- Complete interval computation for depth 15, residue 26164. -/
theorem bounds_15_26164 : exactInterval 15 26164 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_26164 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 26164) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_26164 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_26164 : oddCount 26164 15 = 4 ∧ acceleratedOrbit 15 26164 = 65 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_26164 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 26164) = 3 ^ 4 * m + 65 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_26164.1, data_15_26164.2]

/-- Complete interval computation for depth 15, residue 26165. -/
theorem bounds_15_26165 : exactInterval 15 26165 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_26165 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 26165) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_26165 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_26165 : oddCount 26165 15 = 4 ∧ acceleratedOrbit 15 26165 = 65 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_26165 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 26165) = 3 ^ 4 * m + 65 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_26165.1, data_15_26165.2]

/-- Complete interval computation for depth 15, residue 26166. -/
theorem bounds_15_26166 : exactInterval 15 26166 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_26166 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 26166) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_26166 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_26166 : oddCount 26166 15 = 9 ∧ acceleratedOrbit 15 26166 = 15719 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_26166 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 26166) = 3 ^ 9 * m + 15719 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_26166.1, data_15_26166.2]

/-- Complete interval computation for depth 15, residue 26167. -/
theorem bounds_15_26167 : exactInterval 15 26167 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_26167 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 26167) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_26167 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_26167 : oddCount 26167 15 = 9 ∧ acceleratedOrbit 15 26167 = 15719 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_26167 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 26167) = 3 ^ 9 * m + 15719 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_26167.1, data_15_26167.2]

/-- Complete interval computation for depth 15, residue 26168. -/
theorem bounds_15_26168 : exactInterval 15 26168 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_26168 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 26168) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_26168 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_26168 : oddCount 26168 15 = 7 ∧ acceleratedOrbit 15 26168 = 1748 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_26168 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 26168) = 3 ^ 7 * m + 1748 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_26168.1, data_15_26168.2]

/-- Complete interval computation for depth 15, residue 26169. -/
theorem bounds_15_26169 : exactInterval 15 26169 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_26169 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 26169) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_26169 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_26169 : oddCount 26169 15 = 7 ∧ acceleratedOrbit 15 26169 = 1747 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_26169 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 26169) = 3 ^ 7 * m + 1747 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_26169.1, data_15_26169.2]

/-- Complete interval computation for depth 15, residue 26170. -/
theorem bounds_15_26170 : exactInterval 15 26170 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_26170 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 26170) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_26170 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_26170 : oddCount 26170 15 = 7 ∧ acceleratedOrbit 15 26170 = 1748 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_26170 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 26170) = 3 ^ 7 * m + 1748 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_26170.1, data_15_26170.2]

/-- Complete interval computation for depth 15, residue 26171. -/
theorem bounds_15_26171 : exactInterval 15 26171 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_26171 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 26171) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_26171 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_26171 : oddCount 26171 15 = 7 ∧ acceleratedOrbit 15 26171 = 1747 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_26171 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 26171) = 3 ^ 7 * m + 1747 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_26171.1, data_15_26171.2]

/-- Complete interval computation for depth 15, residue 26172. -/
theorem bounds_15_26172 : exactInterval 15 26172 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_26172 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 26172) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_26172 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_26172 : oddCount 26172 15 = 7 ∧ acceleratedOrbit 15 26172 = 1748 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_26172 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 26172) = 3 ^ 7 * m + 1748 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_26172.1, data_15_26172.2]

/-- Complete interval computation for depth 15, residue 26173. -/
theorem bounds_15_26173 : exactInterval 15 26173 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_26173 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 26173) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_26173 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_26173 : oddCount 26173 15 = 7 ∧ acceleratedOrbit 15 26173 = 1748 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_26173 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 26173) = 3 ^ 7 * m + 1748 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_26173.1, data_15_26173.2]

/-- Complete interval computation for depth 15, residue 26174. -/
theorem bounds_15_26174 : exactInterval 15 26174 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_26174 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 26174) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_26174 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_26174 : oddCount 26174 15 = 9 ∧ acceleratedOrbit 15 26174 = 15724 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_26174 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 26174) = 3 ^ 9 * m + 15724 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_26174.1, data_15_26174.2]

/-- Complete interval computation for depth 15, residue 26175. -/
theorem bounds_15_26175 : exactInterval 15 26175 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_26175 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 26175) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_26175 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_26175 : oddCount 26175 15 = 9 ∧ acceleratedOrbit 15 26175 = 15724 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_26175 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 26175) = 3 ^ 9 * m + 15724 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_26175.1, data_15_26175.2]

/-- Complete interval computation for depth 15, residue 26176. -/
theorem bounds_15_26176 : exactInterval 15 26176 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_26176 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 26176) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_26176 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_26176 : oddCount 26176 15 = 4 ∧ acceleratedOrbit 15 26176 = 65 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_26176 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 26176) = 3 ^ 4 * m + 65 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_26176.1, data_15_26176.2]

/-- Complete interval computation for depth 15, residue 26177. -/
theorem bounds_15_26177 : exactInterval 15 26177 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_26177 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 26177) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_26177 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_26177 : oddCount 26177 15 = 7 ∧ acceleratedOrbit 15 26177 = 1748 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_26177 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 26177) = 3 ^ 7 * m + 1748 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_26177.1, data_15_26177.2]

/-- Complete interval computation for depth 15, residue 26178. -/
theorem bounds_15_26178 : exactInterval 15 26178 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_26178 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 26178) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_26178 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_26178 : oddCount 26178 15 = 7 ∧ acceleratedOrbit 15 26178 = 1748 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_26178 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 26178) = 3 ^ 7 * m + 1748 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_26178.1, data_15_26178.2]

/-- Complete interval computation for depth 15, residue 26179. -/
theorem bounds_15_26179 : exactInterval 15 26179 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_26179 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 26179) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_26179 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_26179 : oddCount 26179 15 = 7 ∧ acceleratedOrbit 15 26179 = 1748 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_26179 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 26179) = 3 ^ 7 * m + 1748 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_26179.1, data_15_26179.2]

/-- Complete interval computation for depth 15, residue 26180. -/
theorem bounds_15_26180 : exactInterval 15 26180 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_26180 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 26180) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_26180 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_26180 : oddCount 26180 15 = 6 ∧ acceleratedOrbit 15 26180 = 584 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_26180 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 26180) = 3 ^ 6 * m + 584 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_26180.1, data_15_26180.2]

end Collatz.Research.PassageAtlas.Batch0799
