import Collatz.Research.DescentIntervals.Classifier

namespace Collatz.Research.StoppingAtlas.Batch0868

open Collatz.Research.DescentIntervals

set_option maxRecDepth 20000
set_option maxHeartbeats 0

/-- Complete interval computation for depth 13, residue 6149. -/
theorem bounds_13_6149 : exactInterval 13 6149 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_13_6149 (m : Nat) :
    stoppingTime (2 ^ 13 * m + 6149) 13 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_13_6149 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_13_6149 : oddCount 6149 13 = 7 ∧ acceleratedOrbit 13 6149 = 1646 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_13_6149 (m : Nat) :
    acceleratedOrbit 13 (2 ^ 13 * m + 6149) = 3 ^ 7 * m + 1646 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_13_6149.1, data_13_6149.2]

/-- Complete interval computation for depth 13, residue 6150. -/
theorem bounds_13_6150 : exactInterval 13 6150 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_13_6150 (m : Nat) :
    stoppingTime (2 ^ 13 * m + 6150) 13 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_13_6150 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_13_6150 : oddCount 6150 13 = 7 ∧ acceleratedOrbit 13 6150 = 1646 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_13_6150 (m : Nat) :
    acceleratedOrbit 13 (2 ^ 13 * m + 6150) = 3 ^ 7 * m + 1646 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_13_6150.1, data_13_6150.2]

/-- Complete interval computation for depth 13, residue 6151. -/
theorem bounds_13_6151 : exactInterval 13 6151 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_13_6151 (m : Nat) :
    stoppingTime (2 ^ 13 * m + 6151) 13 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_13_6151 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_13_6151 : oddCount 6151 13 = 6 ∧ acceleratedOrbit 13 6151 = 548 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_13_6151 (m : Nat) :
    acceleratedOrbit 13 (2 ^ 13 * m + 6151) = 3 ^ 6 * m + 548 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_13_6151.1, data_13_6151.2]

/-- Complete interval computation for depth 13, residue 6152. -/
theorem bounds_13_6152 : exactInterval 13 6152 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_13_6152 (m : Nat) :
    stoppingTime (2 ^ 13 * m + 6152) 13 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_13_6152 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_13_6152 : oddCount 6152 13 = 4 ∧ acceleratedOrbit 13 6152 = 61 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_13_6152 (m : Nat) :
    acceleratedOrbit 13 (2 ^ 13 * m + 6152) = 3 ^ 4 * m + 61 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_13_6152.1, data_13_6152.2]

/-- Complete interval computation for depth 13, residue 6153. -/
theorem bounds_13_6153 : exactInterval 13 6153 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_13_6153 (m : Nat) :
    stoppingTime (2 ^ 13 * m + 6153) 13 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_13_6153 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_13_6153 : oddCount 6153 13 = 8 ∧ acceleratedOrbit 13 6153 = 4931 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_13_6153 (m : Nat) :
    acceleratedOrbit 13 (2 ^ 13 * m + 6153) = 3 ^ 8 * m + 4931 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_13_6153.1, data_13_6153.2]

/-- Complete interval computation for depth 13, residue 6154. -/
theorem bounds_13_6154 : exactInterval 13 6154 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_13_6154 (m : Nat) :
    stoppingTime (2 ^ 13 * m + 6154) 13 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_13_6154 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_13_6154 : oddCount 6154 13 = 4 ∧ acceleratedOrbit 13 6154 = 61 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_13_6154 (m : Nat) :
    acceleratedOrbit 13 (2 ^ 13 * m + 6154) = 3 ^ 4 * m + 61 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_13_6154.1, data_13_6154.2]

/-- Complete interval computation for depth 13, residue 6155. -/
theorem bounds_13_6155 : exactInterval 13 6155 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_13_6155 (m : Nat) :
    stoppingTime (2 ^ 13 * m + 6155) 13 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_13_6155 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_13_6155 : oddCount 6155 13 = 7 ∧ acceleratedOrbit 13 6155 = 1646 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_13_6155 (m : Nat) :
    acceleratedOrbit 13 (2 ^ 13 * m + 6155) = 3 ^ 7 * m + 1646 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_13_6155.1, data_13_6155.2]

/-- Complete interval computation for depth 13, residue 6156. -/
theorem bounds_13_6156 : exactInterval 13 6156 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_13_6156 (m : Nat) :
    stoppingTime (2 ^ 13 * m + 6156) 13 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_13_6156 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_13_6156 : oddCount 6156 13 = 4 ∧ acceleratedOrbit 13 6156 = 61 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_13_6156 (m : Nat) :
    acceleratedOrbit 13 (2 ^ 13 * m + 6156) = 3 ^ 4 * m + 61 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_13_6156.1, data_13_6156.2]

/-- Complete interval computation for depth 13, residue 6157. -/
theorem bounds_13_6157 : exactInterval 13 6157 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_13_6157 (m : Nat) :
    stoppingTime (2 ^ 13 * m + 6157) 13 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_13_6157 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_13_6157 : oddCount 6157 13 = 4 ∧ acceleratedOrbit 13 6157 = 61 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_13_6157 (m : Nat) :
    acceleratedOrbit 13 (2 ^ 13 * m + 6157) = 3 ^ 4 * m + 61 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_13_6157.1, data_13_6157.2]

/-- Complete interval computation for depth 13, residue 6158. -/
theorem bounds_13_6158 : exactInterval 13 6158 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_13_6158 (m : Nat) :
    stoppingTime (2 ^ 13 * m + 6158) 13 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_13_6158 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_13_6158 : oddCount 6158 13 = 7 ∧ acceleratedOrbit 13 6158 = 1646 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_13_6158 (m : Nat) :
    acceleratedOrbit 13 (2 ^ 13 * m + 6158) = 3 ^ 7 * m + 1646 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_13_6158.1, data_13_6158.2]

/-- Complete interval computation for depth 13, residue 6159. -/
theorem bounds_13_6159 : exactInterval 13 6159 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_13_6159 (m : Nat) :
    stoppingTime (2 ^ 13 * m + 6159) 13 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_13_6159 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_13_6159 : oddCount 6159 13 = 7 ∧ acceleratedOrbit 13 6159 = 1646 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_13_6159 (m : Nat) :
    acceleratedOrbit 13 (2 ^ 13 * m + 6159) = 3 ^ 7 * m + 1646 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_13_6159.1, data_13_6159.2]

/-- Complete interval computation for depth 13, residue 6160. -/
theorem bounds_13_6160 : exactInterval 13 6160 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_13_6160 (m : Nat) :
    stoppingTime (2 ^ 13 * m + 6160) 13 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_13_6160 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_13_6160 : oddCount 6160 13 = 5 ∧ acceleratedOrbit 13 6160 = 184 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_13_6160 (m : Nat) :
    acceleratedOrbit 13 (2 ^ 13 * m + 6160) = 3 ^ 5 * m + 184 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_13_6160.1, data_13_6160.2]

/-- Complete interval computation for depth 13, residue 6161. -/
theorem bounds_13_6161 : exactInterval 13 6161 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_13_6161 (m : Nat) :
    stoppingTime (2 ^ 13 * m + 6161) 13 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_13_6161 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_13_6161 : oddCount 6161 13 = 4 ∧ acceleratedOrbit 13 6161 = 61 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_13_6161 (m : Nat) :
    acceleratedOrbit 13 (2 ^ 13 * m + 6161) = 3 ^ 4 * m + 61 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_13_6161.1, data_13_6161.2]

/-- Complete interval computation for depth 13, residue 6162. -/
theorem bounds_13_6162 : exactInterval 13 6162 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_13_6162 (m : Nat) :
    stoppingTime (2 ^ 13 * m + 6162) 13 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_13_6162 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_13_6162 : oddCount 6162 13 = 8 ∧ acceleratedOrbit 13 6162 = 4940 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_13_6162 (m : Nat) :
    acceleratedOrbit 13 (2 ^ 13 * m + 6162) = 3 ^ 8 * m + 4940 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_13_6162.1, data_13_6162.2]

/-- Complete interval computation for depth 13, residue 6163. -/
theorem bounds_13_6163 : exactInterval 13 6163 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_13_6163 (m : Nat) :
    stoppingTime (2 ^ 13 * m + 6163) 13 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_13_6163 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_13_6163 : oddCount 6163 13 = 8 ∧ acceleratedOrbit 13 6163 = 4940 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_13_6163 (m : Nat) :
    acceleratedOrbit 13 (2 ^ 13 * m + 6163) = 3 ^ 8 * m + 4940 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_13_6163.1, data_13_6163.2]

end Collatz.Research.StoppingAtlas.Batch0868
