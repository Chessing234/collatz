import Collatz.Research.DescentIntervals.Classifier

namespace Collatz.Research.StoppingAtlas.Batch0998

open Collatz.Research.DescentIntervals

set_option maxRecDepth 20000
set_option maxHeartbeats 0

/-- Complete interval computation for depth 13, residue 8145. -/
theorem bounds_13_8145 : exactInterval 13 8145 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_13_8145 (m : Nat) :
    stoppingTime (2 ^ 13 * m + 8145) 13 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_13_8145 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_13_8145 : oddCount 8145 13 = 7 ∧ acceleratedOrbit 13 8145 = 2177 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_13_8145 (m : Nat) :
    acceleratedOrbit 13 (2 ^ 13 * m + 8145) = 3 ^ 7 * m + 2177 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_13_8145.1, data_13_8145.2]

/-- Complete interval computation for depth 13, residue 8146. -/
theorem bounds_13_8146 : exactInterval 13 8146 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_13_8146 (m : Nat) :
    stoppingTime (2 ^ 13 * m + 8146) 13 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_13_8146 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_13_8146 : oddCount 8146 13 = 8 ∧ acceleratedOrbit 13 8146 = 6527 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_13_8146 (m : Nat) :
    acceleratedOrbit 13 (2 ^ 13 * m + 8146) = 3 ^ 8 * m + 6527 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_13_8146.1, data_13_8146.2]

/-- Complete interval computation for depth 13, residue 8147. -/
theorem bounds_13_8147 : exactInterval 13 8147 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_13_8147 (m : Nat) :
    stoppingTime (2 ^ 13 * m + 8147) 13 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_13_8147 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_13_8147 : oddCount 8147 13 = 8 ∧ acceleratedOrbit 13 8147 = 6527 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_13_8147 (m : Nat) :
    acceleratedOrbit 13 (2 ^ 13 * m + 8147) = 3 ^ 8 * m + 6527 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_13_8147.1, data_13_8147.2]

/-- Complete interval computation for depth 13, residue 8148. -/
theorem bounds_13_8148 : exactInterval 13 8148 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_13_8148 (m : Nat) :
    stoppingTime (2 ^ 13 * m + 8148) 13 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_13_8148 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_13_8148 : oddCount 8148 13 = 7 ∧ acceleratedOrbit 13 8148 = 2186 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_13_8148 (m : Nat) :
    acceleratedOrbit 13 (2 ^ 13 * m + 8148) = 3 ^ 7 * m + 2186 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_13_8148.1, data_13_8148.2]

/-- Complete interval computation for depth 13, residue 8149. -/
theorem bounds_13_8149 : exactInterval 13 8149 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_13_8149 (m : Nat) :
    stoppingTime (2 ^ 13 * m + 8149) 13 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_13_8149 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_13_8149 : oddCount 8149 13 = 7 ∧ acceleratedOrbit 13 8149 = 2186 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_13_8149 (m : Nat) :
    acceleratedOrbit 13 (2 ^ 13 * m + 8149) = 3 ^ 7 * m + 2186 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_13_8149.1, data_13_8149.2]

/-- Complete interval computation for depth 13, residue 8150. -/
theorem bounds_13_8150 : exactInterval 13 8150 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_13_8150 (m : Nat) :
    stoppingTime (2 ^ 13 * m + 8150) 13 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_13_8150 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_13_8150 : oddCount 8150 13 = 9 ∧ acceleratedOrbit 13 8150 = 19592 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_13_8150 (m : Nat) :
    acceleratedOrbit 13 (2 ^ 13 * m + 8150) = 3 ^ 9 * m + 19592 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_13_8150.1, data_13_8150.2]

/-- Complete interval computation for depth 13, residue 8151. -/
theorem bounds_13_8151 : exactInterval 13 8151 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_13_8151 (m : Nat) :
    stoppingTime (2 ^ 13 * m + 8151) 13 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_13_8151 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_13_8151 : oddCount 8151 13 = 9 ∧ acceleratedOrbit 13 8151 = 19592 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_13_8151 (m : Nat) :
    acceleratedOrbit 13 (2 ^ 13 * m + 8151) = 3 ^ 9 * m + 19592 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_13_8151.1, data_13_8151.2]

/-- Complete interval computation for depth 13, residue 8152. -/
theorem bounds_13_8152 : exactInterval 13 8152 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_13_8152 (m : Nat) :
    stoppingTime (2 ^ 13 * m + 8152) 13 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_13_8152 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_13_8152 : oddCount 8152 13 = 7 ∧ acceleratedOrbit 13 8152 = 2180 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_13_8152 (m : Nat) :
    acceleratedOrbit 13 (2 ^ 13 * m + 8152) = 3 ^ 7 * m + 2180 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_13_8152.1, data_13_8152.2]

/-- Complete interval computation for depth 13, residue 8153. -/
theorem bounds_13_8153 : exactInterval 13 8153 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_13_8153 (m : Nat) :
    stoppingTime (2 ^ 13 * m + 8153) 13 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_13_8153 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_13_8153 : oddCount 8153 13 = 6 ∧ acceleratedOrbit 13 8153 = 728 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_13_8153 (m : Nat) :
    acceleratedOrbit 13 (2 ^ 13 * m + 8153) = 3 ^ 6 * m + 728 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_13_8153.1, data_13_8153.2]

/-- Complete interval computation for depth 13, residue 8154. -/
theorem bounds_13_8154 : exactInterval 13 8154 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_13_8154 (m : Nat) :
    stoppingTime (2 ^ 13 * m + 8154) 13 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_13_8154 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_13_8154 : oddCount 8154 13 = 7 ∧ acceleratedOrbit 13 8154 = 2180 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_13_8154 (m : Nat) :
    acceleratedOrbit 13 (2 ^ 13 * m + 8154) = 3 ^ 7 * m + 2180 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_13_8154.1, data_13_8154.2]

/-- Complete interval computation for depth 13, residue 8155. -/
theorem bounds_13_8155 : exactInterval 13 8155 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_13_8155 (m : Nat) :
    stoppingTime (2 ^ 13 * m + 8155) 13 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_13_8155 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_13_8155 : oddCount 8155 13 = 9 ∧ acceleratedOrbit 13 8155 = 19601 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_13_8155 (m : Nat) :
    acceleratedOrbit 13 (2 ^ 13 * m + 8155) = 3 ^ 9 * m + 19601 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_13_8155.1, data_13_8155.2]

/-- Complete interval computation for depth 13, residue 8156. -/
theorem bounds_13_8156 : exactInterval 13 8156 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_13_8156 (m : Nat) :
    stoppingTime (2 ^ 13 * m + 8156) 13 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_13_8156 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_13_8156 : oddCount 8156 13 = 7 ∧ acceleratedOrbit 13 8156 = 2180 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_13_8156 (m : Nat) :
    acceleratedOrbit 13 (2 ^ 13 * m + 8156) = 3 ^ 7 * m + 2180 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_13_8156.1, data_13_8156.2]

/-- Complete interval computation for depth 13, residue 8157. -/
theorem bounds_13_8157 : exactInterval 13 8157 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_13_8157 (m : Nat) :
    stoppingTime (2 ^ 13 * m + 8157) 13 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_13_8157 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_13_8157 : oddCount 8157 13 = 7 ∧ acceleratedOrbit 13 8157 = 2180 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_13_8157 (m : Nat) :
    acceleratedOrbit 13 (2 ^ 13 * m + 8157) = 3 ^ 7 * m + 2180 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_13_8157.1, data_13_8157.2]

/-- Complete interval computation for depth 13, residue 8158. -/
theorem bounds_13_8158 : exactInterval 13 8158 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_13_8158 (m : Nat) :
    stoppingTime (2 ^ 13 * m + 8158) 13 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_13_8158 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_13_8158 : oddCount 8158 13 = 8 ∧ acceleratedOrbit 13 8158 = 6536 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_13_8158 (m : Nat) :
    acceleratedOrbit 13 (2 ^ 13 * m + 8158) = 3 ^ 8 * m + 6536 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_13_8158.1, data_13_8158.2]

/-- Complete interval computation for depth 13, residue 8159. -/
theorem bounds_13_8159 : exactInterval 13 8159 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_13_8159 (m : Nat) :
    stoppingTime (2 ^ 13 * m + 8159) 13 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_13_8159 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_13_8159 : oddCount 8159 13 = 8 ∧ acceleratedOrbit 13 8159 = 6536 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_13_8159 (m : Nat) :
    acceleratedOrbit 13 (2 ^ 13 * m + 8159) = 3 ^ 8 * m + 6536 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_13_8159.1, data_13_8159.2]

/-- Complete interval computation for depth 13, residue 8160. -/
theorem bounds_13_8160 : exactInterval 13 8160 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_13_8160 (m : Nat) :
    stoppingTime (2 ^ 13 * m + 8160) 13 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_13_8160 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_13_8160 : oddCount 8160 13 = 8 ∧ acceleratedOrbit 13 8160 = 6560 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_13_8160 (m : Nat) :
    acceleratedOrbit 13 (2 ^ 13 * m + 8160) = 3 ^ 8 * m + 6560 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_13_8160.1, data_13_8160.2]

end Collatz.Research.StoppingAtlas.Batch0998
