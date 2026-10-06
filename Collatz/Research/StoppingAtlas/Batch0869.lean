import Collatz.Research.DescentIntervals.Classifier

namespace Collatz.Research.StoppingAtlas.Batch0869

open Collatz.Research.DescentIntervals

set_option maxRecDepth 20000
set_option maxHeartbeats 0

/-- Complete interval computation for depth 13, residue 6164. -/
theorem bounds_13_6164 : exactInterval 13 6164 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_13_6164 (m : Nat) :
    stoppingTime (2 ^ 13 * m + 6164) 13 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_13_6164 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_13_6164 : oddCount 6164 13 = 5 ∧ acceleratedOrbit 13 6164 = 184 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_13_6164 (m : Nat) :
    acceleratedOrbit 13 (2 ^ 13 * m + 6164) = 3 ^ 5 * m + 184 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_13_6164.1, data_13_6164.2]

/-- Complete interval computation for depth 13, residue 6165. -/
theorem bounds_13_6165 : exactInterval 13 6165 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_13_6165 (m : Nat) :
    stoppingTime (2 ^ 13 * m + 6165) 13 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_13_6165 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_13_6165 : oddCount 6165 13 = 5 ∧ acceleratedOrbit 13 6165 = 184 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_13_6165 (m : Nat) :
    acceleratedOrbit 13 (2 ^ 13 * m + 6165) = 3 ^ 5 * m + 184 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_13_6165.1, data_13_6165.2]

/-- Complete interval computation for depth 13, residue 6166. -/
theorem bounds_13_6166 : exactInterval 13 6166 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_13_6166 (m : Nat) :
    stoppingTime (2 ^ 13 * m + 6166) 13 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_13_6166 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_13_6166 : oddCount 6166 13 = 4 ∧ acceleratedOrbit 13 6166 = 61 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_13_6166 (m : Nat) :
    acceleratedOrbit 13 (2 ^ 13 * m + 6166) = 3 ^ 4 * m + 61 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_13_6166.1, data_13_6166.2]

/-- Complete interval computation for depth 13, residue 6167. -/
theorem bounds_13_6167 : exactInterval 13 6167 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_13_6167 (m : Nat) :
    stoppingTime (2 ^ 13 * m + 6167) 13 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_13_6167 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_13_6167 : oddCount 6167 13 = 4 ∧ acceleratedOrbit 13 6167 = 61 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_13_6167 (m : Nat) :
    acceleratedOrbit 13 (2 ^ 13 * m + 6167) = 3 ^ 4 * m + 61 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_13_6167.1, data_13_6167.2]

/-- Complete interval computation for depth 13, residue 6168. -/
theorem bounds_13_6168 : exactInterval 13 6168 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_13_6168 (m : Nat) :
    stoppingTime (2 ^ 13 * m + 6168) 13 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_13_6168 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_13_6168 : oddCount 6168 13 = 5 ∧ acceleratedOrbit 13 6168 = 184 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_13_6168 (m : Nat) :
    acceleratedOrbit 13 (2 ^ 13 * m + 6168) = 3 ^ 5 * m + 184 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_13_6168.1, data_13_6168.2]

/-- Complete interval computation for depth 13, residue 6169. -/
theorem bounds_13_6169 : exactInterval 13 6169 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_13_6169 (m : Nat) :
    stoppingTime (2 ^ 13 * m + 6169) 13 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_13_6169 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_13_6169 : oddCount 6169 13 = 7 ∧ acceleratedOrbit 13 6169 = 1648 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_13_6169 (m : Nat) :
    acceleratedOrbit 13 (2 ^ 13 * m + 6169) = 3 ^ 7 * m + 1648 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_13_6169.1, data_13_6169.2]

/-- Complete interval computation for depth 13, residue 6170. -/
theorem bounds_13_6170 : exactInterval 13 6170 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_13_6170 (m : Nat) :
    stoppingTime (2 ^ 13 * m + 6170) 13 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_13_6170 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_13_6170 : oddCount 6170 13 = 5 ∧ acceleratedOrbit 13 6170 = 184 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_13_6170 (m : Nat) :
    acceleratedOrbit 13 (2 ^ 13 * m + 6170) = 3 ^ 5 * m + 184 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_13_6170.1, data_13_6170.2]

/-- Complete interval computation for depth 13, residue 6171. -/
theorem bounds_13_6171 : exactInterval 13 6171 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_13_6171 (m : Nat) :
    stoppingTime (2 ^ 13 * m + 6171) 13 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_13_6171 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_13_6171 : oddCount 6171 13 = 9 ∧ acceleratedOrbit 13 6171 = 14831 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_13_6171 (m : Nat) :
    acceleratedOrbit 13 (2 ^ 13 * m + 6171) = 3 ^ 9 * m + 14831 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_13_6171.1, data_13_6171.2]

/-- Complete interval computation for depth 13, residue 6172. -/
theorem bounds_13_6172 : exactInterval 13 6172 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_13_6172 (m : Nat) :
    stoppingTime (2 ^ 13 * m + 6172) 13 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_13_6172 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_13_6172 : oddCount 6172 13 = 6 ∧ acceleratedOrbit 13 6172 = 550 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_13_6172 (m : Nat) :
    acceleratedOrbit 13 (2 ^ 13 * m + 6172) = 3 ^ 6 * m + 550 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_13_6172.1, data_13_6172.2]

/-- Complete interval computation for depth 13, residue 6173. -/
theorem bounds_13_6173 : exactInterval 13 6173 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_13_6173 (m : Nat) :
    stoppingTime (2 ^ 13 * m + 6173) 13 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_13_6173 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_13_6173 : oddCount 6173 13 = 6 ∧ acceleratedOrbit 13 6173 = 550 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_13_6173 (m : Nat) :
    acceleratedOrbit 13 (2 ^ 13 * m + 6173) = 3 ^ 6 * m + 550 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_13_6173.1, data_13_6173.2]

/-- Complete interval computation for depth 13, residue 6174. -/
theorem bounds_13_6174 : exactInterval 13 6174 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_13_6174 (m : Nat) :
    stoppingTime (2 ^ 13 * m + 6174) 13 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_13_6174 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_13_6174 : oddCount 6174 13 = 6 ∧ acceleratedOrbit 13 6174 = 550 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_13_6174 (m : Nat) :
    acceleratedOrbit 13 (2 ^ 13 * m + 6174) = 3 ^ 6 * m + 550 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_13_6174.1, data_13_6174.2]

/-- Complete interval computation for depth 13, residue 6175. -/
theorem bounds_13_6175 : exactInterval 13 6175 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_13_6175 (m : Nat) :
    stoppingTime (2 ^ 13 * m + 6175) 13 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_13_6175 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_13_6175 : oddCount 6175 13 = 9 ∧ acceleratedOrbit 13 6175 = 14840 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_13_6175 (m : Nat) :
    acceleratedOrbit 13 (2 ^ 13 * m + 6175) = 3 ^ 9 * m + 14840 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_13_6175.1, data_13_6175.2]

/-- Complete interval computation for depth 13, residue 6176. -/
theorem bounds_13_6176 : exactInterval 13 6176 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_13_6176 (m : Nat) :
    stoppingTime (2 ^ 13 * m + 6176) 13 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_13_6176 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_13_6176 : oddCount 6176 13 = 4 ∧ acceleratedOrbit 13 6176 = 62 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_13_6176 (m : Nat) :
    acceleratedOrbit 13 (2 ^ 13 * m + 6176) = 3 ^ 4 * m + 62 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_13_6176.1, data_13_6176.2]

/-- Complete interval computation for depth 13, residue 6177. -/
theorem bounds_13_6177 : exactInterval 13 6177 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_13_6177 (m : Nat) :
    stoppingTime (2 ^ 13 * m + 6177) 13 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_13_6177 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_13_6177 : oddCount 6177 13 = 6 ∧ acceleratedOrbit 13 6177 = 550 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_13_6177 (m : Nat) :
    acceleratedOrbit 13 (2 ^ 13 * m + 6177) = 3 ^ 6 * m + 550 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_13_6177.1, data_13_6177.2]

/-- Complete interval computation for depth 13, residue 6178. -/
theorem bounds_13_6178 : exactInterval 13 6178 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_13_6178 (m : Nat) :
    stoppingTime (2 ^ 13 * m + 6178) 13 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_13_6178 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_13_6178 : oddCount 6178 13 = 5 ∧ acceleratedOrbit 13 6178 = 184 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_13_6178 (m : Nat) :
    acceleratedOrbit 13 (2 ^ 13 * m + 6178) = 3 ^ 5 * m + 184 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_13_6178.1, data_13_6178.2]

end Collatz.Research.StoppingAtlas.Batch0869
