import Collatz.Research.DescentIntervals.Classifier

namespace Collatz.Research.StoppingAtlas.Batch0999

open Collatz.Research.DescentIntervals

set_option maxRecDepth 20000
set_option maxHeartbeats 0

/-- Complete interval computation for depth 13, residue 8161. -/
theorem bounds_13_8161 : exactInterval 13 8161 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_13_8161 (m : Nat) :
    stoppingTime (2 ^ 13 * m + 8161) 13 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_13_8161 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_13_8161 : oddCount 8161 13 = 9 ∧ acceleratedOrbit 13 8161 = 19615 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_13_8161 (m : Nat) :
    acceleratedOrbit 13 (2 ^ 13 * m + 8161) = 3 ^ 9 * m + 19615 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_13_8161.1, data_13_8161.2]

/-- Complete interval computation for depth 13, residue 8162. -/
theorem bounds_13_8162 : exactInterval 13 8162 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_13_8162 (m : Nat) :
    stoppingTime (2 ^ 13 * m + 8162) 13 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_13_8162 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_13_8162 : oddCount 8162 13 = 7 ∧ acceleratedOrbit 13 8162 = 2186 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_13_8162 (m : Nat) :
    acceleratedOrbit 13 (2 ^ 13 * m + 8162) = 3 ^ 7 * m + 2186 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_13_8162.1, data_13_8162.2]

/-- Complete interval computation for depth 13, residue 8163. -/
theorem bounds_13_8163 : exactInterval 13 8163 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_13_8163 (m : Nat) :
    stoppingTime (2 ^ 13 * m + 8163) 13 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_13_8163 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_13_8163 : oddCount 8163 13 = 7 ∧ acceleratedOrbit 13 8163 = 2186 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_13_8163 (m : Nat) :
    acceleratedOrbit 13 (2 ^ 13 * m + 8163) = 3 ^ 7 * m + 2186 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_13_8163.1, data_13_8163.2]

/-- Complete interval computation for depth 13, residue 8164. -/
theorem bounds_13_8164 : exactInterval 13 8164 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_13_8164 (m : Nat) :
    stoppingTime (2 ^ 13 * m + 8164) 13 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_13_8164 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_13_8164 : oddCount 8164 13 = 7 ∧ acceleratedOrbit 13 8164 = 2182 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_13_8164 (m : Nat) :
    acceleratedOrbit 13 (2 ^ 13 * m + 8164) = 3 ^ 7 * m + 2182 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_13_8164.1, data_13_8164.2]

/-- Complete interval computation for depth 13, residue 8165. -/
theorem bounds_13_8165 : exactInterval 13 8165 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_13_8165 (m : Nat) :
    stoppingTime (2 ^ 13 * m + 8165) 13 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_13_8165 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_13_8165 : oddCount 8165 13 = 7 ∧ acceleratedOrbit 13 8165 = 2182 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_13_8165 (m : Nat) :
    acceleratedOrbit 13 (2 ^ 13 * m + 8165) = 3 ^ 7 * m + 2182 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_13_8165.1, data_13_8165.2]

/-- Complete interval computation for depth 13, residue 8166. -/
theorem bounds_13_8166 : exactInterval 13 8166 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_13_8166 (m : Nat) :
    stoppingTime (2 ^ 13 * m + 8166) 13 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_13_8166 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_13_8166 : oddCount 8166 13 = 7 ∧ acceleratedOrbit 13 8166 = 2182 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_13_8166 (m : Nat) :
    acceleratedOrbit 13 (2 ^ 13 * m + 8166) = 3 ^ 7 * m + 2182 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_13_8166.1, data_13_8166.2]

/-- Complete interval computation for depth 13, residue 8167. -/
theorem bounds_13_8167 : exactInterval 13 8167 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_13_8167 (m : Nat) :
    stoppingTime (2 ^ 13 * m + 8167) 13 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_13_8167 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_13_8167 : oddCount 8167 13 = 9 ∧ acceleratedOrbit 13 8167 = 19628 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_13_8167 (m : Nat) :
    acceleratedOrbit 13 (2 ^ 13 * m + 8167) = 3 ^ 9 * m + 19628 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_13_8167.1, data_13_8167.2]

/-- Complete interval computation for depth 13, residue 8168. -/
theorem bounds_13_8168 : exactInterval 13 8168 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_13_8168 (m : Nat) :
    stoppingTime (2 ^ 13 * m + 8168) 13 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_13_8168 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_13_8168 : oddCount 8168 13 = 8 ∧ acceleratedOrbit 13 8168 = 6560 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_13_8168 (m : Nat) :
    acceleratedOrbit 13 (2 ^ 13 * m + 8168) = 3 ^ 8 * m + 6560 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_13_8168.1, data_13_8168.2]

/-- Complete interval computation for depth 13, residue 8169. -/
theorem bounds_13_8169 : exactInterval 13 8169 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_13_8169 (m : Nat) :
    stoppingTime (2 ^ 13 * m + 8169) 13 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_13_8169 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_13_8169 : oddCount 8169 13 = 8 ∧ acceleratedOrbit 13 8169 = 6544 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_13_8169 (m : Nat) :
    acceleratedOrbit 13 (2 ^ 13 * m + 8169) = 3 ^ 8 * m + 6544 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_13_8169.1, data_13_8169.2]

/-- Complete interval computation for depth 13, residue 8170. -/
theorem bounds_13_8170 : exactInterval 13 8170 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_13_8170 (m : Nat) :
    stoppingTime (2 ^ 13 * m + 8170) 13 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_13_8170 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_13_8170 : oddCount 8170 13 = 8 ∧ acceleratedOrbit 13 8170 = 6560 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_13_8170 (m : Nat) :
    acceleratedOrbit 13 (2 ^ 13 * m + 8170) = 3 ^ 8 * m + 6560 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_13_8170.1, data_13_8170.2]

/-- Complete interval computation for depth 13, residue 8171. -/
theorem bounds_13_8171 : exactInterval 13 8171 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_13_8171 (m : Nat) :
    stoppingTime (2 ^ 13 * m + 8171) 13 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_13_8171 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_13_8171 : oddCount 8171 13 = 10 ∧ acceleratedOrbit 13 8171 = 58913 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_13_8171 (m : Nat) :
    acceleratedOrbit 13 (2 ^ 13 * m + 8171) = 3 ^ 10 * m + 58913 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_13_8171.1, data_13_8171.2]

/-- Complete interval computation for depth 13, residue 8172. -/
theorem bounds_13_8172 : exactInterval 13 8172 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_13_8172 (m : Nat) :
    stoppingTime (2 ^ 13 * m + 8172) 13 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_13_8172 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_13_8172 : oddCount 8172 13 = 8 ∧ acceleratedOrbit 13 8172 = 6551 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_13_8172 (m : Nat) :
    acceleratedOrbit 13 (2 ^ 13 * m + 8172) = 3 ^ 8 * m + 6551 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_13_8172.1, data_13_8172.2]

/-- Complete interval computation for depth 13, residue 8173. -/
theorem bounds_13_8173 : exactInterval 13 8173 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_13_8173 (m : Nat) :
    stoppingTime (2 ^ 13 * m + 8173) 13 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_13_8173 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_13_8173 : oddCount 8173 13 = 8 ∧ acceleratedOrbit 13 8173 = 6551 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_13_8173 (m : Nat) :
    acceleratedOrbit 13 (2 ^ 13 * m + 8173) = 3 ^ 8 * m + 6551 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_13_8173.1, data_13_8173.2]

/-- Complete interval computation for depth 13, residue 8174. -/
theorem bounds_13_8174 : exactInterval 13 8174 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_13_8174 (m : Nat) :
    stoppingTime (2 ^ 13 * m + 8174) 13 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_13_8174 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_13_8174 : oddCount 8174 13 = 8 ∧ acceleratedOrbit 13 8174 = 6551 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_13_8174 (m : Nat) :
    acceleratedOrbit 13 (2 ^ 13 * m + 8174) = 3 ^ 8 * m + 6551 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_13_8174.1, data_13_8174.2]

/-- Complete interval computation for depth 13, residue 8175. -/
theorem bounds_13_8175 : exactInterval 13 8175 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_13_8175 (m : Nat) :
    stoppingTime (2 ^ 13 * m + 8175) 13 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_13_8175 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_13_8175 : oddCount 8175 13 = 9 ∧ acceleratedOrbit 13 8175 = 19646 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_13_8175 (m : Nat) :
    acceleratedOrbit 13 (2 ^ 13 * m + 8175) = 3 ^ 9 * m + 19646 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_13_8175.1, data_13_8175.2]

end Collatz.Research.StoppingAtlas.Batch0999
