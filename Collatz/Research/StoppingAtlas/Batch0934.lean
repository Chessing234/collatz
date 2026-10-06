import Collatz.Research.DescentIntervals.Classifier

namespace Collatz.Research.StoppingAtlas.Batch0934

open Collatz.Research.DescentIntervals

set_option maxRecDepth 20000
set_option maxHeartbeats 0

/-- Complete interval computation for depth 13, residue 7162. -/
theorem bounds_13_7162 : exactInterval 13 7162 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_13_7162 (m : Nat) :
    stoppingTime (2 ^ 13 * m + 7162) 13 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_13_7162 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_13_7162 : oddCount 7162 13 = 8 ∧ acceleratedOrbit 13 7162 = 5741 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_13_7162 (m : Nat) :
    acceleratedOrbit 13 (2 ^ 13 * m + 7162) = 3 ^ 8 * m + 5741 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_13_7162.1, data_13_7162.2]

/-- Complete interval computation for depth 13, residue 7163. -/
theorem bounds_13_7163 : exactInterval 13 7163 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_13_7163 (m : Nat) :
    stoppingTime (2 ^ 13 * m + 7163) 13 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_13_7163 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_13_7163 : oddCount 7163 13 = 9 ∧ acceleratedOrbit 13 7163 = 17216 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_13_7163 (m : Nat) :
    acceleratedOrbit 13 (2 ^ 13 * m + 7163) = 3 ^ 9 * m + 17216 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_13_7163.1, data_13_7163.2]

/-- Complete interval computation for depth 13, residue 7164. -/
theorem bounds_13_7164 : exactInterval 13 7164 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_13_7164 (m : Nat) :
    stoppingTime (2 ^ 13 * m + 7164) 13 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_13_7164 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_13_7164 : oddCount 7164 13 = 10 ∧ acceleratedOrbit 13 7164 = 51668 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_13_7164 (m : Nat) :
    acceleratedOrbit 13 (2 ^ 13 * m + 7164) = 3 ^ 10 * m + 51668 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_13_7164.1, data_13_7164.2]

/-- Complete interval computation for depth 13, residue 7165. -/
theorem bounds_13_7165 : exactInterval 13 7165 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_13_7165 (m : Nat) :
    stoppingTime (2 ^ 13 * m + 7165) 13 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_13_7165 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_13_7165 : oddCount 7165 13 = 10 ∧ acceleratedOrbit 13 7165 = 51668 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_13_7165 (m : Nat) :
    acceleratedOrbit 13 (2 ^ 13 * m + 7165) = 3 ^ 10 * m + 51668 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_13_7165.1, data_13_7165.2]

/-- Complete interval computation for depth 13, residue 7166. -/
theorem bounds_13_7166 : exactInterval 13 7166 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_13_7166 (m : Nat) :
    stoppingTime (2 ^ 13 * m + 7166) 13 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_13_7166 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_13_7166 : oddCount 7166 13 = 10 ∧ acceleratedOrbit 13 7166 = 51668 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_13_7166 (m : Nat) :
    acceleratedOrbit 13 (2 ^ 13 * m + 7166) = 3 ^ 10 * m + 51668 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_13_7166.1, data_13_7166.2]

/-- Complete interval computation for depth 13, residue 7167. -/
theorem bounds_13_7167 : exactInterval 13 7167 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_13_7167 (m : Nat) :
    stoppingTime (2 ^ 13 * m + 7167) 13 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_13_7167 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_13_7167 : oddCount 7167 13 = 12 ∧ acceleratedOrbit 13 7167 = 465011 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_13_7167 (m : Nat) :
    acceleratedOrbit 13 (2 ^ 13 * m + 7167) = 3 ^ 12 * m + 465011 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_13_7167.1, data_13_7167.2]

/-- Complete interval computation for depth 13, residue 7168. -/
theorem bounds_13_7168 : exactInterval 13 7168 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_13_7168 (m : Nat) :
    stoppingTime (2 ^ 13 * m + 7168) 13 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_13_7168 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_13_7168 : oddCount 7168 13 = 3 ∧ acceleratedOrbit 13 7168 = 26 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_13_7168 (m : Nat) :
    acceleratedOrbit 13 (2 ^ 13 * m + 7168) = 3 ^ 3 * m + 26 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_13_7168.1, data_13_7168.2]

/-- Complete interval computation for depth 13, residue 7169. -/
theorem bounds_13_7169 : exactInterval 13 7169 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_13_7169 (m : Nat) :
    stoppingTime (2 ^ 13 * m + 7169) 13 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_13_7169 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_13_7169 : oddCount 7169 13 = 7 ∧ acceleratedOrbit 13 7169 = 1916 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_13_7169 (m : Nat) :
    acceleratedOrbit 13 (2 ^ 13 * m + 7169) = 3 ^ 7 * m + 1916 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_13_7169.1, data_13_7169.2]

/-- Complete interval computation for depth 13, residue 7170. -/
theorem bounds_13_7170 : exactInterval 13 7170 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_13_7170 (m : Nat) :
    stoppingTime (2 ^ 13 * m + 7170) 13 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_13_7170 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_13_7170 : oddCount 7170 13 = 8 ∧ acceleratedOrbit 13 7170 = 5750 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_13_7170 (m : Nat) :
    acceleratedOrbit 13 (2 ^ 13 * m + 7170) = 3 ^ 8 * m + 5750 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_13_7170.1, data_13_7170.2]

/-- Complete interval computation for depth 13, residue 7171. -/
theorem bounds_13_7171 : exactInterval 13 7171 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_13_7171 (m : Nat) :
    stoppingTime (2 ^ 13 * m + 7171) 13 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_13_7171 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_13_7171 : oddCount 7171 13 = 8 ∧ acceleratedOrbit 13 7171 = 5750 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_13_7171 (m : Nat) :
    acceleratedOrbit 13 (2 ^ 13 * m + 7171) = 3 ^ 8 * m + 5750 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_13_7171.1, data_13_7171.2]

/-- Complete interval computation for depth 13, residue 7172. -/
theorem bounds_13_7172 : exactInterval 13 7172 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_13_7172 (m : Nat) :
    stoppingTime (2 ^ 13 * m + 7172) 13 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_13_7172 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_13_7172 : oddCount 7172 13 = 4 ∧ acceleratedOrbit 13 7172 = 71 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_13_7172 (m : Nat) :
    acceleratedOrbit 13 (2 ^ 13 * m + 7172) = 3 ^ 4 * m + 71 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_13_7172.1, data_13_7172.2]

/-- Complete interval computation for depth 13, residue 7173. -/
theorem bounds_13_7173 : exactInterval 13 7173 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_13_7173 (m : Nat) :
    stoppingTime (2 ^ 13 * m + 7173) 13 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_13_7173 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_13_7173 : oddCount 7173 13 = 4 ∧ acceleratedOrbit 13 7173 = 71 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_13_7173 (m : Nat) :
    acceleratedOrbit 13 (2 ^ 13 * m + 7173) = 3 ^ 4 * m + 71 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_13_7173.1, data_13_7173.2]

/-- Complete interval computation for depth 13, residue 7174. -/
theorem bounds_13_7174 : exactInterval 13 7174 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_13_7174 (m : Nat) :
    stoppingTime (2 ^ 13 * m + 7174) 13 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_13_7174 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_13_7174 : oddCount 7174 13 = 4 ∧ acceleratedOrbit 13 7174 = 71 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_13_7174 (m : Nat) :
    acceleratedOrbit 13 (2 ^ 13 * m + 7174) = 3 ^ 4 * m + 71 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_13_7174.1, data_13_7174.2]

/-- Complete interval computation for depth 13, residue 7175. -/
theorem bounds_13_7175 : exactInterval 13 7175 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_13_7175 (m : Nat) :
    stoppingTime (2 ^ 13 * m + 7175) 13 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_13_7175 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_13_7175 : oddCount 7175 13 = 8 ∧ acceleratedOrbit 13 7175 = 5750 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_13_7175 (m : Nat) :
    acceleratedOrbit 13 (2 ^ 13 * m + 7175) = 3 ^ 8 * m + 5750 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_13_7175.1, data_13_7175.2]

/-- Complete interval computation for depth 13, residue 7176. -/
theorem bounds_13_7176 : exactInterval 13 7176 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_13_7176 (m : Nat) :
    stoppingTime (2 ^ 13 * m + 7176) 13 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_13_7176 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_13_7176 : oddCount 7176 13 = 6 ∧ acceleratedOrbit 13 7176 = 641 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_13_7176 (m : Nat) :
    acceleratedOrbit 13 (2 ^ 13 * m + 7176) = 3 ^ 6 * m + 641 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_13_7176.1, data_13_7176.2]

/-- Complete interval computation for depth 13, residue 7177. -/
theorem bounds_13_7177 : exactInterval 13 7177 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_13_7177 (m : Nat) :
    stoppingTime (2 ^ 13 * m + 7177) 13 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_13_7177 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_13_7177 : oddCount 7177 13 = 9 ∧ acceleratedOrbit 13 7177 = 17252 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_13_7177 (m : Nat) :
    acceleratedOrbit 13 (2 ^ 13 * m + 7177) = 3 ^ 9 * m + 17252 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_13_7177.1, data_13_7177.2]

end Collatz.Research.StoppingAtlas.Batch0934
