import Collatz.Research.DescentIntervals.Classifier

namespace Collatz.Research.PassageAtlas.Batch0616

open Collatz.Research.DescentIntervals

set_option maxRecDepth 20000
set_option maxHeartbeats 0

/-- Complete interval computation for depth 15, residue 20152. -/
theorem bounds_15_20152 : exactInterval 15 20152 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_20152 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 20152) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_20152 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_20152 : oddCount 20152 15 = 8 ∧ acceleratedOrbit 15 20152 = 4040 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_20152 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 20152) = 3 ^ 8 * m + 4040 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_20152.1, data_15_20152.2]

/-- Complete interval computation for depth 15, residue 20153. -/
theorem bounds_15_20153 : exactInterval 15 20153 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_20153 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 20153) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_20153 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_20153 : oddCount 20153 15 = 9 ∧ acceleratedOrbit 15 20153 = 12109 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_20153 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 20153) = 3 ^ 9 * m + 12109 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_20153.1, data_15_20153.2]

/-- Complete interval computation for depth 15, residue 20154. -/
theorem bounds_15_20154 : exactInterval 15 20154 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_20154 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 20154) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_20154 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_20154 : oddCount 20154 15 = 8 ∧ acceleratedOrbit 15 20154 = 4040 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_20154 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 20154) = 3 ^ 8 * m + 4040 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_20154.1, data_15_20154.2]

/-- Complete interval computation for depth 15, residue 20155. -/
theorem bounds_15_20155 : exactInterval 15 20155 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_20155 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 20155) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_20155 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_20155 : oddCount 20155 15 = 9 ∧ acceleratedOrbit 15 20155 = 12109 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_20155 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 20155) = 3 ^ 9 * m + 12109 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_20155.1, data_15_20155.2]

/-- Complete interval computation for depth 15, residue 20156. -/
theorem bounds_15_20156 : exactInterval 15 20156 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_20156 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 20156) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_20156 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_20156 : oddCount 20156 15 = 6 ∧ acceleratedOrbit 15 20156 = 449 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_20156 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 20156) = 3 ^ 6 * m + 449 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_20156.1, data_15_20156.2]

/-- Complete interval computation for depth 15, residue 20157. -/
theorem bounds_15_20157 : exactInterval 15 20157 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_20157 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 20157) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_20157 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_20157 : oddCount 20157 15 = 6 ∧ acceleratedOrbit 15 20157 = 449 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_20157 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 20157) = 3 ^ 6 * m + 449 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_20157.1, data_15_20157.2]

/-- Complete interval computation for depth 15, residue 20158. -/
theorem bounds_15_20158 : exactInterval 15 20158 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_20158 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 20158) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_20158 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_20158 : oddCount 20158 15 = 6 ∧ acceleratedOrbit 15 20158 = 449 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_20158 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 20158) = 3 ^ 6 * m + 449 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_20158.1, data_15_20158.2]

/-- Complete interval computation for depth 15, residue 20159. -/
theorem bounds_15_20159 : exactInterval 15 20159 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_20159 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 20159) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_20159 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_20159 : oddCount 20159 15 = 11 ∧ acceleratedOrbit 15 20159 = 108989 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_20159 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 20159) = 3 ^ 11 * m + 108989 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_20159.1, data_15_20159.2]

/-- Complete interval computation for depth 15, residue 20160. -/
theorem bounds_15_20160 : exactInterval 15 20160 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_20160 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 20160) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_20160 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_20160 : oddCount 20160 15 = 4 ∧ acceleratedOrbit 15 20160 = 50 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_20160 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 20160) = 3 ^ 4 * m + 50 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_20160.1, data_15_20160.2]

/-- Complete interval computation for depth 15, residue 20161. -/
theorem bounds_15_20161 : exactInterval 15 20161 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_20161 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 20161) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_20161 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_20161 : oddCount 20161 15 = 8 ∧ acceleratedOrbit 15 20161 = 4040 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_20161 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 20161) = 3 ^ 8 * m + 4040 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_20161.1, data_15_20161.2]

/-- Complete interval computation for depth 15, residue 20162. -/
theorem bounds_15_20162 : exactInterval 15 20162 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_20162 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 20162) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_20162 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_20162 : oddCount 20162 15 = 7 ∧ acceleratedOrbit 15 20162 = 1346 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_20162 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 20162) = 3 ^ 7 * m + 1346 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_20162.1, data_15_20162.2]

/-- Complete interval computation for depth 15, residue 20163. -/
theorem bounds_15_20163 : exactInterval 15 20163 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_20163 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 20163) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_20163 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_20163 : oddCount 20163 15 = 7 ∧ acceleratedOrbit 15 20163 = 1346 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_20163 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 20163) = 3 ^ 7 * m + 1346 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_20163.1, data_15_20163.2]

/-- Complete interval computation for depth 15, residue 20164. -/
theorem bounds_15_20164 : exactInterval 15 20164 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_20164 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 20164) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_20164 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_20164 : oddCount 20164 15 = 4 ∧ acceleratedOrbit 15 20164 = 50 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_20164 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 20164) = 3 ^ 4 * m + 50 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_20164.1, data_15_20164.2]

/-- Complete interval computation for depth 15, residue 20165. -/
theorem bounds_15_20165 : exactInterval 15 20165 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_20165 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 20165) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_20165 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_20165 : oddCount 20165 15 = 4 ∧ acceleratedOrbit 15 20165 = 50 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_20165 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 20165) = 3 ^ 4 * m + 50 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_20165.1, data_15_20165.2]

/-- Complete interval computation for depth 15, residue 20166. -/
theorem bounds_15_20166 : exactInterval 15 20166 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_20166 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 20166) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_20166 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_20166 : oddCount 20166 15 = 4 ∧ acceleratedOrbit 15 20166 = 50 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_20166 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 20166) = 3 ^ 4 * m + 50 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_20166.1, data_15_20166.2]

/-- Complete interval computation for depth 15, residue 20167. -/
theorem bounds_15_20167 : exactInterval 15 20167 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_20167 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 20167) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_20167 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_20167 : oddCount 20167 15 = 8 ∧ acceleratedOrbit 15 20167 = 4040 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_20167 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 20167) = 3 ^ 8 * m + 4040 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_20167.1, data_15_20167.2]

/-- Complete interval computation for depth 15, residue 20168. -/
theorem bounds_15_20168 : exactInterval 15 20168 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_20168 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 20168) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_20168 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_20168 : oddCount 20168 15 = 4 ∧ acceleratedOrbit 15 20168 = 50 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_20168 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 20168) = 3 ^ 4 * m + 50 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_20168.1, data_15_20168.2]

/-- Complete interval computation for depth 15, residue 20169. -/
theorem bounds_15_20169 : exactInterval 15 20169 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_20169 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 20169) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_20169 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_20169 : oddCount 20169 15 = 8 ∧ acceleratedOrbit 15 20169 = 4040 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_20169 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 20169) = 3 ^ 8 * m + 4040 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_20169.1, data_15_20169.2]

/-- Complete interval computation for depth 15, residue 20170. -/
theorem bounds_15_20170 : exactInterval 15 20170 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_20170 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 20170) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_20170 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_20170 : oddCount 20170 15 = 4 ∧ acceleratedOrbit 15 20170 = 50 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_20170 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 20170) = 3 ^ 4 * m + 50 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_20170.1, data_15_20170.2]

/-- Complete interval computation for depth 15, residue 20171. -/
theorem bounds_15_20171 : exactInterval 15 20171 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_20171 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 20171) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_20171 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_20171 : oddCount 20171 15 = 10 ∧ acceleratedOrbit 15 20171 = 36359 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_20171 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 20171) = 3 ^ 10 * m + 36359 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_20171.1, data_15_20171.2]

/-- Complete interval computation for depth 15, residue 20172. -/
theorem bounds_15_20172 : exactInterval 15 20172 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_20172 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 20172) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_20172 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_20172 : oddCount 20172 15 = 4 ∧ acceleratedOrbit 15 20172 = 50 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_20172 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 20172) = 3 ^ 4 * m + 50 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_20172.1, data_15_20172.2]

/-- Complete interval computation for depth 15, residue 20173. -/
theorem bounds_15_20173 : exactInterval 15 20173 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_20173 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 20173) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_20173 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_20173 : oddCount 20173 15 = 4 ∧ acceleratedOrbit 15 20173 = 50 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_20173 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 20173) = 3 ^ 4 * m + 50 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_20173.1, data_15_20173.2]

/-- Complete interval computation for depth 15, residue 20174. -/
theorem bounds_15_20174 : exactInterval 15 20174 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_20174 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 20174) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_20174 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_20174 : oddCount 20174 15 = 12 ∧ acceleratedOrbit 15 20174 = 327230 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_20174 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 20174) = 3 ^ 12 * m + 327230 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_20174.1, data_15_20174.2]

/-- Complete interval computation for depth 15, residue 20175. -/
theorem bounds_15_20175 : exactInterval 15 20175 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_20175 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 20175) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_20175 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_20175 : oddCount 20175 15 = 12 ∧ acceleratedOrbit 15 20175 = 327230 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_20175 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 20175) = 3 ^ 12 * m + 327230 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_20175.1, data_15_20175.2]

/-- Complete interval computation for depth 15, residue 20176. -/
theorem bounds_15_20176 : exactInterval 15 20176 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_20176 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 20176) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_20176 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_20176 : oddCount 20176 15 = 4 ∧ acceleratedOrbit 15 20176 = 50 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_20176 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 20176) = 3 ^ 4 * m + 50 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_20176.1, data_15_20176.2]

/-- Complete interval computation for depth 15, residue 20177. -/
theorem bounds_15_20177 : exactInterval 15 20177 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_20177 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 20177) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_20177 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_20177 : oddCount 20177 15 = 6 ∧ acceleratedOrbit 15 20177 = 449 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_20177 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 20177) = 3 ^ 6 * m + 449 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_20177.1, data_15_20177.2]

/-- Complete interval computation for depth 15, residue 20178. -/
theorem bounds_15_20178 : exactInterval 15 20178 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_20178 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 20178) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_20178 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_20178 : oddCount 20178 15 = 6 ∧ acceleratedOrbit 15 20178 = 449 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_20178 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 20178) = 3 ^ 6 * m + 449 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_20178.1, data_15_20178.2]

/-- Complete interval computation for depth 15, residue 20179. -/
theorem bounds_15_20179 : exactInterval 15 20179 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_20179 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 20179) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_20179 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_20179 : oddCount 20179 15 = 6 ∧ acceleratedOrbit 15 20179 = 449 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_20179 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 20179) = 3 ^ 6 * m + 449 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_20179.1, data_15_20179.2]

/-- Complete interval computation for depth 15, residue 20180. -/
theorem bounds_15_20180 : exactInterval 15 20180 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_20180 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 20180) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_20180 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_20180 : oddCount 20180 15 = 4 ∧ acceleratedOrbit 15 20180 = 50 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_20180 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 20180) = 3 ^ 4 * m + 50 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_20180.1, data_15_20180.2]

/-- Complete interval computation for depth 15, residue 20181. -/
theorem bounds_15_20181 : exactInterval 15 20181 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_20181 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 20181) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_20181 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_20181 : oddCount 20181 15 = 4 ∧ acceleratedOrbit 15 20181 = 50 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_20181 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 20181) = 3 ^ 4 * m + 50 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_20181.1, data_15_20181.2]

/-- Complete interval computation for depth 15, residue 20182. -/
theorem bounds_15_20182 : exactInterval 15 20182 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_20182 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 20182) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_20182 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_20182 : oddCount 20182 15 = 8 ∧ acceleratedOrbit 15 20182 = 4043 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_20182 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 20182) = 3 ^ 8 * m + 4043 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_20182.1, data_15_20182.2]

/-- Complete interval computation for depth 15, residue 20183. -/
theorem bounds_15_20183 : exactInterval 15 20183 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_20183 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 20183) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_20183 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_20183 : oddCount 20183 15 = 8 ∧ acceleratedOrbit 15 20183 = 4043 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_20183 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 20183) = 3 ^ 8 * m + 4043 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_20183.1, data_15_20183.2]

/-- Complete interval computation for depth 15, residue 20184. -/
theorem bounds_15_20184 : exactInterval 15 20184 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_20184 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 20184) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_20184 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_20184 : oddCount 20184 15 = 7 ∧ acceleratedOrbit 15 20184 = 1349 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_20184 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 20184) = 3 ^ 7 * m + 1349 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_20184.1, data_15_20184.2]

end Collatz.Research.PassageAtlas.Batch0616
