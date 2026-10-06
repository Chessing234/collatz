import Collatz.Research.DescentIntervals.Classifier

namespace Collatz.Research.PassageAtlas.Batch0830

open Collatz.Research.DescentIntervals

set_option maxRecDepth 20000
set_option maxHeartbeats 0

/-- Complete interval computation for depth 15, residue 27164. -/
theorem bounds_15_27164 : exactInterval 15 27164 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_27164 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 27164) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_27164 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_27164 : oddCount 27164 15 = 6 ∧ acceleratedOrbit 15 27164 = 605 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_27164 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 27164) = 3 ^ 6 * m + 605 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_27164.1, data_15_27164.2]

/-- Complete interval computation for depth 15, residue 27165. -/
theorem bounds_15_27165 : exactInterval 15 27165 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_27165 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 27165) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_27165 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_27165 : oddCount 27165 15 = 6 ∧ acceleratedOrbit 15 27165 = 605 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_27165 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 27165) = 3 ^ 6 * m + 605 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_27165.1, data_15_27165.2]

/-- Complete interval computation for depth 15, residue 27166. -/
theorem bounds_15_27166 : exactInterval 15 27166 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_27166 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 27166) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_27166 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_27166 : oddCount 27166 15 = 6 ∧ acceleratedOrbit 15 27166 = 605 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_27166 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 27166) = 3 ^ 6 * m + 605 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_27166.1, data_15_27166.2]

/-- Complete interval computation for depth 15, residue 27167. -/
theorem bounds_15_27167 : exactInterval 15 27167 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_27167 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 27167) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_27167 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_27167 : oddCount 27167 15 = 8 ∧ acceleratedOrbit 15 27167 = 5440 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_27167 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 27167) = 3 ^ 8 * m + 5440 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_27167.1, data_15_27167.2]

/-- Complete interval computation for depth 15, residue 27168. -/
theorem bounds_15_27168 : exactInterval 15 27168 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_27168 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 27168) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_27168 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_27168 : oddCount 27168 15 = 6 ∧ acceleratedOrbit 15 27168 = 607 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_27168 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 27168) = 3 ^ 6 * m + 607 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_27168.1, data_15_27168.2]

/-- Complete interval computation for depth 15, residue 27169. -/
theorem bounds_15_27169 : exactInterval 15 27169 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_27169 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 27169) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_27169 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_27169 : oddCount 27169 15 = 6 ∧ acceleratedOrbit 15 27169 = 605 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_27169 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 27169) = 3 ^ 6 * m + 605 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_27169.1, data_15_27169.2]

/-- Complete interval computation for depth 15, residue 27170. -/
theorem bounds_15_27170 : exactInterval 15 27170 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_27170 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 27170) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_27170 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_27170 : oddCount 27170 15 = 6 ∧ acceleratedOrbit 15 27170 = 605 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_27170 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 27170) = 3 ^ 6 * m + 605 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_27170.1, data_15_27170.2]

/-- Complete interval computation for depth 15, residue 27171. -/
theorem bounds_15_27171 : exactInterval 15 27171 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_27171 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 27171) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_27171 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_27171 : oddCount 27171 15 = 6 ∧ acceleratedOrbit 15 27171 = 605 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_27171 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 27171) = 3 ^ 6 * m + 605 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_27171.1, data_15_27171.2]

/-- Complete interval computation for depth 15, residue 27172. -/
theorem bounds_15_27172 : exactInterval 15 27172 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_27172 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 27172) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_27172 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_27172 : oddCount 27172 15 = 7 ∧ acceleratedOrbit 15 27172 = 1814 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_27172 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 27172) = 3 ^ 7 * m + 1814 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_27172.1, data_15_27172.2]

/-- Complete interval computation for depth 15, residue 27173. -/
theorem bounds_15_27173 : exactInterval 15 27173 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_27173 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 27173) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_27173 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_27173 : oddCount 27173 15 = 7 ∧ acceleratedOrbit 15 27173 = 1814 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_27173 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 27173) = 3 ^ 7 * m + 1814 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_27173.1, data_15_27173.2]

/-- Complete interval computation for depth 15, residue 27174. -/
theorem bounds_15_27174 : exactInterval 15 27174 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_27174 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 27174) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_27174 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_27174 : oddCount 27174 15 = 7 ∧ acceleratedOrbit 15 27174 = 1814 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_27174 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 27174) = 3 ^ 7 * m + 1814 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_27174.1, data_15_27174.2]

/-- Complete interval computation for depth 15, residue 27175. -/
theorem bounds_15_27175 : exactInterval 15 27175 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_27175 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 27175) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_27175 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_27175 : oddCount 27175 15 = 7 ∧ acceleratedOrbit 15 27175 = 1814 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_27175 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 27175) = 3 ^ 7 * m + 1814 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_27175.1, data_15_27175.2]

/-- Complete interval computation for depth 15, residue 27176. -/
theorem bounds_15_27176 : exactInterval 15 27176 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_27176 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 27176) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_27176 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_27176 : oddCount 27176 15 = 6 ∧ acceleratedOrbit 15 27176 = 607 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_27176 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 27176) = 3 ^ 6 * m + 607 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_27176.1, data_15_27176.2]

/-- Complete interval computation for depth 15, residue 27177. -/
theorem bounds_15_27177 : exactInterval 15 27177 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_27177 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 27177) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_27177 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_27177 : oddCount 27177 15 = 11 ∧ acceleratedOrbit 15 27177 = 146933 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_27177 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 27177) = 3 ^ 11 * m + 146933 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_27177.1, data_15_27177.2]

/-- Complete interval computation for depth 15, residue 27178. -/
theorem bounds_15_27178 : exactInterval 15 27178 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_27178 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 27178) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_27178 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_27178 : oddCount 27178 15 = 6 ∧ acceleratedOrbit 15 27178 = 607 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_27178 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 27178) = 3 ^ 6 * m + 607 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_27178.1, data_15_27178.2]

/-- Complete interval computation for depth 15, residue 27179. -/
theorem bounds_15_27179 : exactInterval 15 27179 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_27179 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 27179) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_27179 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_27179 : oddCount 27179 15 = 6 ∧ acceleratedOrbit 15 27179 = 605 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_27179 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 27179) = 3 ^ 6 * m + 605 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_27179.1, data_15_27179.2]

/-- Complete interval computation for depth 15, residue 27180. -/
theorem bounds_15_27180 : exactInterval 15 27180 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_27180 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 27180) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_27180 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_27180 : oddCount 27180 15 = 6 ∧ acceleratedOrbit 15 27180 = 605 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_27180 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 27180) = 3 ^ 6 * m + 605 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_27180.1, data_15_27180.2]

/-- Complete interval computation for depth 15, residue 27181. -/
theorem bounds_15_27181 : exactInterval 15 27181 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_27181 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 27181) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_27181 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_27181 : oddCount 27181 15 = 6 ∧ acceleratedOrbit 15 27181 = 605 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_27181 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 27181) = 3 ^ 6 * m + 605 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_27181.1, data_15_27181.2]

/-- Complete interval computation for depth 15, residue 27182. -/
theorem bounds_15_27182 : exactInterval 15 27182 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_27182 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 27182) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_27182 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_27182 : oddCount 27182 15 = 6 ∧ acceleratedOrbit 15 27182 = 605 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_27182 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 27182) = 3 ^ 6 * m + 605 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_27182.1, data_15_27182.2]

/-- Complete interval computation for depth 15, residue 27183. -/
theorem bounds_15_27183 : exactInterval 15 27183 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_27183 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 27183) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_27183 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_27183 : oddCount 27183 15 = 8 ∧ acceleratedOrbit 15 27183 = 5443 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_27183 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 27183) = 3 ^ 8 * m + 5443 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_27183.1, data_15_27183.2]

/-- Complete interval computation for depth 15, residue 27184. -/
theorem bounds_15_27184 : exactInterval 15 27184 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_27184 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 27184) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_27184 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_27184 : oddCount 27184 15 = 6 ∧ acceleratedOrbit 15 27184 = 607 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_27184 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 27184) = 3 ^ 6 * m + 607 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_27184.1, data_15_27184.2]

/-- Complete interval computation for depth 15, residue 27185. -/
theorem bounds_15_27185 : exactInterval 15 27185 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_27185 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 27185) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_27185 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_27185 : oddCount 27185 15 = 10 ∧ acceleratedOrbit 15 27185 = 49004 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_27185 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 27185) = 3 ^ 10 * m + 49004 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_27185.1, data_15_27185.2]

/-- Complete interval computation for depth 15, residue 27186. -/
theorem bounds_15_27186 : exactInterval 15 27186 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_27186 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 27186) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_27186 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_27186 : oddCount 27186 15 = 10 ∧ acceleratedOrbit 15 27186 = 49004 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_27186 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 27186) = 3 ^ 10 * m + 49004 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_27186.1, data_15_27186.2]

/-- Complete interval computation for depth 15, residue 27187. -/
theorem bounds_15_27187 : exactInterval 15 27187 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_27187 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 27187) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_27187 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_27187 : oddCount 27187 15 = 10 ∧ acceleratedOrbit 15 27187 = 49004 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_27187 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 27187) = 3 ^ 10 * m + 49004 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_27187.1, data_15_27187.2]

/-- Complete interval computation for depth 15, residue 27188. -/
theorem bounds_15_27188 : exactInterval 15 27188 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_27188 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 27188) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_27188 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_27188 : oddCount 27188 15 = 6 ∧ acceleratedOrbit 15 27188 = 607 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_27188 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 27188) = 3 ^ 6 * m + 607 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_27188.1, data_15_27188.2]

/-- Complete interval computation for depth 15, residue 27189. -/
theorem bounds_15_27189 : exactInterval 15 27189 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_27189 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 27189) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_27189 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_27189 : oddCount 27189 15 = 6 ∧ acceleratedOrbit 15 27189 = 607 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_27189 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 27189) = 3 ^ 6 * m + 607 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_27189.1, data_15_27189.2]

/-- Complete interval computation for depth 15, residue 27190. -/
theorem bounds_15_27190 : exactInterval 15 27190 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_27190 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 27190) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_27190 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_27190 : oddCount 27190 15 = 11 ∧ acceleratedOrbit 15 27190 = 147008 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_27190 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 27190) = 3 ^ 11 * m + 147008 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_27190.1, data_15_27190.2]

/-- Complete interval computation for depth 15, residue 27191. -/
theorem bounds_15_27191 : exactInterval 15 27191 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_27191 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 27191) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_27191 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_27191 : oddCount 27191 15 = 11 ∧ acceleratedOrbit 15 27191 = 147008 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_27191 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 27191) = 3 ^ 11 * m + 147008 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_27191.1, data_15_27191.2]

/-- Complete interval computation for depth 15, residue 27192. -/
theorem bounds_15_27192 : exactInterval 15 27192 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_27192 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 27192) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_27192 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_27192 : oddCount 27192 15 = 8 ∧ acceleratedOrbit 15 27192 = 5447 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_27192 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 27192) = 3 ^ 8 * m + 5447 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_27192.1, data_15_27192.2]

/-- Complete interval computation for depth 15, residue 27193. -/
theorem bounds_15_27193 : exactInterval 15 27193 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_27193 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 27193) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_27193 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_27193 : oddCount 27193 15 = 9 ∧ acceleratedOrbit 15 27193 = 16337 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_27193 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 27193) = 3 ^ 9 * m + 16337 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_27193.1, data_15_27193.2]

/-- Complete interval computation for depth 15, residue 27194. -/
theorem bounds_15_27194 : exactInterval 15 27194 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_27194 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 27194) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_27194 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_27194 : oddCount 27194 15 = 8 ∧ acceleratedOrbit 15 27194 = 5447 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_27194 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 27194) = 3 ^ 8 * m + 5447 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_27194.1, data_15_27194.2]

/-- Complete interval computation for depth 15, residue 27195. -/
theorem bounds_15_27195 : exactInterval 15 27195 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_27195 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 27195) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_27195 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_27195 : oddCount 27195 15 = 8 ∧ acceleratedOrbit 15 27195 = 5447 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_27195 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 27195) = 3 ^ 8 * m + 5447 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_27195.1, data_15_27195.2]

/-- Complete interval computation for depth 15, residue 27196. -/
theorem bounds_15_27196 : exactInterval 15 27196 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_27196 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 27196) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_27196 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_27196 : oddCount 27196 15 = 8 ∧ acceleratedOrbit 15 27196 = 5447 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_27196 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 27196) = 3 ^ 8 * m + 5447 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_27196.1, data_15_27196.2]

end Collatz.Research.PassageAtlas.Batch0830
