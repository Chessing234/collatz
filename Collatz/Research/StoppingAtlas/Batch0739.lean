import Collatz.Research.DescentIntervals.Classifier

namespace Collatz.Research.StoppingAtlas.Batch0739

open Collatz.Research.DescentIntervals

set_option maxRecDepth 20000
set_option maxHeartbeats 0

/-- Complete interval computation for depth 13, residue 4167. -/
theorem bounds_13_4167 : exactInterval 13 4167 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_13_4167 (m : Nat) :
    stoppingTime (2 ^ 13 * m + 4167) 13 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_13_4167 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_13_4167 : oddCount 4167 13 = 10 ∧ acceleratedOrbit 13 4167 = 30050 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_13_4167 (m : Nat) :
    acceleratedOrbit 13 (2 ^ 13 * m + 4167) = 3 ^ 10 * m + 30050 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_13_4167.1, data_13_4167.2]

/-- Complete interval computation for depth 13, residue 4168. -/
theorem bounds_13_4168 : exactInterval 13 4168 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_13_4168 (m : Nat) :
    stoppingTime (2 ^ 13 * m + 4168) 13 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_13_4168 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_13_4168 : oddCount 4168 13 = 5 ∧ acceleratedOrbit 13 4168 = 124 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_13_4168 (m : Nat) :
    acceleratedOrbit 13 (2 ^ 13 * m + 4168) = 3 ^ 5 * m + 124 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_13_4168.1, data_13_4168.2]

/-- Complete interval computation for depth 13, residue 4169. -/
theorem bounds_13_4169 : exactInterval 13 4169 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_13_4169 (m : Nat) :
    stoppingTime (2 ^ 13 * m + 4169) 13 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_13_4169 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_13_4169 : oddCount 4169 13 = 8 ∧ acceleratedOrbit 13 4169 = 3341 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_13_4169 (m : Nat) :
    acceleratedOrbit 13 (2 ^ 13 * m + 4169) = 3 ^ 8 * m + 3341 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_13_4169.1, data_13_4169.2]

/-- Complete interval computation for depth 13, residue 4170. -/
theorem bounds_13_4170 : exactInterval 13 4170 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_13_4170 (m : Nat) :
    stoppingTime (2 ^ 13 * m + 4170) 13 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_13_4170 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_13_4170 : oddCount 4170 13 = 5 ∧ acceleratedOrbit 13 4170 = 124 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_13_4170 (m : Nat) :
    acceleratedOrbit 13 (2 ^ 13 * m + 4170) = 3 ^ 5 * m + 124 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_13_4170.1, data_13_4170.2]

/-- Complete interval computation for depth 13, residue 4171. -/
theorem bounds_13_4171 : exactInterval 13 4171 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_13_4171 (m : Nat) :
    stoppingTime (2 ^ 13 * m + 4171) 13 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_13_4171 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_13_4171 : oddCount 4171 13 = 5 ∧ acceleratedOrbit 13 4171 = 125 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_13_4171 (m : Nat) :
    acceleratedOrbit 13 (2 ^ 13 * m + 4171) = 3 ^ 5 * m + 125 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_13_4171.1, data_13_4171.2]

/-- Complete interval computation for depth 13, residue 4172. -/
theorem bounds_13_4172 : exactInterval 13 4172 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_13_4172 (m : Nat) :
    stoppingTime (2 ^ 13 * m + 4172) 13 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_13_4172 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_13_4172 : oddCount 4172 13 = 5 ∧ acceleratedOrbit 13 4172 = 124 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_13_4172 (m : Nat) :
    acceleratedOrbit 13 (2 ^ 13 * m + 4172) = 3 ^ 5 * m + 124 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_13_4172.1, data_13_4172.2]

/-- Complete interval computation for depth 13, residue 4173. -/
theorem bounds_13_4173 : exactInterval 13 4173 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_13_4173 (m : Nat) :
    stoppingTime (2 ^ 13 * m + 4173) 13 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_13_4173 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_13_4173 : oddCount 4173 13 = 5 ∧ acceleratedOrbit 13 4173 = 124 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_13_4173 (m : Nat) :
    acceleratedOrbit 13 (2 ^ 13 * m + 4173) = 3 ^ 5 * m + 124 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_13_4173.1, data_13_4173.2]

/-- Complete interval computation for depth 13, residue 4174. -/
theorem bounds_13_4174 : exactInterval 13 4174 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_13_4174 (m : Nat) :
    stoppingTime (2 ^ 13 * m + 4174) 13 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_13_4174 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_13_4174 : oddCount 4174 13 = 8 ∧ acceleratedOrbit 13 4174 = 3347 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_13_4174 (m : Nat) :
    acceleratedOrbit 13 (2 ^ 13 * m + 4174) = 3 ^ 8 * m + 3347 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_13_4174.1, data_13_4174.2]

/-- Complete interval computation for depth 13, residue 4175. -/
theorem bounds_13_4175 : exactInterval 13 4175 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_13_4175 (m : Nat) :
    stoppingTime (2 ^ 13 * m + 4175) 13 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_13_4175 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_13_4175 : oddCount 4175 13 = 8 ∧ acceleratedOrbit 13 4175 = 3347 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_13_4175 (m : Nat) :
    acceleratedOrbit 13 (2 ^ 13 * m + 4175) = 3 ^ 8 * m + 3347 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_13_4175.1, data_13_4175.2]

/-- Complete interval computation for depth 13, residue 4176. -/
theorem bounds_13_4176 : exactInterval 13 4176 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_13_4176 (m : Nat) :
    stoppingTime (2 ^ 13 * m + 4176) 13 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_13_4176 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_13_4176 : oddCount 4176 13 = 3 ∧ acceleratedOrbit 13 4176 = 14 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_13_4176 (m : Nat) :
    acceleratedOrbit 13 (2 ^ 13 * m + 4176) = 3 ^ 3 * m + 14 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_13_4176.1, data_13_4176.2]

/-- Complete interval computation for depth 13, residue 4177. -/
theorem bounds_13_4177 : exactInterval 13 4177 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_13_4177 (m : Nat) :
    stoppingTime (2 ^ 13 * m + 4177) 13 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_13_4177 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_13_4177 : oddCount 4177 13 = 5 ∧ acceleratedOrbit 13 4177 = 124 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_13_4177 (m : Nat) :
    acceleratedOrbit 13 (2 ^ 13 * m + 4177) = 3 ^ 5 * m + 124 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_13_4177.1, data_13_4177.2]

/-- Complete interval computation for depth 13, residue 4178. -/
theorem bounds_13_4178 : exactInterval 13 4178 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_13_4178 (m : Nat) :
    stoppingTime (2 ^ 13 * m + 4178) 13 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_13_4178 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_13_4178 : oddCount 4178 13 = 8 ∧ acceleratedOrbit 13 4178 = 3349 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_13_4178 (m : Nat) :
    acceleratedOrbit 13 (2 ^ 13 * m + 4178) = 3 ^ 8 * m + 3349 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_13_4178.1, data_13_4178.2]

/-- Complete interval computation for depth 13, residue 4179. -/
theorem bounds_13_4179 : exactInterval 13 4179 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_13_4179 (m : Nat) :
    stoppingTime (2 ^ 13 * m + 4179) 13 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_13_4179 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_13_4179 : oddCount 4179 13 = 8 ∧ acceleratedOrbit 13 4179 = 3349 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_13_4179 (m : Nat) :
    acceleratedOrbit 13 (2 ^ 13 * m + 4179) = 3 ^ 8 * m + 3349 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_13_4179.1, data_13_4179.2]

/-- Complete interval computation for depth 13, residue 4180. -/
theorem bounds_13_4180 : exactInterval 13 4180 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_13_4180 (m : Nat) :
    stoppingTime (2 ^ 13 * m + 4180) 13 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_13_4180 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_13_4180 : oddCount 4180 13 = 3 ∧ acceleratedOrbit 13 4180 = 14 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_13_4180 (m : Nat) :
    acceleratedOrbit 13 (2 ^ 13 * m + 4180) = 3 ^ 3 * m + 14 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_13_4180.1, data_13_4180.2]

/-- Complete interval computation for depth 13, residue 4181. -/
theorem bounds_13_4181 : exactInterval 13 4181 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_13_4181 (m : Nat) :
    stoppingTime (2 ^ 13 * m + 4181) 13 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_13_4181 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_13_4181 : oddCount 4181 13 = 3 ∧ acceleratedOrbit 13 4181 = 14 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_13_4181 (m : Nat) :
    acceleratedOrbit 13 (2 ^ 13 * m + 4181) = 3 ^ 3 * m + 14 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_13_4181.1, data_13_4181.2]

/-- Complete interval computation for depth 13, residue 4182. -/
theorem bounds_13_4182 : exactInterval 13 4182 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_13_4182 (m : Nat) :
    stoppingTime (2 ^ 13 * m + 4182) 13 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_13_4182 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_13_4182 : oddCount 4182 13 = 6 ∧ acceleratedOrbit 13 4182 = 373 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_13_4182 (m : Nat) :
    acceleratedOrbit 13 (2 ^ 13 * m + 4182) = 3 ^ 6 * m + 373 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_13_4182.1, data_13_4182.2]

end Collatz.Research.StoppingAtlas.Batch0739
