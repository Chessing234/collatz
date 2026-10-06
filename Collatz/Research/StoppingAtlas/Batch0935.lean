import Collatz.Research.DescentIntervals.Classifier

namespace Collatz.Research.StoppingAtlas.Batch0935

open Collatz.Research.DescentIntervals

set_option maxRecDepth 20000
set_option maxHeartbeats 0

/-- Complete interval computation for depth 13, residue 7178. -/
theorem bounds_13_7178 : exactInterval 13 7178 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_13_7178 (m : Nat) :
    stoppingTime (2 ^ 13 * m + 7178) 13 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_13_7178 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_13_7178 : oddCount 7178 13 = 6 ∧ acceleratedOrbit 13 7178 = 641 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_13_7178 (m : Nat) :
    acceleratedOrbit 13 (2 ^ 13 * m + 7178) = 3 ^ 6 * m + 641 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_13_7178.1, data_13_7178.2]

/-- Complete interval computation for depth 13, residue 7179. -/
theorem bounds_13_7179 : exactInterval 13 7179 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_13_7179 (m : Nat) :
    stoppingTime (2 ^ 13 * m + 7179) 13 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_13_7179 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_13_7179 : oddCount 7179 13 = 4 ∧ acceleratedOrbit 13 7179 = 71 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_13_7179 (m : Nat) :
    acceleratedOrbit 13 (2 ^ 13 * m + 7179) = 3 ^ 4 * m + 71 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_13_7179.1, data_13_7179.2]

/-- Complete interval computation for depth 13, residue 7180. -/
theorem bounds_13_7180 : exactInterval 13 7180 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_13_7180 (m : Nat) :
    stoppingTime (2 ^ 13 * m + 7180) 13 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_13_7180 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_13_7180 : oddCount 7180 13 = 6 ∧ acceleratedOrbit 13 7180 = 641 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_13_7180 (m : Nat) :
    acceleratedOrbit 13 (2 ^ 13 * m + 7180) = 3 ^ 6 * m + 641 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_13_7180.1, data_13_7180.2]

/-- Complete interval computation for depth 13, residue 7181. -/
theorem bounds_13_7181 : exactInterval 13 7181 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_13_7181 (m : Nat) :
    stoppingTime (2 ^ 13 * m + 7181) 13 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_13_7181 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_13_7181 : oddCount 7181 13 = 6 ∧ acceleratedOrbit 13 7181 = 641 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_13_7181 (m : Nat) :
    acceleratedOrbit 13 (2 ^ 13 * m + 7181) = 3 ^ 6 * m + 641 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_13_7181.1, data_13_7181.2]

/-- Complete interval computation for depth 13, residue 7182. -/
theorem bounds_13_7182 : exactInterval 13 7182 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_13_7182 (m : Nat) :
    stoppingTime (2 ^ 13 * m + 7182) 13 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_13_7182 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_13_7182 : oddCount 7182 13 = 7 ∧ acceleratedOrbit 13 7182 = 1919 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_13_7182 (m : Nat) :
    acceleratedOrbit 13 (2 ^ 13 * m + 7182) = 3 ^ 7 * m + 1919 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_13_7182.1, data_13_7182.2]

/-- Complete interval computation for depth 13, residue 7183. -/
theorem bounds_13_7183 : exactInterval 13 7183 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_13_7183 (m : Nat) :
    stoppingTime (2 ^ 13 * m + 7183) 13 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_13_7183 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_13_7183 : oddCount 7183 13 = 7 ∧ acceleratedOrbit 13 7183 = 1919 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_13_7183 (m : Nat) :
    acceleratedOrbit 13 (2 ^ 13 * m + 7183) = 3 ^ 7 * m + 1919 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_13_7183.1, data_13_7183.2]

/-- Complete interval computation for depth 13, residue 7184. -/
theorem bounds_13_7184 : exactInterval 13 7184 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_13_7184 (m : Nat) :
    stoppingTime (2 ^ 13 * m + 7184) 13 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_13_7184 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_13_7184 : oddCount 7184 13 = 5 ∧ acceleratedOrbit 13 7184 = 215 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_13_7184 (m : Nat) :
    acceleratedOrbit 13 (2 ^ 13 * m + 7184) = 3 ^ 5 * m + 215 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_13_7184.1, data_13_7184.2]

/-- Complete interval computation for depth 13, residue 7185. -/
theorem bounds_13_7185 : exactInterval 13 7185 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_13_7185 (m : Nat) :
    stoppingTime (2 ^ 13 * m + 7185) 13 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_13_7185 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_13_7185 : oddCount 7185 13 = 6 ∧ acceleratedOrbit 13 7185 = 641 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_13_7185 (m : Nat) :
    acceleratedOrbit 13 (2 ^ 13 * m + 7185) = 3 ^ 6 * m + 641 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_13_7185.1, data_13_7185.2]

/-- Complete interval computation for depth 13, residue 7186. -/
theorem bounds_13_7186 : exactInterval 13 7186 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_13_7186 (m : Nat) :
    stoppingTime (2 ^ 13 * m + 7186) 13 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_13_7186 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_13_7186 : oddCount 7186 13 = 6 ∧ acceleratedOrbit 13 7186 = 640 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_13_7186 (m : Nat) :
    acceleratedOrbit 13 (2 ^ 13 * m + 7186) = 3 ^ 6 * m + 640 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_13_7186.1, data_13_7186.2]

/-- Complete interval computation for depth 13, residue 7187. -/
theorem bounds_13_7187 : exactInterval 13 7187 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_13_7187 (m : Nat) :
    stoppingTime (2 ^ 13 * m + 7187) 13 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_13_7187 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_13_7187 : oddCount 7187 13 = 6 ∧ acceleratedOrbit 13 7187 = 640 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_13_7187 (m : Nat) :
    acceleratedOrbit 13 (2 ^ 13 * m + 7187) = 3 ^ 6 * m + 640 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_13_7187.1, data_13_7187.2]

/-- Complete interval computation for depth 13, residue 7188. -/
theorem bounds_13_7188 : exactInterval 13 7188 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_13_7188 (m : Nat) :
    stoppingTime (2 ^ 13 * m + 7188) 13 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_13_7188 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_13_7188 : oddCount 7188 13 = 5 ∧ acceleratedOrbit 13 7188 = 215 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_13_7188 (m : Nat) :
    acceleratedOrbit 13 (2 ^ 13 * m + 7188) = 3 ^ 5 * m + 215 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_13_7188.1, data_13_7188.2]

/-- Complete interval computation for depth 13, residue 7189. -/
theorem bounds_13_7189 : exactInterval 13 7189 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_13_7189 (m : Nat) :
    stoppingTime (2 ^ 13 * m + 7189) 13 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_13_7189 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_13_7189 : oddCount 7189 13 = 5 ∧ acceleratedOrbit 13 7189 = 215 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_13_7189 (m : Nat) :
    acceleratedOrbit 13 (2 ^ 13 * m + 7189) = 3 ^ 5 * m + 215 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_13_7189.1, data_13_7189.2]

/-- Complete interval computation for depth 13, residue 7190. -/
theorem bounds_13_7190 : exactInterval 13 7190 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_13_7190 (m : Nat) :
    stoppingTime (2 ^ 13 * m + 7190) 13 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_13_7190 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_13_7190 : oddCount 7190 13 = 6 ∧ acceleratedOrbit 13 7190 = 641 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_13_7190 (m : Nat) :
    acceleratedOrbit 13 (2 ^ 13 * m + 7190) = 3 ^ 6 * m + 641 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_13_7190.1, data_13_7190.2]

/-- Complete interval computation for depth 13, residue 7191. -/
theorem bounds_13_7191 : exactInterval 13 7191 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_13_7191 (m : Nat) :
    stoppingTime (2 ^ 13 * m + 7191) 13 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_13_7191 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_13_7191 : oddCount 7191 13 = 6 ∧ acceleratedOrbit 13 7191 = 641 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_13_7191 (m : Nat) :
    acceleratedOrbit 13 (2 ^ 13 * m + 7191) = 3 ^ 6 * m + 641 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_13_7191.1, data_13_7191.2]

/-- Complete interval computation for depth 13, residue 7192. -/
theorem bounds_13_7192 : exactInterval 13 7192 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_13_7192 (m : Nat) :
    stoppingTime (2 ^ 13 * m + 7192) 13 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_13_7192 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_13_7192 : oddCount 7192 13 = 5 ∧ acceleratedOrbit 13 7192 = 215 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_13_7192 (m : Nat) :
    acceleratedOrbit 13 (2 ^ 13 * m + 7192) = 3 ^ 5 * m + 215 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_13_7192.1, data_13_7192.2]

end Collatz.Research.StoppingAtlas.Batch0935
