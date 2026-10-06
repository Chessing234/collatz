import Collatz.Research.DescentIntervals.Classifier

namespace Collatz.Research.StoppingAtlas.Batch1000

open Collatz.Research.DescentIntervals

set_option maxRecDepth 20000
set_option maxHeartbeats 0

/-- Complete interval computation for depth 13, residue 8176. -/
theorem bounds_13_8176 : exactInterval 13 8176 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_13_8176 (m : Nat) :
    stoppingTime (2 ^ 13 * m + 8176) 13 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_13_8176 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_13_8176 : oddCount 8176 13 = 9 ∧ acceleratedOrbit 13 8176 = 19682 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_13_8176 (m : Nat) :
    acceleratedOrbit 13 (2 ^ 13 * m + 8176) = 3 ^ 9 * m + 19682 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_13_8176.1, data_13_8176.2]

/-- Complete interval computation for depth 13, residue 8177. -/
theorem bounds_13_8177 : exactInterval 13 8177 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_13_8177 (m : Nat) :
    stoppingTime (2 ^ 13 * m + 8177) 13 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_13_8177 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_13_8177 : oddCount 8177 13 = 8 ∧ acceleratedOrbit 13 8177 = 6560 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_13_8177 (m : Nat) :
    acceleratedOrbit 13 (2 ^ 13 * m + 8177) = 3 ^ 8 * m + 6560 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_13_8177.1, data_13_8177.2]

/-- Complete interval computation for depth 13, residue 8178. -/
theorem bounds_13_8178 : exactInterval 13 8178 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_13_8178 (m : Nat) :
    stoppingTime (2 ^ 13 * m + 8178) 13 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_13_8178 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_13_8178 : oddCount 8178 13 = 8 ∧ acceleratedOrbit 13 8178 = 6554 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_13_8178 (m : Nat) :
    acceleratedOrbit 13 (2 ^ 13 * m + 8178) = 3 ^ 8 * m + 6554 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_13_8178.1, data_13_8178.2]

/-- Complete interval computation for depth 13, residue 8179. -/
theorem bounds_13_8179 : exactInterval 13 8179 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_13_8179 (m : Nat) :
    stoppingTime (2 ^ 13 * m + 8179) 13 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_13_8179 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_13_8179 : oddCount 8179 13 = 8 ∧ acceleratedOrbit 13 8179 = 6554 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_13_8179 (m : Nat) :
    acceleratedOrbit 13 (2 ^ 13 * m + 8179) = 3 ^ 8 * m + 6554 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_13_8179.1, data_13_8179.2]

/-- Complete interval computation for depth 13, residue 8180. -/
theorem bounds_13_8180 : exactInterval 13 8180 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_13_8180 (m : Nat) :
    stoppingTime (2 ^ 13 * m + 8180) 13 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_13_8180 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_13_8180 : oddCount 8180 13 = 9 ∧ acceleratedOrbit 13 8180 = 19682 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_13_8180 (m : Nat) :
    acceleratedOrbit 13 (2 ^ 13 * m + 8180) = 3 ^ 9 * m + 19682 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_13_8180.1, data_13_8180.2]

/-- Complete interval computation for depth 13, residue 8181. -/
theorem bounds_13_8181 : exactInterval 13 8181 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_13_8181 (m : Nat) :
    stoppingTime (2 ^ 13 * m + 8181) 13 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_13_8181 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_13_8181 : oddCount 8181 13 = 9 ∧ acceleratedOrbit 13 8181 = 19682 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_13_8181 (m : Nat) :
    acceleratedOrbit 13 (2 ^ 13 * m + 8181) = 3 ^ 9 * m + 19682 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_13_8181.1, data_13_8181.2]

/-- Complete interval computation for depth 13, residue 8182. -/
theorem bounds_13_8182 : exactInterval 13 8182 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_13_8182 (m : Nat) :
    stoppingTime (2 ^ 13 * m + 8182) 13 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_13_8182 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_13_8182 : oddCount 8182 13 = 8 ∧ acceleratedOrbit 13 8182 = 6556 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_13_8182 (m : Nat) :
    acceleratedOrbit 13 (2 ^ 13 * m + 8182) = 3 ^ 8 * m + 6556 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_13_8182.1, data_13_8182.2]

/-- Complete interval computation for depth 13, residue 8183. -/
theorem bounds_13_8183 : exactInterval 13 8183 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_13_8183 (m : Nat) :
    stoppingTime (2 ^ 13 * m + 8183) 13 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_13_8183 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_13_8183 : oddCount 8183 13 = 8 ∧ acceleratedOrbit 13 8183 = 6556 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_13_8183 (m : Nat) :
    acceleratedOrbit 13 (2 ^ 13 * m + 8183) = 3 ^ 8 * m + 6556 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_13_8183.1, data_13_8183.2]

/-- Complete interval computation for depth 13, residue 8184. -/
theorem bounds_13_8184 : exactInterval 13 8184 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_13_8184 (m : Nat) :
    stoppingTime (2 ^ 13 * m + 8184) 13 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_13_8184 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_13_8184 : oddCount 8184 13 = 10 ∧ acceleratedOrbit 13 8184 = 59048 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_13_8184 (m : Nat) :
    acceleratedOrbit 13 (2 ^ 13 * m + 8184) = 3 ^ 10 * m + 59048 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_13_8184.1, data_13_8184.2]

/-- Complete interval computation for depth 13, residue 8185. -/
theorem bounds_13_8185 : exactInterval 13 8185 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_13_8185 (m : Nat) :
    stoppingTime (2 ^ 13 * m + 8185) 13 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_13_8185 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_13_8185 : oddCount 8185 13 = 9 ∧ acceleratedOrbit 13 8185 = 19673 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_13_8185 (m : Nat) :
    acceleratedOrbit 13 (2 ^ 13 * m + 8185) = 3 ^ 9 * m + 19673 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_13_8185.1, data_13_8185.2]

/-- Complete interval computation for depth 13, residue 8186. -/
theorem bounds_13_8186 : exactInterval 13 8186 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_13_8186 (m : Nat) :
    stoppingTime (2 ^ 13 * m + 8186) 13 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_13_8186 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_13_8186 : oddCount 8186 13 = 10 ∧ acceleratedOrbit 13 8186 = 59048 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_13_8186 (m : Nat) :
    acceleratedOrbit 13 (2 ^ 13 * m + 8186) = 3 ^ 10 * m + 59048 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_13_8186.1, data_13_8186.2]

/-- Complete interval computation for depth 13, residue 8187. -/
theorem bounds_13_8187 : exactInterval 13 8187 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_13_8187 (m : Nat) :
    stoppingTime (2 ^ 13 * m + 8187) 13 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_13_8187 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_13_8187 : oddCount 8187 13 = 9 ∧ acceleratedOrbit 13 8187 = 19676 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_13_8187 (m : Nat) :
    acceleratedOrbit 13 (2 ^ 13 * m + 8187) = 3 ^ 9 * m + 19676 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_13_8187.1, data_13_8187.2]

/-- Complete interval computation for depth 13, residue 8188. -/
theorem bounds_13_8188 : exactInterval 13 8188 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_13_8188 (m : Nat) :
    stoppingTime (2 ^ 13 * m + 8188) 13 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_13_8188 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_13_8188 : oddCount 8188 13 = 11 ∧ acceleratedOrbit 13 8188 = 177146 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_13_8188 (m : Nat) :
    acceleratedOrbit 13 (2 ^ 13 * m + 8188) = 3 ^ 11 * m + 177146 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_13_8188.1, data_13_8188.2]

/-- Complete interval computation for depth 13, residue 8189. -/
theorem bounds_13_8189 : exactInterval 13 8189 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_13_8189 (m : Nat) :
    stoppingTime (2 ^ 13 * m + 8189) 13 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_13_8189 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_13_8189 : oddCount 8189 13 = 11 ∧ acceleratedOrbit 13 8189 = 177146 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_13_8189 (m : Nat) :
    acceleratedOrbit 13 (2 ^ 13 * m + 8189) = 3 ^ 11 * m + 177146 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_13_8189.1, data_13_8189.2]

/-- Complete interval computation for depth 13, residue 8190. -/
theorem bounds_13_8190 : exactInterval 13 8190 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_13_8190 (m : Nat) :
    stoppingTime (2 ^ 13 * m + 8190) 13 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_13_8190 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_13_8190 : oddCount 8190 13 = 12 ∧ acceleratedOrbit 13 8190 = 531440 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_13_8190 (m : Nat) :
    acceleratedOrbit 13 (2 ^ 13 * m + 8190) = 3 ^ 12 * m + 531440 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_13_8190.1, data_13_8190.2]

/-- Complete interval computation for depth 13, residue 8191. -/
theorem bounds_13_8191 : exactInterval 13 8191 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_13_8191 (m : Nat) :
    stoppingTime (2 ^ 13 * m + 8191) 13 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_13_8191 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_13_8191 : oddCount 8191 13 = 13 ∧ acceleratedOrbit 13 8191 = 1594322 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_13_8191 (m : Nat) :
    acceleratedOrbit 13 (2 ^ 13 * m + 8191) = 3 ^ 13 * m + 1594322 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_13_8191.1, data_13_8191.2]

end Collatz.Research.StoppingAtlas.Batch1000
