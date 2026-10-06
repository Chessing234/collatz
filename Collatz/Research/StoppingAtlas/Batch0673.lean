import Collatz.Research.DescentIntervals.Classifier

namespace Collatz.Research.StoppingAtlas.Batch0673

open Collatz.Research.DescentIntervals

set_option maxRecDepth 20000
set_option maxHeartbeats 0

/-- Complete interval computation for depth 13, residue 3153. -/
theorem bounds_13_3153 : exactInterval 13 3153 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_13_3153 (m : Nat) :
    stoppingTime (2 ^ 13 * m + 3153) 13 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_13_3153 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_13_3153 : oddCount 3153 13 = 6 ∧ acceleratedOrbit 13 3153 = 281 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_13_3153 (m : Nat) :
    acceleratedOrbit 13 (2 ^ 13 * m + 3153) = 3 ^ 6 * m + 281 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_13_3153.1, data_13_3153.2]

/-- Complete interval computation for depth 13, residue 3154. -/
theorem bounds_13_3154 : exactInterval 13 3154 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_13_3154 (m : Nat) :
    stoppingTime (2 ^ 13 * m + 3154) 13 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_13_3154 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_13_3154 : oddCount 3154 13 = 10 ∧ acceleratedOrbit 13 3154 = 22760 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_13_3154 (m : Nat) :
    acceleratedOrbit 13 (2 ^ 13 * m + 3154) = 3 ^ 10 * m + 22760 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_13_3154.1, data_13_3154.2]

/-- Complete interval computation for depth 13, residue 3155. -/
theorem bounds_13_3155 : exactInterval 13 3155 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_13_3155 (m : Nat) :
    stoppingTime (2 ^ 13 * m + 3155) 13 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_13_3155 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_13_3155 : oddCount 3155 13 = 10 ∧ acceleratedOrbit 13 3155 = 22760 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_13_3155 (m : Nat) :
    acceleratedOrbit 13 (2 ^ 13 * m + 3155) = 3 ^ 10 * m + 22760 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_13_3155.1, data_13_3155.2]

/-- Complete interval computation for depth 13, residue 3156. -/
theorem bounds_13_3156 : exactInterval 13 3156 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_13_3156 (m : Nat) :
    stoppingTime (2 ^ 13 * m + 3156) 13 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_13_3156 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_13_3156 : oddCount 3156 13 = 3 ∧ acceleratedOrbit 13 3156 = 11 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_13_3156 (m : Nat) :
    acceleratedOrbit 13 (2 ^ 13 * m + 3156) = 3 ^ 3 * m + 11 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_13_3156.1, data_13_3156.2]

/-- Complete interval computation for depth 13, residue 3157. -/
theorem bounds_13_3157 : exactInterval 13 3157 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_13_3157 (m : Nat) :
    stoppingTime (2 ^ 13 * m + 3157) 13 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_13_3157 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_13_3157 : oddCount 3157 13 = 3 ∧ acceleratedOrbit 13 3157 = 11 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_13_3157 (m : Nat) :
    acceleratedOrbit 13 (2 ^ 13 * m + 3157) = 3 ^ 3 * m + 11 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_13_3157.1, data_13_3157.2]

/-- Complete interval computation for depth 13, residue 3158. -/
theorem bounds_13_3158 : exactInterval 13 3158 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_13_3158 (m : Nat) :
    stoppingTime (2 ^ 13 * m + 3158) 13 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_13_3158 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_13_3158 : oddCount 3158 13 = 5 ∧ acceleratedOrbit 13 3158 = 94 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_13_3158 (m : Nat) :
    acceleratedOrbit 13 (2 ^ 13 * m + 3158) = 3 ^ 5 * m + 94 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_13_3158.1, data_13_3158.2]

/-- Complete interval computation for depth 13, residue 3159. -/
theorem bounds_13_3159 : exactInterval 13 3159 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_13_3159 (m : Nat) :
    stoppingTime (2 ^ 13 * m + 3159) 13 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_13_3159 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_13_3159 : oddCount 3159 13 = 5 ∧ acceleratedOrbit 13 3159 = 94 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_13_3159 (m : Nat) :
    acceleratedOrbit 13 (2 ^ 13 * m + 3159) = 3 ^ 5 * m + 94 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_13_3159.1, data_13_3159.2]

/-- Complete interval computation for depth 13, residue 3160. -/
theorem bounds_13_3160 : exactInterval 13 3160 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_13_3160 (m : Nat) :
    stoppingTime (2 ^ 13 * m + 3160) 13 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_13_3160 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_13_3160 : oddCount 3160 13 = 6 ∧ acceleratedOrbit 13 3160 = 283 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_13_3160 (m : Nat) :
    acceleratedOrbit 13 (2 ^ 13 * m + 3160) = 3 ^ 6 * m + 283 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_13_3160.1, data_13_3160.2]

/-- Complete interval computation for depth 13, residue 3161. -/
theorem bounds_13_3161 : exactInterval 13 3161 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_13_3161 (m : Nat) :
    stoppingTime (2 ^ 13 * m + 3161) 13 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_13_3161 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_13_3161 : oddCount 3161 13 = 8 ∧ acceleratedOrbit 13 3161 = 2537 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_13_3161 (m : Nat) :
    acceleratedOrbit 13 (2 ^ 13 * m + 3161) = 3 ^ 8 * m + 2537 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_13_3161.1, data_13_3161.2]

/-- Complete interval computation for depth 13, residue 3162. -/
theorem bounds_13_3162 : exactInterval 13 3162 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_13_3162 (m : Nat) :
    stoppingTime (2 ^ 13 * m + 3162) 13 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_13_3162 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_13_3162 : oddCount 3162 13 = 6 ∧ acceleratedOrbit 13 3162 = 283 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_13_3162 (m : Nat) :
    acceleratedOrbit 13 (2 ^ 13 * m + 3162) = 3 ^ 6 * m + 283 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_13_3162.1, data_13_3162.2]

/-- Complete interval computation for depth 13, residue 3163. -/
theorem bounds_13_3163 : exactInterval 13 3163 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_13_3163 (m : Nat) :
    stoppingTime (2 ^ 13 * m + 3163) 13 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_13_3163 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_13_3163 : oddCount 3163 13 = 9 ∧ acceleratedOrbit 13 3163 = 7604 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_13_3163 (m : Nat) :
    acceleratedOrbit 13 (2 ^ 13 * m + 3163) = 3 ^ 9 * m + 7604 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_13_3163.1, data_13_3163.2]

/-- Complete interval computation for depth 13, residue 3164. -/
theorem bounds_13_3164 : exactInterval 13 3164 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_13_3164 (m : Nat) :
    stoppingTime (2 ^ 13 * m + 3164) 13 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_13_3164 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_13_3164 : oddCount 3164 13 = 6 ∧ acceleratedOrbit 13 3164 = 283 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_13_3164 (m : Nat) :
    acceleratedOrbit 13 (2 ^ 13 * m + 3164) = 3 ^ 6 * m + 283 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_13_3164.1, data_13_3164.2]

/-- Complete interval computation for depth 13, residue 3165. -/
theorem bounds_13_3165 : exactInterval 13 3165 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_13_3165 (m : Nat) :
    stoppingTime (2 ^ 13 * m + 3165) 13 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_13_3165 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_13_3165 : oddCount 3165 13 = 6 ∧ acceleratedOrbit 13 3165 = 283 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_13_3165 (m : Nat) :
    acceleratedOrbit 13 (2 ^ 13 * m + 3165) = 3 ^ 6 * m + 283 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_13_3165.1, data_13_3165.2]

/-- Complete interval computation for depth 13, residue 3166. -/
theorem bounds_13_3166 : exactInterval 13 3166 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_13_3166 (m : Nat) :
    stoppingTime (2 ^ 13 * m + 3166) 13 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_13_3166 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_13_3166 : oddCount 3166 13 = 10 ∧ acceleratedOrbit 13 3166 = 22841 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_13_3166 (m : Nat) :
    acceleratedOrbit 13 (2 ^ 13 * m + 3166) = 3 ^ 10 * m + 22841 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_13_3166.1, data_13_3166.2]

/-- Complete interval computation for depth 13, residue 3167. -/
theorem bounds_13_3167 : exactInterval 13 3167 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_13_3167 (m : Nat) :
    stoppingTime (2 ^ 13 * m + 3167) 13 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_13_3167 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_13_3167 : oddCount 3167 13 = 10 ∧ acceleratedOrbit 13 3167 = 22841 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_13_3167 (m : Nat) :
    acceleratedOrbit 13 (2 ^ 13 * m + 3167) = 3 ^ 10 * m + 22841 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_13_3167.1, data_13_3167.2]

/-- Complete interval computation for depth 13, residue 3168. -/
theorem bounds_13_3168 : exactInterval 13 3168 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_13_3168 (m : Nat) :
    stoppingTime (2 ^ 13 * m + 3168) 13 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_13_3168 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_13_3168 : oddCount 3168 13 = 3 ∧ acceleratedOrbit 13 3168 = 11 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_13_3168 (m : Nat) :
    acceleratedOrbit 13 (2 ^ 13 * m + 3168) = 3 ^ 3 * m + 11 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_13_3168.1, data_13_3168.2]

end Collatz.Research.StoppingAtlas.Batch0673
