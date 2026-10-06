import Collatz.Research.DescentIntervals.Classifier

namespace Collatz.Research.StoppingAtlas.Batch0406

open Collatz.Research.DescentIntervals

set_option maxRecDepth 20000
set_option maxHeartbeats 0

/-- Complete interval computation for depth 12, residue 3148. -/
theorem bounds_12_3148 : exactInterval 12 3148 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_12_3148 (m : Nat) :
    stoppingTime (2 ^ 12 * m + 3148) 12 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_12_3148 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_12_3148 : oddCount 3148 12 = 6 ∧ acceleratedOrbit 12 3148 = 562 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_12_3148 (m : Nat) :
    acceleratedOrbit 12 (2 ^ 12 * m + 3148) = 3 ^ 6 * m + 562 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_12_3148.1, data_12_3148.2]

/-- Complete interval computation for depth 12, residue 3149. -/
theorem bounds_12_3149 : exactInterval 12 3149 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_12_3149 (m : Nat) :
    stoppingTime (2 ^ 12 * m + 3149) 12 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_12_3149 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_12_3149 : oddCount 3149 12 = 6 ∧ acceleratedOrbit 12 3149 = 562 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_12_3149 (m : Nat) :
    acceleratedOrbit 12 (2 ^ 12 * m + 3149) = 3 ^ 6 * m + 562 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_12_3149.1, data_12_3149.2]

/-- Complete interval computation for depth 12, residue 3150. -/
theorem bounds_12_3150 : exactInterval 12 3150 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_12_3150 (m : Nat) :
    stoppingTime (2 ^ 12 * m + 3150) 12 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_12_3150 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_12_3150 : oddCount 3150 12 = 5 ∧ acceleratedOrbit 12 3150 = 187 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_12_3150 (m : Nat) :
    acceleratedOrbit 12 (2 ^ 12 * m + 3150) = 3 ^ 5 * m + 187 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_12_3150.1, data_12_3150.2]

/-- Complete interval computation for depth 12, residue 3151. -/
theorem bounds_12_3151 : exactInterval 12 3151 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_12_3151 (m : Nat) :
    stoppingTime (2 ^ 12 * m + 3151) 12 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_12_3151 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_12_3151 : oddCount 3151 12 = 5 ∧ acceleratedOrbit 12 3151 = 187 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_12_3151 (m : Nat) :
    acceleratedOrbit 12 (2 ^ 12 * m + 3151) = 3 ^ 5 * m + 187 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_12_3151.1, data_12_3151.2]

/-- Complete interval computation for depth 12, residue 3152. -/
theorem bounds_12_3152 : exactInterval 12 3152 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_12_3152 (m : Nat) :
    stoppingTime (2 ^ 12 * m + 3152) 12 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_12_3152 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_12_3152 : oddCount 3152 12 = 2 ∧ acceleratedOrbit 12 3152 = 7 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_12_3152 (m : Nat) :
    acceleratedOrbit 12 (2 ^ 12 * m + 3152) = 3 ^ 2 * m + 7 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_12_3152.1, data_12_3152.2]

/-- Complete interval computation for depth 12, residue 3153. -/
theorem bounds_12_3153 : exactInterval 12 3153 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_12_3153 (m : Nat) :
    stoppingTime (2 ^ 12 * m + 3153) 12 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_12_3153 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_12_3153 : oddCount 3153 12 = 6 ∧ acceleratedOrbit 12 3153 = 562 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_12_3153 (m : Nat) :
    acceleratedOrbit 12 (2 ^ 12 * m + 3153) = 3 ^ 6 * m + 562 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_12_3153.1, data_12_3153.2]

/-- Complete interval computation for depth 12, residue 3154. -/
theorem bounds_12_3154 : exactInterval 12 3154 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_12_3154 (m : Nat) :
    stoppingTime (2 ^ 12 * m + 3154) 12 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_12_3154 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_12_3154 : oddCount 3154 12 = 9 ∧ acceleratedOrbit 12 3154 = 15173 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_12_3154 (m : Nat) :
    acceleratedOrbit 12 (2 ^ 12 * m + 3154) = 3 ^ 9 * m + 15173 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_12_3154.1, data_12_3154.2]

/-- Complete interval computation for depth 12, residue 3155. -/
theorem bounds_12_3155 : exactInterval 12 3155 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_12_3155 (m : Nat) :
    stoppingTime (2 ^ 12 * m + 3155) 12 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_12_3155 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_12_3155 : oddCount 3155 12 = 9 ∧ acceleratedOrbit 12 3155 = 15173 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_12_3155 (m : Nat) :
    acceleratedOrbit 12 (2 ^ 12 * m + 3155) = 3 ^ 9 * m + 15173 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_12_3155.1, data_12_3155.2]

/-- Complete interval computation for depth 12, residue 3156. -/
theorem bounds_12_3156 : exactInterval 12 3156 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_12_3156 (m : Nat) :
    stoppingTime (2 ^ 12 * m + 3156) 12 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_12_3156 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_12_3156 : oddCount 3156 12 = 2 ∧ acceleratedOrbit 12 3156 = 7 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_12_3156 (m : Nat) :
    acceleratedOrbit 12 (2 ^ 12 * m + 3156) = 3 ^ 2 * m + 7 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_12_3156.1, data_12_3156.2]

/-- Complete interval computation for depth 12, residue 3157. -/
theorem bounds_12_3157 : exactInterval 12 3157 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_12_3157 (m : Nat) :
    stoppingTime (2 ^ 12 * m + 3157) 12 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_12_3157 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_12_3157 : oddCount 3157 12 = 2 ∧ acceleratedOrbit 12 3157 = 7 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_12_3157 (m : Nat) :
    acceleratedOrbit 12 (2 ^ 12 * m + 3157) = 3 ^ 2 * m + 7 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_12_3157.1, data_12_3157.2]

/-- Complete interval computation for depth 12, residue 3158. -/
theorem bounds_12_3158 : exactInterval 12 3158 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_12_3158 (m : Nat) :
    stoppingTime (2 ^ 12 * m + 3158) 12 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_12_3158 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_12_3158 : oddCount 3158 12 = 5 ∧ acceleratedOrbit 12 3158 = 188 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_12_3158 (m : Nat) :
    acceleratedOrbit 12 (2 ^ 12 * m + 3158) = 3 ^ 5 * m + 188 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_12_3158.1, data_12_3158.2]

/-- Complete interval computation for depth 12, residue 3159. -/
theorem bounds_12_3159 : exactInterval 12 3159 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_12_3159 (m : Nat) :
    stoppingTime (2 ^ 12 * m + 3159) 12 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_12_3159 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_12_3159 : oddCount 3159 12 = 5 ∧ acceleratedOrbit 12 3159 = 188 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_12_3159 (m : Nat) :
    acceleratedOrbit 12 (2 ^ 12 * m + 3159) = 3 ^ 5 * m + 188 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_12_3159.1, data_12_3159.2]

/-- Complete interval computation for depth 12, residue 3160. -/
theorem bounds_12_3160 : exactInterval 12 3160 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_12_3160 (m : Nat) :
    stoppingTime (2 ^ 12 * m + 3160) 12 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_12_3160 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_12_3160 : oddCount 3160 12 = 6 ∧ acceleratedOrbit 12 3160 = 566 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_12_3160 (m : Nat) :
    acceleratedOrbit 12 (2 ^ 12 * m + 3160) = 3 ^ 6 * m + 566 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_12_3160.1, data_12_3160.2]

/-- Complete interval computation for depth 12, residue 3161. -/
theorem bounds_12_3161 : exactInterval 12 3161 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_12_3161 (m : Nat) :
    stoppingTime (2 ^ 12 * m + 3161) 12 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_12_3161 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_12_3161 : oddCount 3161 12 = 7 ∧ acceleratedOrbit 12 3161 = 1691 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_12_3161 (m : Nat) :
    acceleratedOrbit 12 (2 ^ 12 * m + 3161) = 3 ^ 7 * m + 1691 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_12_3161.1, data_12_3161.2]

/-- Complete interval computation for depth 12, residue 3162. -/
theorem bounds_12_3162 : exactInterval 12 3162 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_12_3162 (m : Nat) :
    stoppingTime (2 ^ 12 * m + 3162) 12 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_12_3162 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_12_3162 : oddCount 3162 12 = 6 ∧ acceleratedOrbit 12 3162 = 566 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_12_3162 (m : Nat) :
    acceleratedOrbit 12 (2 ^ 12 * m + 3162) = 3 ^ 6 * m + 566 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_12_3162.1, data_12_3162.2]

/-- Complete interval computation for depth 12, residue 3163. -/
theorem bounds_12_3163 : exactInterval 12 3163 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_12_3163 (m : Nat) :
    stoppingTime (2 ^ 12 * m + 3163) 12 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_12_3163 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_12_3163 : oddCount 3163 12 = 8 ∧ acceleratedOrbit 12 3163 = 5069 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_12_3163 (m : Nat) :
    acceleratedOrbit 12 (2 ^ 12 * m + 3163) = 3 ^ 8 * m + 5069 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_12_3163.1, data_12_3163.2]

end Collatz.Research.StoppingAtlas.Batch0406
