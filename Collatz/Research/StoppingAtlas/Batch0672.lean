import Collatz.Research.DescentIntervals.Classifier

namespace Collatz.Research.StoppingAtlas.Batch0672

open Collatz.Research.DescentIntervals

set_option maxRecDepth 20000
set_option maxHeartbeats 0

/-- Complete interval computation for depth 13, residue 3138. -/
theorem bounds_13_3138 : exactInterval 13 3138 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_13_3138 (m : Nat) :
    stoppingTime (2 ^ 13 * m + 3138) 13 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_13_3138 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_13_3138 : oddCount 3138 13 = 6 ∧ acceleratedOrbit 13 3138 = 280 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_13_3138 (m : Nat) :
    acceleratedOrbit 13 (2 ^ 13 * m + 3138) = 3 ^ 6 * m + 280 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_13_3138.1, data_13_3138.2]

/-- Complete interval computation for depth 13, residue 3139. -/
theorem bounds_13_3139 : exactInterval 13 3139 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_13_3139 (m : Nat) :
    stoppingTime (2 ^ 13 * m + 3139) 13 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_13_3139 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_13_3139 : oddCount 3139 13 = 6 ∧ acceleratedOrbit 13 3139 = 280 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_13_3139 (m : Nat) :
    acceleratedOrbit 13 (2 ^ 13 * m + 3139) = 3 ^ 6 * m + 280 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_13_3139.1, data_13_3139.2]

/-- Complete interval computation for depth 13, residue 3140. -/
theorem bounds_13_3140 : exactInterval 13 3140 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_13_3140 (m : Nat) :
    stoppingTime (2 ^ 13 * m + 3140) 13 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_13_3140 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_13_3140 : oddCount 3140 13 = 5 ∧ acceleratedOrbit 13 3140 = 94 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_13_3140 (m : Nat) :
    acceleratedOrbit 13 (2 ^ 13 * m + 3140) = 3 ^ 5 * m + 94 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_13_3140.1, data_13_3140.2]

/-- Complete interval computation for depth 13, residue 3141. -/
theorem bounds_13_3141 : exactInterval 13 3141 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_13_3141 (m : Nat) :
    stoppingTime (2 ^ 13 * m + 3141) 13 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_13_3141 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_13_3141 : oddCount 3141 13 = 5 ∧ acceleratedOrbit 13 3141 = 94 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_13_3141 (m : Nat) :
    acceleratedOrbit 13 (2 ^ 13 * m + 3141) = 3 ^ 5 * m + 94 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_13_3141.1, data_13_3141.2]

/-- Complete interval computation for depth 13, residue 3142. -/
theorem bounds_13_3142 : exactInterval 13 3142 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_13_3142 (m : Nat) :
    stoppingTime (2 ^ 13 * m + 3142) 13 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_13_3142 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_13_3142 : oddCount 3142 13 = 5 ∧ acceleratedOrbit 13 3142 = 94 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_13_3142 (m : Nat) :
    acceleratedOrbit 13 (2 ^ 13 * m + 3142) = 3 ^ 5 * m + 94 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_13_3142.1, data_13_3142.2]

/-- Complete interval computation for depth 13, residue 3143. -/
theorem bounds_13_3143 : exactInterval 13 3143 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_13_3143 (m : Nat) :
    stoppingTime (2 ^ 13 * m + 3143) 13 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_13_3143 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_13_3143 : oddCount 3143 13 = 8 ∧ acceleratedOrbit 13 3143 = 2519 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_13_3143 (m : Nat) :
    acceleratedOrbit 13 (2 ^ 13 * m + 3143) = 3 ^ 8 * m + 2519 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_13_3143.1, data_13_3143.2]

/-- Complete interval computation for depth 13, residue 3144. -/
theorem bounds_13_3144 : exactInterval 13 3144 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_13_3144 (m : Nat) :
    stoppingTime (2 ^ 13 * m + 3144) 13 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_13_3144 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_13_3144 : oddCount 3144 13 = 6 ∧ acceleratedOrbit 13 3144 = 281 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_13_3144 (m : Nat) :
    acceleratedOrbit 13 (2 ^ 13 * m + 3144) = 3 ^ 6 * m + 281 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_13_3144.1, data_13_3144.2]

/-- Complete interval computation for depth 13, residue 3145. -/
theorem bounds_13_3145 : exactInterval 13 3145 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_13_3145 (m : Nat) :
    stoppingTime (2 ^ 13 * m + 3145) 13 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_13_3145 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_13_3145 : oddCount 3145 13 = 8 ∧ acceleratedOrbit 13 3145 = 2521 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_13_3145 (m : Nat) :
    acceleratedOrbit 13 (2 ^ 13 * m + 3145) = 3 ^ 8 * m + 2521 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_13_3145.1, data_13_3145.2]

/-- Complete interval computation for depth 13, residue 3146. -/
theorem bounds_13_3146 : exactInterval 13 3146 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_13_3146 (m : Nat) :
    stoppingTime (2 ^ 13 * m + 3146) 13 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_13_3146 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_13_3146 : oddCount 3146 13 = 6 ∧ acceleratedOrbit 13 3146 = 281 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_13_3146 (m : Nat) :
    acceleratedOrbit 13 (2 ^ 13 * m + 3146) = 3 ^ 6 * m + 281 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_13_3146.1, data_13_3146.2]

/-- Complete interval computation for depth 13, residue 3147. -/
theorem bounds_13_3147 : exactInterval 13 3147 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_13_3147 (m : Nat) :
    stoppingTime (2 ^ 13 * m + 3147) 13 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_13_3147 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_13_3147 : oddCount 3147 13 = 5 ∧ acceleratedOrbit 13 3147 = 94 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_13_3147 (m : Nat) :
    acceleratedOrbit 13 (2 ^ 13 * m + 3147) = 3 ^ 5 * m + 94 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_13_3147.1, data_13_3147.2]

/-- Complete interval computation for depth 13, residue 3148. -/
theorem bounds_13_3148 : exactInterval 13 3148 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_13_3148 (m : Nat) :
    stoppingTime (2 ^ 13 * m + 3148) 13 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_13_3148 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_13_3148 : oddCount 3148 13 = 6 ∧ acceleratedOrbit 13 3148 = 281 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_13_3148 (m : Nat) :
    acceleratedOrbit 13 (2 ^ 13 * m + 3148) = 3 ^ 6 * m + 281 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_13_3148.1, data_13_3148.2]

/-- Complete interval computation for depth 13, residue 3149. -/
theorem bounds_13_3149 : exactInterval 13 3149 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_13_3149 (m : Nat) :
    stoppingTime (2 ^ 13 * m + 3149) 13 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_13_3149 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_13_3149 : oddCount 3149 13 = 6 ∧ acceleratedOrbit 13 3149 = 281 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_13_3149 (m : Nat) :
    acceleratedOrbit 13 (2 ^ 13 * m + 3149) = 3 ^ 6 * m + 281 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_13_3149.1, data_13_3149.2]

/-- Complete interval computation for depth 13, residue 3150. -/
theorem bounds_13_3150 : exactInterval 13 3150 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_13_3150 (m : Nat) :
    stoppingTime (2 ^ 13 * m + 3150) 13 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_13_3150 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_13_3150 : oddCount 3150 13 = 6 ∧ acceleratedOrbit 13 3150 = 281 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_13_3150 (m : Nat) :
    acceleratedOrbit 13 (2 ^ 13 * m + 3150) = 3 ^ 6 * m + 281 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_13_3150.1, data_13_3150.2]

/-- Complete interval computation for depth 13, residue 3151. -/
theorem bounds_13_3151 : exactInterval 13 3151 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_13_3151 (m : Nat) :
    stoppingTime (2 ^ 13 * m + 3151) 13 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_13_3151 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_13_3151 : oddCount 3151 13 = 6 ∧ acceleratedOrbit 13 3151 = 281 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_13_3151 (m : Nat) :
    acceleratedOrbit 13 (2 ^ 13 * m + 3151) = 3 ^ 6 * m + 281 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_13_3151.1, data_13_3151.2]

/-- Complete interval computation for depth 13, residue 3152. -/
theorem bounds_13_3152 : exactInterval 13 3152 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_13_3152 (m : Nat) :
    stoppingTime (2 ^ 13 * m + 3152) 13 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_13_3152 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_13_3152 : oddCount 3152 13 = 3 ∧ acceleratedOrbit 13 3152 = 11 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_13_3152 (m : Nat) :
    acceleratedOrbit 13 (2 ^ 13 * m + 3152) = 3 ^ 3 * m + 11 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_13_3152.1, data_13_3152.2]

end Collatz.Research.StoppingAtlas.Batch0672
