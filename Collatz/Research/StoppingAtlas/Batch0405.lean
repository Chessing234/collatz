import Collatz.Research.DescentIntervals.Classifier

namespace Collatz.Research.StoppingAtlas.Batch0405

open Collatz.Research.DescentIntervals

set_option maxRecDepth 20000
set_option maxHeartbeats 0

/-- Complete interval computation for depth 12, residue 3133. -/
theorem bounds_12_3133 : exactInterval 12 3133 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_12_3133 (m : Nat) :
    stoppingTime (2 ^ 12 * m + 3133) 12 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_12_3133 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_12_3133 : oddCount 3133 12 = 4 ∧ acceleratedOrbit 12 3133 = 62 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_12_3133 (m : Nat) :
    acceleratedOrbit 12 (2 ^ 12 * m + 3133) = 3 ^ 4 * m + 62 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_12_3133.1, data_12_3133.2]

/-- Complete interval computation for depth 12, residue 3134. -/
theorem bounds_12_3134 : exactInterval 12 3134 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_12_3134 (m : Nat) :
    stoppingTime (2 ^ 12 * m + 3134) 12 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_12_3134 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_12_3134 : oddCount 3134 12 = 8 ∧ acceleratedOrbit 12 3134 = 5024 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_12_3134 (m : Nat) :
    acceleratedOrbit 12 (2 ^ 12 * m + 3134) = 3 ^ 8 * m + 5024 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_12_3134.1, data_12_3134.2]

/-- Complete interval computation for depth 12, residue 3135. -/
theorem bounds_12_3135 : exactInterval 12 3135 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_12_3135 (m : Nat) :
    stoppingTime (2 ^ 12 * m + 3135) 12 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_12_3135 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_12_3135 : oddCount 3135 12 = 8 ∧ acceleratedOrbit 12 3135 = 5024 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_12_3135 (m : Nat) :
    acceleratedOrbit 12 (2 ^ 12 * m + 3135) = 3 ^ 8 * m + 5024 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_12_3135.1, data_12_3135.2]

/-- Complete interval computation for depth 12, residue 3136. -/
theorem bounds_12_3136 : exactInterval 12 3136 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_12_3136 (m : Nat) :
    stoppingTime (2 ^ 12 * m + 3136) 12 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_12_3136 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_12_3136 : oddCount 3136 12 = 2 ∧ acceleratedOrbit 12 3136 = 7 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_12_3136 (m : Nat) :
    acceleratedOrbit 12 (2 ^ 12 * m + 3136) = 3 ^ 2 * m + 7 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_12_3136.1, data_12_3136.2]

/-- Complete interval computation for depth 12, residue 3137. -/
theorem bounds_12_3137 : exactInterval 12 3137 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_12_3137 (m : Nat) :
    stoppingTime (2 ^ 12 * m + 3137) 12 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_12_3137 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_12_3137 : oddCount 3137 12 = 6 ∧ acceleratedOrbit 12 3137 = 560 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_12_3137 (m : Nat) :
    acceleratedOrbit 12 (2 ^ 12 * m + 3137) = 3 ^ 6 * m + 560 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_12_3137.1, data_12_3137.2]

/-- Complete interval computation for depth 12, residue 3138. -/
theorem bounds_12_3138 : exactInterval 12 3138 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_12_3138 (m : Nat) :
    stoppingTime (2 ^ 12 * m + 3138) 12 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_12_3138 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_12_3138 : oddCount 3138 12 = 6 ∧ acceleratedOrbit 12 3138 = 560 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_12_3138 (m : Nat) :
    acceleratedOrbit 12 (2 ^ 12 * m + 3138) = 3 ^ 6 * m + 560 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_12_3138.1, data_12_3138.2]

/-- Complete interval computation for depth 12, residue 3139. -/
theorem bounds_12_3139 : exactInterval 12 3139 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_12_3139 (m : Nat) :
    stoppingTime (2 ^ 12 * m + 3139) 12 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_12_3139 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_12_3139 : oddCount 3139 12 = 6 ∧ acceleratedOrbit 12 3139 = 560 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_12_3139 (m : Nat) :
    acceleratedOrbit 12 (2 ^ 12 * m + 3139) = 3 ^ 6 * m + 560 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_12_3139.1, data_12_3139.2]

/-- Complete interval computation for depth 12, residue 3140. -/
theorem bounds_12_3140 : exactInterval 12 3140 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_12_3140 (m : Nat) :
    stoppingTime (2 ^ 12 * m + 3140) 12 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_12_3140 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_12_3140 : oddCount 3140 12 = 5 ∧ acceleratedOrbit 12 3140 = 188 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_12_3140 (m : Nat) :
    acceleratedOrbit 12 (2 ^ 12 * m + 3140) = 3 ^ 5 * m + 188 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_12_3140.1, data_12_3140.2]

/-- Complete interval computation for depth 12, residue 3141. -/
theorem bounds_12_3141 : exactInterval 12 3141 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_12_3141 (m : Nat) :
    stoppingTime (2 ^ 12 * m + 3141) 12 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_12_3141 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_12_3141 : oddCount 3141 12 = 5 ∧ acceleratedOrbit 12 3141 = 188 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_12_3141 (m : Nat) :
    acceleratedOrbit 12 (2 ^ 12 * m + 3141) = 3 ^ 5 * m + 188 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_12_3141.1, data_12_3141.2]

/-- Complete interval computation for depth 12, residue 3142. -/
theorem bounds_12_3142 : exactInterval 12 3142 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_12_3142 (m : Nat) :
    stoppingTime (2 ^ 12 * m + 3142) 12 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_12_3142 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_12_3142 : oddCount 3142 12 = 5 ∧ acceleratedOrbit 12 3142 = 188 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_12_3142 (m : Nat) :
    acceleratedOrbit 12 (2 ^ 12 * m + 3142) = 3 ^ 5 * m + 188 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_12_3142.1, data_12_3142.2]

/-- Complete interval computation for depth 12, residue 3143. -/
theorem bounds_12_3143 : exactInterval 12 3143 = ⟨0, none⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_12_3143 (m : Nat) :
    stoppingTime (2 ^ 12 * m + 3143) 12 ↔ 0 ≤ m := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_12_3143 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_12_3143 : oddCount 3143 12 = 7 ∧ acceleratedOrbit 12 3143 = 1679 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_12_3143 (m : Nat) :
    acceleratedOrbit 12 (2 ^ 12 * m + 3143) = 3 ^ 7 * m + 1679 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_12_3143.1, data_12_3143.2]

/-- Complete interval computation for depth 12, residue 3144. -/
theorem bounds_12_3144 : exactInterval 12 3144 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_12_3144 (m : Nat) :
    stoppingTime (2 ^ 12 * m + 3144) 12 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_12_3144 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_12_3144 : oddCount 3144 12 = 6 ∧ acceleratedOrbit 12 3144 = 562 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_12_3144 (m : Nat) :
    acceleratedOrbit 12 (2 ^ 12 * m + 3144) = 3 ^ 6 * m + 562 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_12_3144.1, data_12_3144.2]

/-- Complete interval computation for depth 12, residue 3145. -/
theorem bounds_12_3145 : exactInterval 12 3145 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_12_3145 (m : Nat) :
    stoppingTime (2 ^ 12 * m + 3145) 12 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_12_3145 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_12_3145 : oddCount 3145 12 = 8 ∧ acceleratedOrbit 12 3145 = 5042 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_12_3145 (m : Nat) :
    acceleratedOrbit 12 (2 ^ 12 * m + 3145) = 3 ^ 8 * m + 5042 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_12_3145.1, data_12_3145.2]

/-- Complete interval computation for depth 12, residue 3146. -/
theorem bounds_12_3146 : exactInterval 12 3146 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_12_3146 (m : Nat) :
    stoppingTime (2 ^ 12 * m + 3146) 12 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_12_3146 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_12_3146 : oddCount 3146 12 = 6 ∧ acceleratedOrbit 12 3146 = 562 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_12_3146 (m : Nat) :
    acceleratedOrbit 12 (2 ^ 12 * m + 3146) = 3 ^ 6 * m + 562 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_12_3146.1, data_12_3146.2]

/-- Complete interval computation for depth 12, residue 3147. -/
theorem bounds_12_3147 : exactInterval 12 3147 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_12_3147 (m : Nat) :
    stoppingTime (2 ^ 12 * m + 3147) 12 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_12_3147 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_12_3147 : oddCount 3147 12 = 5 ∧ acceleratedOrbit 12 3147 = 188 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_12_3147 (m : Nat) :
    acceleratedOrbit 12 (2 ^ 12 * m + 3147) = 3 ^ 5 * m + 188 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_12_3147.1, data_12_3147.2]

end Collatz.Research.StoppingAtlas.Batch0405
