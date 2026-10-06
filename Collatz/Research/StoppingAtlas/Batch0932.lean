import Collatz.Research.DescentIntervals.Classifier

namespace Collatz.Research.StoppingAtlas.Batch0932

open Collatz.Research.DescentIntervals

set_option maxRecDepth 20000
set_option maxHeartbeats 0

/-- Complete interval computation for depth 13, residue 7132. -/
theorem bounds_13_7132 : exactInterval 13 7132 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_13_7132 (m : Nat) :
    stoppingTime (2 ^ 13 * m + 7132) 13 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_13_7132 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_13_7132 : oddCount 7132 13 = 7 ∧ acceleratedOrbit 13 7132 = 1907 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_13_7132 (m : Nat) :
    acceleratedOrbit 13 (2 ^ 13 * m + 7132) = 3 ^ 7 * m + 1907 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_13_7132.1, data_13_7132.2]

/-- Complete interval computation for depth 13, residue 7133. -/
theorem bounds_13_7133 : exactInterval 13 7133 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_13_7133 (m : Nat) :
    stoppingTime (2 ^ 13 * m + 7133) 13 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_13_7133 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_13_7133 : oddCount 7133 13 = 7 ∧ acceleratedOrbit 13 7133 = 1907 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_13_7133 (m : Nat) :
    acceleratedOrbit 13 (2 ^ 13 * m + 7133) = 3 ^ 7 * m + 1907 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_13_7133.1, data_13_7133.2]

/-- Complete interval computation for depth 13, residue 7134. -/
theorem bounds_13_7134 : exactInterval 13 7134 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_13_7134 (m : Nat) :
    stoppingTime (2 ^ 13 * m + 7134) 13 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_13_7134 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_13_7134 : oddCount 7134 13 = 9 ∧ acceleratedOrbit 13 7134 = 17147 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_13_7134 (m : Nat) :
    acceleratedOrbit 13 (2 ^ 13 * m + 7134) = 3 ^ 9 * m + 17147 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_13_7134.1, data_13_7134.2]

/-- Complete interval computation for depth 13, residue 7135. -/
theorem bounds_13_7135 : exactInterval 13 7135 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_13_7135 (m : Nat) :
    stoppingTime (2 ^ 13 * m + 7135) 13 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_13_7135 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_13_7135 : oddCount 7135 13 = 9 ∧ acceleratedOrbit 13 7135 = 17147 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_13_7135 (m : Nat) :
    acceleratedOrbit 13 (2 ^ 13 * m + 7135) = 3 ^ 9 * m + 17147 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_13_7135.1, data_13_7135.2]

/-- Complete interval computation for depth 13, residue 7136. -/
theorem bounds_13_7136 : exactInterval 13 7136 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_13_7136 (m : Nat) :
    stoppingTime (2 ^ 13 * m + 7136) 13 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_13_7136 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_13_7136 : oddCount 7136 13 = 6 ∧ acceleratedOrbit 13 7136 = 638 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_13_7136 (m : Nat) :
    acceleratedOrbit 13 (2 ^ 13 * m + 7136) = 3 ^ 6 * m + 638 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_13_7136.1, data_13_7136.2]

/-- Complete interval computation for depth 13, residue 7137. -/
theorem bounds_13_7137 : exactInterval 13 7137 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_13_7137 (m : Nat) :
    stoppingTime (2 ^ 13 * m + 7137) 13 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_13_7137 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_13_7137 : oddCount 7137 13 = 7 ∧ acceleratedOrbit 13 7137 = 1906 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_13_7137 (m : Nat) :
    acceleratedOrbit 13 (2 ^ 13 * m + 7137) = 3 ^ 7 * m + 1906 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_13_7137.1, data_13_7137.2]

/-- Complete interval computation for depth 13, residue 7138. -/
theorem bounds_13_7138 : exactInterval 13 7138 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_13_7138 (m : Nat) :
    stoppingTime (2 ^ 13 * m + 7138) 13 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_13_7138 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_13_7138 : oddCount 7138 13 = 6 ∧ acceleratedOrbit 13 7138 = 638 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_13_7138 (m : Nat) :
    acceleratedOrbit 13 (2 ^ 13 * m + 7138) = 3 ^ 6 * m + 638 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_13_7138.1, data_13_7138.2]

/-- Complete interval computation for depth 13, residue 7139. -/
theorem bounds_13_7139 : exactInterval 13 7139 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_13_7139 (m : Nat) :
    stoppingTime (2 ^ 13 * m + 7139) 13 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_13_7139 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_13_7139 : oddCount 7139 13 = 6 ∧ acceleratedOrbit 13 7139 = 638 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_13_7139 (m : Nat) :
    acceleratedOrbit 13 (2 ^ 13 * m + 7139) = 3 ^ 6 * m + 638 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_13_7139.1, data_13_7139.2]

/-- Complete interval computation for depth 13, residue 7140. -/
theorem bounds_13_7140 : exactInterval 13 7140 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_13_7140 (m : Nat) :
    stoppingTime (2 ^ 13 * m + 7140) 13 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_13_7140 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_13_7140 : oddCount 7140 13 = 5 ∧ acceleratedOrbit 13 7140 = 212 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_13_7140 (m : Nat) :
    acceleratedOrbit 13 (2 ^ 13 * m + 7140) = 3 ^ 5 * m + 212 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_13_7140.1, data_13_7140.2]

/-- Complete interval computation for depth 13, residue 7141. -/
theorem bounds_13_7141 : exactInterval 13 7141 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_13_7141 (m : Nat) :
    stoppingTime (2 ^ 13 * m + 7141) 13 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_13_7141 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_13_7141 : oddCount 7141 13 = 5 ∧ acceleratedOrbit 13 7141 = 212 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_13_7141 (m : Nat) :
    acceleratedOrbit 13 (2 ^ 13 * m + 7141) = 3 ^ 5 * m + 212 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_13_7141.1, data_13_7141.2]

/-- Complete interval computation for depth 13, residue 7142. -/
theorem bounds_13_7142 : exactInterval 13 7142 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_13_7142 (m : Nat) :
    stoppingTime (2 ^ 13 * m + 7142) 13 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_13_7142 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_13_7142 : oddCount 7142 13 = 5 ∧ acceleratedOrbit 13 7142 = 212 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_13_7142 (m : Nat) :
    acceleratedOrbit 13 (2 ^ 13 * m + 7142) = 3 ^ 5 * m + 212 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_13_7142.1, data_13_7142.2]

/-- Complete interval computation for depth 13, residue 7143. -/
theorem bounds_13_7143 : exactInterval 13 7143 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_13_7143 (m : Nat) :
    stoppingTime (2 ^ 13 * m + 7143) 13 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_13_7143 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_13_7143 : oddCount 7143 13 = 8 ∧ acceleratedOrbit 13 7143 = 5723 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_13_7143 (m : Nat) :
    acceleratedOrbit 13 (2 ^ 13 * m + 7143) = 3 ^ 8 * m + 5723 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_13_7143.1, data_13_7143.2]

/-- Complete interval computation for depth 13, residue 7144. -/
theorem bounds_13_7144 : exactInterval 13 7144 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_13_7144 (m : Nat) :
    stoppingTime (2 ^ 13 * m + 7144) 13 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_13_7144 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_13_7144 : oddCount 7144 13 = 6 ∧ acceleratedOrbit 13 7144 = 638 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_13_7144 (m : Nat) :
    acceleratedOrbit 13 (2 ^ 13 * m + 7144) = 3 ^ 6 * m + 638 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_13_7144.1, data_13_7144.2]

/-- Complete interval computation for depth 13, residue 7145. -/
theorem bounds_13_7145 : exactInterval 13 7145 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_13_7145 (m : Nat) :
    stoppingTime (2 ^ 13 * m + 7145) 13 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_13_7145 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_13_7145 : oddCount 7145 13 = 11 ∧ acceleratedOrbit 13 7145 = 154547 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_13_7145 (m : Nat) :
    acceleratedOrbit 13 (2 ^ 13 * m + 7145) = 3 ^ 11 * m + 154547 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_13_7145.1, data_13_7145.2]

/-- Complete interval computation for depth 13, residue 7146. -/
theorem bounds_13_7146 : exactInterval 13 7146 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_13_7146 (m : Nat) :
    stoppingTime (2 ^ 13 * m + 7146) 13 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_13_7146 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_13_7146 : oddCount 7146 13 = 6 ∧ acceleratedOrbit 13 7146 = 638 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_13_7146 (m : Nat) :
    acceleratedOrbit 13 (2 ^ 13 * m + 7146) = 3 ^ 6 * m + 638 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_13_7146.1, data_13_7146.2]

end Collatz.Research.StoppingAtlas.Batch0932
