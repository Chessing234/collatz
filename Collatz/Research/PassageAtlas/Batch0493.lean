import Collatz.Research.DescentIntervals.Classifier

namespace Collatz.Research.PassageAtlas.Batch0493

open Collatz.Research.DescentIntervals

set_option maxRecDepth 20000
set_option maxHeartbeats 0

/-- Complete interval computation for depth 15, residue 16121. -/
theorem bounds_15_16121 : exactInterval 15 16121 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_16121 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 16121) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_16121 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_16121 : oddCount 16121 15 = 8 ∧ acceleratedOrbit 15 16121 = 3230 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_16121 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 16121) = 3 ^ 8 * m + 3230 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_16121.1, data_15_16121.2]

/-- Complete interval computation for depth 15, residue 16122. -/
theorem bounds_15_16122 : exactInterval 15 16122 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_16122 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 16122) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_16122 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_16122 : oddCount 16122 15 = 8 ∧ acceleratedOrbit 15 16122 = 3230 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_16122 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 16122) = 3 ^ 8 * m + 3230 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_16122.1, data_15_16122.2]

/-- Complete interval computation for depth 15, residue 16123. -/
theorem bounds_15_16123 : exactInterval 15 16123 = ⟨0, none⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_16123 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 16123) 15 ↔ 0 ≤ m := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_16123 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_16123 : oddCount 16123 15 = 9 ∧ acceleratedOrbit 15 16123 = 9686 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_16123 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 16123) = 3 ^ 9 * m + 9686 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_16123.1, data_15_16123.2]

/-- Complete interval computation for depth 15, residue 16124. -/
theorem bounds_15_16124 : exactInterval 15 16124 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_16124 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 16124) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_16124 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_16124 : oddCount 16124 15 = 9 ∧ acceleratedOrbit 15 16124 = 9688 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_16124 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 16124) = 3 ^ 9 * m + 9688 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_16124.1, data_15_16124.2]

/-- Complete interval computation for depth 15, residue 16125. -/
theorem bounds_15_16125 : exactInterval 15 16125 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_16125 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 16125) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_16125 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_16125 : oddCount 16125 15 = 9 ∧ acceleratedOrbit 15 16125 = 9688 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_16125 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 16125) = 3 ^ 9 * m + 9688 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_16125.1, data_15_16125.2]

/-- Complete interval computation for depth 15, residue 16126. -/
theorem bounds_15_16126 : exactInterval 15 16126 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_16126 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 16126) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_16126 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_16126 : oddCount 16126 15 = 9 ∧ acceleratedOrbit 15 16126 = 9688 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_16126 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 16126) = 3 ^ 9 * m + 9688 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_16126.1, data_15_16126.2]

/-- Complete interval computation for depth 15, residue 16127. -/
theorem bounds_15_16127 : exactInterval 15 16127 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_16127 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 16127) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_16127 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_16127 : oddCount 16127 15 = 12 ∧ acceleratedOrbit 15 16127 = 261569 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_16127 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 16127) = 3 ^ 12 * m + 261569 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_16127.1, data_15_16127.2]

/-- Complete interval computation for depth 15, residue 16128. -/
theorem bounds_15_16128 : exactInterval 15 16128 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_16128 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 16128) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_16128 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_16128 : oddCount 16128 15 = 6 ∧ acceleratedOrbit 15 16128 = 364 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_16128 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 16128) = 3 ^ 6 * m + 364 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_16128.1, data_15_16128.2]

/-- Complete interval computation for depth 15, residue 16129. -/
theorem bounds_15_16129 : exactInterval 15 16129 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_16129 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 16129) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_16129 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_16129 : oddCount 16129 15 = 7 ∧ acceleratedOrbit 15 16129 = 1079 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_16129 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 16129) = 3 ^ 7 * m + 1079 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_16129.1, data_15_16129.2]

/-- Complete interval computation for depth 15, residue 16130. -/
theorem bounds_15_16130 : exactInterval 15 16130 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_16130 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 16130) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_16130 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_16130 : oddCount 16130 15 = 6 ∧ acceleratedOrbit 15 16130 = 359 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_16130 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 16130) = 3 ^ 6 * m + 359 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_16130.1, data_15_16130.2]

/-- Complete interval computation for depth 15, residue 16131. -/
theorem bounds_15_16131 : exactInterval 15 16131 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_16131 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 16131) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_16131 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_16131 : oddCount 16131 15 = 6 ∧ acceleratedOrbit 15 16131 = 359 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_16131 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 16131) = 3 ^ 6 * m + 359 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_16131.1, data_15_16131.2]

/-- Complete interval computation for depth 15, residue 16132. -/
theorem bounds_15_16132 : exactInterval 15 16132 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_16132 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 16132) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_16132 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_16132 : oddCount 16132 15 = 7 ∧ acceleratedOrbit 15 16132 = 1079 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_16132 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 16132) = 3 ^ 7 * m + 1079 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_16132.1, data_15_16132.2]

/-- Complete interval computation for depth 15, residue 16133. -/
theorem bounds_15_16133 : exactInterval 15 16133 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_16133 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 16133) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_16133 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_16133 : oddCount 16133 15 = 7 ∧ acceleratedOrbit 15 16133 = 1079 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_16133 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 16133) = 3 ^ 7 * m + 1079 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_16133.1, data_15_16133.2]

/-- Complete interval computation for depth 15, residue 16134. -/
theorem bounds_15_16134 : exactInterval 15 16134 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_16134 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 16134) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_16134 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_16134 : oddCount 16134 15 = 7 ∧ acceleratedOrbit 15 16134 = 1079 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_16134 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 16134) = 3 ^ 7 * m + 1079 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_16134.1, data_15_16134.2]

/-- Complete interval computation for depth 15, residue 16135. -/
theorem bounds_15_16135 : exactInterval 15 16135 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_16135 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 16135) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_16135 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_16135 : oddCount 16135 15 = 6 ∧ acceleratedOrbit 15 16135 = 359 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_16135 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 16135) = 3 ^ 6 * m + 359 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_16135.1, data_15_16135.2]

/-- Complete interval computation for depth 15, residue 16136. -/
theorem bounds_15_16136 : exactInterval 15 16136 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_16136 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 16136) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_16136 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_16136 : oddCount 16136 15 = 8 ∧ acceleratedOrbit 15 16136 = 3235 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_16136 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 16136) = 3 ^ 8 * m + 3235 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_16136.1, data_15_16136.2]

/-- Complete interval computation for depth 15, residue 16137. -/
theorem bounds_15_16137 : exactInterval 15 16137 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_16137 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 16137) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_16137 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_16137 : oddCount 16137 15 = 9 ∧ acceleratedOrbit 15 16137 = 9695 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_16137 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 16137) = 3 ^ 9 * m + 9695 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_16137.1, data_15_16137.2]

/-- Complete interval computation for depth 15, residue 16138. -/
theorem bounds_15_16138 : exactInterval 15 16138 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_16138 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 16138) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_16138 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_16138 : oddCount 16138 15 = 8 ∧ acceleratedOrbit 15 16138 = 3235 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_16138 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 16138) = 3 ^ 8 * m + 3235 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_16138.1, data_15_16138.2]

/-- Complete interval computation for depth 15, residue 16139. -/
theorem bounds_15_16139 : exactInterval 15 16139 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_16139 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 16139) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_16139 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_16139 : oddCount 16139 15 = 8 ∧ acceleratedOrbit 15 16139 = 3233 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_16139 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 16139) = 3 ^ 8 * m + 3233 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_16139.1, data_15_16139.2]

/-- Complete interval computation for depth 15, residue 16140. -/
theorem bounds_15_16140 : exactInterval 15 16140 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_16140 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 16140) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_16140 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_16140 : oddCount 16140 15 = 8 ∧ acceleratedOrbit 15 16140 = 3235 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_16140 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 16140) = 3 ^ 8 * m + 3235 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_16140.1, data_15_16140.2]

/-- Complete interval computation for depth 15, residue 16141. -/
theorem bounds_15_16141 : exactInterval 15 16141 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_16141 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 16141) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_16141 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_16141 : oddCount 16141 15 = 8 ∧ acceleratedOrbit 15 16141 = 3235 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_16141 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 16141) = 3 ^ 8 * m + 3235 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_16141.1, data_15_16141.2]

/-- Complete interval computation for depth 15, residue 16142. -/
theorem bounds_15_16142 : exactInterval 15 16142 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_16142 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 16142) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_16142 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_16142 : oddCount 16142 15 = 7 ∧ acceleratedOrbit 15 16142 = 1079 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_16142 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 16142) = 3 ^ 7 * m + 1079 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_16142.1, data_15_16142.2]

/-- Complete interval computation for depth 15, residue 16143. -/
theorem bounds_15_16143 : exactInterval 15 16143 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_16143 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 16143) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_16143 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_16143 : oddCount 16143 15 = 7 ∧ acceleratedOrbit 15 16143 = 1079 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_16143 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 16143) = 3 ^ 7 * m + 1079 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_16143.1, data_15_16143.2]

/-- Complete interval computation for depth 15, residue 16144. -/
theorem bounds_15_16144 : exactInterval 15 16144 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_16144 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 16144) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_16144 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_16144 : oddCount 16144 15 = 5 ∧ acceleratedOrbit 15 16144 = 121 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_16144 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 16144) = 3 ^ 5 * m + 121 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_16144.1, data_15_16144.2]

/-- Complete interval computation for depth 15, residue 16145. -/
theorem bounds_15_16145 : exactInterval 15 16145 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_16145 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 16145) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_16145 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_16145 : oddCount 16145 15 = 8 ∧ acceleratedOrbit 15 16145 = 3235 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_16145 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 16145) = 3 ^ 8 * m + 3235 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_16145.1, data_15_16145.2]

/-- Complete interval computation for depth 15, residue 16146. -/
theorem bounds_15_16146 : exactInterval 15 16146 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_16146 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 16146) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_16146 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_16146 : oddCount 16146 15 = 10 ∧ acceleratedOrbit 15 16146 = 29105 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_16146 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 16146) = 3 ^ 10 * m + 29105 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_16146.1, data_15_16146.2]

/-- Complete interval computation for depth 15, residue 16147. -/
theorem bounds_15_16147 : exactInterval 15 16147 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_16147 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 16147) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_16147 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_16147 : oddCount 16147 15 = 10 ∧ acceleratedOrbit 15 16147 = 29105 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_16147 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 16147) = 3 ^ 10 * m + 29105 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_16147.1, data_15_16147.2]

/-- Complete interval computation for depth 15, residue 16148. -/
theorem bounds_15_16148 : exactInterval 15 16148 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_16148 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 16148) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_16148 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_16148 : oddCount 16148 15 = 5 ∧ acceleratedOrbit 15 16148 = 121 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_16148 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 16148) = 3 ^ 5 * m + 121 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_16148.1, data_15_16148.2]

/-- Complete interval computation for depth 15, residue 16149. -/
theorem bounds_15_16149 : exactInterval 15 16149 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_16149 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 16149) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_16149 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_16149 : oddCount 16149 15 = 5 ∧ acceleratedOrbit 15 16149 = 121 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_16149 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 16149) = 3 ^ 5 * m + 121 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_16149.1, data_15_16149.2]

/-- Complete interval computation for depth 15, residue 16150. -/
theorem bounds_15_16150 : exactInterval 15 16150 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_16150 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 16150) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_16150 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_16150 : oddCount 16150 15 = 8 ∧ acceleratedOrbit 15 16150 = 3235 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_16150 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 16150) = 3 ^ 8 * m + 3235 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_16150.1, data_15_16150.2]

/-- Complete interval computation for depth 15, residue 16151. -/
theorem bounds_15_16151 : exactInterval 15 16151 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_16151 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 16151) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_16151 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_16151 : oddCount 16151 15 = 8 ∧ acceleratedOrbit 15 16151 = 3235 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_16151 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 16151) = 3 ^ 8 * m + 3235 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_16151.1, data_15_16151.2]

/-- Complete interval computation for depth 15, residue 16152. -/
theorem bounds_15_16152 : exactInterval 15 16152 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_16152 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 16152) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_16152 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_16152 : oddCount 16152 15 = 5 ∧ acceleratedOrbit 15 16152 = 121 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_16152 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 16152) = 3 ^ 5 * m + 121 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_16152.1, data_15_16152.2]

/-- Complete interval computation for depth 15, residue 16153. -/
theorem bounds_15_16153 : exactInterval 15 16153 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_16153 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 16153) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_16153 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_16153 : oddCount 16153 15 = 11 ∧ acceleratedOrbit 15 16153 = 87344 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_16153 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 16153) = 3 ^ 11 * m + 87344 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_16153.1, data_15_16153.2]

end Collatz.Research.PassageAtlas.Batch0493
