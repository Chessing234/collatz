import Collatz.Research.DescentIntervals.Classifier

namespace Collatz.Research.PassageAtlas.Batch0432

open Collatz.Research.DescentIntervals

set_option maxRecDepth 20000
set_option maxHeartbeats 0

/-- Complete interval computation for depth 15, residue 14123. -/
theorem bounds_15_14123 : exactInterval 15 14123 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_14123 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 14123) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_14123 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_14123 : oddCount 14123 15 = 7 ∧ acceleratedOrbit 15 14123 = 944 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_14123 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 14123) = 3 ^ 7 * m + 944 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_14123.1, data_15_14123.2]

/-- Complete interval computation for depth 15, residue 14124. -/
theorem bounds_15_14124 : exactInterval 15 14124 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_14124 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 14124) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_14124 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_14124 : oddCount 14124 15 = 8 ∧ acceleratedOrbit 15 14124 = 2834 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_14124 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 14124) = 3 ^ 8 * m + 2834 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_14124.1, data_15_14124.2]

/-- Complete interval computation for depth 15, residue 14125. -/
theorem bounds_15_14125 : exactInterval 15 14125 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_14125 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 14125) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_14125 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_14125 : oddCount 14125 15 = 8 ∧ acceleratedOrbit 15 14125 = 2834 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_14125 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 14125) = 3 ^ 8 * m + 2834 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_14125.1, data_15_14125.2]

/-- Complete interval computation for depth 15, residue 14126. -/
theorem bounds_15_14126 : exactInterval 15 14126 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_14126 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 14126) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_14126 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_14126 : oddCount 14126 15 = 8 ∧ acceleratedOrbit 15 14126 = 2834 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_14126 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 14126) = 3 ^ 8 * m + 2834 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_14126.1, data_15_14126.2]

/-- Complete interval computation for depth 15, residue 14127. -/
theorem bounds_15_14127 : exactInterval 15 14127 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_14127 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 14127) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_14127 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_14127 : oddCount 14127 15 = 7 ∧ acceleratedOrbit 15 14127 = 943 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_14127 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 14127) = 3 ^ 7 * m + 943 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_14127.1, data_15_14127.2]

/-- Complete interval computation for depth 15, residue 14128. -/
theorem bounds_15_14128 : exactInterval 15 14128 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_14128 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 14128) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_14128 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_14128 : oddCount 14128 15 = 4 ∧ acceleratedOrbit 15 14128 = 35 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_14128 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 14128) = 3 ^ 4 * m + 35 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_14128.1, data_15_14128.2]

/-- Complete interval computation for depth 15, residue 14129. -/
theorem bounds_15_14129 : exactInterval 15 14129 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_14129 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 14129) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_14129 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_14129 : oddCount 14129 15 = 8 ∧ acceleratedOrbit 15 14129 = 2834 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_14129 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 14129) = 3 ^ 8 * m + 2834 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_14129.1, data_15_14129.2]

/-- Complete interval computation for depth 15, residue 14130. -/
theorem bounds_15_14130 : exactInterval 15 14130 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_14130 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 14130) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_14130 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_14130 : oddCount 14130 15 = 8 ∧ acceleratedOrbit 15 14130 = 2834 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_14130 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 14130) = 3 ^ 8 * m + 2834 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_14130.1, data_15_14130.2]

/-- Complete interval computation for depth 15, residue 14131. -/
theorem bounds_15_14131 : exactInterval 15 14131 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_14131 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 14131) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_14131 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_14131 : oddCount 14131 15 = 8 ∧ acceleratedOrbit 15 14131 = 2834 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_14131 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 14131) = 3 ^ 8 * m + 2834 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_14131.1, data_15_14131.2]

/-- Complete interval computation for depth 15, residue 14132. -/
theorem bounds_15_14132 : exactInterval 15 14132 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_14132 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 14132) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_14132 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_14132 : oddCount 14132 15 = 4 ∧ acceleratedOrbit 15 14132 = 35 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_14132 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 14132) = 3 ^ 4 * m + 35 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_14132.1, data_15_14132.2]

/-- Complete interval computation for depth 15, residue 14133. -/
theorem bounds_15_14133 : exactInterval 15 14133 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_14133 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 14133) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_14133 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_14133 : oddCount 14133 15 = 4 ∧ acceleratedOrbit 15 14133 = 35 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_14133 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 14133) = 3 ^ 4 * m + 35 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_14133.1, data_15_14133.2]

/-- Complete interval computation for depth 15, residue 14134. -/
theorem bounds_15_14134 : exactInterval 15 14134 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_14134 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 14134) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_14134 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_14134 : oddCount 14134 15 = 7 ∧ acceleratedOrbit 15 14134 = 944 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_14134 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 14134) = 3 ^ 7 * m + 944 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_14134.1, data_15_14134.2]

/-- Complete interval computation for depth 15, residue 14135. -/
theorem bounds_15_14135 : exactInterval 15 14135 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_14135 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 14135) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_14135 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_14135 : oddCount 14135 15 = 7 ∧ acceleratedOrbit 15 14135 = 944 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_14135 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 14135) = 3 ^ 7 * m + 944 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_14135.1, data_15_14135.2]

/-- Complete interval computation for depth 15, residue 14136. -/
theorem bounds_15_14136 : exactInterval 15 14136 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_14136 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 14136) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_14136 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_14136 : oddCount 14136 15 = 9 ∧ acceleratedOrbit 15 14136 = 8498 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_14136 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 14136) = 3 ^ 9 * m + 8498 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_14136.1, data_15_14136.2]

/-- Complete interval computation for depth 15, residue 14137. -/
theorem bounds_15_14137 : exactInterval 15 14137 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_14137 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 14137) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_14137 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_14137 : oddCount 14137 15 = 9 ∧ acceleratedOrbit 15 14137 = 8495 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_14137 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 14137) = 3 ^ 9 * m + 8495 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_14137.1, data_15_14137.2]

/-- Complete interval computation for depth 15, residue 14138. -/
theorem bounds_15_14138 : exactInterval 15 14138 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_14138 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 14138) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_14138 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_14138 : oddCount 14138 15 = 9 ∧ acceleratedOrbit 15 14138 = 8498 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_14138 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 14138) = 3 ^ 9 * m + 8498 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_14138.1, data_15_14138.2]

/-- Complete interval computation for depth 15, residue 14139. -/
theorem bounds_15_14139 : exactInterval 15 14139 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_14139 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 14139) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_14139 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_14139 : oddCount 14139 15 = 8 ∧ acceleratedOrbit 15 14139 = 2834 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_14139 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 14139) = 3 ^ 8 * m + 2834 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_14139.1, data_15_14139.2]

/-- Complete interval computation for depth 15, residue 14140. -/
theorem bounds_15_14140 : exactInterval 15 14140 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_14140 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 14140) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_14140 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_14140 : oddCount 14140 15 = 9 ∧ acceleratedOrbit 15 14140 = 8498 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_14140 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 14140) = 3 ^ 9 * m + 8498 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_14140.1, data_15_14140.2]

/-- Complete interval computation for depth 15, residue 14141. -/
theorem bounds_15_14141 : exactInterval 15 14141 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_14141 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 14141) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_14141 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_14141 : oddCount 14141 15 = 9 ∧ acceleratedOrbit 15 14141 = 8498 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_14141 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 14141) = 3 ^ 9 * m + 8498 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_14141.1, data_15_14141.2]

/-- Complete interval computation for depth 15, residue 14142. -/
theorem bounds_15_14142 : exactInterval 15 14142 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_14142 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 14142) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_14142 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_14142 : oddCount 14142 15 = 7 ∧ acceleratedOrbit 15 14142 = 944 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_14142 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 14142) = 3 ^ 7 * m + 944 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_14142.1, data_15_14142.2]

/-- Complete interval computation for depth 15, residue 14143. -/
theorem bounds_15_14143 : exactInterval 15 14143 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_14143 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 14143) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_14143 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_14143 : oddCount 14143 15 = 7 ∧ acceleratedOrbit 15 14143 = 944 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_14143 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 14143) = 3 ^ 7 * m + 944 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_14143.1, data_15_14143.2]

/-- Complete interval computation for depth 15, residue 14144. -/
theorem bounds_15_14144 : exactInterval 15 14144 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_14144 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 14144) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_14144 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_14144 : oddCount 14144 15 = 5 ∧ acceleratedOrbit 15 14144 = 107 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_14144 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 14144) = 3 ^ 5 * m + 107 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_14144.1, data_15_14144.2]

/-- Complete interval computation for depth 15, residue 14145. -/
theorem bounds_15_14145 : exactInterval 15 14145 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_14145 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 14145) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_14145 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_14145 : oddCount 14145 15 = 4 ∧ acceleratedOrbit 15 14145 = 35 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_14145 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 14145) = 3 ^ 4 * m + 35 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_14145.1, data_15_14145.2]

/-- Complete interval computation for depth 15, residue 14146. -/
theorem bounds_15_14146 : exactInterval 15 14146 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_14146 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 14146) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_14146 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_14146 : oddCount 14146 15 = 9 ∧ acceleratedOrbit 15 14146 = 8504 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_14146 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 14146) = 3 ^ 9 * m + 8504 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_14146.1, data_15_14146.2]

/-- Complete interval computation for depth 15, residue 14147. -/
theorem bounds_15_14147 : exactInterval 15 14147 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_14147 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 14147) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_14147 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_14147 : oddCount 14147 15 = 9 ∧ acceleratedOrbit 15 14147 = 8504 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_14147 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 14147) = 3 ^ 9 * m + 8504 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_14147.1, data_15_14147.2]

/-- Complete interval computation for depth 15, residue 14148. -/
theorem bounds_15_14148 : exactInterval 15 14148 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_14148 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 14148) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_14148 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_14148 : oddCount 14148 15 = 4 ∧ acceleratedOrbit 15 14148 = 35 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_14148 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 14148) = 3 ^ 4 * m + 35 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_14148.1, data_15_14148.2]

/-- Complete interval computation for depth 15, residue 14149. -/
theorem bounds_15_14149 : exactInterval 15 14149 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_14149 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 14149) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_14149 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_14149 : oddCount 14149 15 = 4 ∧ acceleratedOrbit 15 14149 = 35 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_14149 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 14149) = 3 ^ 4 * m + 35 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_14149.1, data_15_14149.2]

/-- Complete interval computation for depth 15, residue 14150. -/
theorem bounds_15_14150 : exactInterval 15 14150 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_14150 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 14150) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_14150 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_14150 : oddCount 14150 15 = 4 ∧ acceleratedOrbit 15 14150 = 35 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_14150 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 14150) = 3 ^ 4 * m + 35 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_14150.1, data_15_14150.2]

/-- Complete interval computation for depth 15, residue 14151. -/
theorem bounds_15_14151 : exactInterval 15 14151 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_14151 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 14151) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_14151 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_14151 : oddCount 14151 15 = 10 ∧ acceleratedOrbit 15 14151 = 25505 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_14151 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 14151) = 3 ^ 10 * m + 25505 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_14151.1, data_15_14151.2]

/-- Complete interval computation for depth 15, residue 14152. -/
theorem bounds_15_14152 : exactInterval 15 14152 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_14152 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 14152) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_14152 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_14152 : oddCount 14152 15 = 8 ∧ acceleratedOrbit 15 14152 = 2837 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_14152 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 14152) = 3 ^ 8 * m + 2837 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_14152.1, data_15_14152.2]

/-- Complete interval computation for depth 15, residue 14153. -/
theorem bounds_15_14153 : exactInterval 15 14153 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_14153 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 14153) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_14153 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_14153 : oddCount 14153 15 = 10 ∧ acceleratedOrbit 15 14153 = 25514 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_14153 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 14153) = 3 ^ 10 * m + 25514 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_14153.1, data_15_14153.2]

/-- Complete interval computation for depth 15, residue 14154. -/
theorem bounds_15_14154 : exactInterval 15 14154 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_14154 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 14154) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_14154 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_14154 : oddCount 14154 15 = 8 ∧ acceleratedOrbit 15 14154 = 2837 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_14154 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 14154) = 3 ^ 8 * m + 2837 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_14154.1, data_15_14154.2]

end Collatz.Research.PassageAtlas.Batch0432
