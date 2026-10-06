import Collatz.Research.DescentIntervals.Classifier

namespace Collatz.Research.PassageAtlas.Batch0371

open Collatz.Research.DescentIntervals

set_option maxRecDepth 20000
set_option maxHeartbeats 0

/-- Complete interval computation for depth 15, residue 12124. -/
theorem bounds_15_12124 : exactInterval 15 12124 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_12124 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 12124) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_12124 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_12124 : oddCount 12124 15 = 10 ∧ acceleratedOrbit 15 12124 = 21869 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_12124 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 12124) = 3 ^ 10 * m + 21869 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_12124.1, data_15_12124.2]

/-- Complete interval computation for depth 15, residue 12125. -/
theorem bounds_15_12125 : exactInterval 15 12125 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_12125 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 12125) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_12125 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_12125 : oddCount 12125 15 = 10 ∧ acceleratedOrbit 15 12125 = 21869 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_12125 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 12125) = 3 ^ 10 * m + 21869 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_12125.1, data_15_12125.2]

/-- Complete interval computation for depth 15, residue 12126. -/
theorem bounds_15_12126 : exactInterval 15 12126 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_12126 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 12126) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_12126 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_12126 : oddCount 12126 15 = 9 ∧ acceleratedOrbit 15 12126 = 7289 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_12126 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 12126) = 3 ^ 9 * m + 7289 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_12126.1, data_15_12126.2]

/-- Complete interval computation for depth 15, residue 12127. -/
theorem bounds_15_12127 : exactInterval 15 12127 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_12127 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 12127) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_12127 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_12127 : oddCount 12127 15 = 9 ∧ acceleratedOrbit 15 12127 = 7289 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_12127 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 12127) = 3 ^ 9 * m + 7289 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_12127.1, data_15_12127.2]

/-- Complete interval computation for depth 15, residue 12128. -/
theorem bounds_15_12128 : exactInterval 15 12128 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_12128 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 12128) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_12128 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_12128 : oddCount 12128 15 = 6 ∧ acceleratedOrbit 15 12128 = 271 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_12128 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 12128) = 3 ^ 6 * m + 271 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_12128.1, data_15_12128.2]

/-- Complete interval computation for depth 15, residue 12129. -/
theorem bounds_15_12129 : exactInterval 15 12129 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_12129 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 12129) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_12129 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_12129 : oddCount 12129 15 = 10 ∧ acceleratedOrbit 15 12129 = 21863 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_12129 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 12129) = 3 ^ 10 * m + 21863 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_12129.1, data_15_12129.2]

/-- Complete interval computation for depth 15, residue 12130. -/
theorem bounds_15_12130 : exactInterval 15 12130 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_12130 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 12130) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_12130 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_12130 : oddCount 12130 15 = 3 ∧ acceleratedOrbit 15 12130 = 10 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_12130 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 12130) = 3 ^ 3 * m + 10 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_12130.1, data_15_12130.2]

/-- Complete interval computation for depth 15, residue 12131. -/
theorem bounds_15_12131 : exactInterval 15 12131 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_12131 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 12131) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_12131 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_12131 : oddCount 12131 15 = 3 ∧ acceleratedOrbit 15 12131 = 10 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_12131 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 12131) = 3 ^ 3 * m + 10 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_12131.1, data_15_12131.2]

/-- Complete interval computation for depth 15, residue 12132. -/
theorem bounds_15_12132 : exactInterval 15 12132 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_12132 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 12132) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_12132 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_12132 : oddCount 12132 15 = 3 ∧ acceleratedOrbit 15 12132 = 10 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_12132 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 12132) = 3 ^ 3 * m + 10 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_12132.1, data_15_12132.2]

/-- Complete interval computation for depth 15, residue 12133. -/
theorem bounds_15_12133 : exactInterval 15 12133 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_12133 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 12133) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_12133 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_12133 : oddCount 12133 15 = 3 ∧ acceleratedOrbit 15 12133 = 10 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_12133 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 12133) = 3 ^ 3 * m + 10 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_12133.1, data_15_12133.2]

/-- Complete interval computation for depth 15, residue 12134. -/
theorem bounds_15_12134 : exactInterval 15 12134 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_12134 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 12134) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_12134 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_12134 : oddCount 12134 15 = 3 ∧ acceleratedOrbit 15 12134 = 10 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_12134 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 12134) = 3 ^ 3 * m + 10 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_12134.1, data_15_12134.2]

/-- Complete interval computation for depth 15, residue 12135. -/
theorem bounds_15_12135 : exactInterval 15 12135 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_12135 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 12135) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_12135 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_12135 : oddCount 12135 15 = 14 ∧ acceleratedOrbit 15 12135 = 1771469 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_12135 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 12135) = 3 ^ 14 * m + 1771469 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_12135.1, data_15_12135.2]

/-- Complete interval computation for depth 15, residue 12136. -/
theorem bounds_15_12136 : exactInterval 15 12136 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_12136 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 12136) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_12136 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_12136 : oddCount 12136 15 = 6 ∧ acceleratedOrbit 15 12136 = 271 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_12136 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 12136) = 3 ^ 6 * m + 271 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_12136.1, data_15_12136.2]

/-- Complete interval computation for depth 15, residue 12137. -/
theorem bounds_15_12137 : exactInterval 15 12137 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_12137 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 12137) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_12137 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_12137 : oddCount 12137 15 = 8 ∧ acceleratedOrbit 15 12137 = 2431 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_12137 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 12137) = 3 ^ 8 * m + 2431 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_12137.1, data_15_12137.2]

/-- Complete interval computation for depth 15, residue 12138. -/
theorem bounds_15_12138 : exactInterval 15 12138 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_12138 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 12138) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_12138 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_12138 : oddCount 12138 15 = 6 ∧ acceleratedOrbit 15 12138 = 271 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_12138 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 12138) = 3 ^ 6 * m + 271 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_12138.1, data_15_12138.2]

/-- Complete interval computation for depth 15, residue 12139. -/
theorem bounds_15_12139 : exactInterval 15 12139 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_12139 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 12139) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_12139 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_12139 : oddCount 12139 15 = 8 ∧ acceleratedOrbit 15 12139 = 2432 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_12139 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 12139) = 3 ^ 8 * m + 2432 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_12139.1, data_15_12139.2]

/-- Complete interval computation for depth 15, residue 12140. -/
theorem bounds_15_12140 : exactInterval 15 12140 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_12140 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 12140) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_12140 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_12140 : oddCount 12140 15 = 7 ∧ acceleratedOrbit 15 12140 = 811 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_12140 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 12140) = 3 ^ 7 * m + 811 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_12140.1, data_15_12140.2]

/-- Complete interval computation for depth 15, residue 12141. -/
theorem bounds_15_12141 : exactInterval 15 12141 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_12141 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 12141) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_12141 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_12141 : oddCount 12141 15 = 7 ∧ acceleratedOrbit 15 12141 = 811 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_12141 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 12141) = 3 ^ 7 * m + 811 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_12141.1, data_15_12141.2]

/-- Complete interval computation for depth 15, residue 12142. -/
theorem bounds_15_12142 : exactInterval 15 12142 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_12142 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 12142) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_12142 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_12142 : oddCount 12142 15 = 7 ∧ acceleratedOrbit 15 12142 = 811 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_12142 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 12142) = 3 ^ 7 * m + 811 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_12142.1, data_15_12142.2]

/-- Complete interval computation for depth 15, residue 12143. -/
theorem bounds_15_12143 : exactInterval 15 12143 = ⟨0, none⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_12143 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 12143) 15 ↔ 0 ≤ m := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_12143 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_12143 : oddCount 12143 15 = 9 ∧ acceleratedOrbit 15 12143 = 7295 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_12143 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 12143) = 3 ^ 9 * m + 7295 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_12143.1, data_15_12143.2]

/-- Complete interval computation for depth 15, residue 12144. -/
theorem bounds_15_12144 : exactInterval 15 12144 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_12144 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 12144) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_12144 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_12144 : oddCount 12144 15 = 6 ∧ acceleratedOrbit 15 12144 = 271 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_12144 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 12144) = 3 ^ 6 * m + 271 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_12144.1, data_15_12144.2]

/-- Complete interval computation for depth 15, residue 12145. -/
theorem bounds_15_12145 : exactInterval 15 12145 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_12145 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 12145) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_12145 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_12145 : oddCount 12145 15 = 6 ∧ acceleratedOrbit 15 12145 = 271 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_12145 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 12145) = 3 ^ 6 * m + 271 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_12145.1, data_15_12145.2]

/-- Complete interval computation for depth 15, residue 12146. -/
theorem bounds_15_12146 : exactInterval 15 12146 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_12146 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 12146) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_12146 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_12146 : oddCount 12146 15 = 7 ∧ acceleratedOrbit 15 12146 = 812 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_12146 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 12146) = 3 ^ 7 * m + 812 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_12146.1, data_15_12146.2]

/-- Complete interval computation for depth 15, residue 12147. -/
theorem bounds_15_12147 : exactInterval 15 12147 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_12147 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 12147) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_12147 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_12147 : oddCount 12147 15 = 7 ∧ acceleratedOrbit 15 12147 = 812 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_12147 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 12147) = 3 ^ 7 * m + 812 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_12147.1, data_15_12147.2]

/-- Complete interval computation for depth 15, residue 12148. -/
theorem bounds_15_12148 : exactInterval 15 12148 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_12148 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 12148) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_12148 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_12148 : oddCount 12148 15 = 6 ∧ acceleratedOrbit 15 12148 = 271 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_12148 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 12148) = 3 ^ 6 * m + 271 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_12148.1, data_15_12148.2]

/-- Complete interval computation for depth 15, residue 12149. -/
theorem bounds_15_12149 : exactInterval 15 12149 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_12149 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 12149) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_12149 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_12149 : oddCount 12149 15 = 6 ∧ acceleratedOrbit 15 12149 = 271 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_12149 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 12149) = 3 ^ 6 * m + 271 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_12149.1, data_15_12149.2]

/-- Complete interval computation for depth 15, residue 12150. -/
theorem bounds_15_12150 : exactInterval 15 12150 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_12150 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 12150) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_12150 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_12150 : oddCount 12150 15 = 7 ∧ acceleratedOrbit 15 12150 = 812 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_12150 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 12150) = 3 ^ 7 * m + 812 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_12150.1, data_15_12150.2]

/-- Complete interval computation for depth 15, residue 12151. -/
theorem bounds_15_12151 : exactInterval 15 12151 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_12151 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 12151) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_12151 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_12151 : oddCount 12151 15 = 7 ∧ acceleratedOrbit 15 12151 = 812 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_12151 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 12151) = 3 ^ 7 * m + 812 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_12151.1, data_15_12151.2]

/-- Complete interval computation for depth 15, residue 12152. -/
theorem bounds_15_12152 : exactInterval 15 12152 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_12152 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 12152) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_12152 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_12152 : oddCount 12152 15 = 8 ∧ acceleratedOrbit 15 12152 = 2435 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_12152 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 12152) = 3 ^ 8 * m + 2435 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_12152.1, data_15_12152.2]

/-- Complete interval computation for depth 15, residue 12153. -/
theorem bounds_15_12153 : exactInterval 15 12153 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_12153 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 12153) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_12153 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_12153 : oddCount 12153 15 = 8 ∧ acceleratedOrbit 15 12153 = 2434 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_12153 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 12153) = 3 ^ 8 * m + 2434 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_12153.1, data_15_12153.2]

/-- Complete interval computation for depth 15, residue 12154. -/
theorem bounds_15_12154 : exactInterval 15 12154 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_12154 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 12154) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_12154 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_12154 : oddCount 12154 15 = 8 ∧ acceleratedOrbit 15 12154 = 2435 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_12154 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 12154) = 3 ^ 8 * m + 2435 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_12154.1, data_15_12154.2]

/-- Complete interval computation for depth 15, residue 12155. -/
theorem bounds_15_12155 : exactInterval 15 12155 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_12155 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 12155) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_12155 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_12155 : oddCount 12155 15 = 9 ∧ acceleratedOrbit 15 12155 = 7303 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_12155 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 12155) = 3 ^ 9 * m + 7303 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_12155.1, data_15_12155.2]

end Collatz.Research.PassageAtlas.Batch0371
