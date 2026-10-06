import Collatz.Research.DescentIntervals.Classifier

namespace Collatz.Research.PassageAtlas.Batch0737

open Collatz.Research.DescentIntervals

set_option maxRecDepth 20000
set_option maxHeartbeats 0

/-- Complete interval computation for depth 15, residue 24117. -/
theorem bounds_15_24117 : exactInterval 15 24117 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_24117 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 24117) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_24117 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_24117 : oddCount 24117 15 = 3 ∧ acceleratedOrbit 15 24117 = 20 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_24117 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 24117) = 3 ^ 3 * m + 20 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_24117.1, data_15_24117.2]

/-- Complete interval computation for depth 15, residue 24118. -/
theorem bounds_15_24118 : exactInterval 15 24118 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_24118 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 24118) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_24118 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_24118 : oddCount 24118 15 = 11 ∧ acceleratedOrbit 15 24118 = 130400 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_24118 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 24118) = 3 ^ 11 * m + 130400 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_24118.1, data_15_24118.2]

/-- Complete interval computation for depth 15, residue 24119. -/
theorem bounds_15_24119 : exactInterval 15 24119 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_24119 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 24119) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_24119 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_24119 : oddCount 24119 15 = 11 ∧ acceleratedOrbit 15 24119 = 130400 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_24119 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 24119) = 3 ^ 11 * m + 130400 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_24119.1, data_15_24119.2]

/-- Complete interval computation for depth 15, residue 24120. -/
theorem bounds_15_24120 : exactInterval 15 24120 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_24120 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 24120) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_24120 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_24120 : oddCount 24120 15 = 9 ∧ acceleratedOrbit 15 24120 = 14498 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_24120 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 24120) = 3 ^ 9 * m + 14498 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_24120.1, data_15_24120.2]

/-- Complete interval computation for depth 15, residue 24121. -/
theorem bounds_15_24121 : exactInterval 15 24121 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_24121 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 24121) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_24121 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_24121 : oddCount 24121 15 = 9 ∧ acceleratedOrbit 15 24121 = 14492 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_24121 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 24121) = 3 ^ 9 * m + 14492 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_24121.1, data_15_24121.2]

/-- Complete interval computation for depth 15, residue 24122. -/
theorem bounds_15_24122 : exactInterval 15 24122 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_24122 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 24122) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_24122 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_24122 : oddCount 24122 15 = 9 ∧ acceleratedOrbit 15 24122 = 14498 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_24122 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 24122) = 3 ^ 9 * m + 14498 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_24122.1, data_15_24122.2]

/-- Complete interval computation for depth 15, residue 24123. -/
theorem bounds_15_24123 : exactInterval 15 24123 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_24123 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 24123) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_24123 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_24123 : oddCount 24123 15 = 8 ∧ acceleratedOrbit 15 24123 = 4832 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_24123 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 24123) = 3 ^ 8 * m + 4832 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_24123.1, data_15_24123.2]

/-- Complete interval computation for depth 15, residue 24124. -/
theorem bounds_15_24124 : exactInterval 15 24124 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_24124 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 24124) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_24124 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_24124 : oddCount 24124 15 = 9 ∧ acceleratedOrbit 15 24124 = 14498 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_24124 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 24124) = 3 ^ 9 * m + 14498 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_24124.1, data_15_24124.2]

/-- Complete interval computation for depth 15, residue 24125. -/
theorem bounds_15_24125 : exactInterval 15 24125 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_24125 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 24125) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_24125 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_24125 : oddCount 24125 15 = 9 ∧ acceleratedOrbit 15 24125 = 14498 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_24125 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 24125) = 3 ^ 9 * m + 14498 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_24125.1, data_15_24125.2]

/-- Complete interval computation for depth 15, residue 24126. -/
theorem bounds_15_24126 : exactInterval 15 24126 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_24126 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 24126) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_24126 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_24126 : oddCount 24126 15 = 9 ∧ acceleratedOrbit 15 24126 = 14494 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_24126 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 24126) = 3 ^ 9 * m + 14494 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_24126.1, data_15_24126.2]

/-- Complete interval computation for depth 15, residue 24127. -/
theorem bounds_15_24127 : exactInterval 15 24127 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_24127 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 24127) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_24127 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_24127 : oddCount 24127 15 = 9 ∧ acceleratedOrbit 15 24127 = 14494 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_24127 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 24127) = 3 ^ 9 * m + 14494 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_24127.1, data_15_24127.2]

/-- Complete interval computation for depth 15, residue 24128. -/
theorem bounds_15_24128 : exactInterval 15 24128 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_24128 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 24128) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_24128 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_24128 : oddCount 24128 15 = 7 ∧ acceleratedOrbit 15 24128 = 1619 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_24128 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 24128) = 3 ^ 7 * m + 1619 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_24128.1, data_15_24128.2]

/-- Complete interval computation for depth 15, residue 24129. -/
theorem bounds_15_24129 : exactInterval 15 24129 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_24129 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 24129) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_24129 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_24129 : oddCount 24129 15 = 5 ∧ acceleratedOrbit 15 24129 = 179 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_24129 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 24129) = 3 ^ 5 * m + 179 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_24129.1, data_15_24129.2]

/-- Complete interval computation for depth 15, residue 24130. -/
theorem bounds_15_24130 : exactInterval 15 24130 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_24130 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 24130) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_24130 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_24130 : oddCount 24130 15 = 5 ∧ acceleratedOrbit 15 24130 = 179 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_24130 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 24130) = 3 ^ 5 * m + 179 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_24130.1, data_15_24130.2]

/-- Complete interval computation for depth 15, residue 24131. -/
theorem bounds_15_24131 : exactInterval 15 24131 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_24131 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 24131) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_24131 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_24131 : oddCount 24131 15 = 5 ∧ acceleratedOrbit 15 24131 = 179 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_24131 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 24131) = 3 ^ 5 * m + 179 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_24131.1, data_15_24131.2]

/-- Complete interval computation for depth 15, residue 24132. -/
theorem bounds_15_24132 : exactInterval 15 24132 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_24132 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 24132) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_24132 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_24132 : oddCount 24132 15 = 7 ∧ acceleratedOrbit 15 24132 = 1613 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_24132 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 24132) = 3 ^ 7 * m + 1613 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_24132.1, data_15_24132.2]

/-- Complete interval computation for depth 15, residue 24133. -/
theorem bounds_15_24133 : exactInterval 15 24133 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_24133 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 24133) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_24133 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_24133 : oddCount 24133 15 = 7 ∧ acceleratedOrbit 15 24133 = 1613 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_24133 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 24133) = 3 ^ 7 * m + 1613 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_24133.1, data_15_24133.2]

/-- Complete interval computation for depth 15, residue 24134. -/
theorem bounds_15_24134 : exactInterval 15 24134 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_24134 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 24134) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_24134 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_24134 : oddCount 24134 15 = 7 ∧ acceleratedOrbit 15 24134 = 1613 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_24134 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 24134) = 3 ^ 7 * m + 1613 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_24134.1, data_15_24134.2]

/-- Complete interval computation for depth 15, residue 24135. -/
theorem bounds_15_24135 : exactInterval 15 24135 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_24135 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 24135) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_24135 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_24135 : oddCount 24135 15 = 11 ∧ acceleratedOrbit 15 24135 = 130490 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_24135 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 24135) = 3 ^ 11 * m + 130490 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_24135.1, data_15_24135.2]

/-- Complete interval computation for depth 15, residue 24136. -/
theorem bounds_15_24136 : exactInterval 15 24136 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_24136 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 24136) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_24136 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_24136 : oddCount 24136 15 = 7 ∧ acceleratedOrbit 15 24136 = 1613 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_24136 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 24136) = 3 ^ 7 * m + 1613 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_24136.1, data_15_24136.2]

/-- Complete interval computation for depth 15, residue 24137. -/
theorem bounds_15_24137 : exactInterval 15 24137 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_24137 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 24137) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_24137 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_24137 : oddCount 24137 15 = 9 ∧ acceleratedOrbit 15 24137 = 14501 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_24137 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 24137) = 3 ^ 9 * m + 14501 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_24137.1, data_15_24137.2]

/-- Complete interval computation for depth 15, residue 24138. -/
theorem bounds_15_24138 : exactInterval 15 24138 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_24138 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 24138) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_24138 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_24138 : oddCount 24138 15 = 7 ∧ acceleratedOrbit 15 24138 = 1613 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_24138 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 24138) = 3 ^ 7 * m + 1613 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_24138.1, data_15_24138.2]

/-- Complete interval computation for depth 15, residue 24139. -/
theorem bounds_15_24139 : exactInterval 15 24139 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_24139 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 24139) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_24139 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_24139 : oddCount 24139 15 = 7 ∧ acceleratedOrbit 15 24139 = 1613 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_24139 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 24139) = 3 ^ 7 * m + 1613 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_24139.1, data_15_24139.2]

/-- Complete interval computation for depth 15, residue 24140. -/
theorem bounds_15_24140 : exactInterval 15 24140 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_24140 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 24140) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_24140 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_24140 : oddCount 24140 15 = 7 ∧ acceleratedOrbit 15 24140 = 1613 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_24140 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 24140) = 3 ^ 7 * m + 1613 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_24140.1, data_15_24140.2]

/-- Complete interval computation for depth 15, residue 24141. -/
theorem bounds_15_24141 : exactInterval 15 24141 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_24141 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 24141) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_24141 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_24141 : oddCount 24141 15 = 7 ∧ acceleratedOrbit 15 24141 = 1613 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_24141 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 24141) = 3 ^ 7 * m + 1613 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_24141.1, data_15_24141.2]

/-- Complete interval computation for depth 15, residue 24142. -/
theorem bounds_15_24142 : exactInterval 15 24142 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_24142 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 24142) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_24142 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_24142 : oddCount 24142 15 = 8 ∧ acceleratedOrbit 15 24142 = 4835 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_24142 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 24142) = 3 ^ 8 * m + 4835 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_24142.1, data_15_24142.2]

/-- Complete interval computation for depth 15, residue 24143. -/
theorem bounds_15_24143 : exactInterval 15 24143 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_24143 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 24143) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_24143 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_24143 : oddCount 24143 15 = 8 ∧ acceleratedOrbit 15 24143 = 4835 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_24143 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 24143) = 3 ^ 8 * m + 4835 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_24143.1, data_15_24143.2]

/-- Complete interval computation for depth 15, residue 24144. -/
theorem bounds_15_24144 : exactInterval 15 24144 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_24144 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 24144) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_24144 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_24144 : oddCount 24144 15 = 7 ∧ acceleratedOrbit 15 24144 = 1619 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_24144 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 24144) = 3 ^ 7 * m + 1619 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_24144.1, data_15_24144.2]

/-- Complete interval computation for depth 15, residue 24145. -/
theorem bounds_15_24145 : exactInterval 15 24145 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_24145 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 24145) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_24145 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_24145 : oddCount 24145 15 = 7 ∧ acceleratedOrbit 15 24145 = 1612 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_24145 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 24145) = 3 ^ 7 * m + 1612 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_24145.1, data_15_24145.2]

/-- Complete interval computation for depth 15, residue 24146. -/
theorem bounds_15_24146 : exactInterval 15 24146 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_24146 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 24146) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_24146 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_24146 : oddCount 24146 15 = 7 ∧ acceleratedOrbit 15 24146 = 1612 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_24146 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 24146) = 3 ^ 7 * m + 1612 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_24146.1, data_15_24146.2]

/-- Complete interval computation for depth 15, residue 24147. -/
theorem bounds_15_24147 : exactInterval 15 24147 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_24147 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 24147) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_24147 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_24147 : oddCount 24147 15 = 7 ∧ acceleratedOrbit 15 24147 = 1612 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_24147 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 24147) = 3 ^ 7 * m + 1612 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_24147.1, data_15_24147.2]

/-- Complete interval computation for depth 15, residue 24148. -/
theorem bounds_15_24148 : exactInterval 15 24148 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_24148 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 24148) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_24148 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_24148 : oddCount 24148 15 = 7 ∧ acceleratedOrbit 15 24148 = 1619 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_24148 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 24148) = 3 ^ 7 * m + 1619 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_24148.1, data_15_24148.2]

/-- Complete interval computation for depth 15, residue 24149. -/
theorem bounds_15_24149 : exactInterval 15 24149 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_24149 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 24149) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_24149 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_24149 : oddCount 24149 15 = 7 ∧ acceleratedOrbit 15 24149 = 1619 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_24149 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 24149) = 3 ^ 7 * m + 1619 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_24149.1, data_15_24149.2]

end Collatz.Research.PassageAtlas.Batch0737
