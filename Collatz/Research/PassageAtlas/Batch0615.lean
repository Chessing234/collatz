import Collatz.Research.DescentIntervals.Classifier

namespace Collatz.Research.PassageAtlas.Batch0615

open Collatz.Research.DescentIntervals

set_option maxRecDepth 20000
set_option maxHeartbeats 0

/-- Complete interval computation for depth 15, residue 20119. -/
theorem bounds_15_20119 : exactInterval 15 20119 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_20119 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 20119) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_20119 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_20119 : oddCount 20119 15 = 6 ∧ acceleratedOrbit 15 20119 = 449 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_20119 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 20119) = 3 ^ 6 * m + 449 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_20119.1, data_15_20119.2]

/-- Complete interval computation for depth 15, residue 20120. -/
theorem bounds_15_20120 : exactInterval 15 20120 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_20120 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 20120) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_20120 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_20120 : oddCount 20120 15 = 6 ∧ acceleratedOrbit 15 20120 = 448 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_20120 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 20120) = 3 ^ 6 * m + 448 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_20120.1, data_15_20120.2]

/-- Complete interval computation for depth 15, residue 20121. -/
theorem bounds_15_20121 : exactInterval 15 20121 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_20121 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 20121) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_20121 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_20121 : oddCount 20121 15 = 9 ∧ acceleratedOrbit 15 20121 = 12089 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_20121 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 20121) = 3 ^ 9 * m + 12089 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_20121.1, data_15_20121.2]

/-- Complete interval computation for depth 15, residue 20122. -/
theorem bounds_15_20122 : exactInterval 15 20122 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_20122 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 20122) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_20122 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_20122 : oddCount 20122 15 = 6 ∧ acceleratedOrbit 15 20122 = 448 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_20122 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 20122) = 3 ^ 6 * m + 448 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_20122.1, data_15_20122.2]

/-- Complete interval computation for depth 15, residue 20123. -/
theorem bounds_15_20123 : exactInterval 15 20123 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_20123 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 20123) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_20123 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_20123 : oddCount 20123 15 = 11 ∧ acceleratedOrbit 15 20123 = 108796 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_20123 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 20123) = 3 ^ 11 * m + 108796 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_20123.1, data_15_20123.2]

/-- Complete interval computation for depth 15, residue 20124. -/
theorem bounds_15_20124 : exactInterval 15 20124 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_20124 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 20124) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_20124 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_20124 : oddCount 20124 15 = 8 ∧ acceleratedOrbit 15 20124 = 4031 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_20124 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 20124) = 3 ^ 8 * m + 4031 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_20124.1, data_15_20124.2]

/-- Complete interval computation for depth 15, residue 20125. -/
theorem bounds_15_20125 : exactInterval 15 20125 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_20125 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 20125) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_20125 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_20125 : oddCount 20125 15 = 8 ∧ acceleratedOrbit 15 20125 = 4031 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_20125 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 20125) = 3 ^ 8 * m + 4031 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_20125.1, data_15_20125.2]

/-- Complete interval computation for depth 15, residue 20126. -/
theorem bounds_15_20126 : exactInterval 15 20126 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_20126 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 20126) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_20126 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_20126 : oddCount 20126 15 = 8 ∧ acceleratedOrbit 15 20126 = 4031 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_20126 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 20126) = 3 ^ 8 * m + 4031 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_20126.1, data_15_20126.2]

/-- Complete interval computation for depth 15, residue 20127. -/
theorem bounds_15_20127 : exactInterval 15 20127 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_20127 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 20127) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_20127 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_20127 : oddCount 20127 15 = 10 ∧ acceleratedOrbit 15 20127 = 36272 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_20127 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 20127) = 3 ^ 10 * m + 36272 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_20127.1, data_15_20127.2]

/-- Complete interval computation for depth 15, residue 20128. -/
theorem bounds_15_20128 : exactInterval 15 20128 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_20128 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 20128) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_20128 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_20128 : oddCount 20128 15 = 5 ∧ acceleratedOrbit 15 20128 = 152 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_20128 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 20128) = 3 ^ 5 * m + 152 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_20128.1, data_15_20128.2]

/-- Complete interval computation for depth 15, residue 20129. -/
theorem bounds_15_20129 : exactInterval 15 20129 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_20129 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 20129) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_20129 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_20129 : oddCount 20129 15 = 9 ∧ acceleratedOrbit 15 20129 = 12095 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_20129 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 20129) = 3 ^ 9 * m + 12095 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_20129.1, data_15_20129.2]

/-- Complete interval computation for depth 15, residue 20130. -/
theorem bounds_15_20130 : exactInterval 15 20130 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_20130 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 20130) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_20130 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_20130 : oddCount 20130 15 = 6 ∧ acceleratedOrbit 15 20130 = 448 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_20130 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 20130) = 3 ^ 6 * m + 448 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_20130.1, data_15_20130.2]

/-- Complete interval computation for depth 15, residue 20131. -/
theorem bounds_15_20131 : exactInterval 15 20131 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_20131 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 20131) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_20131 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_20131 : oddCount 20131 15 = 6 ∧ acceleratedOrbit 15 20131 = 448 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_20131 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 20131) = 3 ^ 6 * m + 448 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_20131.1, data_15_20131.2]

/-- Complete interval computation for depth 15, residue 20132. -/
theorem bounds_15_20132 : exactInterval 15 20132 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_20132 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 20132) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_20132 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_20132 : oddCount 20132 15 = 9 ∧ acceleratedOrbit 15 20132 = 12097 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_20132 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 20132) = 3 ^ 9 * m + 12097 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_20132.1, data_15_20132.2]

/-- Complete interval computation for depth 15, residue 20133. -/
theorem bounds_15_20133 : exactInterval 15 20133 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_20133 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 20133) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_20133 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_20133 : oddCount 20133 15 = 9 ∧ acceleratedOrbit 15 20133 = 12097 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_20133 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 20133) = 3 ^ 9 * m + 12097 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_20133.1, data_15_20133.2]

/-- Complete interval computation for depth 15, residue 20134. -/
theorem bounds_15_20134 : exactInterval 15 20134 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_20134 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 20134) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_20134 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_20134 : oddCount 20134 15 = 9 ∧ acceleratedOrbit 15 20134 = 12097 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_20134 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 20134) = 3 ^ 9 * m + 12097 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_20134.1, data_15_20134.2]

/-- Complete interval computation for depth 15, residue 20135. -/
theorem bounds_15_20135 : exactInterval 15 20135 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_20135 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 20135) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_20135 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_20135 : oddCount 20135 15 = 11 ∧ acceleratedOrbit 15 20135 = 108863 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_20135 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 20135) = 3 ^ 11 * m + 108863 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_20135.1, data_15_20135.2]

/-- Complete interval computation for depth 15, residue 20136. -/
theorem bounds_15_20136 : exactInterval 15 20136 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_20136 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 20136) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_20136 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_20136 : oddCount 20136 15 = 5 ∧ acceleratedOrbit 15 20136 = 152 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_20136 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 20136) = 3 ^ 5 * m + 152 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_20136.1, data_15_20136.2]

/-- Complete interval computation for depth 15, residue 20137. -/
theorem bounds_15_20137 : exactInterval 15 20137 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_20137 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 20137) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_20137 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_20137 : oddCount 20137 15 = 11 ∧ acceleratedOrbit 15 20137 = 108872 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_20137 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 20137) = 3 ^ 11 * m + 108872 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_20137.1, data_15_20137.2]

/-- Complete interval computation for depth 15, residue 20138. -/
theorem bounds_15_20138 : exactInterval 15 20138 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_20138 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 20138) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_20138 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_20138 : oddCount 20138 15 = 5 ∧ acceleratedOrbit 15 20138 = 152 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_20138 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 20138) = 3 ^ 5 * m + 152 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_20138.1, data_15_20138.2]

/-- Complete interval computation for depth 15, residue 20139. -/
theorem bounds_15_20139 : exactInterval 15 20139 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_20139 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 20139) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_20139 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_20139 : oddCount 20139 15 = 8 ∧ acceleratedOrbit 15 20139 = 4033 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_20139 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 20139) = 3 ^ 8 * m + 4033 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_20139.1, data_15_20139.2]

/-- Complete interval computation for depth 15, residue 20140. -/
theorem bounds_15_20140 : exactInterval 15 20140 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_20140 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 20140) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_20140 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_20140 : oddCount 20140 15 = 7 ∧ acceleratedOrbit 15 20140 = 1345 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_20140 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 20140) = 3 ^ 7 * m + 1345 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_20140.1, data_15_20140.2]

/-- Complete interval computation for depth 15, residue 20141. -/
theorem bounds_15_20141 : exactInterval 15 20141 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_20141 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 20141) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_20141 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_20141 : oddCount 20141 15 = 7 ∧ acceleratedOrbit 15 20141 = 1345 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_20141 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 20141) = 3 ^ 7 * m + 1345 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_20141.1, data_15_20141.2]

/-- Complete interval computation for depth 15, residue 20142. -/
theorem bounds_15_20142 : exactInterval 15 20142 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_20142 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 20142) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_20142 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_20142 : oddCount 20142 15 = 7 ∧ acceleratedOrbit 15 20142 = 1345 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_20142 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 20142) = 3 ^ 7 * m + 1345 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_20142.1, data_15_20142.2]

/-- Complete interval computation for depth 15, residue 20143. -/
theorem bounds_15_20143 : exactInterval 15 20143 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_20143 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 20143) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_20143 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_20143 : oddCount 20143 15 = 8 ∧ acceleratedOrbit 15 20143 = 4034 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_20143 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 20143) = 3 ^ 8 * m + 4034 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_20143.1, data_15_20143.2]

/-- Complete interval computation for depth 15, residue 20144. -/
theorem bounds_15_20144 : exactInterval 15 20144 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_20144 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 20144) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_20144 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_20144 : oddCount 20144 15 = 8 ∧ acceleratedOrbit 15 20144 = 4040 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_20144 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 20144) = 3 ^ 8 * m + 4040 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_20144.1, data_15_20144.2]

/-- Complete interval computation for depth 15, residue 20145. -/
theorem bounds_15_20145 : exactInterval 15 20145 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_20145 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 20145) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_20145 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_20145 : oddCount 20145 15 = 6 ∧ acceleratedOrbit 15 20145 = 449 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_20145 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 20145) = 3 ^ 6 * m + 449 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_20145.1, data_15_20145.2]

/-- Complete interval computation for depth 15, residue 20146. -/
theorem bounds_15_20146 : exactInterval 15 20146 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_20146 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 20146) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_20146 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_20146 : oddCount 20146 15 = 6 ∧ acceleratedOrbit 15 20146 = 449 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_20146 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 20146) = 3 ^ 6 * m + 449 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_20146.1, data_15_20146.2]

/-- Complete interval computation for depth 15, residue 20147. -/
theorem bounds_15_20147 : exactInterval 15 20147 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_20147 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 20147) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_20147 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_20147 : oddCount 20147 15 = 6 ∧ acceleratedOrbit 15 20147 = 449 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_20147 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 20147) = 3 ^ 6 * m + 449 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_20147.1, data_15_20147.2]

/-- Complete interval computation for depth 15, residue 20148. -/
theorem bounds_15_20148 : exactInterval 15 20148 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_20148 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 20148) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_20148 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_20148 : oddCount 20148 15 = 8 ∧ acceleratedOrbit 15 20148 = 4040 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_20148 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 20148) = 3 ^ 8 * m + 4040 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_20148.1, data_15_20148.2]

/-- Complete interval computation for depth 15, residue 20149. -/
theorem bounds_15_20149 : exactInterval 15 20149 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_20149 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 20149) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_20149 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_20149 : oddCount 20149 15 = 8 ∧ acceleratedOrbit 15 20149 = 4040 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_20149 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 20149) = 3 ^ 8 * m + 4040 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_20149.1, data_15_20149.2]

/-- Complete interval computation for depth 15, residue 20150. -/
theorem bounds_15_20150 : exactInterval 15 20150 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_20150 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 20150) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_20150 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_20150 : oddCount 20150 15 = 9 ∧ acceleratedOrbit 15 20150 = 12106 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_20150 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 20150) = 3 ^ 9 * m + 12106 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_20150.1, data_15_20150.2]

/-- Complete interval computation for depth 15, residue 20151. -/
theorem bounds_15_20151 : exactInterval 15 20151 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_20151 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 20151) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_20151 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_20151 : oddCount 20151 15 = 9 ∧ acceleratedOrbit 15 20151 = 12106 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_20151 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 20151) = 3 ^ 9 * m + 12106 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_20151.1, data_15_20151.2]

end Collatz.Research.PassageAtlas.Batch0615
