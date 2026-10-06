import Collatz.Research.DescentIntervals.Classifier

namespace Collatz.Research.PassageAtlas.Batch0462

open Collatz.Research.DescentIntervals

set_option maxRecDepth 20000
set_option maxHeartbeats 0

/-- Complete interval computation for depth 15, residue 15106. -/
theorem bounds_15_15106 : exactInterval 15 15106 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_15106 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 15106) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_15106 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_15106 : oddCount 15106 15 = 7 ∧ acceleratedOrbit 15 15106 = 1009 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_15106 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 15106) = 3 ^ 7 * m + 1009 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_15106.1, data_15_15106.2]

/-- Complete interval computation for depth 15, residue 15107. -/
theorem bounds_15_15107 : exactInterval 15 15107 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_15107 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 15107) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_15107 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_15107 : oddCount 15107 15 = 7 ∧ acceleratedOrbit 15 15107 = 1009 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_15107 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 15107) = 3 ^ 7 * m + 1009 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_15107.1, data_15_15107.2]

/-- Complete interval computation for depth 15, residue 15108. -/
theorem bounds_15_15108 : exactInterval 15 15108 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_15108 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 15108) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_15108 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_15108 : oddCount 15108 15 = 6 ∧ acceleratedOrbit 15 15108 = 337 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_15108 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 15108) = 3 ^ 6 * m + 337 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_15108.1, data_15_15108.2]

/-- Complete interval computation for depth 15, residue 15109. -/
theorem bounds_15_15109 : exactInterval 15 15109 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_15109 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 15109) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_15109 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_15109 : oddCount 15109 15 = 6 ∧ acceleratedOrbit 15 15109 = 337 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_15109 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 15109) = 3 ^ 6 * m + 337 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_15109.1, data_15_15109.2]

/-- Complete interval computation for depth 15, residue 15110. -/
theorem bounds_15_15110 : exactInterval 15 15110 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_15110 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 15110) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_15110 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_15110 : oddCount 15110 15 = 6 ∧ acceleratedOrbit 15 15110 = 337 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_15110 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 15110) = 3 ^ 6 * m + 337 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_15110.1, data_15_15110.2]

/-- Complete interval computation for depth 15, residue 15111. -/
theorem bounds_15_15111 : exactInterval 15 15111 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_15111 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 15111) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_15111 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_15111 : oddCount 15111 15 = 10 ∧ acceleratedOrbit 15 15111 = 27236 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_15111 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 15111) = 3 ^ 10 * m + 27236 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_15111.1, data_15_15111.2]

/-- Complete interval computation for depth 15, residue 15112. -/
theorem bounds_15_15112 : exactInterval 15 15112 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_15112 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 15112) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_15112 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_15112 : oddCount 15112 15 = 7 ∧ acceleratedOrbit 15 15112 = 1010 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_15112 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 15112) = 3 ^ 7 * m + 1010 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_15112.1, data_15_15112.2]

/-- Complete interval computation for depth 15, residue 15113. -/
theorem bounds_15_15113 : exactInterval 15 15113 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_15113 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 15113) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_15113 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_15113 : oddCount 15113 15 = 9 ∧ acceleratedOrbit 15 15113 = 9080 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_15113 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 15113) = 3 ^ 9 * m + 9080 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_15113.1, data_15_15113.2]

/-- Complete interval computation for depth 15, residue 15114. -/
theorem bounds_15_15114 : exactInterval 15 15114 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_15114 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 15114) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_15114 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_15114 : oddCount 15114 15 = 7 ∧ acceleratedOrbit 15 15114 = 1010 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_15114 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 15114) = 3 ^ 7 * m + 1010 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_15114.1, data_15_15114.2]

/-- Complete interval computation for depth 15, residue 15115. -/
theorem bounds_15_15115 : exactInterval 15 15115 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_15115 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 15115) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_15115 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_15115 : oddCount 15115 15 = 9 ∧ acceleratedOrbit 15 15115 = 9082 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_15115 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 15115) = 3 ^ 9 * m + 9082 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_15115.1, data_15_15115.2]

/-- Complete interval computation for depth 15, residue 15116. -/
theorem bounds_15_15116 : exactInterval 15 15116 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_15116 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 15116) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_15116 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_15116 : oddCount 15116 15 = 7 ∧ acceleratedOrbit 15 15116 = 1010 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_15116 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 15116) = 3 ^ 7 * m + 1010 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_15116.1, data_15_15116.2]

/-- Complete interval computation for depth 15, residue 15117. -/
theorem bounds_15_15117 : exactInterval 15 15117 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_15117 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 15117) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_15117 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_15117 : oddCount 15117 15 = 7 ∧ acceleratedOrbit 15 15117 = 1010 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_15117 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 15117) = 3 ^ 7 * m + 1010 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_15117.1, data_15_15117.2]

/-- Complete interval computation for depth 15, residue 15118. -/
theorem bounds_15_15118 : exactInterval 15 15118 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_15118 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 15118) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_15118 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_15118 : oddCount 15118 15 = 6 ∧ acceleratedOrbit 15 15118 = 337 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_15118 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 15118) = 3 ^ 6 * m + 337 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_15118.1, data_15_15118.2]

/-- Complete interval computation for depth 15, residue 15119. -/
theorem bounds_15_15119 : exactInterval 15 15119 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_15119 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 15119) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_15119 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_15119 : oddCount 15119 15 = 6 ∧ acceleratedOrbit 15 15119 = 337 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_15119 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 15119) = 3 ^ 6 * m + 337 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_15119.1, data_15_15119.2]

/-- Complete interval computation for depth 15, residue 15120. -/
theorem bounds_15_15120 : exactInterval 15 15120 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_15120 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 15120) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_15120 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_15120 : oddCount 15120 15 = 4 ∧ acceleratedOrbit 15 15120 = 38 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_15120 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 15120) = 3 ^ 4 * m + 38 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_15120.1, data_15_15120.2]

/-- Complete interval computation for depth 15, residue 15121. -/
theorem bounds_15_15121 : exactInterval 15 15121 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_15121 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 15121) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_15121 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_15121 : oddCount 15121 15 = 7 ∧ acceleratedOrbit 15 15121 = 1010 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_15121 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 15121) = 3 ^ 7 * m + 1010 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_15121.1, data_15_15121.2]

/-- Complete interval computation for depth 15, residue 15122. -/
theorem bounds_15_15122 : exactInterval 15 15122 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_15122 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 15122) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_15122 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_15122 : oddCount 15122 15 = 7 ∧ acceleratedOrbit 15 15122 = 1010 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_15122 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 15122) = 3 ^ 7 * m + 1010 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_15122.1, data_15_15122.2]

/-- Complete interval computation for depth 15, residue 15123. -/
theorem bounds_15_15123 : exactInterval 15 15123 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_15123 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 15123) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_15123 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_15123 : oddCount 15123 15 = 7 ∧ acceleratedOrbit 15 15123 = 1010 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_15123 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 15123) = 3 ^ 7 * m + 1010 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_15123.1, data_15_15123.2]

/-- Complete interval computation for depth 15, residue 15124. -/
theorem bounds_15_15124 : exactInterval 15 15124 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_15124 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 15124) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_15124 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_15124 : oddCount 15124 15 = 4 ∧ acceleratedOrbit 15 15124 = 38 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_15124 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 15124) = 3 ^ 4 * m + 38 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_15124.1, data_15_15124.2]

/-- Complete interval computation for depth 15, residue 15125. -/
theorem bounds_15_15125 : exactInterval 15 15125 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_15125 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 15125) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_15125 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_15125 : oddCount 15125 15 = 4 ∧ acceleratedOrbit 15 15125 = 38 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_15125 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 15125) = 3 ^ 4 * m + 38 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_15125.1, data_15_15125.2]

/-- Complete interval computation for depth 15, residue 15126. -/
theorem bounds_15_15126 : exactInterval 15 15126 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_15126 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 15126) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_15126 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_15126 : oddCount 15126 15 = 7 ∧ acceleratedOrbit 15 15126 = 1010 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_15126 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 15126) = 3 ^ 7 * m + 1010 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_15126.1, data_15_15126.2]

/-- Complete interval computation for depth 15, residue 15127. -/
theorem bounds_15_15127 : exactInterval 15 15127 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_15127 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 15127) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_15127 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_15127 : oddCount 15127 15 = 7 ∧ acceleratedOrbit 15 15127 = 1010 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_15127 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 15127) = 3 ^ 7 * m + 1010 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_15127.1, data_15_15127.2]

/-- Complete interval computation for depth 15, residue 15128. -/
theorem bounds_15_15128 : exactInterval 15 15128 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_15128 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 15128) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_15128 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_15128 : oddCount 15128 15 = 4 ∧ acceleratedOrbit 15 15128 = 38 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_15128 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 15128) = 3 ^ 4 * m + 38 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_15128.1, data_15_15128.2]

/-- Complete interval computation for depth 15, residue 15129. -/
theorem bounds_15_15129 : exactInterval 15 15129 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_15129 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 15129) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_15129 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_15129 : oddCount 15129 15 = 11 ∧ acceleratedOrbit 15 15129 = 81809 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_15129 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 15129) = 3 ^ 11 * m + 81809 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_15129.1, data_15_15129.2]

/-- Complete interval computation for depth 15, residue 15130. -/
theorem bounds_15_15130 : exactInterval 15 15130 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_15130 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 15130) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_15130 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_15130 : oddCount 15130 15 = 4 ∧ acceleratedOrbit 15 15130 = 38 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_15130 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 15130) = 3 ^ 4 * m + 38 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_15130.1, data_15_15130.2]

/-- Complete interval computation for depth 15, residue 15131. -/
theorem bounds_15_15131 : exactInterval 15 15131 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_15131 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 15131) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_15131 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_15131 : oddCount 15131 15 = 12 ∧ acceleratedOrbit 15 15131 = 245423 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_15131 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 15131) = 3 ^ 12 * m + 245423 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_15131.1, data_15_15131.2]

/-- Complete interval computation for depth 15, residue 15132. -/
theorem bounds_15_15132 : exactInterval 15 15132 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_15132 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 15132) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_15132 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_15132 : oddCount 15132 15 = 6 ∧ acceleratedOrbit 15 15132 = 337 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_15132 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 15132) = 3 ^ 6 * m + 337 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_15132.1, data_15_15132.2]

/-- Complete interval computation for depth 15, residue 15133. -/
theorem bounds_15_15133 : exactInterval 15 15133 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_15133 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 15133) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_15133 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_15133 : oddCount 15133 15 = 6 ∧ acceleratedOrbit 15 15133 = 337 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_15133 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 15133) = 3 ^ 6 * m + 337 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_15133.1, data_15_15133.2]

/-- Complete interval computation for depth 15, residue 15134. -/
theorem bounds_15_15134 : exactInterval 15 15134 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_15134 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 15134) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_15134 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_15134 : oddCount 15134 15 = 6 ∧ acceleratedOrbit 15 15134 = 337 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_15134 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 15134) = 3 ^ 6 * m + 337 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_15134.1, data_15_15134.2]

/-- Complete interval computation for depth 15, residue 15135. -/
theorem bounds_15_15135 : exactInterval 15 15135 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_15135 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 15135) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_15135 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_15135 : oddCount 15135 15 = 11 ∧ acceleratedOrbit 15 15135 = 81830 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_15135 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 15135) = 3 ^ 11 * m + 81830 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_15135.1, data_15_15135.2]

/-- Complete interval computation for depth 15, residue 15136. -/
theorem bounds_15_15136 : exactInterval 15 15136 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_15136 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 15136) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_15136 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_15136 : oddCount 15136 15 = 4 ∧ acceleratedOrbit 15 15136 = 38 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_15136 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 15136) = 3 ^ 4 * m + 38 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_15136.1, data_15_15136.2]

/-- Complete interval computation for depth 15, residue 15137. -/
theorem bounds_15_15137 : exactInterval 15 15137 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_15137 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 15137) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_15137 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_15137 : oddCount 15137 15 = 9 ∧ acceleratedOrbit 15 15137 = 9098 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_15137 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 15137) = 3 ^ 9 * m + 9098 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_15137.1, data_15_15137.2]

end Collatz.Research.PassageAtlas.Batch0462
