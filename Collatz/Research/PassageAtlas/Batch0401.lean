import Collatz.Research.DescentIntervals.Classifier

namespace Collatz.Research.PassageAtlas.Batch0401

open Collatz.Research.DescentIntervals

set_option maxRecDepth 20000
set_option maxHeartbeats 0

/-- Complete interval computation for depth 15, residue 13107. -/
theorem bounds_15_13107 : exactInterval 15 13107 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_13107 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 13107) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_13107 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_13107 : oddCount 13107 15 = 6 ∧ acceleratedOrbit 15 13107 = 292 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_13107 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 13107) = 3 ^ 6 * m + 292 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_13107.1, data_15_13107.2]

/-- Complete interval computation for depth 15, residue 13108. -/
theorem bounds_15_13108 : exactInterval 15 13108 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_13108 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 13108) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_13108 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_13108 : oddCount 13108 15 = 5 ∧ acceleratedOrbit 15 13108 = 98 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_13108 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 13108) = 3 ^ 5 * m + 98 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_13108.1, data_15_13108.2]

/-- Complete interval computation for depth 15, residue 13109. -/
theorem bounds_15_13109 : exactInterval 15 13109 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_13109 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 13109) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_13109 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_13109 : oddCount 13109 15 = 5 ∧ acceleratedOrbit 15 13109 = 98 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_13109 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 13109) = 3 ^ 5 * m + 98 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_13109.1, data_15_13109.2]

/-- Complete interval computation for depth 15, residue 13110. -/
theorem bounds_15_13110 : exactInterval 15 13110 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_13110 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 13110) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_13110 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_13110 : oddCount 13110 15 = 9 ∧ acceleratedOrbit 15 13110 = 7877 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_13110 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 13110) = 3 ^ 9 * m + 7877 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_13110.1, data_15_13110.2]

/-- Complete interval computation for depth 15, residue 13111. -/
theorem bounds_15_13111 : exactInterval 15 13111 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_13111 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 13111) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_13111 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_13111 : oddCount 13111 15 = 9 ∧ acceleratedOrbit 15 13111 = 7877 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_13111 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 13111) = 3 ^ 9 * m + 7877 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_13111.1, data_15_13111.2]

/-- Complete interval computation for depth 15, residue 13112. -/
theorem bounds_15_13112 : exactInterval 15 13112 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_13112 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 13112) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_13112 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_13112 : oddCount 13112 15 = 9 ∧ acceleratedOrbit 15 13112 = 7883 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_13112 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 13112) = 3 ^ 9 * m + 7883 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_13112.1, data_15_13112.2]

/-- Complete interval computation for depth 15, residue 13113. -/
theorem bounds_15_13113 : exactInterval 15 13113 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_13113 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 13113) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_13113 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_13113 : oddCount 13113 15 = 9 ∧ acceleratedOrbit 15 13113 = 7879 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_13113 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 13113) = 3 ^ 9 * m + 7879 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_13113.1, data_15_13113.2]

/-- Complete interval computation for depth 15, residue 13114. -/
theorem bounds_15_13114 : exactInterval 15 13114 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_13114 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 13114) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_13114 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_13114 : oddCount 13114 15 = 9 ∧ acceleratedOrbit 15 13114 = 7883 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_13114 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 13114) = 3 ^ 9 * m + 7883 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_13114.1, data_15_13114.2]

/-- Complete interval computation for depth 15, residue 13115. -/
theorem bounds_15_13115 : exactInterval 15 13115 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_13115 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 13115) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_13115 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_13115 : oddCount 13115 15 = 9 ∧ acceleratedOrbit 15 13115 = 7883 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_13115 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 13115) = 3 ^ 9 * m + 7883 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_13115.1, data_15_13115.2]

/-- Complete interval computation for depth 15, residue 13116. -/
theorem bounds_15_13116 : exactInterval 15 13116 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_13116 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 13116) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_13116 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_13116 : oddCount 13116 15 = 9 ∧ acceleratedOrbit 15 13116 = 7883 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_13116 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 13116) = 3 ^ 9 * m + 7883 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_13116.1, data_15_13116.2]

/-- Complete interval computation for depth 15, residue 13117. -/
theorem bounds_15_13117 : exactInterval 15 13117 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_13117 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 13117) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_13117 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_13117 : oddCount 13117 15 = 9 ∧ acceleratedOrbit 15 13117 = 7883 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_13117 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 13117) = 3 ^ 9 * m + 7883 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_13117.1, data_15_13117.2]

/-- Complete interval computation for depth 15, residue 13118. -/
theorem bounds_15_13118 : exactInterval 15 13118 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_13118 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 13118) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_13118 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_13118 : oddCount 13118 15 = 8 ∧ acceleratedOrbit 15 13118 = 2627 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_13118 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 13118) = 3 ^ 8 * m + 2627 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_13118.1, data_15_13118.2]

/-- Complete interval computation for depth 15, residue 13119. -/
theorem bounds_15_13119 : exactInterval 15 13119 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_13119 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 13119) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_13119 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_13119 : oddCount 13119 15 = 8 ∧ acceleratedOrbit 15 13119 = 2627 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_13119 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 13119) = 3 ^ 8 * m + 2627 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_13119.1, data_15_13119.2]

/-- Complete interval computation for depth 15, residue 13120. -/
theorem bounds_15_13120 : exactInterval 15 13120 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_13120 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 13120) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_13120 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_13120 : oddCount 13120 15 = 3 ∧ acceleratedOrbit 15 13120 = 11 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_13120 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 13120) = 3 ^ 3 * m + 11 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_13120.1, data_15_13120.2]

/-- Complete interval computation for depth 15, residue 13121. -/
theorem bounds_15_13121 : exactInterval 15 13121 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_13121 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 13121) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_13121 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_13121 : oddCount 13121 15 = 5 ∧ acceleratedOrbit 15 13121 = 98 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_13121 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 13121) = 3 ^ 5 * m + 98 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_13121.1, data_15_13121.2]

/-- Complete interval computation for depth 15, residue 13122. -/
theorem bounds_15_13122 : exactInterval 15 13122 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_13122 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 13122) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_13122 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_13122 : oddCount 13122 15 = 8 ∧ acceleratedOrbit 15 13122 = 2629 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_13122 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 13122) = 3 ^ 8 * m + 2629 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_13122.1, data_15_13122.2]

/-- Complete interval computation for depth 15, residue 13123. -/
theorem bounds_15_13123 : exactInterval 15 13123 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_13123 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 13123) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_13123 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_13123 : oddCount 13123 15 = 8 ∧ acceleratedOrbit 15 13123 = 2629 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_13123 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 13123) = 3 ^ 8 * m + 2629 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_13123.1, data_15_13123.2]

/-- Complete interval computation for depth 15, residue 13124. -/
theorem bounds_15_13124 : exactInterval 15 13124 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_13124 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 13124) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_13124 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_13124 : oddCount 13124 15 = 8 ∧ acceleratedOrbit 15 13124 = 2632 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_13124 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 13124) = 3 ^ 8 * m + 2632 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_13124.1, data_15_13124.2]

/-- Complete interval computation for depth 15, residue 13125. -/
theorem bounds_15_13125 : exactInterval 15 13125 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_13125 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 13125) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_13125 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_13125 : oddCount 13125 15 = 8 ∧ acceleratedOrbit 15 13125 = 2632 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_13125 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 13125) = 3 ^ 8 * m + 2632 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_13125.1, data_15_13125.2]

/-- Complete interval computation for depth 15, residue 13126. -/
theorem bounds_15_13126 : exactInterval 15 13126 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_13126 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 13126) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_13126 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_13126 : oddCount 13126 15 = 8 ∧ acceleratedOrbit 15 13126 = 2632 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_13126 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 13126) = 3 ^ 8 * m + 2632 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_13126.1, data_15_13126.2]

/-- Complete interval computation for depth 15, residue 13127. -/
theorem bounds_15_13127 : exactInterval 15 13127 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_13127 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 13127) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_13127 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_13127 : oddCount 13127 15 = 11 ∧ acceleratedOrbit 15 13127 = 70976 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_13127 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 13127) = 3 ^ 11 * m + 70976 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_13127.1, data_15_13127.2]

/-- Complete interval computation for depth 15, residue 13128. -/
theorem bounds_15_13128 : exactInterval 15 13128 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_13128 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 13128) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_13128 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_13128 : oddCount 13128 15 = 8 ∧ acceleratedOrbit 15 13128 = 2632 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_13128 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 13128) = 3 ^ 8 * m + 2632 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_13128.1, data_15_13128.2]

/-- Complete interval computation for depth 15, residue 13129. -/
theorem bounds_15_13129 : exactInterval 15 13129 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_13129 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 13129) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_13129 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_13129 : oddCount 13129 15 = 7 ∧ acceleratedOrbit 15 13129 = 877 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_13129 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 13129) = 3 ^ 7 * m + 877 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_13129.1, data_15_13129.2]

/-- Complete interval computation for depth 15, residue 13130. -/
theorem bounds_15_13130 : exactInterval 15 13130 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_13130 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 13130) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_13130 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_13130 : oddCount 13130 15 = 8 ∧ acceleratedOrbit 15 13130 = 2632 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_13130 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 13130) = 3 ^ 8 * m + 2632 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_13130.1, data_15_13130.2]

/-- Complete interval computation for depth 15, residue 13131. -/
theorem bounds_15_13131 : exactInterval 15 13131 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_13131 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 13131) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_13131 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_13131 : oddCount 13131 15 = 8 ∧ acceleratedOrbit 15 13131 = 2632 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_13131 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 13131) = 3 ^ 8 * m + 2632 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_13131.1, data_15_13131.2]

/-- Complete interval computation for depth 15, residue 13132. -/
theorem bounds_15_13132 : exactInterval 15 13132 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_13132 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 13132) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_13132 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_13132 : oddCount 13132 15 = 8 ∧ acceleratedOrbit 15 13132 = 2632 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_13132 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 13132) = 3 ^ 8 * m + 2632 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_13132.1, data_15_13132.2]

/-- Complete interval computation for depth 15, residue 13133. -/
theorem bounds_15_13133 : exactInterval 15 13133 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_13133 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 13133) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_13133 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_13133 : oddCount 13133 15 = 8 ∧ acceleratedOrbit 15 13133 = 2632 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_13133 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 13133) = 3 ^ 8 * m + 2632 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_13133.1, data_15_13133.2]

/-- Complete interval computation for depth 15, residue 13134. -/
theorem bounds_15_13134 : exactInterval 15 13134 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_13134 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 13134) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_13134 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_13134 : oddCount 13134 15 = 7 ∧ acceleratedOrbit 15 13134 = 877 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_13134 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 13134) = 3 ^ 7 * m + 877 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_13134.1, data_15_13134.2]

/-- Complete interval computation for depth 15, residue 13135. -/
theorem bounds_15_13135 : exactInterval 15 13135 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_13135 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 13135) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_13135 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_13135 : oddCount 13135 15 = 7 ∧ acceleratedOrbit 15 13135 = 877 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_13135 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 13135) = 3 ^ 7 * m + 877 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_13135.1, data_15_13135.2]

/-- Complete interval computation for depth 15, residue 13136. -/
theorem bounds_15_13136 : exactInterval 15 13136 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_13136 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 13136) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_13136 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_13136 : oddCount 13136 15 = 3 ∧ acceleratedOrbit 15 13136 = 11 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_13136 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 13136) = 3 ^ 3 * m + 11 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_13136.1, data_15_13136.2]

/-- Complete interval computation for depth 15, residue 13137. -/
theorem bounds_15_13137 : exactInterval 15 13137 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_13137 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 13137) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_13137 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_13137 : oddCount 13137 15 = 9 ∧ acceleratedOrbit 15 13137 = 7894 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_13137 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 13137) = 3 ^ 9 * m + 7894 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_13137.1, data_15_13137.2]

/-- Complete interval computation for depth 15, residue 13138. -/
theorem bounds_15_13138 : exactInterval 15 13138 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_13138 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 13138) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_13138 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_13138 : oddCount 13138 15 = 9 ∧ acceleratedOrbit 15 13138 = 7894 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_13138 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 13138) = 3 ^ 9 * m + 7894 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_13138.1, data_15_13138.2]

end Collatz.Research.PassageAtlas.Batch0401
