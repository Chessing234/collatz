import Collatz.Research.DescentIntervals.Classifier

namespace Collatz.Research.PassageAtlas.Batch0523

open Collatz.Research.DescentIntervals

set_option maxRecDepth 20000
set_option maxHeartbeats 0

/-- Complete interval computation for depth 15, residue 17104. -/
theorem bounds_15_17104 : exactInterval 15 17104 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_17104 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 17104) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_17104 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_17104 : oddCount 17104 15 = 5 ∧ acceleratedOrbit 15 17104 = 128 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_17104 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 17104) = 3 ^ 5 * m + 128 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_17104.1, data_15_17104.2]

/-- Complete interval computation for depth 15, residue 17105. -/
theorem bounds_15_17105 : exactInterval 15 17105 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_17105 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 17105) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_17105 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_17105 : oddCount 17105 15 = 8 ∧ acceleratedOrbit 15 17105 = 3428 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_17105 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 17105) = 3 ^ 8 * m + 3428 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_17105.1, data_15_17105.2]

/-- Complete interval computation for depth 15, residue 17106. -/
theorem bounds_15_17106 : exactInterval 15 17106 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_17106 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 17106) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_17106 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_17106 : oddCount 17106 15 = 8 ∧ acceleratedOrbit 15 17106 = 3428 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_17106 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 17106) = 3 ^ 8 * m + 3428 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_17106.1, data_15_17106.2]

/-- Complete interval computation for depth 15, residue 17107. -/
theorem bounds_15_17107 : exactInterval 15 17107 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_17107 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 17107) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_17107 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_17107 : oddCount 17107 15 = 8 ∧ acceleratedOrbit 15 17107 = 3428 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_17107 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 17107) = 3 ^ 8 * m + 3428 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_17107.1, data_15_17107.2]

/-- Complete interval computation for depth 15, residue 17108. -/
theorem bounds_15_17108 : exactInterval 15 17108 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_17108 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 17108) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_17108 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_17108 : oddCount 17108 15 = 5 ∧ acceleratedOrbit 15 17108 = 128 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_17108 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 17108) = 3 ^ 5 * m + 128 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_17108.1, data_15_17108.2]

/-- Complete interval computation for depth 15, residue 17109. -/
theorem bounds_15_17109 : exactInterval 15 17109 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_17109 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 17109) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_17109 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_17109 : oddCount 17109 15 = 5 ∧ acceleratedOrbit 15 17109 = 128 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_17109 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 17109) = 3 ^ 5 * m + 128 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_17109.1, data_15_17109.2]

/-- Complete interval computation for depth 15, residue 17110. -/
theorem bounds_15_17110 : exactInterval 15 17110 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_17110 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 17110) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_17110 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_17110 : oddCount 17110 15 = 8 ∧ acceleratedOrbit 15 17110 = 3428 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_17110 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 17110) = 3 ^ 8 * m + 3428 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_17110.1, data_15_17110.2]

/-- Complete interval computation for depth 15, residue 17111. -/
theorem bounds_15_17111 : exactInterval 15 17111 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_17111 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 17111) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_17111 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_17111 : oddCount 17111 15 = 8 ∧ acceleratedOrbit 15 17111 = 3428 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_17111 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 17111) = 3 ^ 8 * m + 3428 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_17111.1, data_15_17111.2]

/-- Complete interval computation for depth 15, residue 17112. -/
theorem bounds_15_17112 : exactInterval 15 17112 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_17112 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 17112) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_17112 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_17112 : oddCount 17112 15 = 10 ∧ acceleratedOrbit 15 17112 = 30860 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_17112 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 17112) = 3 ^ 10 * m + 30860 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_17112.1, data_15_17112.2]

/-- Complete interval computation for depth 15, residue 17113. -/
theorem bounds_15_17113 : exactInterval 15 17113 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_17113 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 17113) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_17113 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_17113 : oddCount 17113 15 = 5 ∧ acceleratedOrbit 15 17113 = 127 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_17113 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 17113) = 3 ^ 5 * m + 127 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_17113.1, data_15_17113.2]

/-- Complete interval computation for depth 15, residue 17114. -/
theorem bounds_15_17114 : exactInterval 15 17114 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_17114 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 17114) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_17114 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_17114 : oddCount 17114 15 = 10 ∧ acceleratedOrbit 15 17114 = 30860 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_17114 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 17114) = 3 ^ 10 * m + 30860 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_17114.1, data_15_17114.2]

/-- Complete interval computation for depth 15, residue 17115. -/
theorem bounds_15_17115 : exactInterval 15 17115 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_17115 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 17115) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_17115 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_17115 : oddCount 17115 15 = 9 ∧ acceleratedOrbit 15 17115 = 10282 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_17115 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 17115) = 3 ^ 9 * m + 10282 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_17115.1, data_15_17115.2]

/-- Complete interval computation for depth 15, residue 17116. -/
theorem bounds_15_17116 : exactInterval 15 17116 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_17116 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 17116) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_17116 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_17116 : oddCount 17116 15 = 10 ∧ acceleratedOrbit 15 17116 = 30860 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_17116 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 17116) = 3 ^ 10 * m + 30860 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_17116.1, data_15_17116.2]

/-- Complete interval computation for depth 15, residue 17117. -/
theorem bounds_15_17117 : exactInterval 15 17117 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_17117 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 17117) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_17117 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_17117 : oddCount 17117 15 = 10 ∧ acceleratedOrbit 15 17117 = 30860 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_17117 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 17117) = 3 ^ 10 * m + 30860 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_17117.1, data_15_17117.2]

/-- Complete interval computation for depth 15, residue 17118. -/
theorem bounds_15_17118 : exactInterval 15 17118 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_17118 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 17118) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_17118 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_17118 : oddCount 17118 15 = 9 ∧ acceleratedOrbit 15 17118 = 10286 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_17118 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 17118) = 3 ^ 9 * m + 10286 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_17118.1, data_15_17118.2]

/-- Complete interval computation for depth 15, residue 17119. -/
theorem bounds_15_17119 : exactInterval 15 17119 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_17119 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 17119) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_17119 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_17119 : oddCount 17119 15 = 9 ∧ acceleratedOrbit 15 17119 = 10286 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_17119 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 17119) = 3 ^ 9 * m + 10286 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_17119.1, data_15_17119.2]

/-- Complete interval computation for depth 15, residue 17120. -/
theorem bounds_15_17120 : exactInterval 15 17120 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_17120 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 17120) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_17120 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_17120 : oddCount 17120 15 = 5 ∧ acceleratedOrbit 15 17120 = 128 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_17120 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 17120) = 3 ^ 5 * m + 128 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_17120.1, data_15_17120.2]

/-- Complete interval computation for depth 15, residue 17121. -/
theorem bounds_15_17121 : exactInterval 15 17121 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_17121 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 17121) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_17121 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_17121 : oddCount 17121 15 = 11 ∧ acceleratedOrbit 15 17121 = 92573 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_17121 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 17121) = 3 ^ 11 * m + 92573 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_17121.1, data_15_17121.2]

/-- Complete interval computation for depth 15, residue 17122. -/
theorem bounds_15_17122 : exactInterval 15 17122 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_17122 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 17122) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_17122 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_17122 : oddCount 17122 15 = 5 ∧ acceleratedOrbit 15 17122 = 128 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_17122 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 17122) = 3 ^ 5 * m + 128 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_17122.1, data_15_17122.2]

/-- Complete interval computation for depth 15, residue 17123. -/
theorem bounds_15_17123 : exactInterval 15 17123 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_17123 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 17123) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_17123 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_17123 : oddCount 17123 15 = 5 ∧ acceleratedOrbit 15 17123 = 128 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_17123 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 17123) = 3 ^ 5 * m + 128 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_17123.1, data_15_17123.2]

/-- Complete interval computation for depth 15, residue 17124. -/
theorem bounds_15_17124 : exactInterval 15 17124 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_17124 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 17124) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_17124 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_17124 : oddCount 17124 15 = 7 ∧ acceleratedOrbit 15 17124 = 1144 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_17124 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 17124) = 3 ^ 7 * m + 1144 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_17124.1, data_15_17124.2]

/-- Complete interval computation for depth 15, residue 17125. -/
theorem bounds_15_17125 : exactInterval 15 17125 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_17125 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 17125) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_17125 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_17125 : oddCount 17125 15 = 7 ∧ acceleratedOrbit 15 17125 = 1144 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_17125 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 17125) = 3 ^ 7 * m + 1144 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_17125.1, data_15_17125.2]

/-- Complete interval computation for depth 15, residue 17126. -/
theorem bounds_15_17126 : exactInterval 15 17126 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_17126 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 17126) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_17126 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_17126 : oddCount 17126 15 = 7 ∧ acceleratedOrbit 15 17126 = 1144 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_17126 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 17126) = 3 ^ 7 * m + 1144 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_17126.1, data_15_17126.2]

/-- Complete interval computation for depth 15, residue 17127. -/
theorem bounds_15_17127 : exactInterval 15 17127 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_17127 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 17127) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_17127 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_17127 : oddCount 17127 15 = 10 ∧ acceleratedOrbit 15 17127 = 30866 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_17127 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 17127) = 3 ^ 10 * m + 30866 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_17127.1, data_15_17127.2]

/-- Complete interval computation for depth 15, residue 17128. -/
theorem bounds_15_17128 : exactInterval 15 17128 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_17128 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 17128) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_17128 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_17128 : oddCount 17128 15 = 5 ∧ acceleratedOrbit 15 17128 = 128 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_17128 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 17128) = 3 ^ 5 * m + 128 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_17128.1, data_15_17128.2]

/-- Complete interval computation for depth 15, residue 17129. -/
theorem bounds_15_17129 : exactInterval 15 17129 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_17129 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 17129) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_17129 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_17129 : oddCount 17129 15 = 10 ∧ acceleratedOrbit 15 17129 = 30871 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_17129 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 17129) = 3 ^ 10 * m + 30871 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_17129.1, data_15_17129.2]

/-- Complete interval computation for depth 15, residue 17130. -/
theorem bounds_15_17130 : exactInterval 15 17130 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_17130 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 17130) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_17130 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_17130 : oddCount 17130 15 = 5 ∧ acceleratedOrbit 15 17130 = 128 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_17130 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 17130) = 3 ^ 5 * m + 128 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_17130.1, data_15_17130.2]

/-- Complete interval computation for depth 15, residue 17131. -/
theorem bounds_15_17131 : exactInterval 15 17131 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_17131 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 17131) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_17131 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_17131 : oddCount 17131 15 = 8 ∧ acceleratedOrbit 15 17131 = 3431 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_17131 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 17131) = 3 ^ 8 * m + 3431 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_17131.1, data_15_17131.2]

/-- Complete interval computation for depth 15, residue 17132. -/
theorem bounds_15_17132 : exactInterval 15 17132 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_17132 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 17132) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_17132 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_17132 : oddCount 17132 15 = 7 ∧ acceleratedOrbit 15 17132 = 1144 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_17132 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 17132) = 3 ^ 7 * m + 1144 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_17132.1, data_15_17132.2]

/-- Complete interval computation for depth 15, residue 17133. -/
theorem bounds_15_17133 : exactInterval 15 17133 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_17133 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 17133) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_17133 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_17133 : oddCount 17133 15 = 7 ∧ acceleratedOrbit 15 17133 = 1144 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_17133 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 17133) = 3 ^ 7 * m + 1144 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_17133.1, data_15_17133.2]

/-- Complete interval computation for depth 15, residue 17134. -/
theorem bounds_15_17134 : exactInterval 15 17134 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_17134 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 17134) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_17134 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_17134 : oddCount 17134 15 = 7 ∧ acceleratedOrbit 15 17134 = 1144 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_17134 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 17134) = 3 ^ 7 * m + 1144 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_17134.1, data_15_17134.2]

/-- Complete interval computation for depth 15, residue 17135. -/
theorem bounds_15_17135 : exactInterval 15 17135 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_17135 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 17135) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_17135 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_17135 : oddCount 17135 15 = 10 ∧ acceleratedOrbit 15 17135 = 30880 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_17135 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 17135) = 3 ^ 10 * m + 30880 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_17135.1, data_15_17135.2]

/-- Complete interval computation for depth 15, residue 17136. -/
theorem bounds_15_17136 : exactInterval 15 17136 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_17136 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 17136) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_17136 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_17136 : oddCount 17136 15 = 7 ∧ acceleratedOrbit 15 17136 = 1145 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_17136 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 17136) = 3 ^ 7 * m + 1145 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_17136.1, data_15_17136.2]

end Collatz.Research.PassageAtlas.Batch0523
