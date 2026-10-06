import Collatz.Research.DescentIntervals.Classifier

namespace Collatz.Research.PassageAtlas.Batch0645

open Collatz.Research.DescentIntervals

set_option maxRecDepth 20000
set_option maxHeartbeats 0

/-- Complete interval computation for depth 15, residue 21102. -/
theorem bounds_15_21102 : exactInterval 15 21102 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_21102 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 21102) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_21102 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_21102 : oddCount 21102 15 = 8 ∧ acceleratedOrbit 15 21102 = 4226 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_21102 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 21102) = 3 ^ 8 * m + 4226 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_21102.1, data_15_21102.2]

/-- Complete interval computation for depth 15, residue 21103. -/
theorem bounds_15_21103 : exactInterval 15 21103 = ⟨0, none⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_21103 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 21103) 15 ↔ 0 ≤ m := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_21103 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_21103 : oddCount 21103 15 = 9 ∧ acceleratedOrbit 15 21103 = 12677 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_21103 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 21103) = 3 ^ 9 * m + 12677 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_21103.1, data_15_21103.2]

/-- Complete interval computation for depth 15, residue 21104. -/
theorem bounds_15_21104 : exactInterval 15 21104 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_21104 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 21104) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_21104 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_21104 : oddCount 21104 15 = 6 ∧ acceleratedOrbit 15 21104 = 470 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_21104 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 21104) = 3 ^ 6 * m + 470 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_21104.1, data_15_21104.2]

/-- Complete interval computation for depth 15, residue 21105. -/
theorem bounds_15_21105 : exactInterval 15 21105 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_21105 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 21105) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_21105 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_21105 : oddCount 21105 15 = 5 ∧ acceleratedOrbit 15 21105 = 157 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_21105 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 21105) = 3 ^ 5 * m + 157 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_21105.1, data_15_21105.2]

/-- Complete interval computation for depth 15, residue 21106. -/
theorem bounds_15_21106 : exactInterval 15 21106 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_21106 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 21106) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_21106 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_21106 : oddCount 21106 15 = 7 ∧ acceleratedOrbit 15 21106 = 1409 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_21106 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 21106) = 3 ^ 7 * m + 1409 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_21106.1, data_15_21106.2]

/-- Complete interval computation for depth 15, residue 21107. -/
theorem bounds_15_21107 : exactInterval 15 21107 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_21107 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 21107) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_21107 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_21107 : oddCount 21107 15 = 7 ∧ acceleratedOrbit 15 21107 = 1409 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_21107 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 21107) = 3 ^ 7 * m + 1409 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_21107.1, data_15_21107.2]

/-- Complete interval computation for depth 15, residue 21108. -/
theorem bounds_15_21108 : exactInterval 15 21108 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_21108 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 21108) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_21108 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_21108 : oddCount 21108 15 = 6 ∧ acceleratedOrbit 15 21108 = 470 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_21108 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 21108) = 3 ^ 6 * m + 470 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_21108.1, data_15_21108.2]

/-- Complete interval computation for depth 15, residue 21109. -/
theorem bounds_15_21109 : exactInterval 15 21109 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_21109 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 21109) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_21109 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_21109 : oddCount 21109 15 = 6 ∧ acceleratedOrbit 15 21109 = 470 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_21109 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 21109) = 3 ^ 6 * m + 470 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_21109.1, data_15_21109.2]

/-- Complete interval computation for depth 15, residue 21110. -/
theorem bounds_15_21110 : exactInterval 15 21110 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_21110 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 21110) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_21110 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_21110 : oddCount 21110 15 = 6 ∧ acceleratedOrbit 15 21110 = 470 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_21110 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 21110) = 3 ^ 6 * m + 470 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_21110.1, data_15_21110.2]

/-- Complete interval computation for depth 15, residue 21111. -/
theorem bounds_15_21111 : exactInterval 15 21111 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_21111 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 21111) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_21111 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_21111 : oddCount 21111 15 = 6 ∧ acceleratedOrbit 15 21111 = 470 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_21111 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 21111) = 3 ^ 6 * m + 470 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_21111.1, data_15_21111.2]

/-- Complete interval computation for depth 15, residue 21112. -/
theorem bounds_15_21112 : exactInterval 15 21112 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_21112 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 21112) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_21112 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_21112 : oddCount 21112 15 = 6 ∧ acceleratedOrbit 15 21112 = 470 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_21112 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 21112) = 3 ^ 6 * m + 470 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_21112.1, data_15_21112.2]

/-- Complete interval computation for depth 15, residue 21113. -/
theorem bounds_15_21113 : exactInterval 15 21113 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_21113 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 21113) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_21113 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_21113 : oddCount 21113 15 = 8 ∧ acceleratedOrbit 15 21113 = 4229 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_21113 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 21113) = 3 ^ 8 * m + 4229 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_21113.1, data_15_21113.2]

/-- Complete interval computation for depth 15, residue 21114. -/
theorem bounds_15_21114 : exactInterval 15 21114 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_21114 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 21114) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_21114 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_21114 : oddCount 21114 15 = 6 ∧ acceleratedOrbit 15 21114 = 470 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_21114 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 21114) = 3 ^ 6 * m + 470 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_21114.1, data_15_21114.2]

/-- Complete interval computation for depth 15, residue 21115. -/
theorem bounds_15_21115 : exactInterval 15 21115 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_21115 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 21115) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_21115 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_21115 : oddCount 21115 15 = 8 ∧ acceleratedOrbit 15 21115 = 4229 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_21115 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 21115) = 3 ^ 8 * m + 4229 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_21115.1, data_15_21115.2]

/-- Complete interval computation for depth 15, residue 21116. -/
theorem bounds_15_21116 : exactInterval 15 21116 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_21116 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 21116) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_21116 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_21116 : oddCount 21116 15 = 10 ∧ acceleratedOrbit 15 21116 = 38060 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_21116 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 21116) = 3 ^ 10 * m + 38060 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_21116.1, data_15_21116.2]

/-- Complete interval computation for depth 15, residue 21117. -/
theorem bounds_15_21117 : exactInterval 15 21117 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_21117 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 21117) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_21117 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_21117 : oddCount 21117 15 = 10 ∧ acceleratedOrbit 15 21117 = 38060 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_21117 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 21117) = 3 ^ 10 * m + 38060 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_21117.1, data_15_21117.2]

/-- Complete interval computation for depth 15, residue 21118. -/
theorem bounds_15_21118 : exactInterval 15 21118 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_21118 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 21118) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_21118 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_21118 : oddCount 21118 15 = 10 ∧ acceleratedOrbit 15 21118 = 38060 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_21118 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 21118) = 3 ^ 10 * m + 38060 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_21118.1, data_15_21118.2]

/-- Complete interval computation for depth 15, residue 21119. -/
theorem bounds_15_21119 : exactInterval 15 21119 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_21119 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 21119) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_21119 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_21119 : oddCount 21119 15 = 10 ∧ acceleratedOrbit 15 21119 = 38059 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_21119 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 21119) = 3 ^ 10 * m + 38059 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_21119.1, data_15_21119.2]

/-- Complete interval computation for depth 15, residue 21120. -/
theorem bounds_15_21120 : exactInterval 15 21120 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_21120 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 21120) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_21120 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_21120 : oddCount 21120 15 = 5 ∧ acceleratedOrbit 15 21120 = 161 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_21120 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 21120) = 3 ^ 5 * m + 161 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_21120.1, data_15_21120.2]

/-- Complete interval computation for depth 15, residue 21121. -/
theorem bounds_15_21121 : exactInterval 15 21121 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_21121 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 21121) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_21121 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_21121 : oddCount 21121 15 = 10 ∧ acceleratedOrbit 15 21121 = 38069 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_21121 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 21121) = 3 ^ 10 * m + 38069 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_21121.1, data_15_21121.2]

/-- Complete interval computation for depth 15, residue 21122. -/
theorem bounds_15_21122 : exactInterval 15 21122 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_21122 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 21122) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_21122 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_21122 : oddCount 21122 15 = 5 ∧ acceleratedOrbit 15 21122 = 157 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_21122 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 21122) = 3 ^ 5 * m + 157 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_21122.1, data_15_21122.2]

/-- Complete interval computation for depth 15, residue 21123. -/
theorem bounds_15_21123 : exactInterval 15 21123 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_21123 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 21123) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_21123 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_21123 : oddCount 21123 15 = 5 ∧ acceleratedOrbit 15 21123 = 157 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_21123 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 21123) = 3 ^ 5 * m + 157 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_21123.1, data_15_21123.2]

/-- Complete interval computation for depth 15, residue 21124. -/
theorem bounds_15_21124 : exactInterval 15 21124 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_21124 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 21124) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_21124 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_21124 : oddCount 21124 15 = 8 ∧ acceleratedOrbit 15 21124 = 4232 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_21124 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 21124) = 3 ^ 8 * m + 4232 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_21124.1, data_15_21124.2]

/-- Complete interval computation for depth 15, residue 21125. -/
theorem bounds_15_21125 : exactInterval 15 21125 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_21125 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 21125) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_21125 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_21125 : oddCount 21125 15 = 8 ∧ acceleratedOrbit 15 21125 = 4232 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_21125 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 21125) = 3 ^ 8 * m + 4232 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_21125.1, data_15_21125.2]

/-- Complete interval computation for depth 15, residue 21126. -/
theorem bounds_15_21126 : exactInterval 15 21126 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_21126 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 21126) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_21126 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_21126 : oddCount 21126 15 = 8 ∧ acceleratedOrbit 15 21126 = 4232 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_21126 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 21126) = 3 ^ 8 * m + 4232 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_21126.1, data_15_21126.2]

/-- Complete interval computation for depth 15, residue 21127. -/
theorem bounds_15_21127 : exactInterval 15 21127 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_21127 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 21127) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_21127 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_21127 : oddCount 21127 15 = 8 ∧ acceleratedOrbit 15 21127 = 4232 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_21127 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 21127) = 3 ^ 8 * m + 4232 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_21127.1, data_15_21127.2]

/-- Complete interval computation for depth 15, residue 21128. -/
theorem bounds_15_21128 : exactInterval 15 21128 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_21128 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 21128) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_21128 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_21128 : oddCount 21128 15 = 8 ∧ acceleratedOrbit 15 21128 = 4238 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_21128 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 21128) = 3 ^ 8 * m + 4238 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_21128.1, data_15_21128.2]

/-- Complete interval computation for depth 15, residue 21129. -/
theorem bounds_15_21129 : exactInterval 15 21129 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_21129 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 21129) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_21129 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_21129 : oddCount 21129 15 = 8 ∧ acceleratedOrbit 15 21129 = 4231 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_21129 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 21129) = 3 ^ 8 * m + 4231 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_21129.1, data_15_21129.2]

/-- Complete interval computation for depth 15, residue 21130. -/
theorem bounds_15_21130 : exactInterval 15 21130 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_21130 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 21130) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_21130 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_21130 : oddCount 21130 15 = 8 ∧ acceleratedOrbit 15 21130 = 4238 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_21130 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 21130) = 3 ^ 8 * m + 4238 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_21130.1, data_15_21130.2]

/-- Complete interval computation for depth 15, residue 21131. -/
theorem bounds_15_21131 : exactInterval 15 21131 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_21131 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 21131) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_21131 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_21131 : oddCount 21131 15 = 8 ∧ acceleratedOrbit 15 21131 = 4232 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_21131 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 21131) = 3 ^ 8 * m + 4232 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_21131.1, data_15_21131.2]

/-- Complete interval computation for depth 15, residue 21132. -/
theorem bounds_15_21132 : exactInterval 15 21132 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_21132 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 21132) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_21132 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_21132 : oddCount 21132 15 = 8 ∧ acceleratedOrbit 15 21132 = 4238 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_21132 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 21132) = 3 ^ 8 * m + 4238 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_21132.1, data_15_21132.2]

/-- Complete interval computation for depth 15, residue 21133. -/
theorem bounds_15_21133 : exactInterval 15 21133 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_21133 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 21133) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_21133 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_21133 : oddCount 21133 15 = 8 ∧ acceleratedOrbit 15 21133 = 4238 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_21133 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 21133) = 3 ^ 8 * m + 4238 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_21133.1, data_15_21133.2]

/-- Complete interval computation for depth 15, residue 21134. -/
theorem bounds_15_21134 : exactInterval 15 21134 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_21134 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 21134) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_21134 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_21134 : oddCount 21134 15 = 10 ∧ acceleratedOrbit 15 21134 = 38090 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_21134 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 21134) = 3 ^ 10 * m + 38090 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_21134.1, data_15_21134.2]

end Collatz.Research.PassageAtlas.Batch0645
