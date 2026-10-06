import Collatz.Research.DescentIntervals.Classifier

namespace Collatz.Research.PassageAtlas.Batch0340

open Collatz.Research.DescentIntervals

set_option maxRecDepth 20000
set_option maxHeartbeats 0

/-- Complete interval computation for depth 15, residue 11108. -/
theorem bounds_15_11108 : exactInterval 15 11108 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_11108 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 11108) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_11108 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_11108 : oddCount 11108 15 = 5 ∧ acceleratedOrbit 15 11108 = 83 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_11108 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 11108) = 3 ^ 5 * m + 83 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_11108.1, data_15_11108.2]

/-- Complete interval computation for depth 15, residue 11109. -/
theorem bounds_15_11109 : exactInterval 15 11109 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_11109 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 11109) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_11109 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_11109 : oddCount 11109 15 = 5 ∧ acceleratedOrbit 15 11109 = 83 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_11109 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 11109) = 3 ^ 5 * m + 83 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_11109.1, data_15_11109.2]

/-- Complete interval computation for depth 15, residue 11110. -/
theorem bounds_15_11110 : exactInterval 15 11110 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_11110 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 11110) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_11110 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_11110 : oddCount 11110 15 = 5 ∧ acceleratedOrbit 15 11110 = 83 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_11110 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 11110) = 3 ^ 5 * m + 83 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_11110.1, data_15_11110.2]

/-- Complete interval computation for depth 15, residue 11111. -/
theorem bounds_15_11111 : exactInterval 15 11111 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_11111 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 11111) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_11111 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_11111 : oddCount 11111 15 = 12 ∧ acceleratedOrbit 15 11111 = 180224 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_11111 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 11111) = 3 ^ 12 * m + 180224 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_11111.1, data_15_11111.2]

/-- Complete interval computation for depth 15, residue 11112. -/
theorem bounds_15_11112 : exactInterval 15 11112 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_11112 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 11112) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_11112 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_11112 : oddCount 11112 15 = 6 ∧ acceleratedOrbit 15 11112 = 248 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_11112 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 11112) = 3 ^ 6 * m + 248 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_11112.1, data_15_11112.2]

/-- Complete interval computation for depth 15, residue 11113. -/
theorem bounds_15_11113 : exactInterval 15 11113 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_11113 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 11113) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_11113 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_11113 : oddCount 11113 15 = 10 ∧ acceleratedOrbit 15 11113 = 20033 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_11113 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 11113) = 3 ^ 10 * m + 20033 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_11113.1, data_15_11113.2]

/-- Complete interval computation for depth 15, residue 11114. -/
theorem bounds_15_11114 : exactInterval 15 11114 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_11114 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 11114) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_11114 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_11114 : oddCount 11114 15 = 6 ∧ acceleratedOrbit 15 11114 = 248 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_11114 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 11114) = 3 ^ 6 * m + 248 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_11114.1, data_15_11114.2]

/-- Complete interval computation for depth 15, residue 11115. -/
theorem bounds_15_11115 : exactInterval 15 11115 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_11115 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 11115) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_11115 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_11115 : oddCount 11115 15 = 8 ∧ acceleratedOrbit 15 11115 = 2227 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_11115 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 11115) = 3 ^ 8 * m + 2227 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_11115.1, data_15_11115.2]

/-- Complete interval computation for depth 15, residue 11116. -/
theorem bounds_15_11116 : exactInterval 15 11116 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_11116 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 11116) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_11116 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_11116 : oddCount 11116 15 = 9 ∧ acceleratedOrbit 15 11116 = 6682 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_11116 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 11116) = 3 ^ 9 * m + 6682 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_11116.1, data_15_11116.2]

/-- Complete interval computation for depth 15, residue 11117. -/
theorem bounds_15_11117 : exactInterval 15 11117 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_11117 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 11117) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_11117 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_11117 : oddCount 11117 15 = 9 ∧ acceleratedOrbit 15 11117 = 6682 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_11117 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 11117) = 3 ^ 9 * m + 6682 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_11117.1, data_15_11117.2]

/-- Complete interval computation for depth 15, residue 11118. -/
theorem bounds_15_11118 : exactInterval 15 11118 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_11118 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 11118) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_11118 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_11118 : oddCount 11118 15 = 9 ∧ acceleratedOrbit 15 11118 = 6682 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_11118 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 11118) = 3 ^ 9 * m + 6682 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_11118.1, data_15_11118.2]

/-- Complete interval computation for depth 15, residue 11119. -/
theorem bounds_15_11119 : exactInterval 15 11119 = ⟨0, none⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_11119 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 11119) 15 ↔ 0 ≤ m := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_11119 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_11119 : oddCount 11119 15 = 9 ∧ acceleratedOrbit 15 11119 = 6680 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_11119 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 11119) = 3 ^ 9 * m + 6680 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_11119.1, data_15_11119.2]

/-- Complete interval computation for depth 15, residue 11120. -/
theorem bounds_15_11120 : exactInterval 15 11120 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_11120 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 11120) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_11120 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_11120 : oddCount 11120 15 = 6 ∧ acceleratedOrbit 15 11120 = 248 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_11120 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 11120) = 3 ^ 6 * m + 248 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_11120.1, data_15_11120.2]

/-- Complete interval computation for depth 15, residue 11121. -/
theorem bounds_15_11121 : exactInterval 15 11121 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_11121 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 11121) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_11121 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_11121 : oddCount 11121 15 = 6 ∧ acceleratedOrbit 15 11121 = 248 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_11121 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 11121) = 3 ^ 6 * m + 248 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_11121.1, data_15_11121.2]

/-- Complete interval computation for depth 15, residue 11122. -/
theorem bounds_15_11122 : exactInterval 15 11122 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_11122 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 11122) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_11122 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_11122 : oddCount 11122 15 = 5 ∧ acceleratedOrbit 15 11122 = 83 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_11122 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 11122) = 3 ^ 5 * m + 83 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_11122.1, data_15_11122.2]

/-- Complete interval computation for depth 15, residue 11123. -/
theorem bounds_15_11123 : exactInterval 15 11123 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_11123 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 11123) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_11123 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_11123 : oddCount 11123 15 = 5 ∧ acceleratedOrbit 15 11123 = 83 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_11123 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 11123) = 3 ^ 5 * m + 83 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_11123.1, data_15_11123.2]

/-- Complete interval computation for depth 15, residue 11124. -/
theorem bounds_15_11124 : exactInterval 15 11124 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_11124 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 11124) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_11124 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_11124 : oddCount 11124 15 = 6 ∧ acceleratedOrbit 15 11124 = 248 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_11124 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 11124) = 3 ^ 6 * m + 248 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_11124.1, data_15_11124.2]

/-- Complete interval computation for depth 15, residue 11125. -/
theorem bounds_15_11125 : exactInterval 15 11125 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_11125 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 11125) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_11125 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_11125 : oddCount 11125 15 = 6 ∧ acceleratedOrbit 15 11125 = 248 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_11125 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 11125) = 3 ^ 6 * m + 248 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_11125.1, data_15_11125.2]

/-- Complete interval computation for depth 15, residue 11126. -/
theorem bounds_15_11126 : exactInterval 15 11126 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_11126 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 11126) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_11126 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_11126 : oddCount 11126 15 = 7 ∧ acceleratedOrbit 15 11126 = 743 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_11126 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 11126) = 3 ^ 7 * m + 743 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_11126.1, data_15_11126.2]

/-- Complete interval computation for depth 15, residue 11127. -/
theorem bounds_15_11127 : exactInterval 15 11127 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_11127 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 11127) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_11127 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_11127 : oddCount 11127 15 = 7 ∧ acceleratedOrbit 15 11127 = 743 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_11127 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 11127) = 3 ^ 7 * m + 743 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_11127.1, data_15_11127.2]

/-- Complete interval computation for depth 15, residue 11128. -/
theorem bounds_15_11128 : exactInterval 15 11128 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_11128 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 11128) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_11128 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_11128 : oddCount 11128 15 = 8 ∧ acceleratedOrbit 15 11128 = 2231 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_11128 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 11128) = 3 ^ 8 * m + 2231 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_11128.1, data_15_11128.2]

/-- Complete interval computation for depth 15, residue 11129. -/
theorem bounds_15_11129 : exactInterval 15 11129 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_11129 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 11129) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_11129 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_11129 : oddCount 11129 15 = 10 ∧ acceleratedOrbit 15 11129 = 20060 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_11129 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 11129) = 3 ^ 10 * m + 20060 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_11129.1, data_15_11129.2]

/-- Complete interval computation for depth 15, residue 11130. -/
theorem bounds_15_11130 : exactInterval 15 11130 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_11130 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 11130) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_11130 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_11130 : oddCount 11130 15 = 8 ∧ acceleratedOrbit 15 11130 = 2231 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_11130 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 11130) = 3 ^ 8 * m + 2231 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_11130.1, data_15_11130.2]

/-- Complete interval computation for depth 15, residue 11131. -/
theorem bounds_15_11131 : exactInterval 15 11131 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_11131 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 11131) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_11131 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_11131 : oddCount 11131 15 = 10 ∧ acceleratedOrbit 15 11131 = 20063 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_11131 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 11131) = 3 ^ 10 * m + 20063 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_11131.1, data_15_11131.2]

/-- Complete interval computation for depth 15, residue 11132. -/
theorem bounds_15_11132 : exactInterval 15 11132 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_11132 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 11132) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_11132 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_11132 : oddCount 11132 15 = 8 ∧ acceleratedOrbit 15 11132 = 2231 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_11132 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 11132) = 3 ^ 8 * m + 2231 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_11132.1, data_15_11132.2]

/-- Complete interval computation for depth 15, residue 11133. -/
theorem bounds_15_11133 : exactInterval 15 11133 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_11133 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 11133) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_11133 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_11133 : oddCount 11133 15 = 8 ∧ acceleratedOrbit 15 11133 = 2231 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_11133 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 11133) = 3 ^ 8 * m + 2231 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_11133.1, data_15_11133.2]

/-- Complete interval computation for depth 15, residue 11134. -/
theorem bounds_15_11134 : exactInterval 15 11134 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_11134 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 11134) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_11134 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_11134 : oddCount 11134 15 = 11 ∧ acceleratedOrbit 15 11134 = 60203 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_11134 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 11134) = 3 ^ 11 * m + 60203 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_11134.1, data_15_11134.2]

/-- Complete interval computation for depth 15, residue 11135. -/
theorem bounds_15_11135 : exactInterval 15 11135 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_11135 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 11135) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_11135 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_11135 : oddCount 11135 15 = 11 ∧ acceleratedOrbit 15 11135 = 60203 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_11135 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 11135) = 3 ^ 11 * m + 60203 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_11135.1, data_15_11135.2]

/-- Complete interval computation for depth 15, residue 11136. -/
theorem bounds_15_11136 : exactInterval 15 11136 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_11136 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 11136) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_11136 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_11136 : oddCount 11136 15 = 4 ∧ acceleratedOrbit 15 11136 = 28 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_11136 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 11136) = 3 ^ 4 * m + 28 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_11136.1, data_15_11136.2]

/-- Complete interval computation for depth 15, residue 11137. -/
theorem bounds_15_11137 : exactInterval 15 11137 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_11137 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 11137) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_11137 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_11137 : oddCount 11137 15 = 10 ∧ acceleratedOrbit 15 11137 = 20078 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_11137 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 11137) = 3 ^ 10 * m + 20078 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_11137.1, data_15_11137.2]

/-- Complete interval computation for depth 15, residue 11138. -/
theorem bounds_15_11138 : exactInterval 15 11138 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_11138 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 11138) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_11138 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_11138 : oddCount 11138 15 = 6 ∧ acceleratedOrbit 15 11138 = 248 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_11138 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 11138) = 3 ^ 6 * m + 248 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_11138.1, data_15_11138.2]

/-- Complete interval computation for depth 15, residue 11139. -/
theorem bounds_15_11139 : exactInterval 15 11139 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_11139 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 11139) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_11139 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_11139 : oddCount 11139 15 = 6 ∧ acceleratedOrbit 15 11139 = 248 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_11139 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 11139) = 3 ^ 6 * m + 248 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_11139.1, data_15_11139.2]

/-- Complete interval computation for depth 15, residue 11140. -/
theorem bounds_15_11140 : exactInterval 15 11140 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_11140 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 11140) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_11140 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_11140 : oddCount 11140 15 = 9 ∧ acceleratedOrbit 15 11140 = 6698 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_11140 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 11140) = 3 ^ 9 * m + 6698 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_11140.1, data_15_11140.2]

end Collatz.Research.PassageAtlas.Batch0340
