import Collatz.Research.DescentIntervals.Classifier

namespace Collatz.Research.PassageAtlas.Batch0706

open Collatz.Research.DescentIntervals

set_option maxRecDepth 20000
set_option maxHeartbeats 0

/-- Complete interval computation for depth 15, residue 23101. -/
theorem bounds_15_23101 : exactInterval 15 23101 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_23101 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 23101) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_23101 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_23101 : oddCount 23101 15 = 8 ∧ acceleratedOrbit 15 23101 = 4627 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_23101 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 23101) = 3 ^ 8 * m + 4627 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_23101.1, data_15_23101.2]

/-- Complete interval computation for depth 15, residue 23102. -/
theorem bounds_15_23102 : exactInterval 15 23102 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_23102 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 23102) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_23102 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_23102 : oddCount 23102 15 = 6 ∧ acceleratedOrbit 15 23102 = 514 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_23102 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 23102) = 3 ^ 6 * m + 514 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_23102.1, data_15_23102.2]

/-- Complete interval computation for depth 15, residue 23103. -/
theorem bounds_15_23103 : exactInterval 15 23103 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_23103 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 23103) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_23103 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_23103 : oddCount 23103 15 = 6 ∧ acceleratedOrbit 15 23103 = 514 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_23103 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 23103) = 3 ^ 6 * m + 514 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_23103.1, data_15_23103.2]

/-- Complete interval computation for depth 15, residue 23104. -/
theorem bounds_15_23104 : exactInterval 15 23104 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_23104 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 23104) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_23104 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_23104 : oddCount 23104 15 = 5 ∧ acceleratedOrbit 15 23104 = 172 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_23104 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 23104) = 3 ^ 5 * m + 172 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_23104.1, data_15_23104.2]

/-- Complete interval computation for depth 15, residue 23105. -/
theorem bounds_15_23105 : exactInterval 15 23105 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_23105 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 23105) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_23105 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_23105 : oddCount 23105 15 = 6 ∧ acceleratedOrbit 15 23105 = 515 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_23105 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 23105) = 3 ^ 6 * m + 515 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_23105.1, data_15_23105.2]

/-- Complete interval computation for depth 15, residue 23106. -/
theorem bounds_15_23106 : exactInterval 15 23106 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_23106 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 23106) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_23106 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_23106 : oddCount 23106 15 = 6 ∧ acceleratedOrbit 15 23106 = 515 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_23106 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 23106) = 3 ^ 6 * m + 515 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_23106.1, data_15_23106.2]

/-- Complete interval computation for depth 15, residue 23107. -/
theorem bounds_15_23107 : exactInterval 15 23107 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_23107 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 23107) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_23107 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_23107 : oddCount 23107 15 = 6 ∧ acceleratedOrbit 15 23107 = 515 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_23107 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 23107) = 3 ^ 6 * m + 515 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_23107.1, data_15_23107.2]

/-- Complete interval computation for depth 15, residue 23108. -/
theorem bounds_15_23108 : exactInterval 15 23108 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_23108 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 23108) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_23108 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_23108 : oddCount 23108 15 = 6 ∧ acceleratedOrbit 15 23108 = 515 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_23108 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 23108) = 3 ^ 6 * m + 515 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_23108.1, data_15_23108.2]

/-- Complete interval computation for depth 15, residue 23109. -/
theorem bounds_15_23109 : exactInterval 15 23109 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_23109 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 23109) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_23109 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_23109 : oddCount 23109 15 = 6 ∧ acceleratedOrbit 15 23109 = 515 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_23109 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 23109) = 3 ^ 6 * m + 515 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_23109.1, data_15_23109.2]

/-- Complete interval computation for depth 15, residue 23110. -/
theorem bounds_15_23110 : exactInterval 15 23110 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_23110 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 23110) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_23110 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_23110 : oddCount 23110 15 = 6 ∧ acceleratedOrbit 15 23110 = 515 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_23110 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 23110) = 3 ^ 6 * m + 515 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_23110.1, data_15_23110.2]

/-- Complete interval computation for depth 15, residue 23111. -/
theorem bounds_15_23111 : exactInterval 15 23111 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_23111 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 23111) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_23111 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_23111 : oddCount 23111 15 = 8 ∧ acceleratedOrbit 15 23111 = 4628 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_23111 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 23111) = 3 ^ 8 * m + 4628 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_23111.1, data_15_23111.2]

/-- Complete interval computation for depth 15, residue 23112. -/
theorem bounds_15_23112 : exactInterval 15 23112 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_23112 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 23112) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_23112 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_23112 : oddCount 23112 15 = 6 ∧ acceleratedOrbit 15 23112 = 515 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_23112 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 23112) = 3 ^ 6 * m + 515 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_23112.1, data_15_23112.2]

/-- Complete interval computation for depth 15, residue 23113. -/
theorem bounds_15_23113 : exactInterval 15 23113 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_23113 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 23113) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_23113 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_23113 : oddCount 23113 15 = 7 ∧ acceleratedOrbit 15 23113 = 1543 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_23113 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 23113) = 3 ^ 7 * m + 1543 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_23113.1, data_15_23113.2]

/-- Complete interval computation for depth 15, residue 23114. -/
theorem bounds_15_23114 : exactInterval 15 23114 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_23114 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 23114) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_23114 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_23114 : oddCount 23114 15 = 6 ∧ acceleratedOrbit 15 23114 = 515 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_23114 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 23114) = 3 ^ 6 * m + 515 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_23114.1, data_15_23114.2]

/-- Complete interval computation for depth 15, residue 23115. -/
theorem bounds_15_23115 : exactInterval 15 23115 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_23115 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 23115) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_23115 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_23115 : oddCount 23115 15 = 6 ∧ acceleratedOrbit 15 23115 = 515 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_23115 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 23115) = 3 ^ 6 * m + 515 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_23115.1, data_15_23115.2]

/-- Complete interval computation for depth 15, residue 23116. -/
theorem bounds_15_23116 : exactInterval 15 23116 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_23116 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 23116) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_23116 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_23116 : oddCount 23116 15 = 6 ∧ acceleratedOrbit 15 23116 = 515 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_23116 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 23116) = 3 ^ 6 * m + 515 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_23116.1, data_15_23116.2]

/-- Complete interval computation for depth 15, residue 23117. -/
theorem bounds_15_23117 : exactInterval 15 23117 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_23117 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 23117) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_23117 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_23117 : oddCount 23117 15 = 6 ∧ acceleratedOrbit 15 23117 = 515 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_23117 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 23117) = 3 ^ 6 * m + 515 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_23117.1, data_15_23117.2]

/-- Complete interval computation for depth 15, residue 23118. -/
theorem bounds_15_23118 : exactInterval 15 23118 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_23118 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 23118) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_23118 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_23118 : oddCount 23118 15 = 8 ∧ acceleratedOrbit 15 23118 = 4630 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_23118 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 23118) = 3 ^ 8 * m + 4630 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_23118.1, data_15_23118.2]

/-- Complete interval computation for depth 15, residue 23119. -/
theorem bounds_15_23119 : exactInterval 15 23119 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_23119 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 23119) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_23119 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_23119 : oddCount 23119 15 = 8 ∧ acceleratedOrbit 15 23119 = 4630 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_23119 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 23119) = 3 ^ 8 * m + 4630 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_23119.1, data_15_23119.2]

/-- Complete interval computation for depth 15, residue 23120. -/
theorem bounds_15_23120 : exactInterval 15 23120 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_23120 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 23120) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_23120 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_23120 : oddCount 23120 15 = 5 ∧ acceleratedOrbit 15 23120 = 172 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_23120 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 23120) = 3 ^ 5 * m + 172 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_23120.1, data_15_23120.2]

/-- Complete interval computation for depth 15, residue 23121. -/
theorem bounds_15_23121 : exactInterval 15 23121 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_23121 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 23121) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_23121 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_23121 : oddCount 23121 15 = 10 ∧ acceleratedOrbit 15 23121 = 41674 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_23121 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 23121) = 3 ^ 10 * m + 41674 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_23121.1, data_15_23121.2]

/-- Complete interval computation for depth 15, residue 23122. -/
theorem bounds_15_23122 : exactInterval 15 23122 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_23122 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 23122) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_23122 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_23122 : oddCount 23122 15 = 10 ∧ acceleratedOrbit 15 23122 = 41674 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_23122 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 23122) = 3 ^ 10 * m + 41674 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_23122.1, data_15_23122.2]

/-- Complete interval computation for depth 15, residue 23123. -/
theorem bounds_15_23123 : exactInterval 15 23123 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_23123 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 23123) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_23123 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_23123 : oddCount 23123 15 = 10 ∧ acceleratedOrbit 15 23123 = 41674 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_23123 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 23123) = 3 ^ 10 * m + 41674 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_23123.1, data_15_23123.2]

/-- Complete interval computation for depth 15, residue 23124. -/
theorem bounds_15_23124 : exactInterval 15 23124 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_23124 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 23124) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_23124 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_23124 : oddCount 23124 15 = 5 ∧ acceleratedOrbit 15 23124 = 172 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_23124 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 23124) = 3 ^ 5 * m + 172 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_23124.1, data_15_23124.2]

/-- Complete interval computation for depth 15, residue 23125. -/
theorem bounds_15_23125 : exactInterval 15 23125 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_23125 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 23125) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_23125 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_23125 : oddCount 23125 15 = 5 ∧ acceleratedOrbit 15 23125 = 172 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_23125 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 23125) = 3 ^ 5 * m + 172 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_23125.1, data_15_23125.2]

/-- Complete interval computation for depth 15, residue 23126. -/
theorem bounds_15_23126 : exactInterval 15 23126 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_23126 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 23126) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_23126 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_23126 : oddCount 23126 15 = 7 ∧ acceleratedOrbit 15 23126 = 1544 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_23126 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 23126) = 3 ^ 7 * m + 1544 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_23126.1, data_15_23126.2]

/-- Complete interval computation for depth 15, residue 23127. -/
theorem bounds_15_23127 : exactInterval 15 23127 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_23127 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 23127) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_23127 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_23127 : oddCount 23127 15 = 7 ∧ acceleratedOrbit 15 23127 = 1544 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_23127 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 23127) = 3 ^ 7 * m + 1544 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_23127.1, data_15_23127.2]

/-- Complete interval computation for depth 15, residue 23128. -/
theorem bounds_15_23128 : exactInterval 15 23128 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_23128 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 23128) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_23128 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_23128 : oddCount 23128 15 = 5 ∧ acceleratedOrbit 15 23128 = 172 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_23128 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 23128) = 3 ^ 5 * m + 172 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_23128.1, data_15_23128.2]

/-- Complete interval computation for depth 15, residue 23129. -/
theorem bounds_15_23129 : exactInterval 15 23129 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_23129 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 23129) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_23129 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_23129 : oddCount 23129 15 = 7 ∧ acceleratedOrbit 15 23129 = 1544 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_23129 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 23129) = 3 ^ 7 * m + 1544 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_23129.1, data_15_23129.2]

/-- Complete interval computation for depth 15, residue 23130. -/
theorem bounds_15_23130 : exactInterval 15 23130 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_23130 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 23130) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_23130 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_23130 : oddCount 23130 15 = 5 ∧ acceleratedOrbit 15 23130 = 172 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_23130 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 23130) = 3 ^ 5 * m + 172 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_23130.1, data_15_23130.2]

/-- Complete interval computation for depth 15, residue 23131. -/
theorem bounds_15_23131 : exactInterval 15 23131 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_23131 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 23131) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_23131 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_23131 : oddCount 23131 15 = 10 ∧ acceleratedOrbit 15 23131 = 41687 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_23131 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 23131) = 3 ^ 10 * m + 41687 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_23131.1, data_15_23131.2]

/-- Complete interval computation for depth 15, residue 23132. -/
theorem bounds_15_23132 : exactInterval 15 23132 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_23132 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 23132) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_23132 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_23132 : oddCount 23132 15 = 5 ∧ acceleratedOrbit 15 23132 = 172 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_23132 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 23132) = 3 ^ 5 * m + 172 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_23132.1, data_15_23132.2]

/-- Complete interval computation for depth 15, residue 23133. -/
theorem bounds_15_23133 : exactInterval 15 23133 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_23133 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 23133) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_23133 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_23133 : oddCount 23133 15 = 5 ∧ acceleratedOrbit 15 23133 = 172 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_23133 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 23133) = 3 ^ 5 * m + 172 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_23133.1, data_15_23133.2]

end Collatz.Research.PassageAtlas.Batch0706
