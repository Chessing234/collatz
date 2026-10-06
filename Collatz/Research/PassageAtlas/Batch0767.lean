import Collatz.Research.DescentIntervals.Classifier

namespace Collatz.Research.PassageAtlas.Batch0767

open Collatz.Research.DescentIntervals

set_option maxRecDepth 20000
set_option maxHeartbeats 0

/-- Complete interval computation for depth 15, residue 25100. -/
theorem bounds_15_25100 : exactInterval 15 25100 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_25100 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 25100) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_25100 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_25100 : oddCount 25100 15 = 6 ∧ acceleratedOrbit 15 25100 = 560 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_25100 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 25100) = 3 ^ 6 * m + 560 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_25100.1, data_15_25100.2]

/-- Complete interval computation for depth 15, residue 25101. -/
theorem bounds_15_25101 : exactInterval 15 25101 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_25101 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 25101) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_25101 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_25101 : oddCount 25101 15 = 6 ∧ acceleratedOrbit 15 25101 = 560 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_25101 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 25101) = 3 ^ 6 * m + 560 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_25101.1, data_15_25101.2]

/-- Complete interval computation for depth 15, residue 25102. -/
theorem bounds_15_25102 : exactInterval 15 25102 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_25102 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 25102) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_25102 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_25102 : oddCount 25102 15 = 8 ∧ acceleratedOrbit 15 25102 = 5027 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_25102 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 25102) = 3 ^ 8 * m + 5027 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_25102.1, data_15_25102.2]

/-- Complete interval computation for depth 15, residue 25103. -/
theorem bounds_15_25103 : exactInterval 15 25103 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_25103 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 25103) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_25103 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_25103 : oddCount 25103 15 = 8 ∧ acceleratedOrbit 15 25103 = 5027 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_25103 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 25103) = 3 ^ 8 * m + 5027 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_25103.1, data_15_25103.2]

/-- Complete interval computation for depth 15, residue 25104. -/
theorem bounds_15_25104 : exactInterval 15 25104 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_25104 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 25104) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_25104 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_25104 : oddCount 25104 15 = 6 ∧ acceleratedOrbit 15 25104 = 560 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_25104 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 25104) = 3 ^ 6 * m + 560 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_25104.1, data_15_25104.2]

/-- Complete interval computation for depth 15, residue 25105. -/
theorem bounds_15_25105 : exactInterval 15 25105 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_25105 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 25105) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_25105 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_25105 : oddCount 25105 15 = 6 ∧ acceleratedOrbit 15 25105 = 560 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_25105 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 25105) = 3 ^ 6 * m + 560 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_25105.1, data_15_25105.2]

/-- Complete interval computation for depth 15, residue 25106. -/
theorem bounds_15_25106 : exactInterval 15 25106 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_25106 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 25106) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_25106 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_25106 : oddCount 25106 15 = 7 ∧ acceleratedOrbit 15 25106 = 1676 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_25106 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 25106) = 3 ^ 7 * m + 1676 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_25106.1, data_15_25106.2]

/-- Complete interval computation for depth 15, residue 25107. -/
theorem bounds_15_25107 : exactInterval 15 25107 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_25107 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 25107) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_25107 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_25107 : oddCount 25107 15 = 7 ∧ acceleratedOrbit 15 25107 = 1676 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_25107 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 25107) = 3 ^ 7 * m + 1676 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_25107.1, data_15_25107.2]

/-- Complete interval computation for depth 15, residue 25108. -/
theorem bounds_15_25108 : exactInterval 15 25108 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_25108 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 25108) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_25108 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_25108 : oddCount 25108 15 = 6 ∧ acceleratedOrbit 15 25108 = 560 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_25108 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 25108) = 3 ^ 6 * m + 560 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_25108.1, data_15_25108.2]

/-- Complete interval computation for depth 15, residue 25109. -/
theorem bounds_15_25109 : exactInterval 15 25109 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_25109 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 25109) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_25109 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_25109 : oddCount 25109 15 = 6 ∧ acceleratedOrbit 15 25109 = 560 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_25109 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 25109) = 3 ^ 6 * m + 560 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_25109.1, data_15_25109.2]

/-- Complete interval computation for depth 15, residue 25110. -/
theorem bounds_15_25110 : exactInterval 15 25110 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_25110 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 25110) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_25110 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_25110 : oddCount 25110 15 = 6 ∧ acceleratedOrbit 15 25110 = 559 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_25110 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 25110) = 3 ^ 6 * m + 559 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_25110.1, data_15_25110.2]

/-- Complete interval computation for depth 15, residue 25111. -/
theorem bounds_15_25111 : exactInterval 15 25111 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_25111 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 25111) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_25111 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_25111 : oddCount 25111 15 = 6 ∧ acceleratedOrbit 15 25111 = 559 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_25111 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 25111) = 3 ^ 6 * m + 559 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_25111.1, data_15_25111.2]

/-- Complete interval computation for depth 15, residue 25112. -/
theorem bounds_15_25112 : exactInterval 15 25112 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_25112 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 25112) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_25112 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_25112 : oddCount 25112 15 = 6 ∧ acceleratedOrbit 15 25112 = 560 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_25112 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 25112) = 3 ^ 6 * m + 560 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_25112.1, data_15_25112.2]

/-- Complete interval computation for depth 15, residue 25113. -/
theorem bounds_15_25113 : exactInterval 15 25113 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_25113 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 25113) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_25113 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_25113 : oddCount 25113 15 = 6 ∧ acceleratedOrbit 15 25113 = 559 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_25113 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 25113) = 3 ^ 6 * m + 559 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_25113.1, data_15_25113.2]

/-- Complete interval computation for depth 15, residue 25114. -/
theorem bounds_15_25114 : exactInterval 15 25114 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_25114 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 25114) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_25114 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_25114 : oddCount 25114 15 = 6 ∧ acceleratedOrbit 15 25114 = 560 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_25114 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 25114) = 3 ^ 6 * m + 560 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_25114.1, data_15_25114.2]

/-- Complete interval computation for depth 15, residue 25115. -/
theorem bounds_15_25115 : exactInterval 15 25115 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_25115 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 25115) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_25115 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_25115 : oddCount 25115 15 = 8 ∧ acceleratedOrbit 15 25115 = 5029 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_25115 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 25115) = 3 ^ 8 * m + 5029 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_25115.1, data_15_25115.2]

/-- Complete interval computation for depth 15, residue 25116. -/
theorem bounds_15_25116 : exactInterval 15 25116 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_25116 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 25116) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_25116 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_25116 : oddCount 25116 15 = 6 ∧ acceleratedOrbit 15 25116 = 559 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_25116 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 25116) = 3 ^ 6 * m + 559 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_25116.1, data_15_25116.2]

/-- Complete interval computation for depth 15, residue 25117. -/
theorem bounds_15_25117 : exactInterval 15 25117 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_25117 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 25117) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_25117 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_25117 : oddCount 25117 15 = 6 ∧ acceleratedOrbit 15 25117 = 559 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_25117 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 25117) = 3 ^ 6 * m + 559 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_25117.1, data_15_25117.2]

/-- Complete interval computation for depth 15, residue 25118. -/
theorem bounds_15_25118 : exactInterval 15 25118 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_25118 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 25118) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_25118 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_25118 : oddCount 25118 15 = 6 ∧ acceleratedOrbit 15 25118 = 559 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_25118 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 25118) = 3 ^ 6 * m + 559 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_25118.1, data_15_25118.2]

/-- Complete interval computation for depth 15, residue 25119. -/
theorem bounds_15_25119 : exactInterval 15 25119 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_25119 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 25119) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_25119 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_25119 : oddCount 25119 15 = 10 ∧ acceleratedOrbit 15 25119 = 45269 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_25119 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 25119) = 3 ^ 10 * m + 45269 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_25119.1, data_15_25119.2]

/-- Complete interval computation for depth 15, residue 25120. -/
theorem bounds_15_25120 : exactInterval 15 25120 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_25120 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 25120) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_25120 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_25120 : oddCount 25120 15 = 5 ∧ acceleratedOrbit 15 25120 = 188 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_25120 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 25120) = 3 ^ 5 * m + 188 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_25120.1, data_15_25120.2]

/-- Complete interval computation for depth 15, residue 25121. -/
theorem bounds_15_25121 : exactInterval 15 25121 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_25121 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 25121) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_25121 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_25121 : oddCount 25121 15 = 6 ∧ acceleratedOrbit 15 25121 = 559 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_25121 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 25121) = 3 ^ 6 * m + 559 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_25121.1, data_15_25121.2]

/-- Complete interval computation for depth 15, residue 25122. -/
theorem bounds_15_25122 : exactInterval 15 25122 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_25122 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 25122) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_25122 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_25122 : oddCount 25122 15 = 6 ∧ acceleratedOrbit 15 25122 = 560 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_25122 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 25122) = 3 ^ 6 * m + 560 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_25122.1, data_15_25122.2]

/-- Complete interval computation for depth 15, residue 25123. -/
theorem bounds_15_25123 : exactInterval 15 25123 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_25123 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 25123) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_25123 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_25123 : oddCount 25123 15 = 6 ∧ acceleratedOrbit 15 25123 = 560 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_25123 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 25123) = 3 ^ 6 * m + 560 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_25123.1, data_15_25123.2]

/-- Complete interval computation for depth 15, residue 25124. -/
theorem bounds_15_25124 : exactInterval 15 25124 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_25124 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 25124) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_25124 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_25124 : oddCount 25124 15 = 8 ∧ acceleratedOrbit 15 25124 = 5032 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_25124 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 25124) = 3 ^ 8 * m + 5032 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_25124.1, data_15_25124.2]

/-- Complete interval computation for depth 15, residue 25125. -/
theorem bounds_15_25125 : exactInterval 15 25125 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_25125 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 25125) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_25125 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_25125 : oddCount 25125 15 = 8 ∧ acceleratedOrbit 15 25125 = 5032 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_25125 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 25125) = 3 ^ 8 * m + 5032 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_25125.1, data_15_25125.2]

/-- Complete interval computation for depth 15, residue 25126. -/
theorem bounds_15_25126 : exactInterval 15 25126 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_25126 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 25126) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_25126 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_25126 : oddCount 25126 15 = 8 ∧ acceleratedOrbit 15 25126 = 5032 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_25126 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 25126) = 3 ^ 8 * m + 5032 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_25126.1, data_15_25126.2]

/-- Complete interval computation for depth 15, residue 25127. -/
theorem bounds_15_25127 : exactInterval 15 25127 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_25127 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 25127) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_25127 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_25127 : oddCount 25127 15 = 8 ∧ acceleratedOrbit 15 25127 = 5032 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_25127 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 25127) = 3 ^ 8 * m + 5032 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_25127.1, data_15_25127.2]

/-- Complete interval computation for depth 15, residue 25128. -/
theorem bounds_15_25128 : exactInterval 15 25128 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_25128 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 25128) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_25128 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_25128 : oddCount 25128 15 = 5 ∧ acceleratedOrbit 15 25128 = 188 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_25128 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 25128) = 3 ^ 5 * m + 188 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_25128.1, data_15_25128.2]

/-- Complete interval computation for depth 15, residue 25129. -/
theorem bounds_15_25129 : exactInterval 15 25129 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_25129 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 25129) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_25129 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_25129 : oddCount 25129 15 = 10 ∧ acceleratedOrbit 15 25129 = 45287 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_25129 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 25129) = 3 ^ 10 * m + 45287 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_25129.1, data_15_25129.2]

/-- Complete interval computation for depth 15, residue 25130. -/
theorem bounds_15_25130 : exactInterval 15 25130 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_25130 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 25130) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_25130 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_25130 : oddCount 25130 15 = 5 ∧ acceleratedOrbit 15 25130 = 188 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_25130 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 25130) = 3 ^ 5 * m + 188 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_25130.1, data_15_25130.2]

/-- Complete interval computation for depth 15, residue 25131. -/
theorem bounds_15_25131 : exactInterval 15 25131 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_25131 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 25131) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_25131 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_25131 : oddCount 25131 15 = 6 ∧ acceleratedOrbit 15 25131 = 560 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_25131 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 25131) = 3 ^ 6 * m + 560 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_25131.1, data_15_25131.2]

/-- Complete interval computation for depth 15, residue 25132. -/
theorem bounds_15_25132 : exactInterval 15 25132 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_25132 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 25132) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_25132 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_25132 : oddCount 25132 15 = 8 ∧ acceleratedOrbit 15 25132 = 5035 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_25132 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 25132) = 3 ^ 8 * m + 5035 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_25132.1, data_15_25132.2]

end Collatz.Research.PassageAtlas.Batch0767
