import Collatz.Research.DescentIntervals.Classifier

namespace Collatz.Research.PassageAtlas.Batch0889

open Collatz.Research.DescentIntervals

set_option maxRecDepth 20000
set_option maxHeartbeats 0

/-- Complete interval computation for depth 15, residue 29097. -/
theorem bounds_15_29097 : exactInterval 15 29097 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_29097 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 29097) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_29097 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_29097 : oddCount 29097 15 = 9 ∧ acceleratedOrbit 15 29097 = 17479 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_29097 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 29097) = 3 ^ 9 * m + 17479 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_29097.1, data_15_29097.2]

/-- Complete interval computation for depth 15, residue 29098. -/
theorem bounds_15_29098 : exactInterval 15 29098 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_29098 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 29098) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_29098 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_29098 : oddCount 29098 15 = 2 ∧ acceleratedOrbit 15 29098 = 8 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_29098 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 29098) = 3 ^ 2 * m + 8 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_29098.1, data_15_29098.2]

/-- Complete interval computation for depth 15, residue 29099. -/
theorem bounds_15_29099 : exactInterval 15 29099 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_29099 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 29099) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_29099 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_29099 : oddCount 29099 15 = 11 ∧ acceleratedOrbit 15 29099 = 157328 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_29099 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 29099) = 3 ^ 11 * m + 157328 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_29099.1, data_15_29099.2]

/-- Complete interval computation for depth 15, residue 29100. -/
theorem bounds_15_29100 : exactInterval 15 29100 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_29100 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 29100) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_29100 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_29100 : oddCount 29100 15 = 9 ∧ acceleratedOrbit 15 29100 = 17486 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_29100 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 29100) = 3 ^ 9 * m + 17486 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_29100.1, data_15_29100.2]

/-- Complete interval computation for depth 15, residue 29101. -/
theorem bounds_15_29101 : exactInterval 15 29101 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_29101 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 29101) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_29101 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_29101 : oddCount 29101 15 = 9 ∧ acceleratedOrbit 15 29101 = 17486 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_29101 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 29101) = 3 ^ 9 * m + 17486 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_29101.1, data_15_29101.2]

/-- Complete interval computation for depth 15, residue 29102. -/
theorem bounds_15_29102 : exactInterval 15 29102 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_29102 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 29102) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_29102 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_29102 : oddCount 29102 15 = 9 ∧ acceleratedOrbit 15 29102 = 17486 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_29102 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 29102) = 3 ^ 9 * m + 17486 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_29102.1, data_15_29102.2]

/-- Complete interval computation for depth 15, residue 29103. -/
theorem bounds_15_29103 : exactInterval 15 29103 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_29103 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 29103) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_29103 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_29103 : oddCount 29103 15 = 7 ∧ acceleratedOrbit 15 29103 = 1943 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_29103 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 29103) = 3 ^ 7 * m + 1943 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_29103.1, data_15_29103.2]

/-- Complete interval computation for depth 15, residue 29104. -/
theorem bounds_15_29104 : exactInterval 15 29104 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_29104 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 29104) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_29104 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_29104 : oddCount 29104 15 = 10 ∧ acceleratedOrbit 15 29104 = 52487 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_29104 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 29104) = 3 ^ 10 * m + 52487 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_29104.1, data_15_29104.2]

/-- Complete interval computation for depth 15, residue 29105. -/
theorem bounds_15_29105 : exactInterval 15 29105 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_29105 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 29105) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_29105 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_29105 : oddCount 29105 15 = 9 ∧ acceleratedOrbit 15 29105 = 17495 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_29105 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 29105) = 3 ^ 9 * m + 17495 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_29105.1, data_15_29105.2]

/-- Complete interval computation for depth 15, residue 29106. -/
theorem bounds_15_29106 : exactInterval 15 29106 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_29106 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 29106) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_29106 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_29106 : oddCount 29106 15 = 9 ∧ acceleratedOrbit 15 29106 = 17495 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_29106 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 29106) = 3 ^ 9 * m + 17495 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_29106.1, data_15_29106.2]

/-- Complete interval computation for depth 15, residue 29107. -/
theorem bounds_15_29107 : exactInterval 15 29107 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_29107 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 29107) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_29107 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_29107 : oddCount 29107 15 = 9 ∧ acceleratedOrbit 15 29107 = 17495 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_29107 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 29107) = 3 ^ 9 * m + 17495 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_29107.1, data_15_29107.2]

/-- Complete interval computation for depth 15, residue 29108. -/
theorem bounds_15_29108 : exactInterval 15 29108 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_29108 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 29108) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_29108 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_29108 : oddCount 29108 15 = 10 ∧ acceleratedOrbit 15 29108 = 52487 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_29108 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 29108) = 3 ^ 10 * m + 52487 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_29108.1, data_15_29108.2]

/-- Complete interval computation for depth 15, residue 29109. -/
theorem bounds_15_29109 : exactInterval 15 29109 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_29109 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 29109) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_29109 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_29109 : oddCount 29109 15 = 10 ∧ acceleratedOrbit 15 29109 = 52487 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_29109 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 29109) = 3 ^ 10 * m + 52487 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_29109.1, data_15_29109.2]

/-- Complete interval computation for depth 15, residue 29110. -/
theorem bounds_15_29110 : exactInterval 15 29110 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_29110 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 29110) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_29110 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_29110 : oddCount 29110 15 = 9 ∧ acceleratedOrbit 15 29110 = 17489 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_29110 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 29110) = 3 ^ 9 * m + 17489 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_29110.1, data_15_29110.2]

/-- Complete interval computation for depth 15, residue 29111. -/
theorem bounds_15_29111 : exactInterval 15 29111 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_29111 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 29111) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_29111 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_29111 : oddCount 29111 15 = 9 ∧ acceleratedOrbit 15 29111 = 17489 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_29111 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 29111) = 3 ^ 9 * m + 17489 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_29111.1, data_15_29111.2]

/-- Complete interval computation for depth 15, residue 29112. -/
theorem bounds_15_29112 : exactInterval 15 29112 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_29112 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 29112) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_29112 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_29112 : oddCount 29112 15 = 10 ∧ acceleratedOrbit 15 29112 = 52487 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_29112 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 29112) = 3 ^ 10 * m + 52487 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_29112.1, data_15_29112.2]

/-- Complete interval computation for depth 15, residue 29113. -/
theorem bounds_15_29113 : exactInterval 15 29113 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_29113 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 29113) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_29113 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_29113 : oddCount 29113 15 = 9 ∧ acceleratedOrbit 15 29113 = 17495 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_29113 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 29113) = 3 ^ 9 * m + 17495 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_29113.1, data_15_29113.2]

/-- Complete interval computation for depth 15, residue 29114. -/
theorem bounds_15_29114 : exactInterval 15 29114 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_29114 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 29114) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_29114 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_29114 : oddCount 29114 15 = 10 ∧ acceleratedOrbit 15 29114 = 52487 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_29114 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 29114) = 3 ^ 10 * m + 52487 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_29114.1, data_15_29114.2]

/-- Complete interval computation for depth 15, residue 29115. -/
theorem bounds_15_29115 : exactInterval 15 29115 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_29115 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 29115) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_29115 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_29115 : oddCount 29115 15 = 9 ∧ acceleratedOrbit 15 29115 = 17491 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_29115 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 29115) = 3 ^ 9 * m + 17491 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_29115.1, data_15_29115.2]

/-- Complete interval computation for depth 15, residue 29116. -/
theorem bounds_15_29116 : exactInterval 15 29116 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_29116 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 29116) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_29116 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_29116 : oddCount 29116 15 = 10 ∧ acceleratedOrbit 15 29116 = 52478 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_29116 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 29116) = 3 ^ 10 * m + 52478 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_29116.1, data_15_29116.2]

/-- Complete interval computation for depth 15, residue 29117. -/
theorem bounds_15_29117 : exactInterval 15 29117 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_29117 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 29117) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_29117 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_29117 : oddCount 29117 15 = 10 ∧ acceleratedOrbit 15 29117 = 52478 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_29117 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 29117) = 3 ^ 10 * m + 52478 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_29117.1, data_15_29117.2]

/-- Complete interval computation for depth 15, residue 29118. -/
theorem bounds_15_29118 : exactInterval 15 29118 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_29118 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 29118) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_29118 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_29118 : oddCount 29118 15 = 10 ∧ acceleratedOrbit 15 29118 = 52478 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_29118 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 29118) = 3 ^ 10 * m + 52478 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_29118.1, data_15_29118.2]

/-- Complete interval computation for depth 15, residue 29119. -/
theorem bounds_15_29119 : exactInterval 15 29119 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_29119 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 29119) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_29119 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_29119 : oddCount 29119 15 = 11 ∧ acceleratedOrbit 15 29119 = 157427 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_29119 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 29119) = 3 ^ 11 * m + 157427 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_29119.1, data_15_29119.2]

/-- Complete interval computation for depth 15, residue 29120. -/
theorem bounds_15_29120 : exactInterval 15 29120 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_29120 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 29120) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_29120 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_29120 : oddCount 29120 15 = 6 ∧ acceleratedOrbit 15 29120 = 650 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_29120 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 29120) = 3 ^ 6 * m + 650 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_29120.1, data_15_29120.2]

/-- Complete interval computation for depth 15, residue 29121. -/
theorem bounds_15_29121 : exactInterval 15 29121 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_29121 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 29121) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_29121 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_29121 : oddCount 29121 15 = 11 ∧ acceleratedOrbit 15 29121 = 157463 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_29121 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 29121) = 3 ^ 11 * m + 157463 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_29121.1, data_15_29121.2]

/-- Complete interval computation for depth 15, residue 29122. -/
theorem bounds_15_29122 : exactInterval 15 29122 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_29122 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 29122) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_29122 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_29122 : oddCount 29122 15 = 12 ∧ acceleratedOrbit 15 29122 = 472391 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_29122 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 29122) = 3 ^ 12 * m + 472391 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_29122.1, data_15_29122.2]

/-- Complete interval computation for depth 15, residue 29123. -/
theorem bounds_15_29123 : exactInterval 15 29123 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_29123 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 29123) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_29123 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_29123 : oddCount 29123 15 = 12 ∧ acceleratedOrbit 15 29123 = 472391 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_29123 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 29123) = 3 ^ 12 * m + 472391 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_29123.1, data_15_29123.2]

/-- Complete interval computation for depth 15, residue 29124. -/
theorem bounds_15_29124 : exactInterval 15 29124 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_29124 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 29124) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_29124 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_29124 : oddCount 29124 15 = 2 ∧ acceleratedOrbit 15 29124 = 8 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_29124 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 29124) = 3 ^ 2 * m + 8 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_29124.1, data_15_29124.2]

/-- Complete interval computation for depth 15, residue 29125. -/
theorem bounds_15_29125 : exactInterval 15 29125 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_29125 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 29125) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_29125 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_29125 : oddCount 29125 15 = 2 ∧ acceleratedOrbit 15 29125 = 8 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_29125 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 29125) = 3 ^ 2 * m + 8 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_29125.1, data_15_29125.2]

/-- Complete interval computation for depth 15, residue 29126. -/
theorem bounds_15_29126 : exactInterval 15 29126 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_29126 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 29126) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_29126 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_29126 : oddCount 29126 15 = 2 ∧ acceleratedOrbit 15 29126 = 8 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_29126 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 29126) = 3 ^ 2 * m + 8 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_29126.1, data_15_29126.2]

/-- Complete interval computation for depth 15, residue 29127. -/
theorem bounds_15_29127 : exactInterval 15 29127 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_29127 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 29127) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_29127 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_29127 : oddCount 29127 15 = 9 ∧ acceleratedOrbit 15 29127 = 17498 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_29127 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 29127) = 3 ^ 9 * m + 17498 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_29127.1, data_15_29127.2]

/-- Complete interval computation for depth 15, residue 29128. -/
theorem bounds_15_29128 : exactInterval 15 29128 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_29128 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 29128) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_29128 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_29128 : oddCount 29128 15 = 7 ∧ acceleratedOrbit 15 29128 = 1946 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_29128 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 29128) = 3 ^ 7 * m + 1946 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_29128.1, data_15_29128.2]

/-- Complete interval computation for depth 15, residue 29129. -/
theorem bounds_15_29129 : exactInterval 15 29129 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_29129 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 29129) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_29129 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_29129 : oddCount 29129 15 = 8 ∧ acceleratedOrbit 15 29129 = 5834 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_29129 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 29129) = 3 ^ 8 * m + 5834 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_29129.1, data_15_29129.2]

end Collatz.Research.PassageAtlas.Batch0889
