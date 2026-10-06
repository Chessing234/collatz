import Collatz.Research.DescentIntervals.Classifier

namespace Collatz.Research.PassageAtlas.Batch0828

open Collatz.Research.DescentIntervals

set_option maxRecDepth 20000
set_option maxHeartbeats 0

/-- Complete interval computation for depth 15, residue 27099. -/
theorem bounds_15_27099 : exactInterval 15 27099 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_27099 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 27099) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_27099 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_27099 : oddCount 27099 15 = 10 ∧ acceleratedOrbit 15 27099 = 48842 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_27099 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 27099) = 3 ^ 10 * m + 48842 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_27099.1, data_15_27099.2]

/-- Complete interval computation for depth 15, residue 27100. -/
theorem bounds_15_27100 : exactInterval 15 27100 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_27100 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 27100) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_27100 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_27100 : oddCount 27100 15 = 4 ∧ acceleratedOrbit 15 27100 = 67 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_27100 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 27100) = 3 ^ 4 * m + 67 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_27100.1, data_15_27100.2]

/-- Complete interval computation for depth 15, residue 27101. -/
theorem bounds_15_27101 : exactInterval 15 27101 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_27101 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 27101) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_27101 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_27101 : oddCount 27101 15 = 4 ∧ acceleratedOrbit 15 27101 = 67 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_27101 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 27101) = 3 ^ 4 * m + 67 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_27101.1, data_15_27101.2]

/-- Complete interval computation for depth 15, residue 27102. -/
theorem bounds_15_27102 : exactInterval 15 27102 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_27102 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 27102) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_27102 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_27102 : oddCount 27102 15 = 13 ∧ acceleratedOrbit 15 27102 = 1318760 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_27102 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 27102) = 3 ^ 13 * m + 1318760 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_27102.1, data_15_27102.2]

/-- Complete interval computation for depth 15, residue 27103. -/
theorem bounds_15_27103 : exactInterval 15 27103 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_27103 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 27103) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_27103 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_27103 : oddCount 27103 15 = 13 ∧ acceleratedOrbit 15 27103 = 1318760 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_27103 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 27103) = 3 ^ 13 * m + 1318760 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_27103.1, data_15_27103.2]

/-- Complete interval computation for depth 15, residue 27104. -/
theorem bounds_15_27104 : exactInterval 15 27104 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_27104 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 27104) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_27104 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_27104 : oddCount 27104 15 = 6 ∧ acceleratedOrbit 15 27104 = 604 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_27104 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 27104) = 3 ^ 6 * m + 604 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_27104.1, data_15_27104.2]

/-- Complete interval computation for depth 15, residue 27105. -/
theorem bounds_15_27105 : exactInterval 15 27105 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_27105 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 27105) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_27105 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_27105 : oddCount 27105 15 = 8 ∧ acceleratedOrbit 15 27105 = 5428 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_27105 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 27105) = 3 ^ 8 * m + 5428 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_27105.1, data_15_27105.2]

/-- Complete interval computation for depth 15, residue 27106. -/
theorem bounds_15_27106 : exactInterval 15 27106 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_27106 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 27106) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_27106 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_27106 : oddCount 27106 15 = 6 ∧ acceleratedOrbit 15 27106 = 604 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_27106 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 27106) = 3 ^ 6 * m + 604 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_27106.1, data_15_27106.2]

/-- Complete interval computation for depth 15, residue 27107. -/
theorem bounds_15_27107 : exactInterval 15 27107 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_27107 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 27107) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_27107 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_27107 : oddCount 27107 15 = 6 ∧ acceleratedOrbit 15 27107 = 604 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_27107 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 27107) = 3 ^ 6 * m + 604 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_27107.1, data_15_27107.2]

/-- Complete interval computation for depth 15, residue 27108. -/
theorem bounds_15_27108 : exactInterval 15 27108 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_27108 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 27108) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_27108 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_27108 : oddCount 27108 15 = 7 ∧ acceleratedOrbit 15 27108 = 1810 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_27108 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 27108) = 3 ^ 7 * m + 1810 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_27108.1, data_15_27108.2]

/-- Complete interval computation for depth 15, residue 27109. -/
theorem bounds_15_27109 : exactInterval 15 27109 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_27109 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 27109) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_27109 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_27109 : oddCount 27109 15 = 7 ∧ acceleratedOrbit 15 27109 = 1810 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_27109 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 27109) = 3 ^ 7 * m + 1810 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_27109.1, data_15_27109.2]

/-- Complete interval computation for depth 15, residue 27110. -/
theorem bounds_15_27110 : exactInterval 15 27110 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_27110 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 27110) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_27110 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_27110 : oddCount 27110 15 = 7 ∧ acceleratedOrbit 15 27110 = 1810 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_27110 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 27110) = 3 ^ 7 * m + 1810 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_27110.1, data_15_27110.2]

/-- Complete interval computation for depth 15, residue 27111. -/
theorem bounds_15_27111 : exactInterval 15 27111 = ⟨0, none⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_27111 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 27111) 15 ↔ 0 ≤ m := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_27111 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_27111 : oddCount 27111 15 = 9 ∧ acceleratedOrbit 15 27111 = 16286 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_27111 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 27111) = 3 ^ 9 * m + 16286 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_27111.1, data_15_27111.2]

/-- Complete interval computation for depth 15, residue 27112. -/
theorem bounds_15_27112 : exactInterval 15 27112 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_27112 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 27112) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_27112 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_27112 : oddCount 27112 15 = 6 ∧ acceleratedOrbit 15 27112 = 604 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_27112 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 27112) = 3 ^ 6 * m + 604 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_27112.1, data_15_27112.2]

/-- Complete interval computation for depth 15, residue 27113. -/
theorem bounds_15_27113 : exactInterval 15 27113 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_27113 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 27113) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_27113 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_27113 : oddCount 27113 15 = 10 ∧ acceleratedOrbit 15 27113 = 48863 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_27113 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 27113) = 3 ^ 10 * m + 48863 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_27113.1, data_15_27113.2]

/-- Complete interval computation for depth 15, residue 27114. -/
theorem bounds_15_27114 : exactInterval 15 27114 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_27114 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 27114) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_27114 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_27114 : oddCount 27114 15 = 6 ∧ acceleratedOrbit 15 27114 = 604 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_27114 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 27114) = 3 ^ 6 * m + 604 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_27114.1, data_15_27114.2]

/-- Complete interval computation for depth 15, residue 27115. -/
theorem bounds_15_27115 : exactInterval 15 27115 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_27115 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 27115) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_27115 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_27115 : oddCount 27115 15 = 9 ∧ acceleratedOrbit 15 27115 = 16289 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_27115 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 27115) = 3 ^ 9 * m + 16289 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_27115.1, data_15_27115.2]

/-- Complete interval computation for depth 15, residue 27116. -/
theorem bounds_15_27116 : exactInterval 15 27116 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_27116 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 27116) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_27116 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_27116 : oddCount 27116 15 = 7 ∧ acceleratedOrbit 15 27116 = 1811 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_27116 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 27116) = 3 ^ 7 * m + 1811 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_27116.1, data_15_27116.2]

/-- Complete interval computation for depth 15, residue 27117. -/
theorem bounds_15_27117 : exactInterval 15 27117 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_27117 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 27117) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_27117 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_27117 : oddCount 27117 15 = 7 ∧ acceleratedOrbit 15 27117 = 1811 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_27117 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 27117) = 3 ^ 7 * m + 1811 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_27117.1, data_15_27117.2]

/-- Complete interval computation for depth 15, residue 27118. -/
theorem bounds_15_27118 : exactInterval 15 27118 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_27118 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 27118) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_27118 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_27118 : oddCount 27118 15 = 7 ∧ acceleratedOrbit 15 27118 = 1811 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_27118 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 27118) = 3 ^ 7 * m + 1811 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_27118.1, data_15_27118.2]

/-- Complete interval computation for depth 15, residue 27119. -/
theorem bounds_15_27119 : exactInterval 15 27119 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_27119 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 27119) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_27119 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_27119 : oddCount 27119 15 = 10 ∧ acceleratedOrbit 15 27119 = 48872 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_27119 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 27119) = 3 ^ 10 * m + 48872 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_27119.1, data_15_27119.2]

/-- Complete interval computation for depth 15, residue 27120. -/
theorem bounds_15_27120 : exactInterval 15 27120 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_27120 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 27120) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_27120 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_27120 : oddCount 27120 15 = 9 ∧ acceleratedOrbit 15 27120 = 16301 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_27120 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 27120) = 3 ^ 9 * m + 16301 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_27120.1, data_15_27120.2]

/-- Complete interval computation for depth 15, residue 27121. -/
theorem bounds_15_27121 : exactInterval 15 27121 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_27121 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 27121) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_27121 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_27121 : oddCount 27121 15 = 6 ∧ acceleratedOrbit 15 27121 = 604 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_27121 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 27121) = 3 ^ 6 * m + 604 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_27121.1, data_15_27121.2]

/-- Complete interval computation for depth 15, residue 27122. -/
theorem bounds_15_27122 : exactInterval 15 27122 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_27122 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 27122) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_27122 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_27122 : oddCount 27122 15 = 7 ∧ acceleratedOrbit 15 27122 = 1811 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_27122 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 27122) = 3 ^ 7 * m + 1811 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_27122.1, data_15_27122.2]

/-- Complete interval computation for depth 15, residue 27123. -/
theorem bounds_15_27123 : exactInterval 15 27123 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_27123 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 27123) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_27123 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_27123 : oddCount 27123 15 = 7 ∧ acceleratedOrbit 15 27123 = 1811 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_27123 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 27123) = 3 ^ 7 * m + 1811 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_27123.1, data_15_27123.2]

/-- Complete interval computation for depth 15, residue 27124. -/
theorem bounds_15_27124 : exactInterval 15 27124 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_27124 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 27124) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_27124 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_27124 : oddCount 27124 15 = 9 ∧ acceleratedOrbit 15 27124 = 16301 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_27124 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 27124) = 3 ^ 9 * m + 16301 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_27124.1, data_15_27124.2]

/-- Complete interval computation for depth 15, residue 27125. -/
theorem bounds_15_27125 : exactInterval 15 27125 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_27125 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 27125) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_27125 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_27125 : oddCount 27125 15 = 9 ∧ acceleratedOrbit 15 27125 = 16301 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_27125 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 27125) = 3 ^ 9 * m + 16301 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_27125.1, data_15_27125.2]

/-- Complete interval computation for depth 15, residue 27126. -/
theorem bounds_15_27126 : exactInterval 15 27126 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_27126 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 27126) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_27126 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_27126 : oddCount 27126 15 = 8 ∧ acceleratedOrbit 15 27126 = 5432 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_27126 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 27126) = 3 ^ 8 * m + 5432 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_27126.1, data_15_27126.2]

/-- Complete interval computation for depth 15, residue 27127. -/
theorem bounds_15_27127 : exactInterval 15 27127 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_27127 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 27127) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_27127 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_27127 : oddCount 27127 15 = 8 ∧ acceleratedOrbit 15 27127 = 5432 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_27127 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 27127) = 3 ^ 8 * m + 5432 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_27127.1, data_15_27127.2]

/-- Complete interval computation for depth 15, residue 27128. -/
theorem bounds_15_27128 : exactInterval 15 27128 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_27128 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 27128) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_27128 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_27128 : oddCount 27128 15 = 9 ∧ acceleratedOrbit 15 27128 = 16301 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_27128 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 27128) = 3 ^ 9 * m + 16301 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_27128.1, data_15_27128.2]

/-- Complete interval computation for depth 15, residue 27129. -/
theorem bounds_15_27129 : exactInterval 15 27129 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_27129 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 27129) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_27129 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_27129 : oddCount 27129 15 = 9 ∧ acceleratedOrbit 15 27129 = 16298 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_27129 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 27129) = 3 ^ 9 * m + 16298 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_27129.1, data_15_27129.2]

/-- Complete interval computation for depth 15, residue 27130. -/
theorem bounds_15_27130 : exactInterval 15 27130 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_27130 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 27130) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_27130 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_27130 : oddCount 27130 15 = 9 ∧ acceleratedOrbit 15 27130 = 16301 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_27130 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 27130) = 3 ^ 9 * m + 16301 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_27130.1, data_15_27130.2]

end Collatz.Research.PassageAtlas.Batch0828
