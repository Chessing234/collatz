import Collatz.Research.DescentIntervals.Classifier

namespace Collatz.Research.PassageAtlas.Batch0950

open Collatz.Research.DescentIntervals

set_option maxRecDepth 20000
set_option maxHeartbeats 0

/-- Complete interval computation for depth 15, residue 31096. -/
theorem bounds_15_31096 : exactInterval 15 31096 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_31096 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 31096) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_31096 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_31096 : oddCount 31096 15 = 6 ∧ acceleratedOrbit 15 31096 = 692 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_31096 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 31096) = 3 ^ 6 * m + 692 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_31096.1, data_15_31096.2]

/-- Complete interval computation for depth 15, residue 31097. -/
theorem bounds_15_31097 : exactInterval 15 31097 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_31097 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 31097) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_31097 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_31097 : oddCount 31097 15 = 12 ∧ acceleratedOrbit 15 31097 = 504377 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_31097 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 31097) = 3 ^ 12 * m + 504377 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_31097.1, data_15_31097.2]

/-- Complete interval computation for depth 15, residue 31098. -/
theorem bounds_15_31098 : exactInterval 15 31098 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_31098 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 31098) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_31098 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_31098 : oddCount 31098 15 = 6 ∧ acceleratedOrbit 15 31098 = 692 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_31098 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 31098) = 3 ^ 6 * m + 692 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_31098.1, data_15_31098.2]

/-- Complete interval computation for depth 15, residue 31099. -/
theorem bounds_15_31099 : exactInterval 15 31099 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_31099 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 31099) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_31099 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_31099 : oddCount 31099 15 = 9 ∧ acceleratedOrbit 15 31099 = 18683 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_31099 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 31099) = 3 ^ 9 * m + 18683 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_31099.1, data_15_31099.2]

/-- Complete interval computation for depth 15, residue 31100. -/
theorem bounds_15_31100 : exactInterval 15 31100 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_31100 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 31100) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_31100 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_31100 : oddCount 31100 15 = 6 ∧ acceleratedOrbit 15 31100 = 692 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_31100 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 31100) = 3 ^ 6 * m + 692 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_31100.1, data_15_31100.2]

/-- Complete interval computation for depth 15, residue 31101. -/
theorem bounds_15_31101 : exactInterval 15 31101 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_31101 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 31101) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_31101 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_31101 : oddCount 31101 15 = 6 ∧ acceleratedOrbit 15 31101 = 692 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_31101 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 31101) = 3 ^ 6 * m + 692 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_31101.1, data_15_31101.2]

/-- Complete interval computation for depth 15, residue 31102. -/
theorem bounds_15_31102 : exactInterval 15 31102 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_31102 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 31102) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_31102 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_31102 : oddCount 31102 15 = 11 ∧ acceleratedOrbit 15 31102 = 168155 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_31102 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 31102) = 3 ^ 11 * m + 168155 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_31102.1, data_15_31102.2]

/-- Complete interval computation for depth 15, residue 31103. -/
theorem bounds_15_31103 : exactInterval 15 31103 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_31103 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 31103) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_31103 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_31103 : oddCount 31103 15 = 11 ∧ acceleratedOrbit 15 31103 = 168155 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_31103 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 31103) = 3 ^ 11 * m + 168155 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_31103.1, data_15_31103.2]

/-- Complete interval computation for depth 15, residue 31104. -/
theorem bounds_15_31104 : exactInterval 15 31104 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_31104 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 31104) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_31104 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_31104 : oddCount 31104 15 = 5 ∧ acceleratedOrbit 15 31104 = 233 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_31104 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 31104) = 3 ^ 5 * m + 233 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_31104.1, data_15_31104.2]

/-- Complete interval computation for depth 15, residue 31105. -/
theorem bounds_15_31105 : exactInterval 15 31105 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_31105 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 31105) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_31105 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_31105 : oddCount 31105 15 = 8 ∧ acceleratedOrbit 15 31105 = 6230 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_31105 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 31105) = 3 ^ 8 * m + 6230 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_31105.1, data_15_31105.2]

/-- Complete interval computation for depth 15, residue 31106. -/
theorem bounds_15_31106 : exactInterval 15 31106 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_31106 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 31106) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_31106 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_31106 : oddCount 31106 15 = 7 ∧ acceleratedOrbit 15 31106 = 2078 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_31106 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 31106) = 3 ^ 7 * m + 2078 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_31106.1, data_15_31106.2]

/-- Complete interval computation for depth 15, residue 31107. -/
theorem bounds_15_31107 : exactInterval 15 31107 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_31107 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 31107) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_31107 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_31107 : oddCount 31107 15 = 7 ∧ acceleratedOrbit 15 31107 = 2078 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_31107 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 31107) = 3 ^ 7 * m + 2078 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_31107.1, data_15_31107.2]

/-- Complete interval computation for depth 15, residue 31108. -/
theorem bounds_15_31108 : exactInterval 15 31108 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_31108 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 31108) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_31108 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_31108 : oddCount 31108 15 = 7 ∧ acceleratedOrbit 15 31108 = 2078 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_31108 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 31108) = 3 ^ 7 * m + 2078 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_31108.1, data_15_31108.2]

/-- Complete interval computation for depth 15, residue 31109. -/
theorem bounds_15_31109 : exactInterval 15 31109 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_31109 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 31109) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_31109 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_31109 : oddCount 31109 15 = 7 ∧ acceleratedOrbit 15 31109 = 2078 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_31109 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 31109) = 3 ^ 7 * m + 2078 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_31109.1, data_15_31109.2]

/-- Complete interval computation for depth 15, residue 31110. -/
theorem bounds_15_31110 : exactInterval 15 31110 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_31110 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 31110) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_31110 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_31110 : oddCount 31110 15 = 7 ∧ acceleratedOrbit 15 31110 = 2078 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_31110 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 31110) = 3 ^ 7 * m + 2078 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_31110.1, data_15_31110.2]

/-- Complete interval computation for depth 15, residue 31111. -/
theorem bounds_15_31111 : exactInterval 15 31111 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_31111 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 31111) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_31111 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_31111 : oddCount 31111 15 = 7 ∧ acceleratedOrbit 15 31111 = 2078 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_31111 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 31111) = 3 ^ 7 * m + 2078 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_31111.1, data_15_31111.2]

/-- Complete interval computation for depth 15, residue 31112. -/
theorem bounds_15_31112 : exactInterval 15 31112 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_31112 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 31112) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_31112 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_31112 : oddCount 31112 15 = 4 ∧ acceleratedOrbit 15 31112 = 77 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_31112 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 31112) = 3 ^ 4 * m + 77 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_31112.1, data_15_31112.2]

/-- Complete interval computation for depth 15, residue 31113. -/
theorem bounds_15_31113 : exactInterval 15 31113 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_31113 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 31113) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_31113 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_31113 : oddCount 31113 15 = 10 ∧ acceleratedOrbit 15 31113 = 56072 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_31113 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 31113) = 3 ^ 10 * m + 56072 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_31113.1, data_15_31113.2]

/-- Complete interval computation for depth 15, residue 31114. -/
theorem bounds_15_31114 : exactInterval 15 31114 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_31114 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 31114) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_31114 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_31114 : oddCount 31114 15 = 4 ∧ acceleratedOrbit 15 31114 = 77 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_31114 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 31114) = 3 ^ 4 * m + 77 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_31114.1, data_15_31114.2]

/-- Complete interval computation for depth 15, residue 31115. -/
theorem bounds_15_31115 : exactInterval 15 31115 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_31115 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 31115) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_31115 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_31115 : oddCount 31115 15 = 10 ∧ acceleratedOrbit 15 31115 = 56078 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_31115 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 31115) = 3 ^ 10 * m + 56078 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_31115.1, data_15_31115.2]

/-- Complete interval computation for depth 15, residue 31116. -/
theorem bounds_15_31116 : exactInterval 15 31116 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_31116 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 31116) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_31116 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_31116 : oddCount 31116 15 = 4 ∧ acceleratedOrbit 15 31116 = 77 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_31116 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 31116) = 3 ^ 4 * m + 77 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_31116.1, data_15_31116.2]

/-- Complete interval computation for depth 15, residue 31117. -/
theorem bounds_15_31117 : exactInterval 15 31117 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_31117 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 31117) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_31117 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_31117 : oddCount 31117 15 = 4 ∧ acceleratedOrbit 15 31117 = 77 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_31117 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 31117) = 3 ^ 4 * m + 77 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_31117.1, data_15_31117.2]

/-- Complete interval computation for depth 15, residue 31118. -/
theorem bounds_15_31118 : exactInterval 15 31118 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_31118 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 31118) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_31118 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_31118 : oddCount 31118 15 = 8 ∧ acceleratedOrbit 15 31118 = 6232 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_31118 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 31118) = 3 ^ 8 * m + 6232 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_31118.1, data_15_31118.2]

/-- Complete interval computation for depth 15, residue 31119. -/
theorem bounds_15_31119 : exactInterval 15 31119 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_31119 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 31119) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_31119 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_31119 : oddCount 31119 15 = 8 ∧ acceleratedOrbit 15 31119 = 6232 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_31119 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 31119) = 3 ^ 8 * m + 6232 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_31119.1, data_15_31119.2]

/-- Complete interval computation for depth 15, residue 31120. -/
theorem bounds_15_31120 : exactInterval 15 31120 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_31120 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 31120) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_31120 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_31120 : oddCount 31120 15 = 4 ∧ acceleratedOrbit 15 31120 = 77 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_31120 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 31120) = 3 ^ 4 * m + 77 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_31120.1, data_15_31120.2]

/-- Complete interval computation for depth 15, residue 31121. -/
theorem bounds_15_31121 : exactInterval 15 31121 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_31121 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 31121) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_31121 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_31121 : oddCount 31121 15 = 8 ∧ acceleratedOrbit 15 31121 = 6236 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_31121 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 31121) = 3 ^ 8 * m + 6236 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_31121.1, data_15_31121.2]

/-- Complete interval computation for depth 15, residue 31122. -/
theorem bounds_15_31122 : exactInterval 15 31122 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_31122 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 31122) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_31122 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_31122 : oddCount 31122 15 = 8 ∧ acceleratedOrbit 15 31122 = 6236 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_31122 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 31122) = 3 ^ 8 * m + 6236 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_31122.1, data_15_31122.2]

/-- Complete interval computation for depth 15, residue 31123. -/
theorem bounds_15_31123 : exactInterval 15 31123 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_31123 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 31123) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_31123 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_31123 : oddCount 31123 15 = 8 ∧ acceleratedOrbit 15 31123 = 6236 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_31123 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 31123) = 3 ^ 8 * m + 6236 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_31123.1, data_15_31123.2]

/-- Complete interval computation for depth 15, residue 31124. -/
theorem bounds_15_31124 : exactInterval 15 31124 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_31124 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 31124) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_31124 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_31124 : oddCount 31124 15 = 4 ∧ acceleratedOrbit 15 31124 = 77 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_31124 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 31124) = 3 ^ 4 * m + 77 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_31124.1, data_15_31124.2]

/-- Complete interval computation for depth 15, residue 31125. -/
theorem bounds_15_31125 : exactInterval 15 31125 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_31125 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 31125) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_31125 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_31125 : oddCount 31125 15 = 4 ∧ acceleratedOrbit 15 31125 = 77 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_31125 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 31125) = 3 ^ 4 * m + 77 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_31125.1, data_15_31125.2]

/-- Complete interval computation for depth 15, residue 31126. -/
theorem bounds_15_31126 : exactInterval 15 31126 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_31126 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 31126) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_31126 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_31126 : oddCount 31126 15 = 8 ∧ acceleratedOrbit 15 31126 = 6236 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_31126 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 31126) = 3 ^ 8 * m + 6236 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_31126.1, data_15_31126.2]

/-- Complete interval computation for depth 15, residue 31127. -/
theorem bounds_15_31127 : exactInterval 15 31127 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_31127 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 31127) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_31127 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_31127 : oddCount 31127 15 = 8 ∧ acceleratedOrbit 15 31127 = 6236 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_31127 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 31127) = 3 ^ 8 * m + 6236 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_31127.1, data_15_31127.2]

/-- Complete interval computation for depth 15, residue 31128. -/
theorem bounds_15_31128 : exactInterval 15 31128 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_31128 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 31128) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_31128 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_31128 : oddCount 31128 15 = 4 ∧ acceleratedOrbit 15 31128 = 77 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_31128 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 31128) = 3 ^ 4 * m + 77 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_31128.1, data_15_31128.2]

end Collatz.Research.PassageAtlas.Batch0950
