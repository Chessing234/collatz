import Collatz.Research.DescentIntervals.Classifier

namespace Collatz.Research.PassageAtlas.Batch0584

open Collatz.Research.DescentIntervals

set_option maxRecDepth 20000
set_option maxHeartbeats 0

/-- Complete interval computation for depth 15, residue 19103. -/
theorem bounds_15_19103 : exactInterval 15 19103 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_19103 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 19103) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_19103 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_19103 : oddCount 19103 15 = 10 ∧ acceleratedOrbit 15 19103 = 34427 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_19103 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 19103) = 3 ^ 10 * m + 34427 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_19103.1, data_15_19103.2]

/-- Complete interval computation for depth 15, residue 19104. -/
theorem bounds_15_19104 : exactInterval 15 19104 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_19104 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 19104) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_19104 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_19104 : oddCount 19104 15 = 3 ∧ acceleratedOrbit 15 19104 = 17 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_19104 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 19104) = 3 ^ 3 * m + 17 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_19104.1, data_15_19104.2]

/-- Complete interval computation for depth 15, residue 19105. -/
theorem bounds_15_19105 : exactInterval 15 19105 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_19105 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 19105) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_19105 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_19105 : oddCount 19105 15 = 8 ∧ acceleratedOrbit 15 19105 = 3826 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_19105 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 19105) = 3 ^ 8 * m + 3826 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_19105.1, data_15_19105.2]

/-- Complete interval computation for depth 15, residue 19106. -/
theorem bounds_15_19106 : exactInterval 15 19106 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_19106 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 19106) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_19106 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_19106 : oddCount 19106 15 = 10 ∧ acceleratedOrbit 15 19106 = 34445 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_19106 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 19106) = 3 ^ 10 * m + 34445 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_19106.1, data_15_19106.2]

/-- Complete interval computation for depth 15, residue 19107. -/
theorem bounds_15_19107 : exactInterval 15 19107 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_19107 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 19107) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_19107 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_19107 : oddCount 19107 15 = 10 ∧ acceleratedOrbit 15 19107 = 34445 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_19107 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 19107) = 3 ^ 10 * m + 34445 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_19107.1, data_15_19107.2]

/-- Complete interval computation for depth 15, residue 19108. -/
theorem bounds_15_19108 : exactInterval 15 19108 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_19108 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 19108) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_19108 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_19108 : oddCount 19108 15 = 10 ∧ acceleratedOrbit 15 19108 = 34445 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_19108 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 19108) = 3 ^ 10 * m + 34445 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_19108.1, data_15_19108.2]

/-- Complete interval computation for depth 15, residue 19109. -/
theorem bounds_15_19109 : exactInterval 15 19109 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_19109 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 19109) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_19109 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_19109 : oddCount 19109 15 = 10 ∧ acceleratedOrbit 15 19109 = 34445 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_19109 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 19109) = 3 ^ 10 * m + 34445 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_19109.1, data_15_19109.2]

/-- Complete interval computation for depth 15, residue 19110. -/
theorem bounds_15_19110 : exactInterval 15 19110 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_19110 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 19110) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_19110 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_19110 : oddCount 19110 15 = 10 ∧ acceleratedOrbit 15 19110 = 34445 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_19110 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 19110) = 3 ^ 10 * m + 34445 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_19110.1, data_15_19110.2]

/-- Complete interval computation for depth 15, residue 19111. -/
theorem bounds_15_19111 : exactInterval 15 19111 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_19111 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 19111) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_19111 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_19111 : oddCount 19111 15 = 10 ∧ acceleratedOrbit 15 19111 = 34442 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_19111 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 19111) = 3 ^ 10 * m + 34442 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_19111.1, data_15_19111.2]

/-- Complete interval computation for depth 15, residue 19112. -/
theorem bounds_15_19112 : exactInterval 15 19112 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_19112 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 19112) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_19112 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_19112 : oddCount 19112 15 = 3 ∧ acceleratedOrbit 15 19112 = 17 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_19112 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 19112) = 3 ^ 3 * m + 17 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_19112.1, data_15_19112.2]

/-- Complete interval computation for depth 15, residue 19113. -/
theorem bounds_15_19113 : exactInterval 15 19113 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_19113 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 19113) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_19113 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_19113 : oddCount 19113 15 = 12 ∧ acceleratedOrbit 15 19113 = 310007 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_19113 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 19113) = 3 ^ 12 * m + 310007 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_19113.1, data_15_19113.2]

/-- Complete interval computation for depth 15, residue 19114. -/
theorem bounds_15_19114 : exactInterval 15 19114 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_19114 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 19114) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_19114 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_19114 : oddCount 19114 15 = 3 ∧ acceleratedOrbit 15 19114 = 17 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_19114 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 19114) = 3 ^ 3 * m + 17 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_19114.1, data_15_19114.2]

/-- Complete interval computation for depth 15, residue 19115. -/
theorem bounds_15_19115 : exactInterval 15 19115 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_19115 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 19115) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_19115 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_19115 : oddCount 19115 15 = 7 ∧ acceleratedOrbit 15 19115 = 1276 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_19115 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 19115) = 3 ^ 7 * m + 1276 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_19115.1, data_15_19115.2]

/-- Complete interval computation for depth 15, residue 19116. -/
theorem bounds_15_19116 : exactInterval 15 19116 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_19116 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 19116) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_19116 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_19116 : oddCount 19116 15 = 7 ∧ acceleratedOrbit 15 19116 = 1277 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_19116 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 19116) = 3 ^ 7 * m + 1277 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_19116.1, data_15_19116.2]

/-- Complete interval computation for depth 15, residue 19117. -/
theorem bounds_15_19117 : exactInterval 15 19117 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_19117 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 19117) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_19117 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_19117 : oddCount 19117 15 = 7 ∧ acceleratedOrbit 15 19117 = 1277 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_19117 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 19117) = 3 ^ 7 * m + 1277 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_19117.1, data_15_19117.2]

/-- Complete interval computation for depth 15, residue 19118. -/
theorem bounds_15_19118 : exactInterval 15 19118 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_19118 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 19118) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_19118 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_19118 : oddCount 19118 15 = 7 ∧ acceleratedOrbit 15 19118 = 1277 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_19118 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 19118) = 3 ^ 7 * m + 1277 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_19118.1, data_15_19118.2]

/-- Complete interval computation for depth 15, residue 19119. -/
theorem bounds_15_19119 : exactInterval 15 19119 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_19119 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 19119) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_19119 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_19119 : oddCount 19119 15 = 8 ∧ acceleratedOrbit 15 19119 = 3829 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_19119 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 19119) = 3 ^ 8 * m + 3829 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_19119.1, data_15_19119.2]

/-- Complete interval computation for depth 15, residue 19120. -/
theorem bounds_15_19120 : exactInterval 15 19120 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_19120 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 19120) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_19120 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_19120 : oddCount 19120 15 = 5 ∧ acceleratedOrbit 15 19120 = 142 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_19120 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 19120) = 3 ^ 5 * m + 142 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_19120.1, data_15_19120.2]

/-- Complete interval computation for depth 15, residue 19121. -/
theorem bounds_15_19121 : exactInterval 15 19121 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_19121 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 19121) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_19121 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_19121 : oddCount 19121 15 = 8 ∧ acceleratedOrbit 15 19121 = 3833 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_19121 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 19121) = 3 ^ 8 * m + 3833 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_19121.1, data_15_19121.2]

/-- Complete interval computation for depth 15, residue 19122. -/
theorem bounds_15_19122 : exactInterval 15 19122 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_19122 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 19122) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_19122 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_19122 : oddCount 19122 15 = 8 ∧ acceleratedOrbit 15 19122 = 3833 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_19122 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 19122) = 3 ^ 8 * m + 3833 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_19122.1, data_15_19122.2]

/-- Complete interval computation for depth 15, residue 19123. -/
theorem bounds_15_19123 : exactInterval 15 19123 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_19123 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 19123) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_19123 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_19123 : oddCount 19123 15 = 8 ∧ acceleratedOrbit 15 19123 = 3833 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_19123 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 19123) = 3 ^ 8 * m + 3833 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_19123.1, data_15_19123.2]

/-- Complete interval computation for depth 15, residue 19124. -/
theorem bounds_15_19124 : exactInterval 15 19124 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_19124 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 19124) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_19124 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_19124 : oddCount 19124 15 = 5 ∧ acceleratedOrbit 15 19124 = 142 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_19124 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 19124) = 3 ^ 5 * m + 142 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_19124.1, data_15_19124.2]

/-- Complete interval computation for depth 15, residue 19125. -/
theorem bounds_15_19125 : exactInterval 15 19125 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_19125 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 19125) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_19125 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_19125 : oddCount 19125 15 = 5 ∧ acceleratedOrbit 15 19125 = 142 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_19125 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 19125) = 3 ^ 5 * m + 142 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_19125.1, data_15_19125.2]

/-- Complete interval computation for depth 15, residue 19126. -/
theorem bounds_15_19126 : exactInterval 15 19126 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_19126 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 19126) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_19126 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_19126 : oddCount 19126 15 = 9 ∧ acceleratedOrbit 15 19126 = 11492 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_19126 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 19126) = 3 ^ 9 * m + 11492 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_19126.1, data_15_19126.2]

/-- Complete interval computation for depth 15, residue 19127. -/
theorem bounds_15_19127 : exactInterval 15 19127 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_19127 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 19127) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_19127 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_19127 : oddCount 19127 15 = 9 ∧ acceleratedOrbit 15 19127 = 11492 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_19127 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 19127) = 3 ^ 9 * m + 11492 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_19127.1, data_15_19127.2]

/-- Complete interval computation for depth 15, residue 19128. -/
theorem bounds_15_19128 : exactInterval 15 19128 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_19128 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 19128) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_19128 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_19128 : oddCount 19128 15 = 5 ∧ acceleratedOrbit 15 19128 = 142 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_19128 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 19128) = 3 ^ 5 * m + 142 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_19128.1, data_15_19128.2]

/-- Complete interval computation for depth 15, residue 19129. -/
theorem bounds_15_19129 : exactInterval 15 19129 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_19129 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 19129) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_19129 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_19129 : oddCount 19129 15 = 8 ∧ acceleratedOrbit 15 19129 = 3833 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_19129 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 19129) = 3 ^ 8 * m + 3833 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_19129.1, data_15_19129.2]

/-- Complete interval computation for depth 15, residue 19130. -/
theorem bounds_15_19130 : exactInterval 15 19130 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_19130 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 19130) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_19130 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_19130 : oddCount 19130 15 = 5 ∧ acceleratedOrbit 15 19130 = 142 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_19130 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 19130) = 3 ^ 5 * m + 142 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_19130.1, data_15_19130.2]

/-- Complete interval computation for depth 15, residue 19131. -/
theorem bounds_15_19131 : exactInterval 15 19131 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_19131 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 19131) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_19131 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_19131 : oddCount 19131 15 = 7 ∧ acceleratedOrbit 15 19131 = 1277 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_19131 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 19131) = 3 ^ 7 * m + 1277 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_19131.1, data_15_19131.2]

/-- Complete interval computation for depth 15, residue 19132. -/
theorem bounds_15_19132 : exactInterval 15 19132 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_19132 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 19132) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_19132 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_19132 : oddCount 19132 15 = 8 ∧ acceleratedOrbit 15 19132 = 3833 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_19132 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 19132) = 3 ^ 8 * m + 3833 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_19132.1, data_15_19132.2]

/-- Complete interval computation for depth 15, residue 19133. -/
theorem bounds_15_19133 : exactInterval 15 19133 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_19133 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 19133) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_19133 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_19133 : oddCount 19133 15 = 8 ∧ acceleratedOrbit 15 19133 = 3833 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_19133 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 19133) = 3 ^ 8 * m + 3833 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_19133.1, data_15_19133.2]

/-- Complete interval computation for depth 15, residue 19134. -/
theorem bounds_15_19134 : exactInterval 15 19134 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_19134 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 19134) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_19134 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_19134 : oddCount 19134 15 = 8 ∧ acceleratedOrbit 15 19134 = 3833 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_19134 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 19134) = 3 ^ 8 * m + 3833 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_19134.1, data_15_19134.2]

/-- Complete interval computation for depth 15, residue 19135. -/
theorem bounds_15_19135 : exactInterval 15 19135 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_19135 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 19135) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_19135 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_19135 : oddCount 19135 15 = 10 ∧ acceleratedOrbit 15 19135 = 34484 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_19135 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 19135) = 3 ^ 10 * m + 34484 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_19135.1, data_15_19135.2]

end Collatz.Research.PassageAtlas.Batch0584
