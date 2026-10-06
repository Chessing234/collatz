import Collatz.Research.DescentIntervals.Classifier

namespace Collatz.Research.PassageAtlas.Batch0859

open Collatz.Research.DescentIntervals

set_option maxRecDepth 20000
set_option maxHeartbeats 0

/-- Complete interval computation for depth 15, residue 28114. -/
theorem bounds_15_28114 : exactInterval 15 28114 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_28114 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 28114) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_28114 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_28114 : oddCount 28114 15 = 8 ∧ acceleratedOrbit 15 28114 = 5630 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_28114 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 28114) = 3 ^ 8 * m + 5630 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_28114.1, data_15_28114.2]

/-- Complete interval computation for depth 15, residue 28115. -/
theorem bounds_15_28115 : exactInterval 15 28115 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_28115 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 28115) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_28115 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_28115 : oddCount 28115 15 = 8 ∧ acceleratedOrbit 15 28115 = 5630 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_28115 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 28115) = 3 ^ 8 * m + 5630 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_28115.1, data_15_28115.2]

/-- Complete interval computation for depth 15, residue 28116. -/
theorem bounds_15_28116 : exactInterval 15 28116 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_28116 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 28116) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_28116 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_28116 : oddCount 28116 15 = 5 ∧ acceleratedOrbit 15 28116 = 209 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_28116 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 28116) = 3 ^ 5 * m + 209 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_28116.1, data_15_28116.2]

/-- Complete interval computation for depth 15, residue 28117. -/
theorem bounds_15_28117 : exactInterval 15 28117 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_28117 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 28117) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_28117 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_28117 : oddCount 28117 15 = 5 ∧ acceleratedOrbit 15 28117 = 209 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_28117 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 28117) = 3 ^ 5 * m + 209 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_28117.1, data_15_28117.2]

/-- Complete interval computation for depth 15, residue 28118. -/
theorem bounds_15_28118 : exactInterval 15 28118 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_28118 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 28118) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_28118 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_28118 : oddCount 28118 15 = 7 ∧ acceleratedOrbit 15 28118 = 1877 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_28118 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 28118) = 3 ^ 7 * m + 1877 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_28118.1, data_15_28118.2]

/-- Complete interval computation for depth 15, residue 28119. -/
theorem bounds_15_28119 : exactInterval 15 28119 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_28119 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 28119) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_28119 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_28119 : oddCount 28119 15 = 7 ∧ acceleratedOrbit 15 28119 = 1877 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_28119 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 28119) = 3 ^ 7 * m + 1877 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_28119.1, data_15_28119.2]

/-- Complete interval computation for depth 15, residue 28120. -/
theorem bounds_15_28120 : exactInterval 15 28120 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_28120 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 28120) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_28120 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_28120 : oddCount 28120 15 = 6 ∧ acceleratedOrbit 15 28120 = 626 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_28120 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 28120) = 3 ^ 6 * m + 626 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_28120.1, data_15_28120.2]

/-- Complete interval computation for depth 15, residue 28121. -/
theorem bounds_15_28121 : exactInterval 15 28121 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_28121 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 28121) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_28121 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_28121 : oddCount 28121 15 = 6 ∧ acceleratedOrbit 15 28121 = 626 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_28121 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 28121) = 3 ^ 6 * m + 626 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_28121.1, data_15_28121.2]

/-- Complete interval computation for depth 15, residue 28122. -/
theorem bounds_15_28122 : exactInterval 15 28122 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_28122 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 28122) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_28122 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_28122 : oddCount 28122 15 = 6 ∧ acceleratedOrbit 15 28122 = 626 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_28122 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 28122) = 3 ^ 6 * m + 626 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_28122.1, data_15_28122.2]

/-- Complete interval computation for depth 15, residue 28123. -/
theorem bounds_15_28123 : exactInterval 15 28123 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_28123 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 28123) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_28123 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_28123 : oddCount 28123 15 = 8 ∧ acceleratedOrbit 15 28123 = 5633 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_28123 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 28123) = 3 ^ 8 * m + 5633 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_28123.1, data_15_28123.2]

/-- Complete interval computation for depth 15, residue 28124. -/
theorem bounds_15_28124 : exactInterval 15 28124 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_28124 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 28124) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_28124 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_28124 : oddCount 28124 15 = 6 ∧ acceleratedOrbit 15 28124 = 626 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_28124 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 28124) = 3 ^ 6 * m + 626 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_28124.1, data_15_28124.2]

/-- Complete interval computation for depth 15, residue 28125. -/
theorem bounds_15_28125 : exactInterval 15 28125 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_28125 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 28125) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_28125 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_28125 : oddCount 28125 15 = 6 ∧ acceleratedOrbit 15 28125 = 626 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_28125 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 28125) = 3 ^ 6 * m + 626 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_28125.1, data_15_28125.2]

/-- Complete interval computation for depth 15, residue 28126. -/
theorem bounds_15_28126 : exactInterval 15 28126 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_28126 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 28126) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_28126 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_28126 : oddCount 28126 15 = 8 ∧ acceleratedOrbit 15 28126 = 5632 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_28126 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 28126) = 3 ^ 8 * m + 5632 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_28126.1, data_15_28126.2]

/-- Complete interval computation for depth 15, residue 28127. -/
theorem bounds_15_28127 : exactInterval 15 28127 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_28127 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 28127) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_28127 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_28127 : oddCount 28127 15 = 8 ∧ acceleratedOrbit 15 28127 = 5632 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_28127 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 28127) = 3 ^ 8 * m + 5632 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_28127.1, data_15_28127.2]

/-- Complete interval computation for depth 15, residue 28128. -/
theorem bounds_15_28128 : exactInterval 15 28128 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_28128 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 28128) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_28128 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_28128 : oddCount 28128 15 = 7 ∧ acceleratedOrbit 15 28128 = 1880 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_28128 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 28128) = 3 ^ 7 * m + 1880 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_28128.1, data_15_28128.2]

/-- Complete interval computation for depth 15, residue 28129. -/
theorem bounds_15_28129 : exactInterval 15 28129 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_28129 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 28129) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_28129 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_28129 : oddCount 28129 15 = 10 ∧ acceleratedOrbit 15 28129 = 50696 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_28129 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 28129) = 3 ^ 10 * m + 50696 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_28129.1, data_15_28129.2]

/-- Complete interval computation for depth 15, residue 28130. -/
theorem bounds_15_28130 : exactInterval 15 28130 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_28130 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 28130) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_28130 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_28130 : oddCount 28130 15 = 5 ∧ acceleratedOrbit 15 28130 = 209 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_28130 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 28130) = 3 ^ 5 * m + 209 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_28130.1, data_15_28130.2]

/-- Complete interval computation for depth 15, residue 28131. -/
theorem bounds_15_28131 : exactInterval 15 28131 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_28131 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 28131) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_28131 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_28131 : oddCount 28131 15 = 5 ∧ acceleratedOrbit 15 28131 = 209 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_28131 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 28131) = 3 ^ 5 * m + 209 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_28131.1, data_15_28131.2]

/-- Complete interval computation for depth 15, residue 28132. -/
theorem bounds_15_28132 : exactInterval 15 28132 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_28132 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 28132) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_28132 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_28132 : oddCount 28132 15 = 9 ∧ acceleratedOrbit 15 28132 = 16904 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_28132 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 28132) = 3 ^ 9 * m + 16904 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_28132.1, data_15_28132.2]

/-- Complete interval computation for depth 15, residue 28133. -/
theorem bounds_15_28133 : exactInterval 15 28133 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_28133 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 28133) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_28133 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_28133 : oddCount 28133 15 = 9 ∧ acceleratedOrbit 15 28133 = 16904 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_28133 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 28133) = 3 ^ 9 * m + 16904 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_28133.1, data_15_28133.2]

/-- Complete interval computation for depth 15, residue 28134. -/
theorem bounds_15_28134 : exactInterval 15 28134 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_28134 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 28134) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_28134 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_28134 : oddCount 28134 15 = 9 ∧ acceleratedOrbit 15 28134 = 16904 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_28134 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 28134) = 3 ^ 9 * m + 16904 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_28134.1, data_15_28134.2]

/-- Complete interval computation for depth 15, residue 28135. -/
theorem bounds_15_28135 : exactInterval 15 28135 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_28135 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 28135) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_28135 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_28135 : oddCount 28135 15 = 10 ∧ acceleratedOrbit 15 28135 = 50705 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_28135 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 28135) = 3 ^ 10 * m + 50705 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_28135.1, data_15_28135.2]

/-- Complete interval computation for depth 15, residue 28136. -/
theorem bounds_15_28136 : exactInterval 15 28136 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_28136 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 28136) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_28136 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_28136 : oddCount 28136 15 = 7 ∧ acceleratedOrbit 15 28136 = 1880 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_28136 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 28136) = 3 ^ 7 * m + 1880 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_28136.1, data_15_28136.2]

/-- Complete interval computation for depth 15, residue 28137. -/
theorem bounds_15_28137 : exactInterval 15 28137 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_28137 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 28137) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_28137 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_28137 : oddCount 28137 15 = 10 ∧ acceleratedOrbit 15 28137 = 50708 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_28137 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 28137) = 3 ^ 10 * m + 50708 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_28137.1, data_15_28137.2]

/-- Complete interval computation for depth 15, residue 28138. -/
theorem bounds_15_28138 : exactInterval 15 28138 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_28138 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 28138) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_28138 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_28138 : oddCount 28138 15 = 7 ∧ acceleratedOrbit 15 28138 = 1880 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_28138 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 28138) = 3 ^ 7 * m + 1880 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_28138.1, data_15_28138.2]

/-- Complete interval computation for depth 15, residue 28139. -/
theorem bounds_15_28139 : exactInterval 15 28139 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_28139 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 28139) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_28139 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_28139 : oddCount 28139 15 = 10 ∧ acceleratedOrbit 15 28139 = 50711 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_28139 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 28139) = 3 ^ 10 * m + 50711 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_28139.1, data_15_28139.2]

/-- Complete interval computation for depth 15, residue 28140. -/
theorem bounds_15_28140 : exactInterval 15 28140 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_28140 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 28140) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_28140 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_28140 : oddCount 28140 15 = 8 ∧ acceleratedOrbit 15 28140 = 5636 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_28140 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 28140) = 3 ^ 8 * m + 5636 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_28140.1, data_15_28140.2]

/-- Complete interval computation for depth 15, residue 28141. -/
theorem bounds_15_28141 : exactInterval 15 28141 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_28141 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 28141) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_28141 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_28141 : oddCount 28141 15 = 8 ∧ acceleratedOrbit 15 28141 = 5636 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_28141 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 28141) = 3 ^ 8 * m + 5636 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_28141.1, data_15_28141.2]

/-- Complete interval computation for depth 15, residue 28142. -/
theorem bounds_15_28142 : exactInterval 15 28142 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_28142 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 28142) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_28142 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_28142 : oddCount 28142 15 = 8 ∧ acceleratedOrbit 15 28142 = 5636 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_28142 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 28142) = 3 ^ 8 * m + 5636 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_28142.1, data_15_28142.2]

/-- Complete interval computation for depth 15, residue 28143. -/
theorem bounds_15_28143 : exactInterval 15 28143 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_28143 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 28143) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_28143 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_28143 : oddCount 28143 15 = 10 ∧ acceleratedOrbit 15 28143 = 50717 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_28143 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 28143) = 3 ^ 10 * m + 50717 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_28143.1, data_15_28143.2]

/-- Complete interval computation for depth 15, residue 28144. -/
theorem bounds_15_28144 : exactInterval 15 28144 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_28144 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 28144) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_28144 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_28144 : oddCount 28144 15 = 7 ∧ acceleratedOrbit 15 28144 = 1880 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_28144 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 28144) = 3 ^ 7 * m + 1880 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_28144.1, data_15_28144.2]

/-- Complete interval computation for depth 15, residue 28145. -/
theorem bounds_15_28145 : exactInterval 15 28145 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_28145 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 28145) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_28145 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_28145 : oddCount 28145 15 = 7 ∧ acceleratedOrbit 15 28145 = 1880 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_28145 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 28145) = 3 ^ 7 * m + 1880 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_28145.1, data_15_28145.2]

/-- Complete interval computation for depth 15, residue 28146. -/
theorem bounds_15_28146 : exactInterval 15 28146 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_28146 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 28146) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_28146 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_28146 : oddCount 28146 15 = 7 ∧ acceleratedOrbit 15 28146 = 1880 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_28146 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 28146) = 3 ^ 7 * m + 1880 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_28146.1, data_15_28146.2]

end Collatz.Research.PassageAtlas.Batch0859
