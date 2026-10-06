import Collatz.Research.DescentIntervals.Classifier

namespace Collatz.Research.PassageAtlas.Batch0279

open Collatz.Research.DescentIntervals

set_option maxRecDepth 20000
set_option maxHeartbeats 0

/-- Complete interval computation for depth 15, residue 9109. -/
theorem bounds_15_9109 : exactInterval 15 9109 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_9109 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 9109) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_9109 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_9109 : oddCount 9109 15 = 7 ∧ acceleratedOrbit 15 9109 = 611 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_9109 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 9109) = 3 ^ 7 * m + 611 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_9109.1, data_15_9109.2]

/-- Complete interval computation for depth 15, residue 9110. -/
theorem bounds_15_9110 : exactInterval 15 9110 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_9110 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 9110) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_9110 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_9110 : oddCount 9110 15 = 6 ∧ acceleratedOrbit 15 9110 = 203 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_9110 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 9110) = 3 ^ 6 * m + 203 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_9110.1, data_15_9110.2]

/-- Complete interval computation for depth 15, residue 9111. -/
theorem bounds_15_9111 : exactInterval 15 9111 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_9111 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 9111) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_9111 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_9111 : oddCount 9111 15 = 6 ∧ acceleratedOrbit 15 9111 = 203 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_9111 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 9111) = 3 ^ 6 * m + 203 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_9111.1, data_15_9111.2]

/-- Complete interval computation for depth 15, residue 9112. -/
theorem bounds_15_9112 : exactInterval 15 9112 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_9112 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 9112) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_9112 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_9112 : oddCount 9112 15 = 7 ∧ acceleratedOrbit 15 9112 = 611 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_9112 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 9112) = 3 ^ 7 * m + 611 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_9112.1, data_15_9112.2]

/-- Complete interval computation for depth 15, residue 9113. -/
theorem bounds_15_9113 : exactInterval 15 9113 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_9113 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 9113) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_9113 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_9113 : oddCount 9113 15 = 6 ∧ acceleratedOrbit 15 9113 = 203 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_9113 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 9113) = 3 ^ 6 * m + 203 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_9113.1, data_15_9113.2]

/-- Complete interval computation for depth 15, residue 9114. -/
theorem bounds_15_9114 : exactInterval 15 9114 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_9114 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 9114) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_9114 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_9114 : oddCount 9114 15 = 7 ∧ acceleratedOrbit 15 9114 = 611 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_9114 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 9114) = 3 ^ 7 * m + 611 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_9114.1, data_15_9114.2]

/-- Complete interval computation for depth 15, residue 9115. -/
theorem bounds_15_9115 : exactInterval 15 9115 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_9115 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 9115) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_9115 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_9115 : oddCount 9115 15 = 8 ∧ acceleratedOrbit 15 9115 = 1826 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_9115 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 9115) = 3 ^ 8 * m + 1826 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_9115.1, data_15_9115.2]

/-- Complete interval computation for depth 15, residue 9116. -/
theorem bounds_15_9116 : exactInterval 15 9116 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_9116 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 9116) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_9116 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_9116 : oddCount 9116 15 = 9 ∧ acceleratedOrbit 15 9116 = 5480 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_9116 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 9116) = 3 ^ 9 * m + 5480 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_9116.1, data_15_9116.2]

/-- Complete interval computation for depth 15, residue 9117. -/
theorem bounds_15_9117 : exactInterval 15 9117 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_9117 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 9117) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_9117 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_9117 : oddCount 9117 15 = 9 ∧ acceleratedOrbit 15 9117 = 5480 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_9117 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 9117) = 3 ^ 9 * m + 5480 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_9117.1, data_15_9117.2]

/-- Complete interval computation for depth 15, residue 9118. -/
theorem bounds_15_9118 : exactInterval 15 9118 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_9118 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 9118) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_9118 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_9118 : oddCount 9118 15 = 9 ∧ acceleratedOrbit 15 9118 = 5480 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_9118 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 9118) = 3 ^ 9 * m + 5480 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_9118.1, data_15_9118.2]

/-- Complete interval computation for depth 15, residue 9119. -/
theorem bounds_15_9119 : exactInterval 15 9119 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_9119 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 9119) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_9119 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_9119 : oddCount 9119 15 = 10 ∧ acceleratedOrbit 15 9119 = 16436 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_9119 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 9119) = 3 ^ 10 * m + 16436 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_9119.1, data_15_9119.2]

/-- Complete interval computation for depth 15, residue 9120. -/
theorem bounds_15_9120 : exactInterval 15 9120 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_9120 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 9120) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_9120 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_9120 : oddCount 9120 15 = 6 ∧ acceleratedOrbit 15 9120 = 206 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_9120 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 9120) = 3 ^ 6 * m + 206 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_9120.1, data_15_9120.2]

/-- Complete interval computation for depth 15, residue 9121. -/
theorem bounds_15_9121 : exactInterval 15 9121 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_9121 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 9121) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_9121 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_9121 : oddCount 9121 15 = 6 ∧ acceleratedOrbit 15 9121 = 203 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_9121 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 9121) = 3 ^ 6 * m + 203 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_9121.1, data_15_9121.2]

/-- Complete interval computation for depth 15, residue 9122. -/
theorem bounds_15_9122 : exactInterval 15 9122 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_9122 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 9122) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_9122 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_9122 : oddCount 9122 15 = 7 ∧ acceleratedOrbit 15 9122 = 611 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_9122 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 9122) = 3 ^ 7 * m + 611 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_9122.1, data_15_9122.2]

/-- Complete interval computation for depth 15, residue 9123. -/
theorem bounds_15_9123 : exactInterval 15 9123 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_9123 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 9123) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_9123 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_9123 : oddCount 9123 15 = 7 ∧ acceleratedOrbit 15 9123 = 611 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_9123 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 9123) = 3 ^ 7 * m + 611 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_9123.1, data_15_9123.2]

/-- Complete interval computation for depth 15, residue 9124. -/
theorem bounds_15_9124 : exactInterval 15 9124 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_9124 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 9124) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_9124 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_9124 : oddCount 9124 15 = 8 ∧ acceleratedOrbit 15 9124 = 1829 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_9124 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 9124) = 3 ^ 8 * m + 1829 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_9124.1, data_15_9124.2]

/-- Complete interval computation for depth 15, residue 9125. -/
theorem bounds_15_9125 : exactInterval 15 9125 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_9125 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 9125) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_9125 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_9125 : oddCount 9125 15 = 8 ∧ acceleratedOrbit 15 9125 = 1829 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_9125 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 9125) = 3 ^ 8 * m + 1829 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_9125.1, data_15_9125.2]

/-- Complete interval computation for depth 15, residue 9126. -/
theorem bounds_15_9126 : exactInterval 15 9126 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_9126 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 9126) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_9126 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_9126 : oddCount 9126 15 = 8 ∧ acceleratedOrbit 15 9126 = 1829 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_9126 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 9126) = 3 ^ 8 * m + 1829 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_9126.1, data_15_9126.2]

/-- Complete interval computation for depth 15, residue 9127. -/
theorem bounds_15_9127 : exactInterval 15 9127 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_9127 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 9127) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_9127 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_9127 : oddCount 9127 15 = 8 ∧ acceleratedOrbit 15 9127 = 1828 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_9127 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 9127) = 3 ^ 8 * m + 1828 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_9127.1, data_15_9127.2]

/-- Complete interval computation for depth 15, residue 9128. -/
theorem bounds_15_9128 : exactInterval 15 9128 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_9128 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 9128) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_9128 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_9128 : oddCount 9128 15 = 6 ∧ acceleratedOrbit 15 9128 = 206 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_9128 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 9128) = 3 ^ 6 * m + 206 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_9128.1, data_15_9128.2]

/-- Complete interval computation for depth 15, residue 9129. -/
theorem bounds_15_9129 : exactInterval 15 9129 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_9129 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 9129) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_9129 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_9129 : oddCount 9129 15 = 10 ∧ acceleratedOrbit 15 9129 = 16454 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_9129 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 9129) = 3 ^ 10 * m + 16454 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_9129.1, data_15_9129.2]

/-- Complete interval computation for depth 15, residue 9130. -/
theorem bounds_15_9130 : exactInterval 15 9130 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_9130 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 9130) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_9130 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_9130 : oddCount 9130 15 = 6 ∧ acceleratedOrbit 15 9130 = 206 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_9130 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 9130) = 3 ^ 6 * m + 206 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_9130.1, data_15_9130.2]

/-- Complete interval computation for depth 15, residue 9131. -/
theorem bounds_15_9131 : exactInterval 15 9131 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_9131 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 9131) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_9131 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_9131 : oddCount 9131 15 = 8 ∧ acceleratedOrbit 15 9131 = 1829 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_9131 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 9131) = 3 ^ 8 * m + 1829 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_9131.1, data_15_9131.2]

/-- Complete interval computation for depth 15, residue 9132. -/
theorem bounds_15_9132 : exactInterval 15 9132 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_9132 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 9132) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_9132 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_9132 : oddCount 9132 15 = 7 ∧ acceleratedOrbit 15 9132 = 610 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_9132 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 9132) = 3 ^ 7 * m + 610 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_9132.1, data_15_9132.2]

/-- Complete interval computation for depth 15, residue 9133. -/
theorem bounds_15_9133 : exactInterval 15 9133 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_9133 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 9133) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_9133 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_9133 : oddCount 9133 15 = 7 ∧ acceleratedOrbit 15 9133 = 610 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_9133 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 9133) = 3 ^ 7 * m + 610 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_9133.1, data_15_9133.2]

/-- Complete interval computation for depth 15, residue 9134. -/
theorem bounds_15_9134 : exactInterval 15 9134 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_9134 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 9134) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_9134 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_9134 : oddCount 9134 15 = 7 ∧ acceleratedOrbit 15 9134 = 610 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_9134 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 9134) = 3 ^ 7 * m + 610 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_9134.1, data_15_9134.2]

/-- Complete interval computation for depth 15, residue 9135. -/
theorem bounds_15_9135 : exactInterval 15 9135 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_9135 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 9135) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_9135 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_9135 : oddCount 9135 15 = 7 ∧ acceleratedOrbit 15 9135 = 611 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_9135 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 9135) = 3 ^ 7 * m + 611 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_9135.1, data_15_9135.2]

/-- Complete interval computation for depth 15, residue 9136. -/
theorem bounds_15_9136 : exactInterval 15 9136 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_9136 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 9136) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_9136 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_9136 : oddCount 9136 15 = 5 ∧ acceleratedOrbit 15 9136 = 68 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_9136 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 9136) = 3 ^ 5 * m + 68 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_9136.1, data_15_9136.2]

/-- Complete interval computation for depth 15, residue 9137. -/
theorem bounds_15_9137 : exactInterval 15 9137 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_9137 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 9137) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_9137 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_9137 : oddCount 9137 15 = 5 ∧ acceleratedOrbit 15 9137 = 68 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_9137 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 9137) = 3 ^ 5 * m + 68 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_9137.1, data_15_9137.2]

/-- Complete interval computation for depth 15, residue 9138. -/
theorem bounds_15_9138 : exactInterval 15 9138 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_9138 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 9138) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_9138 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_9138 : oddCount 9138 15 = 5 ∧ acceleratedOrbit 15 9138 = 68 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_9138 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 9138) = 3 ^ 5 * m + 68 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_9138.1, data_15_9138.2]

/-- Complete interval computation for depth 15, residue 9139. -/
theorem bounds_15_9139 : exactInterval 15 9139 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_9139 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 9139) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_9139 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_9139 : oddCount 9139 15 = 5 ∧ acceleratedOrbit 15 9139 = 68 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_9139 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 9139) = 3 ^ 5 * m + 68 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_9139.1, data_15_9139.2]

/-- Complete interval computation for depth 15, residue 9140. -/
theorem bounds_15_9140 : exactInterval 15 9140 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_9140 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 9140) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_9140 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_9140 : oddCount 9140 15 = 5 ∧ acceleratedOrbit 15 9140 = 68 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_9140 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 9140) = 3 ^ 5 * m + 68 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_9140.1, data_15_9140.2]

/-- Complete interval computation for depth 15, residue 9141. -/
theorem bounds_15_9141 : exactInterval 15 9141 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_9141 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 9141) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_9141 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_9141 : oddCount 9141 15 = 5 ∧ acceleratedOrbit 15 9141 = 68 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_9141 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 9141) = 3 ^ 5 * m + 68 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_9141.1, data_15_9141.2]

end Collatz.Research.PassageAtlas.Batch0279
