import Collatz.Research.DescentIntervals.Classifier

namespace Collatz.Research.PassageAtlas.Batch0920

open Collatz.Research.DescentIntervals

set_option maxRecDepth 20000
set_option maxHeartbeats 0

/-- Complete interval computation for depth 15, residue 30113. -/
theorem bounds_15_30113 : exactInterval 15 30113 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_30113 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 30113) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_30113 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_30113 : oddCount 30113 15 = 6 ∧ acceleratedOrbit 15 30113 = 670 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_30113 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 30113) = 3 ^ 6 * m + 670 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_30113.1, data_15_30113.2]

/-- Complete interval computation for depth 15, residue 30114. -/
theorem bounds_15_30114 : exactInterval 15 30114 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_30114 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 30114) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_30114 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_30114 : oddCount 30114 15 = 7 ∧ acceleratedOrbit 15 30114 = 2011 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_30114 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 30114) = 3 ^ 7 * m + 2011 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_30114.1, data_15_30114.2]

/-- Complete interval computation for depth 15, residue 30115. -/
theorem bounds_15_30115 : exactInterval 15 30115 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_30115 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 30115) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_30115 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_30115 : oddCount 30115 15 = 7 ∧ acceleratedOrbit 15 30115 = 2011 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_30115 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 30115) = 3 ^ 7 * m + 2011 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_30115.1, data_15_30115.2]

/-- Complete interval computation for depth 15, residue 30116. -/
theorem bounds_15_30116 : exactInterval 15 30116 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_30116 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 30116) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_30116 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_30116 : oddCount 30116 15 = 7 ∧ acceleratedOrbit 15 30116 = 2011 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_30116 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 30116) = 3 ^ 7 * m + 2011 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_30116.1, data_15_30116.2]

/-- Complete interval computation for depth 15, residue 30117. -/
theorem bounds_15_30117 : exactInterval 15 30117 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_30117 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 30117) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_30117 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_30117 : oddCount 30117 15 = 7 ∧ acceleratedOrbit 15 30117 = 2011 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_30117 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 30117) = 3 ^ 7 * m + 2011 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_30117.1, data_15_30117.2]

/-- Complete interval computation for depth 15, residue 30118. -/
theorem bounds_15_30118 : exactInterval 15 30118 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_30118 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 30118) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_30118 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_30118 : oddCount 30118 15 = 7 ∧ acceleratedOrbit 15 30118 = 2011 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_30118 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 30118) = 3 ^ 7 * m + 2011 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_30118.1, data_15_30118.2]

/-- Complete interval computation for depth 15, residue 30119. -/
theorem bounds_15_30119 : exactInterval 15 30119 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_30119 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 30119) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_30119 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_30119 : oddCount 30119 15 = 8 ∧ acceleratedOrbit 15 30119 = 6031 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_30119 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 30119) = 3 ^ 8 * m + 6031 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_30119.1, data_15_30119.2]

/-- Complete interval computation for depth 15, residue 30120. -/
theorem bounds_15_30120 : exactInterval 15 30120 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_30120 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 30120) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_30120 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_30120 : oddCount 30120 15 = 6 ∧ acceleratedOrbit 15 30120 = 674 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_30120 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 30120) = 3 ^ 6 * m + 674 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_30120.1, data_15_30120.2]

/-- Complete interval computation for depth 15, residue 30121. -/
theorem bounds_15_30121 : exactInterval 15 30121 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_30121 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 30121) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_30121 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_30121 : oddCount 30121 15 = 10 ∧ acceleratedOrbit 15 30121 = 54283 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_30121 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 30121) = 3 ^ 10 * m + 54283 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_30121.1, data_15_30121.2]

/-- Complete interval computation for depth 15, residue 30122. -/
theorem bounds_15_30122 : exactInterval 15 30122 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_30122 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 30122) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_30122 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_30122 : oddCount 30122 15 = 6 ∧ acceleratedOrbit 15 30122 = 674 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_30122 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 30122) = 3 ^ 6 * m + 674 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_30122.1, data_15_30122.2]

/-- Complete interval computation for depth 15, residue 30123. -/
theorem bounds_15_30123 : exactInterval 15 30123 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_30123 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 30123) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_30123 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_30123 : oddCount 30123 15 = 8 ∧ acceleratedOrbit 15 30123 = 6032 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_30123 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 30123) = 3 ^ 8 * m + 6032 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_30123.1, data_15_30123.2]

/-- Complete interval computation for depth 15, residue 30124. -/
theorem bounds_15_30124 : exactInterval 15 30124 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_30124 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 30124) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_30124 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_30124 : oddCount 30124 15 = 8 ∧ acceleratedOrbit 15 30124 = 6034 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_30124 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 30124) = 3 ^ 8 * m + 6034 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_30124.1, data_15_30124.2]

/-- Complete interval computation for depth 15, residue 30125. -/
theorem bounds_15_30125 : exactInterval 15 30125 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_30125 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 30125) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_30125 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_30125 : oddCount 30125 15 = 8 ∧ acceleratedOrbit 15 30125 = 6034 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_30125 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 30125) = 3 ^ 8 * m + 6034 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_30125.1, data_15_30125.2]

/-- Complete interval computation for depth 15, residue 30126. -/
theorem bounds_15_30126 : exactInterval 15 30126 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_30126 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 30126) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_30126 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_30126 : oddCount 30126 15 = 8 ∧ acceleratedOrbit 15 30126 = 6034 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_30126 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 30126) = 3 ^ 8 * m + 6034 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_30126.1, data_15_30126.2]

/-- Complete interval computation for depth 15, residue 30127. -/
theorem bounds_15_30127 : exactInterval 15 30127 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_30127 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 30127) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_30127 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_30127 : oddCount 30127 15 = 10 ∧ acceleratedOrbit 15 30127 = 54296 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_30127 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 30127) = 3 ^ 10 * m + 54296 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_30127.1, data_15_30127.2]

/-- Complete interval computation for depth 15, residue 30128. -/
theorem bounds_15_30128 : exactInterval 15 30128 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_30128 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 30128) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_30128 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_30128 : oddCount 30128 15 = 8 ∧ acceleratedOrbit 15 30128 = 6038 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_30128 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 30128) = 3 ^ 8 * m + 6038 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_30128.1, data_15_30128.2]

/-- Complete interval computation for depth 15, residue 30129. -/
theorem bounds_15_30129 : exactInterval 15 30129 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_30129 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 30129) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_30129 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_30129 : oddCount 30129 15 = 5 ∧ acceleratedOrbit 15 30129 = 224 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_30129 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 30129) = 3 ^ 5 * m + 224 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_30129.1, data_15_30129.2]

/-- Complete interval computation for depth 15, residue 30130. -/
theorem bounds_15_30130 : exactInterval 15 30130 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_30130 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 30130) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_30130 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_30130 : oddCount 30130 15 = 5 ∧ acceleratedOrbit 15 30130 = 224 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_30130 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 30130) = 3 ^ 5 * m + 224 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_30130.1, data_15_30130.2]

/-- Complete interval computation for depth 15, residue 30131. -/
theorem bounds_15_30131 : exactInterval 15 30131 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_30131 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 30131) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_30131 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_30131 : oddCount 30131 15 = 5 ∧ acceleratedOrbit 15 30131 = 224 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_30131 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 30131) = 3 ^ 5 * m + 224 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_30131.1, data_15_30131.2]

/-- Complete interval computation for depth 15, residue 30132. -/
theorem bounds_15_30132 : exactInterval 15 30132 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_30132 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 30132) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_30132 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_30132 : oddCount 30132 15 = 8 ∧ acceleratedOrbit 15 30132 = 6038 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_30132 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 30132) = 3 ^ 8 * m + 6038 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_30132.1, data_15_30132.2]

/-- Complete interval computation for depth 15, residue 30133. -/
theorem bounds_15_30133 : exactInterval 15 30133 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_30133 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 30133) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_30133 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_30133 : oddCount 30133 15 = 8 ∧ acceleratedOrbit 15 30133 = 6038 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_30133 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 30133) = 3 ^ 8 * m + 6038 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_30133.1, data_15_30133.2]

/-- Complete interval computation for depth 15, residue 30134. -/
theorem bounds_15_30134 : exactInterval 15 30134 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_30134 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 30134) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_30134 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_30134 : oddCount 30134 15 = 10 ∧ acceleratedOrbit 15 30134 = 54310 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_30134 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 30134) = 3 ^ 10 * m + 54310 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_30134.1, data_15_30134.2]

/-- Complete interval computation for depth 15, residue 30135. -/
theorem bounds_15_30135 : exactInterval 15 30135 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_30135 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 30135) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_30135 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_30135 : oddCount 30135 15 = 10 ∧ acceleratedOrbit 15 30135 = 54310 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_30135 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 30135) = 3 ^ 10 * m + 54310 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_30135.1, data_15_30135.2]

/-- Complete interval computation for depth 15, residue 30136. -/
theorem bounds_15_30136 : exactInterval 15 30136 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_30136 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 30136) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_30136 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_30136 : oddCount 30136 15 = 8 ∧ acceleratedOrbit 15 30136 = 6038 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_30136 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 30136) = 3 ^ 8 * m + 6038 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_30136.1, data_15_30136.2]

/-- Complete interval computation for depth 15, residue 30137. -/
theorem bounds_15_30137 : exactInterval 15 30137 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_30137 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 30137) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_30137 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_30137 : oddCount 30137 15 = 5 ∧ acceleratedOrbit 15 30137 = 224 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_30137 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 30137) = 3 ^ 5 * m + 224 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_30137.1, data_15_30137.2]

/-- Complete interval computation for depth 15, residue 30138. -/
theorem bounds_15_30138 : exactInterval 15 30138 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_30138 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 30138) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_30138 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_30138 : oddCount 30138 15 = 8 ∧ acceleratedOrbit 15 30138 = 6038 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_30138 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 30138) = 3 ^ 8 * m + 6038 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_30138.1, data_15_30138.2]

/-- Complete interval computation for depth 15, residue 30139. -/
theorem bounds_15_30139 : exactInterval 15 30139 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_30139 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 30139) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_30139 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_30139 : oddCount 30139 15 = 9 ∧ acceleratedOrbit 15 30139 = 18107 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_30139 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 30139) = 3 ^ 9 * m + 18107 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_30139.1, data_15_30139.2]

/-- Complete interval computation for depth 15, residue 30140. -/
theorem bounds_15_30140 : exactInterval 15 30140 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_30140 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 30140) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_30140 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_30140 : oddCount 30140 15 = 7 ∧ acceleratedOrbit 15 30140 = 2012 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_30140 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 30140) = 3 ^ 7 * m + 2012 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_30140.1, data_15_30140.2]

/-- Complete interval computation for depth 15, residue 30141. -/
theorem bounds_15_30141 : exactInterval 15 30141 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_30141 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 30141) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_30141 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_30141 : oddCount 30141 15 = 7 ∧ acceleratedOrbit 15 30141 = 2012 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_30141 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 30141) = 3 ^ 7 * m + 2012 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_30141.1, data_15_30141.2]

/-- Complete interval computation for depth 15, residue 30142. -/
theorem bounds_15_30142 : exactInterval 15 30142 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_30142 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 30142) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_30142 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_30142 : oddCount 30142 15 = 7 ∧ acceleratedOrbit 15 30142 = 2012 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_30142 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 30142) = 3 ^ 7 * m + 2012 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_30142.1, data_15_30142.2]

/-- Complete interval computation for depth 15, residue 30143. -/
theorem bounds_15_30143 : exactInterval 15 30143 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_30143 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 30143) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_30143 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_30143 : oddCount 30143 15 = 13 ∧ acceleratedOrbit 15 30143 = 1466657 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_30143 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 30143) = 3 ^ 13 * m + 1466657 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_30143.1, data_15_30143.2]

/-- Complete interval computation for depth 15, residue 30144. -/
theorem bounds_15_30144 : exactInterval 15 30144 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_30144 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 30144) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_30144 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_30144 : oddCount 30144 15 = 6 ∧ acceleratedOrbit 15 30144 = 674 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_30144 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 30144) = 3 ^ 6 * m + 674 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_30144.1, data_15_30144.2]

/-- Complete interval computation for depth 15, residue 30145. -/
theorem bounds_15_30145 : exactInterval 15 30145 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_30145 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 30145) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_30145 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_30145 : oddCount 30145 15 = 8 ∧ acceleratedOrbit 15 30145 = 6038 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_30145 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 30145) = 3 ^ 8 * m + 6038 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_30145.1, data_15_30145.2]

end Collatz.Research.PassageAtlas.Batch0920
