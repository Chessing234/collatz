import Collatz.Research.DescentIntervals.Classifier

namespace Collatz.Research.PassageAtlas.Batch0676

open Collatz.Research.DescentIntervals

set_option maxRecDepth 20000
set_option maxHeartbeats 0

/-- Complete interval computation for depth 15, residue 22118. -/
theorem bounds_15_22118 : exactInterval 15 22118 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_22118 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 22118) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_22118 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_22118 : oddCount 22118 15 = 7 ∧ acceleratedOrbit 15 22118 = 1478 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_22118 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 22118) = 3 ^ 7 * m + 1478 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_22118.1, data_15_22118.2]

/-- Complete interval computation for depth 15, residue 22119. -/
theorem bounds_15_22119 : exactInterval 15 22119 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_22119 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 22119) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_22119 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_22119 : oddCount 22119 15 = 10 ∧ acceleratedOrbit 15 22119 = 39862 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_22119 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 22119) = 3 ^ 10 * m + 39862 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_22119.1, data_15_22119.2]

/-- Complete interval computation for depth 15, residue 22120. -/
theorem bounds_15_22120 : exactInterval 15 22120 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_22120 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 22120) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_22120 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_22120 : oddCount 22120 15 = 4 ∧ acceleratedOrbit 15 22120 = 55 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_22120 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 22120) = 3 ^ 4 * m + 55 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_22120.1, data_15_22120.2]

/-- Complete interval computation for depth 15, residue 22121. -/
theorem bounds_15_22121 : exactInterval 15 22121 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_22121 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 22121) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_22121 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_22121 : oddCount 22121 15 = 9 ∧ acceleratedOrbit 15 22121 = 13289 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_22121 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 22121) = 3 ^ 9 * m + 13289 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_22121.1, data_15_22121.2]

/-- Complete interval computation for depth 15, residue 22122. -/
theorem bounds_15_22122 : exactInterval 15 22122 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_22122 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 22122) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_22122 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_22122 : oddCount 22122 15 = 4 ∧ acceleratedOrbit 15 22122 = 55 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_22122 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 22122) = 3 ^ 4 * m + 55 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_22122.1, data_15_22122.2]

/-- Complete interval computation for depth 15, residue 22123. -/
theorem bounds_15_22123 : exactInterval 15 22123 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_22123 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 22123) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_22123 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_22123 : oddCount 22123 15 = 10 ∧ acceleratedOrbit 15 22123 = 39872 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_22123 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 22123) = 3 ^ 10 * m + 39872 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_22123.1, data_15_22123.2]

/-- Complete interval computation for depth 15, residue 22124. -/
theorem bounds_15_22124 : exactInterval 15 22124 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_22124 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 22124) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_22124 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_22124 : oddCount 22124 15 = 7 ∧ acceleratedOrbit 15 22124 = 1477 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_22124 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 22124) = 3 ^ 7 * m + 1477 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_22124.1, data_15_22124.2]

/-- Complete interval computation for depth 15, residue 22125. -/
theorem bounds_15_22125 : exactInterval 15 22125 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_22125 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 22125) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_22125 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_22125 : oddCount 22125 15 = 7 ∧ acceleratedOrbit 15 22125 = 1477 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_22125 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 22125) = 3 ^ 7 * m + 1477 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_22125.1, data_15_22125.2]

/-- Complete interval computation for depth 15, residue 22126. -/
theorem bounds_15_22126 : exactInterval 15 22126 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_22126 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 22126) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_22126 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_22126 : oddCount 22126 15 = 7 ∧ acceleratedOrbit 15 22126 = 1477 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_22126 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 22126) = 3 ^ 7 * m + 1477 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_22126.1, data_15_22126.2]

/-- Complete interval computation for depth 15, residue 22127. -/
theorem bounds_15_22127 : exactInterval 15 22127 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_22127 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 22127) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_22127 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_22127 : oddCount 22127 15 = 10 ∧ acceleratedOrbit 15 22127 = 39878 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_22127 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 22127) = 3 ^ 10 * m + 39878 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_22127.1, data_15_22127.2]

/-- Complete interval computation for depth 15, residue 22128. -/
theorem bounds_15_22128 : exactInterval 15 22128 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_22128 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 22128) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_22128 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_22128 : oddCount 22128 15 = 9 ∧ acceleratedOrbit 15 22128 = 13304 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_22128 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 22128) = 3 ^ 9 * m + 13304 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_22128.1, data_15_22128.2]

/-- Complete interval computation for depth 15, residue 22129. -/
theorem bounds_15_22129 : exactInterval 15 22129 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_22129 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 22129) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_22129 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_22129 : oddCount 22129 15 = 4 ∧ acceleratedOrbit 15 22129 = 55 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_22129 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 22129) = 3 ^ 4 * m + 55 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_22129.1, data_15_22129.2]

/-- Complete interval computation for depth 15, residue 22130. -/
theorem bounds_15_22130 : exactInterval 15 22130 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_22130 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 22130) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_22130 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_22130 : oddCount 22130 15 = 9 ∧ acceleratedOrbit 15 22130 = 13297 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_22130 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 22130) = 3 ^ 9 * m + 13297 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_22130.1, data_15_22130.2]

/-- Complete interval computation for depth 15, residue 22131. -/
theorem bounds_15_22131 : exactInterval 15 22131 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_22131 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 22131) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_22131 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_22131 : oddCount 22131 15 = 9 ∧ acceleratedOrbit 15 22131 = 13297 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_22131 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 22131) = 3 ^ 9 * m + 13297 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_22131.1, data_15_22131.2]

/-- Complete interval computation for depth 15, residue 22132. -/
theorem bounds_15_22132 : exactInterval 15 22132 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_22132 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 22132) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_22132 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_22132 : oddCount 22132 15 = 9 ∧ acceleratedOrbit 15 22132 = 13304 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_22132 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 22132) = 3 ^ 9 * m + 13304 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_22132.1, data_15_22132.2]

/-- Complete interval computation for depth 15, residue 22133. -/
theorem bounds_15_22133 : exactInterval 15 22133 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_22133 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 22133) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_22133 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_22133 : oddCount 22133 15 = 9 ∧ acceleratedOrbit 15 22133 = 13304 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_22133 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 22133) = 3 ^ 9 * m + 13304 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_22133.1, data_15_22133.2]

/-- Complete interval computation for depth 15, residue 22134. -/
theorem bounds_15_22134 : exactInterval 15 22134 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_22134 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 22134) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_22134 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_22134 : oddCount 22134 15 = 7 ∧ acceleratedOrbit 15 22134 = 1478 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_22134 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 22134) = 3 ^ 7 * m + 1478 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_22134.1, data_15_22134.2]

/-- Complete interval computation for depth 15, residue 22135. -/
theorem bounds_15_22135 : exactInterval 15 22135 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_22135 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 22135) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_22135 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_22135 : oddCount 22135 15 = 7 ∧ acceleratedOrbit 15 22135 = 1478 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_22135 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 22135) = 3 ^ 7 * m + 1478 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_22135.1, data_15_22135.2]

/-- Complete interval computation for depth 15, residue 22136. -/
theorem bounds_15_22136 : exactInterval 15 22136 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_22136 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 22136) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_22136 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_22136 : oddCount 22136 15 = 9 ∧ acceleratedOrbit 15 22136 = 13304 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_22136 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 22136) = 3 ^ 9 * m + 13304 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_22136.1, data_15_22136.2]

/-- Complete interval computation for depth 15, residue 22137. -/
theorem bounds_15_22137 : exactInterval 15 22137 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_22137 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 22137) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_22137 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_22137 : oddCount 22137 15 = 8 ∧ acceleratedOrbit 15 22137 = 4433 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_22137 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 22137) = 3 ^ 8 * m + 4433 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_22137.1, data_15_22137.2]

/-- Complete interval computation for depth 15, residue 22138. -/
theorem bounds_15_22138 : exactInterval 15 22138 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_22138 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 22138) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_22138 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_22138 : oddCount 22138 15 = 9 ∧ acceleratedOrbit 15 22138 = 13304 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_22138 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 22138) = 3 ^ 9 * m + 13304 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_22138.1, data_15_22138.2]

/-- Complete interval computation for depth 15, residue 22139. -/
theorem bounds_15_22139 : exactInterval 15 22139 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_22139 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 22139) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_22139 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_22139 : oddCount 22139 15 = 7 ∧ acceleratedOrbit 15 22139 = 1478 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_22139 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 22139) = 3 ^ 7 * m + 1478 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_22139.1, data_15_22139.2]

/-- Complete interval computation for depth 15, residue 22140. -/
theorem bounds_15_22140 : exactInterval 15 22140 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_22140 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 22140) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_22140 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_22140 : oddCount 22140 15 = 11 ∧ acceleratedOrbit 15 22140 = 119717 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_22140 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 22140) = 3 ^ 11 * m + 119717 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_22140.1, data_15_22140.2]

/-- Complete interval computation for depth 15, residue 22141. -/
theorem bounds_15_22141 : exactInterval 15 22141 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_22141 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 22141) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_22141 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_22141 : oddCount 22141 15 = 11 ∧ acceleratedOrbit 15 22141 = 119717 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_22141 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 22141) = 3 ^ 11 * m + 119717 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_22141.1, data_15_22141.2]

/-- Complete interval computation for depth 15, residue 22142. -/
theorem bounds_15_22142 : exactInterval 15 22142 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_22142 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 22142) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_22142 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_22142 : oddCount 22142 15 = 11 ∧ acceleratedOrbit 15 22142 = 119717 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_22142 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 22142) = 3 ^ 11 * m + 119717 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_22142.1, data_15_22142.2]

/-- Complete interval computation for depth 15, residue 22143. -/
theorem bounds_15_22143 : exactInterval 15 22143 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_22143 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 22143) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_22143 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_22143 : oddCount 22143 15 = 11 ∧ acceleratedOrbit 15 22143 = 119713 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_22143 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 22143) = 3 ^ 11 * m + 119713 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_22143.1, data_15_22143.2]

/-- Complete interval computation for depth 15, residue 22144. -/
theorem bounds_15_22144 : exactInterval 15 22144 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_22144 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 22144) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_22144 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_22144 : oddCount 22144 15 = 4 ∧ acceleratedOrbit 15 22144 = 56 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_22144 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 22144) = 3 ^ 4 * m + 56 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_22144.1, data_15_22144.2]

/-- Complete interval computation for depth 15, residue 22145. -/
theorem bounds_15_22145 : exactInterval 15 22145 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_22145 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 22145) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_22145 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_22145 : oddCount 22145 15 = 11 ∧ acceleratedOrbit 15 22145 = 119738 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_22145 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 22145) = 3 ^ 11 * m + 119738 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_22145.1, data_15_22145.2]

/-- Complete interval computation for depth 15, residue 22146. -/
theorem bounds_15_22146 : exactInterval 15 22146 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_22146 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 22146) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_22146 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_22146 : oddCount 22146 15 = 4 ∧ acceleratedOrbit 15 22146 = 55 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_22146 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 22146) = 3 ^ 4 * m + 55 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_22146.1, data_15_22146.2]

/-- Complete interval computation for depth 15, residue 22147. -/
theorem bounds_15_22147 : exactInterval 15 22147 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_22147 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 22147) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_22147 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_22147 : oddCount 22147 15 = 4 ∧ acceleratedOrbit 15 22147 = 55 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_22147 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 22147) = 3 ^ 4 * m + 55 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_22147.1, data_15_22147.2]

/-- Complete interval computation for depth 15, residue 22148. -/
theorem bounds_15_22148 : exactInterval 15 22148 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_22148 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 22148) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_22148 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_22148 : oddCount 22148 15 = 6 ∧ acceleratedOrbit 15 22148 = 493 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_22148 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 22148) = 3 ^ 6 * m + 493 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_22148.1, data_15_22148.2]

/-- Complete interval computation for depth 15, residue 22149. -/
theorem bounds_15_22149 : exactInterval 15 22149 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_22149 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 22149) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_22149 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_22149 : oddCount 22149 15 = 6 ∧ acceleratedOrbit 15 22149 = 493 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_22149 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 22149) = 3 ^ 6 * m + 493 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_22149.1, data_15_22149.2]

/-- Complete interval computation for depth 15, residue 22150. -/
theorem bounds_15_22150 : exactInterval 15 22150 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_22150 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 22150) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_22150 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_22150 : oddCount 22150 15 = 6 ∧ acceleratedOrbit 15 22150 = 493 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_22150 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 22150) = 3 ^ 6 * m + 493 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_22150.1, data_15_22150.2]

end Collatz.Research.PassageAtlas.Batch0676
