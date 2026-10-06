import Collatz.Research.DescentIntervals.Classifier

namespace Collatz.Research.PassageAtlas.Batch0554

open Collatz.Research.DescentIntervals

set_option maxRecDepth 20000
set_option maxHeartbeats 0

/-- Complete interval computation for depth 15, residue 18120. -/
theorem bounds_15_18120 : exactInterval 15 18120 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_18120 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 18120) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_18120 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_18120 : oddCount 18120 15 = 7 ∧ acceleratedOrbit 15 18120 = 1214 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_18120 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 18120) = 3 ^ 7 * m + 1214 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_18120.1, data_15_18120.2]

/-- Complete interval computation for depth 15, residue 18121. -/
theorem bounds_15_18121 : exactInterval 15 18121 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_18121 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 18121) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_18121 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_18121 : oddCount 18121 15 = 7 ∧ acceleratedOrbit 15 18121 = 1210 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_18121 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 18121) = 3 ^ 7 * m + 1210 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_18121.1, data_15_18121.2]

/-- Complete interval computation for depth 15, residue 18122. -/
theorem bounds_15_18122 : exactInterval 15 18122 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_18122 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 18122) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_18122 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_18122 : oddCount 18122 15 = 7 ∧ acceleratedOrbit 15 18122 = 1214 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_18122 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 18122) = 3 ^ 7 * m + 1214 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_18122.1, data_15_18122.2]

/-- Complete interval computation for depth 15, residue 18123. -/
theorem bounds_15_18123 : exactInterval 15 18123 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_18123 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 18123) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_18123 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_18123 : oddCount 18123 15 = 10 ∧ acceleratedOrbit 15 18123 = 32669 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_18123 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 18123) = 3 ^ 10 * m + 32669 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_18123.1, data_15_18123.2]

/-- Complete interval computation for depth 15, residue 18124. -/
theorem bounds_15_18124 : exactInterval 15 18124 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_18124 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 18124) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_18124 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_18124 : oddCount 18124 15 = 7 ∧ acceleratedOrbit 15 18124 = 1214 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_18124 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 18124) = 3 ^ 7 * m + 1214 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_18124.1, data_15_18124.2]

/-- Complete interval computation for depth 15, residue 18125. -/
theorem bounds_15_18125 : exactInterval 15 18125 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_18125 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 18125) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_18125 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_18125 : oddCount 18125 15 = 7 ∧ acceleratedOrbit 15 18125 = 1214 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_18125 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 18125) = 3 ^ 7 * m + 1214 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_18125.1, data_15_18125.2]

/-- Complete interval computation for depth 15, residue 18126. -/
theorem bounds_15_18126 : exactInterval 15 18126 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_18126 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 18126) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_18126 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_18126 : oddCount 18126 15 = 11 ∧ acceleratedOrbit 15 18126 = 98005 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_18126 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 18126) = 3 ^ 11 * m + 98005 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_18126.1, data_15_18126.2]

/-- Complete interval computation for depth 15, residue 18127. -/
theorem bounds_15_18127 : exactInterval 15 18127 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_18127 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 18127) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_18127 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_18127 : oddCount 18127 15 = 11 ∧ acceleratedOrbit 15 18127 = 98005 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_18127 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 18127) = 3 ^ 11 * m + 98005 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_18127.1, data_15_18127.2]

/-- Complete interval computation for depth 15, residue 18128. -/
theorem bounds_15_18128 : exactInterval 15 18128 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_18128 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 18128) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_18128 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_18128 : oddCount 18128 15 = 8 ∧ acceleratedOrbit 15 18128 = 3644 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_18128 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 18128) = 3 ^ 8 * m + 3644 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_18128.1, data_15_18128.2]

/-- Complete interval computation for depth 15, residue 18129. -/
theorem bounds_15_18129 : exactInterval 15 18129 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_18129 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 18129) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_18129 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_18129 : oddCount 18129 15 = 9 ∧ acceleratedOrbit 15 18129 = 10894 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_18129 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 18129) = 3 ^ 9 * m + 10894 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_18129.1, data_15_18129.2]

/-- Complete interval computation for depth 15, residue 18130. -/
theorem bounds_15_18130 : exactInterval 15 18130 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_18130 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 18130) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_18130 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_18130 : oddCount 18130 15 = 9 ∧ acceleratedOrbit 15 18130 = 10894 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_18130 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 18130) = 3 ^ 9 * m + 10894 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_18130.1, data_15_18130.2]

/-- Complete interval computation for depth 15, residue 18131. -/
theorem bounds_15_18131 : exactInterval 15 18131 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_18131 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 18131) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_18131 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_18131 : oddCount 18131 15 = 9 ∧ acceleratedOrbit 15 18131 = 10894 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_18131 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 18131) = 3 ^ 9 * m + 10894 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_18131.1, data_15_18131.2]

/-- Complete interval computation for depth 15, residue 18132. -/
theorem bounds_15_18132 : exactInterval 15 18132 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_18132 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 18132) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_18132 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_18132 : oddCount 18132 15 = 8 ∧ acceleratedOrbit 15 18132 = 3644 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_18132 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 18132) = 3 ^ 8 * m + 3644 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_18132.1, data_15_18132.2]

/-- Complete interval computation for depth 15, residue 18133. -/
theorem bounds_15_18133 : exactInterval 15 18133 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_18133 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 18133) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_18133 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_18133 : oddCount 18133 15 = 8 ∧ acceleratedOrbit 15 18133 = 3644 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_18133 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 18133) = 3 ^ 8 * m + 3644 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_18133.1, data_15_18133.2]

/-- Complete interval computation for depth 15, residue 18134. -/
theorem bounds_15_18134 : exactInterval 15 18134 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_18134 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 18134) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_18134 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_18134 : oddCount 18134 15 = 6 ∧ acceleratedOrbit 15 18134 = 404 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_18134 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 18134) = 3 ^ 6 * m + 404 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_18134.1, data_15_18134.2]

/-- Complete interval computation for depth 15, residue 18135. -/
theorem bounds_15_18135 : exactInterval 15 18135 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_18135 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 18135) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_18135 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_18135 : oddCount 18135 15 = 6 ∧ acceleratedOrbit 15 18135 = 404 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_18135 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 18135) = 3 ^ 6 * m + 404 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_18135.1, data_15_18135.2]

/-- Complete interval computation for depth 15, residue 18136. -/
theorem bounds_15_18136 : exactInterval 15 18136 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_18136 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 18136) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_18136 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_18136 : oddCount 18136 15 = 8 ∧ acceleratedOrbit 15 18136 = 3635 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_18136 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 18136) = 3 ^ 8 * m + 3635 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_18136.1, data_15_18136.2]

/-- Complete interval computation for depth 15, residue 18137. -/
theorem bounds_15_18137 : exactInterval 15 18137 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_18137 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 18137) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_18137 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_18137 : oddCount 18137 15 = 8 ∧ acceleratedOrbit 15 18137 = 3635 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_18137 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 18137) = 3 ^ 8 * m + 3635 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_18137.1, data_15_18137.2]

/-- Complete interval computation for depth 15, residue 18138. -/
theorem bounds_15_18138 : exactInterval 15 18138 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_18138 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 18138) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_18138 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_18138 : oddCount 18138 15 = 8 ∧ acceleratedOrbit 15 18138 = 3635 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_18138 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 18138) = 3 ^ 8 * m + 3635 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_18138.1, data_15_18138.2]

/-- Complete interval computation for depth 15, residue 18139. -/
theorem bounds_15_18139 : exactInterval 15 18139 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_18139 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 18139) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_18139 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_18139 : oddCount 18139 15 = 9 ∧ acceleratedOrbit 15 18139 = 10898 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_18139 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 18139) = 3 ^ 9 * m + 10898 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_18139.1, data_15_18139.2]

/-- Complete interval computation for depth 15, residue 18140. -/
theorem bounds_15_18140 : exactInterval 15 18140 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_18140 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 18140) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_18140 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_18140 : oddCount 18140 15 = 8 ∧ acceleratedOrbit 15 18140 = 3635 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_18140 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 18140) = 3 ^ 8 * m + 3635 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_18140.1, data_15_18140.2]

/-- Complete interval computation for depth 15, residue 18141. -/
theorem bounds_15_18141 : exactInterval 15 18141 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_18141 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 18141) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_18141 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_18141 : oddCount 18141 15 = 8 ∧ acceleratedOrbit 15 18141 = 3635 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_18141 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 18141) = 3 ^ 8 * m + 3635 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_18141.1, data_15_18141.2]

/-- Complete interval computation for depth 15, residue 18142. -/
theorem bounds_15_18142 : exactInterval 15 18142 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_18142 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 18142) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_18142 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_18142 : oddCount 18142 15 = 7 ∧ acceleratedOrbit 15 18142 = 1211 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_18142 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 18142) = 3 ^ 7 * m + 1211 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_18142.1, data_15_18142.2]

/-- Complete interval computation for depth 15, residue 18143. -/
theorem bounds_15_18143 : exactInterval 15 18143 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_18143 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 18143) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_18143 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_18143 : oddCount 18143 15 = 7 ∧ acceleratedOrbit 15 18143 = 1211 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_18143 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 18143) = 3 ^ 7 * m + 1211 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_18143.1, data_15_18143.2]

/-- Complete interval computation for depth 15, residue 18144. -/
theorem bounds_15_18144 : exactInterval 15 18144 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_18144 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 18144) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_18144 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_18144 : oddCount 18144 15 = 8 ∧ acceleratedOrbit 15 18144 = 3644 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_18144 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 18144) = 3 ^ 8 * m + 3644 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_18144.1, data_15_18144.2]

/-- Complete interval computation for depth 15, residue 18145. -/
theorem bounds_15_18145 : exactInterval 15 18145 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_18145 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 18145) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_18145 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_18145 : oddCount 18145 15 = 9 ∧ acceleratedOrbit 15 18145 = 10901 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_18145 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 18145) = 3 ^ 9 * m + 10901 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_18145.1, data_15_18145.2]

/-- Complete interval computation for depth 15, residue 18146. -/
theorem bounds_15_18146 : exactInterval 15 18146 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_18146 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 18146) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_18146 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_18146 : oddCount 18146 15 = 8 ∧ acceleratedOrbit 15 18146 = 3644 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_18146 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 18146) = 3 ^ 8 * m + 3644 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_18146.1, data_15_18146.2]

/-- Complete interval computation for depth 15, residue 18147. -/
theorem bounds_15_18147 : exactInterval 15 18147 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_18147 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 18147) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_18147 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_18147 : oddCount 18147 15 = 8 ∧ acceleratedOrbit 15 18147 = 3644 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_18147 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 18147) = 3 ^ 8 * m + 3644 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_18147.1, data_15_18147.2]

/-- Complete interval computation for depth 15, residue 18148. -/
theorem bounds_15_18148 : exactInterval 15 18148 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_18148 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 18148) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_18148 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_18148 : oddCount 18148 15 = 7 ∧ acceleratedOrbit 15 18148 = 1214 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_18148 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 18148) = 3 ^ 7 * m + 1214 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_18148.1, data_15_18148.2]

/-- Complete interval computation for depth 15, residue 18149. -/
theorem bounds_15_18149 : exactInterval 15 18149 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_18149 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 18149) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_18149 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_18149 : oddCount 18149 15 = 7 ∧ acceleratedOrbit 15 18149 = 1214 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_18149 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 18149) = 3 ^ 7 * m + 1214 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_18149.1, data_15_18149.2]

/-- Complete interval computation for depth 15, residue 18150. -/
theorem bounds_15_18150 : exactInterval 15 18150 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_18150 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 18150) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_18150 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_18150 : oddCount 18150 15 = 7 ∧ acceleratedOrbit 15 18150 = 1214 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_18150 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 18150) = 3 ^ 7 * m + 1214 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_18150.1, data_15_18150.2]

/-- Complete interval computation for depth 15, residue 18151. -/
theorem bounds_15_18151 : exactInterval 15 18151 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_18151 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 18151) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_18151 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_18151 : oddCount 18151 15 = 11 ∧ acceleratedOrbit 15 18151 = 98135 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_18151 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 18151) = 3 ^ 11 * m + 98135 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_18151.1, data_15_18151.2]

/-- Complete interval computation for depth 15, residue 18152. -/
theorem bounds_15_18152 : exactInterval 15 18152 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_18152 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 18152) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_18152 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_18152 : oddCount 18152 15 = 8 ∧ acceleratedOrbit 15 18152 = 3644 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_18152 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 18152) = 3 ^ 8 * m + 3644 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_18152.1, data_15_18152.2]

end Collatz.Research.PassageAtlas.Batch0554
