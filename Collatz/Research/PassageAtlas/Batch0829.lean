import Collatz.Research.DescentIntervals.Classifier

namespace Collatz.Research.PassageAtlas.Batch0829

open Collatz.Research.DescentIntervals

set_option maxRecDepth 20000
set_option maxHeartbeats 0

/-- Complete interval computation for depth 15, residue 27131. -/
theorem bounds_15_27131 : exactInterval 15 27131 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_27131 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 27131) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_27131 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_27131 : oddCount 27131 15 = 7 ∧ acceleratedOrbit 15 27131 = 1811 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_27131 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 27131) = 3 ^ 7 * m + 1811 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_27131.1, data_15_27131.2]

/-- Complete interval computation for depth 15, residue 27132. -/
theorem bounds_15_27132 : exactInterval 15 27132 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_27132 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 27132) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_27132 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_27132 : oddCount 27132 15 = 9 ∧ acceleratedOrbit 15 27132 = 16300 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_27132 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 27132) = 3 ^ 9 * m + 16300 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_27132.1, data_15_27132.2]

/-- Complete interval computation for depth 15, residue 27133. -/
theorem bounds_15_27133 : exactInterval 15 27133 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_27133 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 27133) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_27133 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_27133 : oddCount 27133 15 = 9 ∧ acceleratedOrbit 15 27133 = 16300 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_27133 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 27133) = 3 ^ 9 * m + 16300 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_27133.1, data_15_27133.2]

/-- Complete interval computation for depth 15, residue 27134. -/
theorem bounds_15_27134 : exactInterval 15 27134 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_27134 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 27134) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_27134 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_27134 : oddCount 27134 15 = 9 ∧ acceleratedOrbit 15 27134 = 16300 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_27134 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 27134) = 3 ^ 9 * m + 16300 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_27134.1, data_15_27134.2]

/-- Complete interval computation for depth 15, residue 27135. -/
theorem bounds_15_27135 : exactInterval 15 27135 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_27135 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 27135) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_27135 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_27135 : oddCount 27135 15 = 14 ∧ acceleratedOrbit 15 27135 = 3960899 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_27135 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 27135) = 3 ^ 14 * m + 3960899 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_27135.1, data_15_27135.2]

/-- Complete interval computation for depth 15, residue 27136. -/
theorem bounds_15_27136 : exactInterval 15 27136 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_27136 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 27136) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_27136 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_27136 : oddCount 27136 15 = 2 ∧ acceleratedOrbit 15 27136 = 8 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_27136 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 27136) = 3 ^ 2 * m + 8 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_27136.1, data_15_27136.2]

/-- Complete interval computation for depth 15, residue 27137. -/
theorem bounds_15_27137 : exactInterval 15 27137 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_27137 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 27137) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_27137 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_27137 : oddCount 27137 15 = 8 ∧ acceleratedOrbit 15 27137 = 5435 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_27137 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 27137) = 3 ^ 8 * m + 5435 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_27137.1, data_15_27137.2]

/-- Complete interval computation for depth 15, residue 27138. -/
theorem bounds_15_27138 : exactInterval 15 27138 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_27138 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 27138) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_27138 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_27138 : oddCount 27138 15 = 6 ∧ acceleratedOrbit 15 27138 = 604 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_27138 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 27138) = 3 ^ 6 * m + 604 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_27138.1, data_15_27138.2]

/-- Complete interval computation for depth 15, residue 27139. -/
theorem bounds_15_27139 : exactInterval 15 27139 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_27139 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 27139) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_27139 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_27139 : oddCount 27139 15 = 6 ∧ acceleratedOrbit 15 27139 = 604 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_27139 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 27139) = 3 ^ 6 * m + 604 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_27139.1, data_15_27139.2]

/-- Complete interval computation for depth 15, residue 27140. -/
theorem bounds_15_27140 : exactInterval 15 27140 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_27140 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 27140) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_27140 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_27140 : oddCount 27140 15 = 8 ∧ acceleratedOrbit 15 27140 = 5437 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_27140 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 27140) = 3 ^ 8 * m + 5437 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_27140.1, data_15_27140.2]

/-- Complete interval computation for depth 15, residue 27141. -/
theorem bounds_15_27141 : exactInterval 15 27141 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_27141 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 27141) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_27141 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_27141 : oddCount 27141 15 = 8 ∧ acceleratedOrbit 15 27141 = 5437 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_27141 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 27141) = 3 ^ 8 * m + 5437 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_27141.1, data_15_27141.2]

/-- Complete interval computation for depth 15, residue 27142. -/
theorem bounds_15_27142 : exactInterval 15 27142 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_27142 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 27142) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_27142 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_27142 : oddCount 27142 15 = 8 ∧ acceleratedOrbit 15 27142 = 5437 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_27142 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 27142) = 3 ^ 8 * m + 5437 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_27142.1, data_15_27142.2]

/-- Complete interval computation for depth 15, residue 27143. -/
theorem bounds_15_27143 : exactInterval 15 27143 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_27143 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 27143) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_27143 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_27143 : oddCount 27143 15 = 9 ∧ acceleratedOrbit 15 27143 = 16307 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_27143 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 27143) = 3 ^ 9 * m + 16307 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_27143.1, data_15_27143.2]

/-- Complete interval computation for depth 15, residue 27144. -/
theorem bounds_15_27144 : exactInterval 15 27144 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_27144 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 27144) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_27144 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_27144 : oddCount 27144 15 = 5 ∧ acceleratedOrbit 15 27144 = 202 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_27144 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 27144) = 3 ^ 5 * m + 202 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_27144.1, data_15_27144.2]

/-- Complete interval computation for depth 15, residue 27145. -/
theorem bounds_15_27145 : exactInterval 15 27145 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_27145 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 27145) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_27145 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_27145 : oddCount 27145 15 = 6 ∧ acceleratedOrbit 15 27145 = 604 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_27145 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 27145) = 3 ^ 6 * m + 604 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_27145.1, data_15_27145.2]

/-- Complete interval computation for depth 15, residue 27146. -/
theorem bounds_15_27146 : exactInterval 15 27146 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_27146 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 27146) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_27146 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_27146 : oddCount 27146 15 = 5 ∧ acceleratedOrbit 15 27146 = 202 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_27146 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 27146) = 3 ^ 5 * m + 202 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_27146.1, data_15_27146.2]

/-- Complete interval computation for depth 15, residue 27147. -/
theorem bounds_15_27147 : exactInterval 15 27147 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_27147 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 27147) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_27147 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_27147 : oddCount 27147 15 = 8 ∧ acceleratedOrbit 15 27147 = 5437 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_27147 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 27147) = 3 ^ 8 * m + 5437 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_27147.1, data_15_27147.2]

/-- Complete interval computation for depth 15, residue 27148. -/
theorem bounds_15_27148 : exactInterval 15 27148 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_27148 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 27148) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_27148 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_27148 : oddCount 27148 15 = 5 ∧ acceleratedOrbit 15 27148 = 202 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_27148 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 27148) = 3 ^ 5 * m + 202 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_27148.1, data_15_27148.2]

/-- Complete interval computation for depth 15, residue 27149. -/
theorem bounds_15_27149 : exactInterval 15 27149 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_27149 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 27149) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_27149 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_27149 : oddCount 27149 15 = 5 ∧ acceleratedOrbit 15 27149 = 202 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_27149 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 27149) = 3 ^ 5 * m + 202 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_27149.1, data_15_27149.2]

/-- Complete interval computation for depth 15, residue 27150. -/
theorem bounds_15_27150 : exactInterval 15 27150 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_27150 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 27150) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_27150 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_27150 : oddCount 27150 15 = 8 ∧ acceleratedOrbit 15 27150 = 5437 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_27150 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 27150) = 3 ^ 8 * m + 5437 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_27150.1, data_15_27150.2]

/-- Complete interval computation for depth 15, residue 27151. -/
theorem bounds_15_27151 : exactInterval 15 27151 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_27151 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 27151) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_27151 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_27151 : oddCount 27151 15 = 8 ∧ acceleratedOrbit 15 27151 = 5437 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_27151 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 27151) = 3 ^ 8 * m + 5437 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_27151.1, data_15_27151.2]

/-- Complete interval computation for depth 15, residue 27152. -/
theorem bounds_15_27152 : exactInterval 15 27152 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_27152 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 27152) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_27152 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_27152 : oddCount 27152 15 = 6 ∧ acceleratedOrbit 15 27152 = 605 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_27152 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 27152) = 3 ^ 6 * m + 605 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_27152.1, data_15_27152.2]

/-- Complete interval computation for depth 15, residue 27153. -/
theorem bounds_15_27153 : exactInterval 15 27153 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_27153 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 27153) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_27153 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_27153 : oddCount 27153 15 = 5 ∧ acceleratedOrbit 15 27153 = 202 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_27153 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 27153) = 3 ^ 5 * m + 202 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_27153.1, data_15_27153.2]

/-- Complete interval computation for depth 15, residue 27154. -/
theorem bounds_15_27154 : exactInterval 15 27154 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_27154 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 27154) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_27154 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_27154 : oddCount 27154 15 = 8 ∧ acceleratedOrbit 15 27154 = 5438 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_27154 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 27154) = 3 ^ 8 * m + 5438 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_27154.1, data_15_27154.2]

/-- Complete interval computation for depth 15, residue 27155. -/
theorem bounds_15_27155 : exactInterval 15 27155 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_27155 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 27155) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_27155 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_27155 : oddCount 27155 15 = 8 ∧ acceleratedOrbit 15 27155 = 5438 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_27155 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 27155) = 3 ^ 8 * m + 5438 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_27155.1, data_15_27155.2]

/-- Complete interval computation for depth 15, residue 27156. -/
theorem bounds_15_27156 : exactInterval 15 27156 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_27156 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 27156) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_27156 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_27156 : oddCount 27156 15 = 6 ∧ acceleratedOrbit 15 27156 = 605 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_27156 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 27156) = 3 ^ 6 * m + 605 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_27156.1, data_15_27156.2]

/-- Complete interval computation for depth 15, residue 27157. -/
theorem bounds_15_27157 : exactInterval 15 27157 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_27157 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 27157) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_27157 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_27157 : oddCount 27157 15 = 6 ∧ acceleratedOrbit 15 27157 = 605 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_27157 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 27157) = 3 ^ 6 * m + 605 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_27157.1, data_15_27157.2]

/-- Complete interval computation for depth 15, residue 27158. -/
theorem bounds_15_27158 : exactInterval 15 27158 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_27158 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 27158) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_27158 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_27158 : oddCount 27158 15 = 8 ∧ acceleratedOrbit 15 27158 = 5440 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_27158 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 27158) = 3 ^ 8 * m + 5440 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_27158.1, data_15_27158.2]

/-- Complete interval computation for depth 15, residue 27159. -/
theorem bounds_15_27159 : exactInterval 15 27159 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_27159 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 27159) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_27159 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_27159 : oddCount 27159 15 = 8 ∧ acceleratedOrbit 15 27159 = 5440 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_27159 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 27159) = 3 ^ 8 * m + 5440 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_27159.1, data_15_27159.2]

/-- Complete interval computation for depth 15, residue 27160. -/
theorem bounds_15_27160 : exactInterval 15 27160 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_27160 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 27160) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_27160 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_27160 : oddCount 27160 15 = 6 ∧ acceleratedOrbit 15 27160 = 605 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_27160 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 27160) = 3 ^ 6 * m + 605 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_27160.1, data_15_27160.2]

/-- Complete interval computation for depth 15, residue 27161. -/
theorem bounds_15_27161 : exactInterval 15 27161 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_27161 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 27161) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_27161 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_27161 : oddCount 27161 15 = 8 ∧ acceleratedOrbit 15 27161 = 5440 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_27161 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 27161) = 3 ^ 8 * m + 5440 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_27161.1, data_15_27161.2]

/-- Complete interval computation for depth 15, residue 27162. -/
theorem bounds_15_27162 : exactInterval 15 27162 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_27162 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 27162) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_27162 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_27162 : oddCount 27162 15 = 6 ∧ acceleratedOrbit 15 27162 = 605 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_27162 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 27162) = 3 ^ 6 * m + 605 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_27162.1, data_15_27162.2]

/-- Complete interval computation for depth 15, residue 27163. -/
theorem bounds_15_27163 : exactInterval 15 27163 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_27163 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 27163) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_27163 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_27163 : oddCount 27163 15 = 7 ∧ acceleratedOrbit 15 27163 = 1813 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_27163 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 27163) = 3 ^ 7 * m + 1813 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_27163.1, data_15_27163.2]

end Collatz.Research.PassageAtlas.Batch0829
