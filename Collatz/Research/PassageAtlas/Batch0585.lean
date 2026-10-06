import Collatz.Research.DescentIntervals.Classifier

namespace Collatz.Research.PassageAtlas.Batch0585

open Collatz.Research.DescentIntervals

set_option maxRecDepth 20000
set_option maxHeartbeats 0

/-- Complete interval computation for depth 15, residue 19136. -/
theorem bounds_15_19136 : exactInterval 15 19136 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_19136 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 19136) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_19136 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_19136 : oddCount 19136 15 = 5 ∧ acceleratedOrbit 15 19136 = 143 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_19136 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 19136) = 3 ^ 5 * m + 143 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_19136.1, data_15_19136.2]

/-- Complete interval computation for depth 15, residue 19137. -/
theorem bounds_15_19137 : exactInterval 15 19137 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_19137 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 19137) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_19137 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_19137 : oddCount 19137 15 = 5 ∧ acceleratedOrbit 15 19137 = 142 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_19137 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 19137) = 3 ^ 5 * m + 142 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_19137.1, data_15_19137.2]

/-- Complete interval computation for depth 15, residue 19138. -/
theorem bounds_15_19138 : exactInterval 15 19138 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_19138 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 19138) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_19138 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_19138 : oddCount 19138 15 = 9 ∧ acceleratedOrbit 15 19138 = 11501 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_19138 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 19138) = 3 ^ 9 * m + 11501 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_19138.1, data_15_19138.2]

/-- Complete interval computation for depth 15, residue 19139. -/
theorem bounds_15_19139 : exactInterval 15 19139 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_19139 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 19139) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_19139 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_19139 : oddCount 19139 15 = 9 ∧ acceleratedOrbit 15 19139 = 11501 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_19139 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 19139) = 3 ^ 9 * m + 11501 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_19139.1, data_15_19139.2]

/-- Complete interval computation for depth 15, residue 19140. -/
theorem bounds_15_19140 : exactInterval 15 19140 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_19140 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 19140) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_19140 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_19140 : oddCount 19140 15 = 6 ∧ acceleratedOrbit 15 19140 = 427 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_19140 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 19140) = 3 ^ 6 * m + 427 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_19140.1, data_15_19140.2]

/-- Complete interval computation for depth 15, residue 19141. -/
theorem bounds_15_19141 : exactInterval 15 19141 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_19141 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 19141) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_19141 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_19141 : oddCount 19141 15 = 6 ∧ acceleratedOrbit 15 19141 = 427 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_19141 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 19141) = 3 ^ 6 * m + 427 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_19141.1, data_15_19141.2]

/-- Complete interval computation for depth 15, residue 19142. -/
theorem bounds_15_19142 : exactInterval 15 19142 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_19142 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 19142) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_19142 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_19142 : oddCount 19142 15 = 6 ∧ acceleratedOrbit 15 19142 = 427 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_19142 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 19142) = 3 ^ 6 * m + 427 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_19142.1, data_15_19142.2]

/-- Complete interval computation for depth 15, residue 19143. -/
theorem bounds_15_19143 : exactInterval 15 19143 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_19143 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 19143) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_19143 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_19143 : oddCount 19143 15 = 10 ∧ acceleratedOrbit 15 19143 = 34505 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_19143 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 19143) = 3 ^ 10 * m + 34505 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_19143.1, data_15_19143.2]

/-- Complete interval computation for depth 15, residue 19144. -/
theorem bounds_15_19144 : exactInterval 15 19144 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_19144 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 19144) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_19144 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_19144 : oddCount 19144 15 = 6 ∧ acceleratedOrbit 15 19144 = 427 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_19144 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 19144) = 3 ^ 6 * m + 427 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_19144.1, data_15_19144.2]

/-- Complete interval computation for depth 15, residue 19145. -/
theorem bounds_15_19145 : exactInterval 15 19145 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_19145 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 19145) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_19145 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_19145 : oddCount 19145 15 = 5 ∧ acceleratedOrbit 15 19145 = 142 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_19145 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 19145) = 3 ^ 5 * m + 142 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_19145.1, data_15_19145.2]

/-- Complete interval computation for depth 15, residue 19146. -/
theorem bounds_15_19146 : exactInterval 15 19146 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_19146 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 19146) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_19146 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_19146 : oddCount 19146 15 = 6 ∧ acceleratedOrbit 15 19146 = 427 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_19146 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 19146) = 3 ^ 6 * m + 427 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_19146.1, data_15_19146.2]

/-- Complete interval computation for depth 15, residue 19147. -/
theorem bounds_15_19147 : exactInterval 15 19147 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_19147 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 19147) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_19147 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_19147 : oddCount 19147 15 = 8 ∧ acceleratedOrbit 15 19147 = 3835 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_19147 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 19147) = 3 ^ 8 * m + 3835 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_19147.1, data_15_19147.2]

/-- Complete interval computation for depth 15, residue 19148. -/
theorem bounds_15_19148 : exactInterval 15 19148 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_19148 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 19148) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_19148 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_19148 : oddCount 19148 15 = 6 ∧ acceleratedOrbit 15 19148 = 427 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_19148 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 19148) = 3 ^ 6 * m + 427 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_19148.1, data_15_19148.2]

/-- Complete interval computation for depth 15, residue 19149. -/
theorem bounds_15_19149 : exactInterval 15 19149 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_19149 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 19149) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_19149 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_19149 : oddCount 19149 15 = 6 ∧ acceleratedOrbit 15 19149 = 427 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_19149 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 19149) = 3 ^ 6 * m + 427 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_19149.1, data_15_19149.2]

/-- Complete interval computation for depth 15, residue 19150. -/
theorem bounds_15_19150 : exactInterval 15 19150 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_19150 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 19150) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_19150 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_19150 : oddCount 19150 15 = 10 ∧ acceleratedOrbit 15 19150 = 34514 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_19150 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 19150) = 3 ^ 10 * m + 34514 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_19150.1, data_15_19150.2]

/-- Complete interval computation for depth 15, residue 19151. -/
theorem bounds_15_19151 : exactInterval 15 19151 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_19151 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 19151) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_19151 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_19151 : oddCount 19151 15 = 10 ∧ acceleratedOrbit 15 19151 = 34514 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_19151 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 19151) = 3 ^ 10 * m + 34514 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_19151.1, data_15_19151.2]

/-- Complete interval computation for depth 15, residue 19152. -/
theorem bounds_15_19152 : exactInterval 15 19152 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_19152 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 19152) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_19152 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_19152 : oddCount 19152 15 = 5 ∧ acceleratedOrbit 15 19152 = 143 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_19152 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 19152) = 3 ^ 5 * m + 143 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_19152.1, data_15_19152.2]

/-- Complete interval computation for depth 15, residue 19153. -/
theorem bounds_15_19153 : exactInterval 15 19153 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_19153 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 19153) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_19153 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_19153 : oddCount 19153 15 = 7 ∧ acceleratedOrbit 15 19153 = 1279 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_19153 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 19153) = 3 ^ 7 * m + 1279 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_19153.1, data_15_19153.2]

/-- Complete interval computation for depth 15, residue 19154. -/
theorem bounds_15_19154 : exactInterval 15 19154 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_19154 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 19154) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_19154 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_19154 : oddCount 19154 15 = 7 ∧ acceleratedOrbit 15 19154 = 1279 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_19154 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 19154) = 3 ^ 7 * m + 1279 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_19154.1, data_15_19154.2]

/-- Complete interval computation for depth 15, residue 19155. -/
theorem bounds_15_19155 : exactInterval 15 19155 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_19155 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 19155) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_19155 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_19155 : oddCount 19155 15 = 7 ∧ acceleratedOrbit 15 19155 = 1279 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_19155 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 19155) = 3 ^ 7 * m + 1279 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_19155.1, data_15_19155.2]

/-- Complete interval computation for depth 15, residue 19156. -/
theorem bounds_15_19156 : exactInterval 15 19156 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_19156 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 19156) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_19156 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_19156 : oddCount 19156 15 = 5 ∧ acceleratedOrbit 15 19156 = 143 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_19156 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 19156) = 3 ^ 5 * m + 143 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_19156.1, data_15_19156.2]

/-- Complete interval computation for depth 15, residue 19157. -/
theorem bounds_15_19157 : exactInterval 15 19157 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_19157 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 19157) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_19157 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_19157 : oddCount 19157 15 = 5 ∧ acceleratedOrbit 15 19157 = 143 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_19157 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 19157) = 3 ^ 5 * m + 143 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_19157.1, data_15_19157.2]

/-- Complete interval computation for depth 15, residue 19158. -/
theorem bounds_15_19158 : exactInterval 15 19158 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_19158 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 19158) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_19158 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_19158 : oddCount 19158 15 = 7 ∧ acceleratedOrbit 15 19158 = 1279 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_19158 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 19158) = 3 ^ 7 * m + 1279 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_19158.1, data_15_19158.2]

/-- Complete interval computation for depth 15, residue 19159. -/
theorem bounds_15_19159 : exactInterval 15 19159 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_19159 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 19159) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_19159 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_19159 : oddCount 19159 15 = 7 ∧ acceleratedOrbit 15 19159 = 1279 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_19159 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 19159) = 3 ^ 7 * m + 1279 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_19159.1, data_15_19159.2]

/-- Complete interval computation for depth 15, residue 19160. -/
theorem bounds_15_19160 : exactInterval 15 19160 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_19160 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 19160) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_19160 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_19160 : oddCount 19160 15 = 7 ∧ acceleratedOrbit 15 19160 = 1280 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_19160 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 19160) = 3 ^ 7 * m + 1280 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_19160.1, data_15_19160.2]

/-- Complete interval computation for depth 15, residue 19161. -/
theorem bounds_15_19161 : exactInterval 15 19161 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_19161 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 19161) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_19161 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_19161 : oddCount 19161 15 = 6 ∧ acceleratedOrbit 15 19161 = 427 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_19161 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 19161) = 3 ^ 6 * m + 427 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_19161.1, data_15_19161.2]

/-- Complete interval computation for depth 15, residue 19162. -/
theorem bounds_15_19162 : exactInterval 15 19162 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_19162 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 19162) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_19162 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_19162 : oddCount 19162 15 = 7 ∧ acceleratedOrbit 15 19162 = 1280 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_19162 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 19162) = 3 ^ 7 * m + 1280 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_19162.1, data_15_19162.2]

/-- Complete interval computation for depth 15, residue 19163. -/
theorem bounds_15_19163 : exactInterval 15 19163 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_19163 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 19163) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_19163 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_19163 : oddCount 19163 15 = 9 ∧ acceleratedOrbit 15 19163 = 11512 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_19163 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 19163) = 3 ^ 9 * m + 11512 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_19163.1, data_15_19163.2]

/-- Complete interval computation for depth 15, residue 19164. -/
theorem bounds_15_19164 : exactInterval 15 19164 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_19164 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 19164) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_19164 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_19164 : oddCount 19164 15 = 7 ∧ acceleratedOrbit 15 19164 = 1280 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_19164 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 19164) = 3 ^ 7 * m + 1280 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_19164.1, data_15_19164.2]

/-- Complete interval computation for depth 15, residue 19165. -/
theorem bounds_15_19165 : exactInterval 15 19165 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_19165 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 19165) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_19165 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_19165 : oddCount 19165 15 = 7 ∧ acceleratedOrbit 15 19165 = 1280 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_19165 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 19165) = 3 ^ 7 * m + 1280 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_19165.1, data_15_19165.2]

/-- Complete interval computation for depth 15, residue 19166. -/
theorem bounds_15_19166 : exactInterval 15 19166 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_19166 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 19166) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_19166 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_19166 : oddCount 19166 15 = 9 ∧ acceleratedOrbit 15 19166 = 11515 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_19166 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 19166) = 3 ^ 9 * m + 11515 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_19166.1, data_15_19166.2]

/-- Complete interval computation for depth 15, residue 19167. -/
theorem bounds_15_19167 : exactInterval 15 19167 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_19167 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 19167) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_19167 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_19167 : oddCount 19167 15 = 9 ∧ acceleratedOrbit 15 19167 = 11515 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_19167 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 19167) = 3 ^ 9 * m + 11515 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_19167.1, data_15_19167.2]

/-- Complete interval computation for depth 15, residue 19168. -/
theorem bounds_15_19168 : exactInterval 15 19168 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_19168 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 19168) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_19168 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_19168 : oddCount 19168 15 = 5 ∧ acceleratedOrbit 15 19168 = 143 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_19168 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 19168) = 3 ^ 5 * m + 143 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_19168.1, data_15_19168.2]

end Collatz.Research.PassageAtlas.Batch0585
