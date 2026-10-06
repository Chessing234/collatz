import Collatz.Research.DescentIntervals.Classifier

namespace Collatz.Research.PassageAtlas.Batch0890

open Collatz.Research.DescentIntervals

set_option maxRecDepth 20000
set_option maxHeartbeats 0

/-- Complete interval computation for depth 15, residue 29130. -/
theorem bounds_15_29130 : exactInterval 15 29130 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_29130 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 29130) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_29130 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_29130 : oddCount 29130 15 = 7 ∧ acceleratedOrbit 15 29130 = 1946 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_29130 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 29130) = 3 ^ 7 * m + 1946 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_29130.1, data_15_29130.2]

/-- Complete interval computation for depth 15, residue 29131. -/
theorem bounds_15_29131 : exactInterval 15 29131 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_29131 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 29131) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_29131 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_29131 : oddCount 29131 15 = 7 ∧ acceleratedOrbit 15 29131 = 1945 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_29131 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 29131) = 3 ^ 7 * m + 1945 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_29131.1, data_15_29131.2]

/-- Complete interval computation for depth 15, residue 29132. -/
theorem bounds_15_29132 : exactInterval 15 29132 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_29132 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 29132) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_29132 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_29132 : oddCount 29132 15 = 7 ∧ acceleratedOrbit 15 29132 = 1946 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_29132 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 29132) = 3 ^ 7 * m + 1946 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_29132.1, data_15_29132.2]

/-- Complete interval computation for depth 15, residue 29133. -/
theorem bounds_15_29133 : exactInterval 15 29133 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_29133 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 29133) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_29133 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_29133 : oddCount 29133 15 = 7 ∧ acceleratedOrbit 15 29133 = 1946 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_29133 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 29133) = 3 ^ 7 * m + 1946 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_29133.1, data_15_29133.2]

/-- Complete interval computation for depth 15, residue 29134. -/
theorem bounds_15_29134 : exactInterval 15 29134 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_29134 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 29134) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_29134 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_29134 : oddCount 29134 15 = 8 ∧ acceleratedOrbit 15 29134 = 5834 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_29134 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 29134) = 3 ^ 8 * m + 5834 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_29134.1, data_15_29134.2]

/-- Complete interval computation for depth 15, residue 29135. -/
theorem bounds_15_29135 : exactInterval 15 29135 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_29135 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 29135) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_29135 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_29135 : oddCount 29135 15 = 8 ∧ acceleratedOrbit 15 29135 = 5834 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_29135 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 29135) = 3 ^ 8 * m + 5834 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_29135.1, data_15_29135.2]

/-- Complete interval computation for depth 15, residue 29136. -/
theorem bounds_15_29136 : exactInterval 15 29136 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_29136 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 29136) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_29136 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_29136 : oddCount 29136 15 = 6 ∧ acceleratedOrbit 15 29136 = 650 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_29136 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 29136) = 3 ^ 6 * m + 650 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_29136.1, data_15_29136.2]

/-- Complete interval computation for depth 15, residue 29137. -/
theorem bounds_15_29137 : exactInterval 15 29137 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_29137 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 29137) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_29137 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_29137 : oddCount 29137 15 = 7 ∧ acceleratedOrbit 15 29137 = 1946 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_29137 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 29137) = 3 ^ 7 * m + 1946 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_29137.1, data_15_29137.2]

/-- Complete interval computation for depth 15, residue 29138. -/
theorem bounds_15_29138 : exactInterval 15 29138 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_29138 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 29138) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_29138 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_29138 : oddCount 29138 15 = 7 ∧ acceleratedOrbit 15 29138 = 1945 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_29138 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 29138) = 3 ^ 7 * m + 1945 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_29138.1, data_15_29138.2]

/-- Complete interval computation for depth 15, residue 29139. -/
theorem bounds_15_29139 : exactInterval 15 29139 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_29139 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 29139) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_29139 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_29139 : oddCount 29139 15 = 7 ∧ acceleratedOrbit 15 29139 = 1945 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_29139 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 29139) = 3 ^ 7 * m + 1945 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_29139.1, data_15_29139.2]

/-- Complete interval computation for depth 15, residue 29140. -/
theorem bounds_15_29140 : exactInterval 15 29140 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_29140 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 29140) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_29140 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_29140 : oddCount 29140 15 = 6 ∧ acceleratedOrbit 15 29140 = 650 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_29140 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 29140) = 3 ^ 6 * m + 650 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_29140.1, data_15_29140.2]

/-- Complete interval computation for depth 15, residue 29141. -/
theorem bounds_15_29141 : exactInterval 15 29141 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_29141 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 29141) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_29141 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_29141 : oddCount 29141 15 = 6 ∧ acceleratedOrbit 15 29141 = 650 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_29141 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 29141) = 3 ^ 6 * m + 650 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_29141.1, data_15_29141.2]

/-- Complete interval computation for depth 15, residue 29142. -/
theorem bounds_15_29142 : exactInterval 15 29142 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_29142 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 29142) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_29142 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_29142 : oddCount 29142 15 = 8 ∧ acceleratedOrbit 15 29142 = 5836 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_29142 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 29142) = 3 ^ 8 * m + 5836 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_29142.1, data_15_29142.2]

/-- Complete interval computation for depth 15, residue 29143. -/
theorem bounds_15_29143 : exactInterval 15 29143 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_29143 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 29143) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_29143 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_29143 : oddCount 29143 15 = 8 ∧ acceleratedOrbit 15 29143 = 5836 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_29143 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 29143) = 3 ^ 8 * m + 5836 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_29143.1, data_15_29143.2]

/-- Complete interval computation for depth 15, residue 29144. -/
theorem bounds_15_29144 : exactInterval 15 29144 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_29144 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 29144) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_29144 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_29144 : oddCount 29144 15 = 6 ∧ acceleratedOrbit 15 29144 = 649 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_29144 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 29144) = 3 ^ 6 * m + 649 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_29144.1, data_15_29144.2]

/-- Complete interval computation for depth 15, residue 29145. -/
theorem bounds_15_29145 : exactInterval 15 29145 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_29145 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 29145) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_29145 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_29145 : oddCount 29145 15 = 6 ∧ acceleratedOrbit 15 29145 = 649 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_29145 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 29145) = 3 ^ 6 * m + 649 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_29145.1, data_15_29145.2]

/-- Complete interval computation for depth 15, residue 29146. -/
theorem bounds_15_29146 : exactInterval 15 29146 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_29146 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 29146) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_29146 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_29146 : oddCount 29146 15 = 6 ∧ acceleratedOrbit 15 29146 = 649 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_29146 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 29146) = 3 ^ 6 * m + 649 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_29146.1, data_15_29146.2]

/-- Complete interval computation for depth 15, residue 29147. -/
theorem bounds_15_29147 : exactInterval 15 29147 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_29147 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 29147) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_29147 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_29147 : oddCount 29147 15 = 7 ∧ acceleratedOrbit 15 29147 = 1946 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_29147 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 29147) = 3 ^ 7 * m + 1946 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_29147.1, data_15_29147.2]

/-- Complete interval computation for depth 15, residue 29148. -/
theorem bounds_15_29148 : exactInterval 15 29148 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_29148 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 29148) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_29148 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_29148 : oddCount 29148 15 = 6 ∧ acceleratedOrbit 15 29148 = 649 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_29148 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 29148) = 3 ^ 6 * m + 649 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_29148.1, data_15_29148.2]

/-- Complete interval computation for depth 15, residue 29149. -/
theorem bounds_15_29149 : exactInterval 15 29149 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_29149 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 29149) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_29149 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_29149 : oddCount 29149 15 = 6 ∧ acceleratedOrbit 15 29149 = 649 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_29149 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 29149) = 3 ^ 6 * m + 649 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_29149.1, data_15_29149.2]

/-- Complete interval computation for depth 15, residue 29150. -/
theorem bounds_15_29150 : exactInterval 15 29150 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_29150 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 29150) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_29150 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_29150 : oddCount 29150 15 = 11 ∧ acceleratedOrbit 15 29150 = 157601 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_29150 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 29150) = 3 ^ 11 * m + 157601 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_29150.1, data_15_29150.2]

/-- Complete interval computation for depth 15, residue 29151. -/
theorem bounds_15_29151 : exactInterval 15 29151 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_29151 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 29151) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_29151 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_29151 : oddCount 29151 15 = 11 ∧ acceleratedOrbit 15 29151 = 157601 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_29151 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 29151) = 3 ^ 11 * m + 157601 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_29151.1, data_15_29151.2]

/-- Complete interval computation for depth 15, residue 29152. -/
theorem bounds_15_29152 : exactInterval 15 29152 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_29152 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 29152) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_29152 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_29152 : oddCount 29152 15 = 6 ∧ acceleratedOrbit 15 29152 = 650 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_29152 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 29152) = 3 ^ 6 * m + 650 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_29152.1, data_15_29152.2]

/-- Complete interval computation for depth 15, residue 29153. -/
theorem bounds_15_29153 : exactInterval 15 29153 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_29153 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 29153) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_29153 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_29153 : oddCount 29153 15 = 7 ∧ acceleratedOrbit 15 29153 = 1946 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_29153 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 29153) = 3 ^ 7 * m + 1946 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_29153.1, data_15_29153.2]

/-- Complete interval computation for depth 15, residue 29154. -/
theorem bounds_15_29154 : exactInterval 15 29154 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_29154 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 29154) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_29154 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_29154 : oddCount 29154 15 = 6 ∧ acceleratedOrbit 15 29154 = 650 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_29154 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 29154) = 3 ^ 6 * m + 650 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_29154.1, data_15_29154.2]

/-- Complete interval computation for depth 15, residue 29155. -/
theorem bounds_15_29155 : exactInterval 15 29155 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_29155 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 29155) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_29155 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_29155 : oddCount 29155 15 = 6 ∧ acceleratedOrbit 15 29155 = 650 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_29155 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 29155) = 3 ^ 6 * m + 650 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_29155.1, data_15_29155.2]

/-- Complete interval computation for depth 15, residue 29156. -/
theorem bounds_15_29156 : exactInterval 15 29156 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_29156 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 29156) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_29156 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_29156 : oddCount 29156 15 = 8 ∧ acceleratedOrbit 15 29156 = 5840 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_29156 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 29156) = 3 ^ 8 * m + 5840 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_29156.1, data_15_29156.2]

/-- Complete interval computation for depth 15, residue 29157. -/
theorem bounds_15_29157 : exactInterval 15 29157 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_29157 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 29157) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_29157 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_29157 : oddCount 29157 15 = 8 ∧ acceleratedOrbit 15 29157 = 5840 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_29157 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 29157) = 3 ^ 8 * m + 5840 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_29157.1, data_15_29157.2]

/-- Complete interval computation for depth 15, residue 29158. -/
theorem bounds_15_29158 : exactInterval 15 29158 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_29158 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 29158) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_29158 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_29158 : oddCount 29158 15 = 8 ∧ acceleratedOrbit 15 29158 = 5840 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_29158 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 29158) = 3 ^ 8 * m + 5840 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_29158.1, data_15_29158.2]

/-- Complete interval computation for depth 15, residue 29159. -/
theorem bounds_15_29159 : exactInterval 15 29159 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_29159 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 29159) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_29159 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_29159 : oddCount 29159 15 = 11 ∧ acceleratedOrbit 15 29159 = 157646 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_29159 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 29159) = 3 ^ 11 * m + 157646 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_29159.1, data_15_29159.2]

/-- Complete interval computation for depth 15, residue 29160. -/
theorem bounds_15_29160 : exactInterval 15 29160 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_29160 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 29160) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_29160 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_29160 : oddCount 29160 15 = 6 ∧ acceleratedOrbit 15 29160 = 650 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_29160 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 29160) = 3 ^ 6 * m + 650 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_29160.1, data_15_29160.2]

/-- Complete interval computation for depth 15, residue 29161. -/
theorem bounds_15_29161 : exactInterval 15 29161 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_29161 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 29161) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_29161 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_29161 : oddCount 29161 15 = 9 ∧ acceleratedOrbit 15 29161 = 17518 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_29161 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 29161) = 3 ^ 9 * m + 17518 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_29161.1, data_15_29161.2]

/-- Complete interval computation for depth 15, residue 29162. -/
theorem bounds_15_29162 : exactInterval 15 29162 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_29162 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 29162) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_29162 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_29162 : oddCount 29162 15 = 6 ∧ acceleratedOrbit 15 29162 = 650 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_29162 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 29162) = 3 ^ 6 * m + 650 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_29162.1, data_15_29162.2]

end Collatz.Research.PassageAtlas.Batch0890
