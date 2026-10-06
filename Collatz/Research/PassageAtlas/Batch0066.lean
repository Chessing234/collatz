import Collatz.Research.DescentIntervals.Classifier

namespace Collatz.Research.PassageAtlas.Batch0066

open Collatz.Research.DescentIntervals

set_option maxRecDepth 20000
set_option maxHeartbeats 0

/-- Complete interval computation for depth 15, residue 2129. -/
theorem bounds_15_2129 : exactInterval 15 2129 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_2129 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 2129) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_2129 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_2129 : oddCount 2129 15 = 7 ∧ acceleratedOrbit 15 2129 = 143 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_2129 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 2129) = 3 ^ 7 * m + 143 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_2129.1, data_15_2129.2]

/-- Complete interval computation for depth 15, residue 2130. -/
theorem bounds_15_2130 : exactInterval 15 2130 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_2130 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 2130) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_2130 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_2130 : oddCount 2130 15 = 9 ∧ acceleratedOrbit 15 2130 = 1282 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_2130 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 2130) = 3 ^ 9 * m + 1282 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_2130.1, data_15_2130.2]

/-- Complete interval computation for depth 15, residue 2131. -/
theorem bounds_15_2131 : exactInterval 15 2131 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_2131 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 2131) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_2131 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_2131 : oddCount 2131 15 = 9 ∧ acceleratedOrbit 15 2131 = 1282 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_2131 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 2131) = 3 ^ 9 * m + 1282 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_2131.1, data_15_2131.2]

/-- Complete interval computation for depth 15, residue 2132. -/
theorem bounds_15_2132 : exactInterval 15 2132 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_2132 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 2132) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_2132 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_2132 : oddCount 2132 15 = 5 ∧ acceleratedOrbit 15 2132 = 17 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_2132 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 2132) = 3 ^ 5 * m + 17 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_2132.1, data_15_2132.2]

/-- Complete interval computation for depth 15, residue 2133. -/
theorem bounds_15_2133 : exactInterval 15 2133 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_2133 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 2133) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_2133 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_2133 : oddCount 2133 15 = 5 ∧ acceleratedOrbit 15 2133 = 17 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_2133 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 2133) = 3 ^ 5 * m + 17 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_2133.1, data_15_2133.2]

/-- Complete interval computation for depth 15, residue 2134. -/
theorem bounds_15_2134 : exactInterval 15 2134 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_2134 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 2134) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_2134 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_2134 : oddCount 2134 15 = 8 ∧ acceleratedOrbit 15 2134 = 431 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_2134 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 2134) = 3 ^ 8 * m + 431 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_2134.1, data_15_2134.2]

/-- Complete interval computation for depth 15, residue 2135. -/
theorem bounds_15_2135 : exactInterval 15 2135 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_2135 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 2135) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_2135 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_2135 : oddCount 2135 15 = 8 ∧ acceleratedOrbit 15 2135 = 431 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_2135 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 2135) = 3 ^ 8 * m + 431 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_2135.1, data_15_2135.2]

/-- Complete interval computation for depth 15, residue 2136. -/
theorem bounds_15_2136 : exactInterval 15 2136 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_2136 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 2136) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_2136 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_2136 : oddCount 2136 15 = 5 ∧ acceleratedOrbit 15 2136 = 16 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_2136 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 2136) = 3 ^ 5 * m + 16 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_2136.1, data_15_2136.2]

/-- Complete interval computation for depth 15, residue 2137. -/
theorem bounds_15_2137 : exactInterval 15 2137 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_2137 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 2137) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_2137 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_2137 : oddCount 2137 15 = 8 ∧ acceleratedOrbit 15 2137 = 431 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_2137 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 2137) = 3 ^ 8 * m + 431 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_2137.1, data_15_2137.2]

/-- Complete interval computation for depth 15, residue 2138. -/
theorem bounds_15_2138 : exactInterval 15 2138 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_2138 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 2138) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_2138 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_2138 : oddCount 2138 15 = 5 ∧ acceleratedOrbit 15 2138 = 16 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_2138 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 2138) = 3 ^ 5 * m + 16 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_2138.1, data_15_2138.2]

/-- Complete interval computation for depth 15, residue 2139. -/
theorem bounds_15_2139 : exactInterval 15 2139 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_2139 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 2139) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_2139 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_2139 : oddCount 2139 15 = 11 ∧ acceleratedOrbit 15 2139 = 11573 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_2139 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 2139) = 3 ^ 11 * m + 11573 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_2139.1, data_15_2139.2]

/-- Complete interval computation for depth 15, residue 2140. -/
theorem bounds_15_2140 : exactInterval 15 2140 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_2140 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 2140) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_2140 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_2140 : oddCount 2140 15 = 5 ∧ acceleratedOrbit 15 2140 = 16 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_2140 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 2140) = 3 ^ 5 * m + 16 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_2140.1, data_15_2140.2]

/-- Complete interval computation for depth 15, residue 2141. -/
theorem bounds_15_2141 : exactInterval 15 2141 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_2141 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 2141) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_2141 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_2141 : oddCount 2141 15 = 5 ∧ acceleratedOrbit 15 2141 = 16 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_2141 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 2141) = 3 ^ 5 * m + 16 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_2141.1, data_15_2141.2]

/-- Complete interval computation for depth 15, residue 2142. -/
theorem bounds_15_2142 : exactInterval 15 2142 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_2142 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 2142) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_2142 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_2142 : oddCount 2142 15 = 9 ∧ acceleratedOrbit 15 2142 = 1289 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_2142 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 2142) = 3 ^ 9 * m + 1289 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_2142.1, data_15_2142.2]

/-- Complete interval computation for depth 15, residue 2143. -/
theorem bounds_15_2143 : exactInterval 15 2143 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_2143 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 2143) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_2143 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_2143 : oddCount 2143 15 = 9 ∧ acceleratedOrbit 15 2143 = 1289 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_2143 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 2143) = 3 ^ 9 * m + 1289 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_2143.1, data_15_2143.2]

/-- Complete interval computation for depth 15, residue 2144. -/
theorem bounds_15_2144 : exactInterval 15 2144 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_2144 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 2144) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_2144 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_2144 : oddCount 2144 15 = 5 ∧ acceleratedOrbit 15 2144 = 17 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_2144 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 2144) = 3 ^ 5 * m + 17 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_2144.1, data_15_2144.2]

/-- Complete interval computation for depth 15, residue 2145. -/
theorem bounds_15_2145 : exactInterval 15 2145 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_2145 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 2145) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_2145 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_2145 : oddCount 2145 15 = 9 ∧ acceleratedOrbit 15 2145 = 1291 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_2145 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 2145) = 3 ^ 9 * m + 1291 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_2145.1, data_15_2145.2]

/-- Complete interval computation for depth 15, residue 2146. -/
theorem bounds_15_2146 : exactInterval 15 2146 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_2146 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 2146) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_2146 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_2146 : oddCount 2146 15 = 5 ∧ acceleratedOrbit 15 2146 = 16 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_2146 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 2146) = 3 ^ 5 * m + 16 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_2146.1, data_15_2146.2]

/-- Complete interval computation for depth 15, residue 2147. -/
theorem bounds_15_2147 : exactInterval 15 2147 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_2147 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 2147) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_2147 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_2147 : oddCount 2147 15 = 5 ∧ acceleratedOrbit 15 2147 = 16 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_2147 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 2147) = 3 ^ 5 * m + 16 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_2147.1, data_15_2147.2]

/-- Complete interval computation for depth 15, residue 2148. -/
theorem bounds_15_2148 : exactInterval 15 2148 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_2148 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 2148) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_2148 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_2148 : oddCount 2148 15 = 5 ∧ acceleratedOrbit 15 2148 = 16 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_2148 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 2148) = 3 ^ 5 * m + 16 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_2148.1, data_15_2148.2]

/-- Complete interval computation for depth 15, residue 2149. -/
theorem bounds_15_2149 : exactInterval 15 2149 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_2149 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 2149) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_2149 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_2149 : oddCount 2149 15 = 5 ∧ acceleratedOrbit 15 2149 = 16 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_2149 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 2149) = 3 ^ 5 * m + 16 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_2149.1, data_15_2149.2]

/-- Complete interval computation for depth 15, residue 2150. -/
theorem bounds_15_2150 : exactInterval 15 2150 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_2150 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 2150) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_2150 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_2150 : oddCount 2150 15 = 5 ∧ acceleratedOrbit 15 2150 = 16 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_2150 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 2150) = 3 ^ 5 * m + 16 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_2150.1, data_15_2150.2]

/-- Complete interval computation for depth 15, residue 2151. -/
theorem bounds_15_2151 : exactInterval 15 2151 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_2151 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 2151) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_2151 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_2151 : oddCount 2151 15 = 12 ∧ acceleratedOrbit 15 2151 = 34910 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_2151 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 2151) = 3 ^ 12 * m + 34910 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_2151.1, data_15_2151.2]

/-- Complete interval computation for depth 15, residue 2152. -/
theorem bounds_15_2152 : exactInterval 15 2152 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_2152 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 2152) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_2152 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_2152 : oddCount 2152 15 = 5 ∧ acceleratedOrbit 15 2152 = 17 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_2152 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 2152) = 3 ^ 5 * m + 17 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_2152.1, data_15_2152.2]

/-- Complete interval computation for depth 15, residue 2153. -/
theorem bounds_15_2153 : exactInterval 15 2153 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_2153 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 2153) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_2153 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_2153 : oddCount 2153 15 = 10 ∧ acceleratedOrbit 15 2153 = 3887 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_2153 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 2153) = 3 ^ 10 * m + 3887 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_2153.1, data_15_2153.2]

/-- Complete interval computation for depth 15, residue 2154. -/
theorem bounds_15_2154 : exactInterval 15 2154 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_2154 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 2154) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_2154 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_2154 : oddCount 2154 15 = 5 ∧ acceleratedOrbit 15 2154 = 17 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_2154 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 2154) = 3 ^ 5 * m + 17 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_2154.1, data_15_2154.2]

/-- Complete interval computation for depth 15, residue 2155. -/
theorem bounds_15_2155 : exactInterval 15 2155 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_2155 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 2155) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_2155 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_2155 : oddCount 2155 15 = 12 ∧ acceleratedOrbit 15 2155 = 34991 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_2155 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 2155) = 3 ^ 12 * m + 34991 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_2155.1, data_15_2155.2]

/-- Complete interval computation for depth 15, residue 2156. -/
theorem bounds_15_2156 : exactInterval 15 2156 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_2156 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 2156) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_2156 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_2156 : oddCount 2156 15 = 8 ∧ acceleratedOrbit 15 2156 = 433 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_2156 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 2156) = 3 ^ 8 * m + 433 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_2156.1, data_15_2156.2]

/-- Complete interval computation for depth 15, residue 2157. -/
theorem bounds_15_2157 : exactInterval 15 2157 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_2157 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 2157) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_2157 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_2157 : oddCount 2157 15 = 8 ∧ acceleratedOrbit 15 2157 = 433 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_2157 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 2157) = 3 ^ 8 * m + 433 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_2157.1, data_15_2157.2]

/-- Complete interval computation for depth 15, residue 2158. -/
theorem bounds_15_2158 : exactInterval 15 2158 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_2158 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 2158) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_2158 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_2158 : oddCount 2158 15 = 8 ∧ acceleratedOrbit 15 2158 = 433 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_2158 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 2158) = 3 ^ 8 * m + 433 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_2158.1, data_15_2158.2]

/-- Complete interval computation for depth 15, residue 2159. -/
theorem bounds_15_2159 : exactInterval 15 2159 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_2159 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 2159) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_2159 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_2159 : oddCount 2159 15 = 10 ∧ acceleratedOrbit 15 2159 = 3893 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_2159 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 2159) = 3 ^ 10 * m + 3893 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_2159.1, data_15_2159.2]

/-- Complete interval computation for depth 15, residue 2160. -/
theorem bounds_15_2160 : exactInterval 15 2160 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_2160 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 2160) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_2160 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_2160 : oddCount 2160 15 = 6 ∧ acceleratedOrbit 15 2160 = 49 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_2160 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 2160) = 3 ^ 6 * m + 49 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_2160.1, data_15_2160.2]

/-- Complete interval computation for depth 15, residue 2161. -/
theorem bounds_15_2161 : exactInterval 15 2161 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_2161 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 2161) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_2161 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_2161 : oddCount 2161 15 = 5 ∧ acceleratedOrbit 15 2161 = 17 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_2161 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 2161) = 3 ^ 5 * m + 17 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_2161.1, data_15_2161.2]

end Collatz.Research.PassageAtlas.Batch0066
