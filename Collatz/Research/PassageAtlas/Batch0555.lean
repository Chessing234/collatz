import Collatz.Research.DescentIntervals.Classifier

namespace Collatz.Research.PassageAtlas.Batch0555

open Collatz.Research.DescentIntervals

set_option maxRecDepth 20000
set_option maxHeartbeats 0

/-- Complete interval computation for depth 15, residue 18153. -/
theorem bounds_15_18153 : exactInterval 15 18153 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_18153 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 18153) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_18153 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_18153 : oddCount 18153 15 = 10 ∧ acceleratedOrbit 15 18153 = 32717 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_18153 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 18153) = 3 ^ 10 * m + 32717 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_18153.1, data_15_18153.2]

/-- Complete interval computation for depth 15, residue 18154. -/
theorem bounds_15_18154 : exactInterval 15 18154 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_18154 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 18154) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_18154 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_18154 : oddCount 18154 15 = 8 ∧ acceleratedOrbit 15 18154 = 3644 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_18154 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 18154) = 3 ^ 8 * m + 3644 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_18154.1, data_15_18154.2]

/-- Complete interval computation for depth 15, residue 18155. -/
theorem bounds_15_18155 : exactInterval 15 18155 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_18155 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 18155) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_18155 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_18155 : oddCount 18155 15 = 10 ∧ acceleratedOrbit 15 18155 = 32723 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_18155 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 18155) = 3 ^ 10 * m + 32723 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_18155.1, data_15_18155.2]

/-- Complete interval computation for depth 15, residue 18156. -/
theorem bounds_15_18156 : exactInterval 15 18156 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_18156 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 18156) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_18156 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_18156 : oddCount 18156 15 = 8 ∧ acceleratedOrbit 15 18156 = 3638 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_18156 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 18156) = 3 ^ 8 * m + 3638 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_18156.1, data_15_18156.2]

/-- Complete interval computation for depth 15, residue 18157. -/
theorem bounds_15_18157 : exactInterval 15 18157 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_18157 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 18157) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_18157 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_18157 : oddCount 18157 15 = 8 ∧ acceleratedOrbit 15 18157 = 3638 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_18157 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 18157) = 3 ^ 8 * m + 3638 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_18157.1, data_15_18157.2]

/-- Complete interval computation for depth 15, residue 18158. -/
theorem bounds_15_18158 : exactInterval 15 18158 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_18158 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 18158) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_18158 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_18158 : oddCount 18158 15 = 8 ∧ acceleratedOrbit 15 18158 = 3638 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_18158 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 18158) = 3 ^ 8 * m + 3638 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_18158.1, data_15_18158.2]

/-- Complete interval computation for depth 15, residue 18159. -/
theorem bounds_15_18159 : exactInterval 15 18159 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_18159 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 18159) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_18159 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_18159 : oddCount 18159 15 = 10 ∧ acceleratedOrbit 15 18159 = 32726 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_18159 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 18159) = 3 ^ 10 * m + 32726 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_18159.1, data_15_18159.2]

/-- Complete interval computation for depth 15, residue 18160. -/
theorem bounds_15_18160 : exactInterval 15 18160 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_18160 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 18160) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_18160 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_18160 : oddCount 18160 15 = 8 ∧ acceleratedOrbit 15 18160 = 3640 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_18160 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 18160) = 3 ^ 8 * m + 3640 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_18160.1, data_15_18160.2]

/-- Complete interval computation for depth 15, residue 18161. -/
theorem bounds_15_18161 : exactInterval 15 18161 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_18161 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 18161) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_18161 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_18161 : oddCount 18161 15 = 8 ∧ acceleratedOrbit 15 18161 = 3644 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_18161 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 18161) = 3 ^ 8 * m + 3644 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_18161.1, data_15_18161.2]

/-- Complete interval computation for depth 15, residue 18162. -/
theorem bounds_15_18162 : exactInterval 15 18162 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_18162 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 18162) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_18162 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_18162 : oddCount 18162 15 = 10 ∧ acceleratedOrbit 15 18162 = 32737 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_18162 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 18162) = 3 ^ 10 * m + 32737 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_18162.1, data_15_18162.2]

/-- Complete interval computation for depth 15, residue 18163. -/
theorem bounds_15_18163 : exactInterval 15 18163 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_18163 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 18163) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_18163 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_18163 : oddCount 18163 15 = 10 ∧ acceleratedOrbit 15 18163 = 32737 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_18163 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 18163) = 3 ^ 10 * m + 32737 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_18163.1, data_15_18163.2]

/-- Complete interval computation for depth 15, residue 18164. -/
theorem bounds_15_18164 : exactInterval 15 18164 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_18164 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 18164) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_18164 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_18164 : oddCount 18164 15 = 8 ∧ acceleratedOrbit 15 18164 = 3640 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_18164 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 18164) = 3 ^ 8 * m + 3640 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_18164.1, data_15_18164.2]

/-- Complete interval computation for depth 15, residue 18165. -/
theorem bounds_15_18165 : exactInterval 15 18165 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_18165 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 18165) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_18165 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_18165 : oddCount 18165 15 = 8 ∧ acceleratedOrbit 15 18165 = 3640 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_18165 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 18165) = 3 ^ 8 * m + 3640 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_18165.1, data_15_18165.2]

/-- Complete interval computation for depth 15, residue 18166. -/
theorem bounds_15_18166 : exactInterval 15 18166 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_18166 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 18166) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_18166 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_18166 : oddCount 18166 15 = 10 ∧ acceleratedOrbit 15 18166 = 32744 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_18166 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 18166) = 3 ^ 10 * m + 32744 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_18166.1, data_15_18166.2]

/-- Complete interval computation for depth 15, residue 18167. -/
theorem bounds_15_18167 : exactInterval 15 18167 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_18167 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 18167) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_18167 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_18167 : oddCount 18167 15 = 10 ∧ acceleratedOrbit 15 18167 = 32744 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_18167 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 18167) = 3 ^ 10 * m + 32744 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_18167.1, data_15_18167.2]

/-- Complete interval computation for depth 15, residue 18168. -/
theorem bounds_15_18168 : exactInterval 15 18168 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_18168 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 18168) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_18168 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_18168 : oddCount 18168 15 = 8 ∧ acceleratedOrbit 15 18168 = 3640 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_18168 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 18168) = 3 ^ 8 * m + 3640 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_18168.1, data_15_18168.2]

/-- Complete interval computation for depth 15, residue 18169. -/
theorem bounds_15_18169 : exactInterval 15 18169 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_18169 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 18169) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_18169 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_18169 : oddCount 18169 15 = 7 ∧ acceleratedOrbit 15 18169 = 1214 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_18169 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 18169) = 3 ^ 7 * m + 1214 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_18169.1, data_15_18169.2]

/-- Complete interval computation for depth 15, residue 18170. -/
theorem bounds_15_18170 : exactInterval 15 18170 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_18170 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 18170) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_18170 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_18170 : oddCount 18170 15 = 8 ∧ acceleratedOrbit 15 18170 = 3640 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_18170 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 18170) = 3 ^ 8 * m + 3640 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_18170.1, data_15_18170.2]

/-- Complete interval computation for depth 15, residue 18171. -/
theorem bounds_15_18171 : exactInterval 15 18171 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_18171 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 18171) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_18171 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_18171 : oddCount 18171 15 = 10 ∧ acceleratedOrbit 15 18171 = 32750 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_18171 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 18171) = 3 ^ 10 * m + 32750 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_18171.1, data_15_18171.2]

/-- Complete interval computation for depth 15, residue 18172. -/
theorem bounds_15_18172 : exactInterval 15 18172 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_18172 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 18172) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_18172 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_18172 : oddCount 18172 15 = 9 ∧ acceleratedOrbit 15 18172 = 10918 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_18172 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 18172) = 3 ^ 9 * m + 10918 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_18172.1, data_15_18172.2]

/-- Complete interval computation for depth 15, residue 18173. -/
theorem bounds_15_18173 : exactInterval 15 18173 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_18173 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 18173) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_18173 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_18173 : oddCount 18173 15 = 9 ∧ acceleratedOrbit 15 18173 = 10918 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_18173 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 18173) = 3 ^ 9 * m + 10918 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_18173.1, data_15_18173.2]

/-- Complete interval computation for depth 15, residue 18174. -/
theorem bounds_15_18174 : exactInterval 15 18174 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_18174 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 18174) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_18174 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_18174 : oddCount 18174 15 = 9 ∧ acceleratedOrbit 15 18174 = 10918 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_18174 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 18174) = 3 ^ 9 * m + 10918 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_18174.1, data_15_18174.2]

/-- Complete interval computation for depth 15, residue 18175. -/
theorem bounds_15_18175 : exactInterval 15 18175 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_18175 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 18175) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_18175 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_18175 : oddCount 18175 15 = 12 ∧ acceleratedOrbit 15 18175 = 294785 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_18175 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 18175) = 3 ^ 12 * m + 294785 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_18175.1, data_15_18175.2]

/-- Complete interval computation for depth 15, residue 18176. -/
theorem bounds_15_18176 : exactInterval 15 18176 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_18176 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 18176) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_18176 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_18176 : oddCount 18176 15 = 5 ∧ acceleratedOrbit 15 18176 = 137 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_18176 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 18176) = 3 ^ 5 * m + 137 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_18176.1, data_15_18176.2]

/-- Complete interval computation for depth 15, residue 18177. -/
theorem bounds_15_18177 : exactInterval 15 18177 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_18177 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 18177) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_18177 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_18177 : oddCount 18177 15 = 8 ∧ acceleratedOrbit 15 18177 = 3644 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_18177 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 18177) = 3 ^ 8 * m + 3644 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_18177.1, data_15_18177.2]

/-- Complete interval computation for depth 15, residue 18178. -/
theorem bounds_15_18178 : exactInterval 15 18178 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_18178 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 18178) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_18178 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_18178 : oddCount 18178 15 = 9 ∧ acceleratedOrbit 15 18178 = 10925 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_18178 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 18178) = 3 ^ 9 * m + 10925 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_18178.1, data_15_18178.2]

/-- Complete interval computation for depth 15, residue 18179. -/
theorem bounds_15_18179 : exactInterval 15 18179 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_18179 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 18179) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_18179 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_18179 : oddCount 18179 15 = 9 ∧ acceleratedOrbit 15 18179 = 10925 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_18179 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 18179) = 3 ^ 9 * m + 10925 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_18179.1, data_15_18179.2]

/-- Complete interval computation for depth 15, residue 18180. -/
theorem bounds_15_18180 : exactInterval 15 18180 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_18180 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 18180) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_18180 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_18180 : oddCount 18180 15 = 9 ∧ acceleratedOrbit 15 18180 = 10934 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_18180 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 18180) = 3 ^ 9 * m + 10934 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_18180.1, data_15_18180.2]

/-- Complete interval computation for depth 15, residue 18181. -/
theorem bounds_15_18181 : exactInterval 15 18181 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_18181 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 18181) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_18181 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_18181 : oddCount 18181 15 = 9 ∧ acceleratedOrbit 15 18181 = 10934 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_18181 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 18181) = 3 ^ 9 * m + 10934 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_18181.1, data_15_18181.2]

/-- Complete interval computation for depth 15, residue 18182. -/
theorem bounds_15_18182 : exactInterval 15 18182 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_18182 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 18182) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_18182 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_18182 : oddCount 18182 15 = 9 ∧ acceleratedOrbit 15 18182 = 10934 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_18182 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 18182) = 3 ^ 9 * m + 10934 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_18182.1, data_15_18182.2]

/-- Complete interval computation for depth 15, residue 18183. -/
theorem bounds_15_18183 : exactInterval 15 18183 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_18183 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 18183) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_18183 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_18183 : oddCount 18183 15 = 9 ∧ acceleratedOrbit 15 18183 = 10925 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_18183 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 18183) = 3 ^ 9 * m + 10925 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_18183.1, data_15_18183.2]

/-- Complete interval computation for depth 15, residue 18184. -/
theorem bounds_15_18184 : exactInterval 15 18184 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_18184 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 18184) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_18184 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_18184 : oddCount 18184 15 = 10 ∧ acceleratedOrbit 15 18184 = 32804 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_18184 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 18184) = 3 ^ 10 * m + 32804 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_18184.1, data_15_18184.2]

/-- Complete interval computation for depth 15, residue 18185. -/
theorem bounds_15_18185 : exactInterval 15 18185 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_18185 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 18185) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_18185 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_18185 : oddCount 18185 15 = 11 ∧ acceleratedOrbit 15 18185 = 98324 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_18185 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 18185) = 3 ^ 11 * m + 98324 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_18185.1, data_15_18185.2]

end Collatz.Research.PassageAtlas.Batch0555
