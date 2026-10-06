import Collatz.Research.DescentIntervals.Classifier

namespace Collatz.Research.PassageAtlas.Batch0674

open Collatz.Research.DescentIntervals

set_option maxRecDepth 20000
set_option maxHeartbeats 0

/-- Complete interval computation for depth 15, residue 22052. -/
theorem bounds_15_22052 : exactInterval 15 22052 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_22052 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 22052) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_22052 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_22052 : oddCount 22052 15 = 8 ∧ acceleratedOrbit 15 22052 = 4418 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_22052 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 22052) = 3 ^ 8 * m + 4418 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_22052.1, data_15_22052.2]

/-- Complete interval computation for depth 15, residue 22053. -/
theorem bounds_15_22053 : exactInterval 15 22053 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_22053 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 22053) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_22053 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_22053 : oddCount 22053 15 = 8 ∧ acceleratedOrbit 15 22053 = 4418 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_22053 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 22053) = 3 ^ 8 * m + 4418 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_22053.1, data_15_22053.2]

/-- Complete interval computation for depth 15, residue 22054. -/
theorem bounds_15_22054 : exactInterval 15 22054 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_22054 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 22054) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_22054 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_22054 : oddCount 22054 15 = 8 ∧ acceleratedOrbit 15 22054 = 4418 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_22054 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 22054) = 3 ^ 8 * m + 4418 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_22054.1, data_15_22054.2]

/-- Complete interval computation for depth 15, residue 22055. -/
theorem bounds_15_22055 : exactInterval 15 22055 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_22055 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 22055) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_22055 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_22055 : oddCount 22055 15 = 8 ∧ acceleratedOrbit 15 22055 = 4418 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_22055 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 22055) = 3 ^ 8 * m + 4418 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_22055.1, data_15_22055.2]

/-- Complete interval computation for depth 15, residue 22056. -/
theorem bounds_15_22056 : exactInterval 15 22056 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_22056 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 22056) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_22056 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_22056 : oddCount 22056 15 = 4 ∧ acceleratedOrbit 15 22056 = 55 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_22056 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 22056) = 3 ^ 4 * m + 55 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_22056.1, data_15_22056.2]

/-- Complete interval computation for depth 15, residue 22057. -/
theorem bounds_15_22057 : exactInterval 15 22057 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_22057 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 22057) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_22057 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_22057 : oddCount 22057 15 = 11 ∧ acceleratedOrbit 15 22057 = 119252 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_22057 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 22057) = 3 ^ 11 * m + 119252 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_22057.1, data_15_22057.2]

/-- Complete interval computation for depth 15, residue 22058. -/
theorem bounds_15_22058 : exactInterval 15 22058 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_22058 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 22058) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_22058 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_22058 : oddCount 22058 15 = 4 ∧ acceleratedOrbit 15 22058 = 55 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_22058 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 22058) = 3 ^ 4 * m + 55 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_22058.1, data_15_22058.2]

/-- Complete interval computation for depth 15, residue 22059. -/
theorem bounds_15_22059 : exactInterval 15 22059 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_22059 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 22059) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_22059 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_22059 : oddCount 22059 15 = 6 ∧ acceleratedOrbit 15 22059 = 491 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_22059 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 22059) = 3 ^ 6 * m + 491 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_22059.1, data_15_22059.2]

/-- Complete interval computation for depth 15, residue 22060. -/
theorem bounds_15_22060 : exactInterval 15 22060 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_22060 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 22060) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_22060 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_22060 : oddCount 22060 15 = 6 ∧ acceleratedOrbit 15 22060 = 491 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_22060 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 22060) = 3 ^ 6 * m + 491 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_22060.1, data_15_22060.2]

/-- Complete interval computation for depth 15, residue 22061. -/
theorem bounds_15_22061 : exactInterval 15 22061 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_22061 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 22061) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_22061 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_22061 : oddCount 22061 15 = 6 ∧ acceleratedOrbit 15 22061 = 491 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_22061 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 22061) = 3 ^ 6 * m + 491 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_22061.1, data_15_22061.2]

/-- Complete interval computation for depth 15, residue 22062. -/
theorem bounds_15_22062 : exactInterval 15 22062 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_22062 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 22062) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_22062 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_22062 : oddCount 22062 15 = 6 ∧ acceleratedOrbit 15 22062 = 491 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_22062 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 22062) = 3 ^ 6 * m + 491 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_22062.1, data_15_22062.2]

/-- Complete interval computation for depth 15, residue 22063. -/
theorem bounds_15_22063 : exactInterval 15 22063 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_22063 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 22063) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_22063 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_22063 : oddCount 22063 15 = 12 ∧ acceleratedOrbit 15 22063 = 357848 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_22063 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 22063) = 3 ^ 12 * m + 357848 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_22063.1, data_15_22063.2]

/-- Complete interval computation for depth 15, residue 22064. -/
theorem bounds_15_22064 : exactInterval 15 22064 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_22064 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 22064) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_22064 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_22064 : oddCount 22064 15 = 4 ∧ acceleratedOrbit 15 22064 = 55 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_22064 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 22064) = 3 ^ 4 * m + 55 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_22064.1, data_15_22064.2]

/-- Complete interval computation for depth 15, residue 22065. -/
theorem bounds_15_22065 : exactInterval 15 22065 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_22065 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 22065) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_22065 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_22065 : oddCount 22065 15 = 9 ∧ acceleratedOrbit 15 22065 = 13259 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_22065 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 22065) = 3 ^ 9 * m + 13259 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_22065.1, data_15_22065.2]

/-- Complete interval computation for depth 15, residue 22066. -/
theorem bounds_15_22066 : exactInterval 15 22066 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_22066 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 22066) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_22066 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_22066 : oddCount 22066 15 = 9 ∧ acceleratedOrbit 15 22066 = 13259 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_22066 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 22066) = 3 ^ 9 * m + 13259 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_22066.1, data_15_22066.2]

/-- Complete interval computation for depth 15, residue 22067. -/
theorem bounds_15_22067 : exactInterval 15 22067 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_22067 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 22067) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_22067 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_22067 : oddCount 22067 15 = 9 ∧ acceleratedOrbit 15 22067 = 13259 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_22067 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 22067) = 3 ^ 9 * m + 13259 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_22067.1, data_15_22067.2]

/-- Complete interval computation for depth 15, residue 22068. -/
theorem bounds_15_22068 : exactInterval 15 22068 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_22068 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 22068) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_22068 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_22068 : oddCount 22068 15 = 4 ∧ acceleratedOrbit 15 22068 = 55 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_22068 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 22068) = 3 ^ 4 * m + 55 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_22068.1, data_15_22068.2]

/-- Complete interval computation for depth 15, residue 22069. -/
theorem bounds_15_22069 : exactInterval 15 22069 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_22069 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 22069) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_22069 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_22069 : oddCount 22069 15 = 4 ∧ acceleratedOrbit 15 22069 = 55 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_22069 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 22069) = 3 ^ 4 * m + 55 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_22069.1, data_15_22069.2]

/-- Complete interval computation for depth 15, residue 22070. -/
theorem bounds_15_22070 : exactInterval 15 22070 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_22070 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 22070) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_22070 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_22070 : oddCount 22070 15 = 10 ∧ acceleratedOrbit 15 22070 = 39776 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_22070 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 22070) = 3 ^ 10 * m + 39776 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_22070.1, data_15_22070.2]

/-- Complete interval computation for depth 15, residue 22071. -/
theorem bounds_15_22071 : exactInterval 15 22071 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_22071 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 22071) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_22071 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_22071 : oddCount 22071 15 = 10 ∧ acceleratedOrbit 15 22071 = 39776 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_22071 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 22071) = 3 ^ 10 * m + 39776 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_22071.1, data_15_22071.2]

/-- Complete interval computation for depth 15, residue 22072. -/
theorem bounds_15_22072 : exactInterval 15 22072 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_22072 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 22072) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_22072 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_22072 : oddCount 22072 15 = 7 ∧ acceleratedOrbit 15 22072 = 1475 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_22072 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 22072) = 3 ^ 7 * m + 1475 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_22072.1, data_15_22072.2]

/-- Complete interval computation for depth 15, residue 22073. -/
theorem bounds_15_22073 : exactInterval 15 22073 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_22073 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 22073) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_22073 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_22073 : oddCount 22073 15 = 8 ∧ acceleratedOrbit 15 22073 = 4421 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_22073 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 22073) = 3 ^ 8 * m + 4421 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_22073.1, data_15_22073.2]

/-- Complete interval computation for depth 15, residue 22074. -/
theorem bounds_15_22074 : exactInterval 15 22074 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_22074 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 22074) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_22074 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_22074 : oddCount 22074 15 = 7 ∧ acceleratedOrbit 15 22074 = 1475 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_22074 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 22074) = 3 ^ 7 * m + 1475 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_22074.1, data_15_22074.2]

/-- Complete interval computation for depth 15, residue 22075. -/
theorem bounds_15_22075 : exactInterval 15 22075 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_22075 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 22075) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_22075 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_22075 : oddCount 22075 15 = 8 ∧ acceleratedOrbit 15 22075 = 4421 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_22075 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 22075) = 3 ^ 8 * m + 4421 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_22075.1, data_15_22075.2]

/-- Complete interval computation for depth 15, residue 22076. -/
theorem bounds_15_22076 : exactInterval 15 22076 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_22076 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 22076) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_22076 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_22076 : oddCount 22076 15 = 7 ∧ acceleratedOrbit 15 22076 = 1475 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_22076 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 22076) = 3 ^ 7 * m + 1475 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_22076.1, data_15_22076.2]

/-- Complete interval computation for depth 15, residue 22077. -/
theorem bounds_15_22077 : exactInterval 15 22077 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_22077 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 22077) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_22077 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_22077 : oddCount 22077 15 = 7 ∧ acceleratedOrbit 15 22077 = 1475 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_22077 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 22077) = 3 ^ 7 * m + 1475 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_22077.1, data_15_22077.2]

/-- Complete interval computation for depth 15, residue 22078. -/
theorem bounds_15_22078 : exactInterval 15 22078 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_22078 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 22078) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_22078 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_22078 : oddCount 22078 15 = 10 ∧ acceleratedOrbit 15 22078 = 39791 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_22078 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 22078) = 3 ^ 10 * m + 39791 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_22078.1, data_15_22078.2]

/-- Complete interval computation for depth 15, residue 22079. -/
theorem bounds_15_22079 : exactInterval 15 22079 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_22079 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 22079) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_22079 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_22079 : oddCount 22079 15 = 10 ∧ acceleratedOrbit 15 22079 = 39791 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_22079 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 22079) = 3 ^ 10 * m + 39791 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_22079.1, data_15_22079.2]

/-- Complete interval computation for depth 15, residue 22080. -/
theorem bounds_15_22080 : exactInterval 15 22080 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_22080 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 22080) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_22080 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_22080 : oddCount 22080 15 = 4 ∧ acceleratedOrbit 15 22080 = 55 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_22080 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 22080) = 3 ^ 4 * m + 55 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_22080.1, data_15_22080.2]

/-- Complete interval computation for depth 15, residue 22081. -/
theorem bounds_15_22081 : exactInterval 15 22081 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_22081 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 22081) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_22081 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_22081 : oddCount 22081 15 = 7 ∧ acceleratedOrbit 15 22081 = 1475 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_22081 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 22081) = 3 ^ 7 * m + 1475 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_22081.1, data_15_22081.2]

/-- Complete interval computation for depth 15, residue 22082. -/
theorem bounds_15_22082 : exactInterval 15 22082 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_22082 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 22082) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_22082 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_22082 : oddCount 22082 15 = 7 ∧ acceleratedOrbit 15 22082 = 1475 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_22082 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 22082) = 3 ^ 7 * m + 1475 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_22082.1, data_15_22082.2]

/-- Complete interval computation for depth 15, residue 22083. -/
theorem bounds_15_22083 : exactInterval 15 22083 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_22083 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 22083) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_22083 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_22083 : oddCount 22083 15 = 7 ∧ acceleratedOrbit 15 22083 = 1475 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_22083 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 22083) = 3 ^ 7 * m + 1475 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_22083.1, data_15_22083.2]

/-- Complete interval computation for depth 15, residue 22084. -/
theorem bounds_15_22084 : exactInterval 15 22084 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_22084 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 22084) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_22084 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_22084 : oddCount 22084 15 = 5 ∧ acceleratedOrbit 15 22084 = 164 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_22084 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 22084) = 3 ^ 5 * m + 164 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_22084.1, data_15_22084.2]

end Collatz.Research.PassageAtlas.Batch0674
