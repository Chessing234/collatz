import Collatz.Research.DescentIntervals.Classifier

namespace Collatz.Research.PassageAtlas.Batch0796

open Collatz.Research.DescentIntervals

set_option maxRecDepth 20000
set_option maxHeartbeats 0

/-- Complete interval computation for depth 15, residue 26050. -/
theorem bounds_15_26050 : exactInterval 15 26050 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_26050 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 26050) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_26050 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_26050 : oddCount 26050 15 = 11 ∧ acceleratedOrbit 15 26050 = 140858 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_26050 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 26050) = 3 ^ 11 * m + 140858 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_26050.1, data_15_26050.2]

/-- Complete interval computation for depth 15, residue 26051. -/
theorem bounds_15_26051 : exactInterval 15 26051 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_26051 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 26051) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_26051 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_26051 : oddCount 26051 15 = 11 ∧ acceleratedOrbit 15 26051 = 140858 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_26051 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 26051) = 3 ^ 11 * m + 140858 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_26051.1, data_15_26051.2]

/-- Complete interval computation for depth 15, residue 26052. -/
theorem bounds_15_26052 : exactInterval 15 26052 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_26052 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 26052) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_26052 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_26052 : oddCount 26052 15 = 4 ∧ acceleratedOrbit 15 26052 = 65 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_26052 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 26052) = 3 ^ 4 * m + 65 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_26052.1, data_15_26052.2]

/-- Complete interval computation for depth 15, residue 26053. -/
theorem bounds_15_26053 : exactInterval 15 26053 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_26053 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 26053) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_26053 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_26053 : oddCount 26053 15 = 4 ∧ acceleratedOrbit 15 26053 = 65 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_26053 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 26053) = 3 ^ 4 * m + 65 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_26053.1, data_15_26053.2]

/-- Complete interval computation for depth 15, residue 26054. -/
theorem bounds_15_26054 : exactInterval 15 26054 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_26054 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 26054) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_26054 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_26054 : oddCount 26054 15 = 4 ∧ acceleratedOrbit 15 26054 = 65 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_26054 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 26054) = 3 ^ 4 * m + 65 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_26054.1, data_15_26054.2]

/-- Complete interval computation for depth 15, residue 26055. -/
theorem bounds_15_26055 : exactInterval 15 26055 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_26055 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 26055) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_26055 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_26055 : oddCount 26055 15 = 9 ∧ acceleratedOrbit 15 26055 = 15653 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_26055 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 26055) = 3 ^ 9 * m + 15653 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_26055.1, data_15_26055.2]

/-- Complete interval computation for depth 15, residue 26056. -/
theorem bounds_15_26056 : exactInterval 15 26056 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_26056 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 26056) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_26056 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_26056 : oddCount 26056 15 = 7 ∧ acceleratedOrbit 15 26056 = 1741 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_26056 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 26056) = 3 ^ 7 * m + 1741 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_26056.1, data_15_26056.2]

/-- Complete interval computation for depth 15, residue 26057. -/
theorem bounds_15_26057 : exactInterval 15 26057 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_26057 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 26057) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_26057 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_26057 : oddCount 26057 15 = 6 ∧ acceleratedOrbit 15 26057 = 580 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_26057 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 26057) = 3 ^ 6 * m + 580 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_26057.1, data_15_26057.2]

/-- Complete interval computation for depth 15, residue 26058. -/
theorem bounds_15_26058 : exactInterval 15 26058 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_26058 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 26058) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_26058 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_26058 : oddCount 26058 15 = 7 ∧ acceleratedOrbit 15 26058 = 1741 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_26058 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 26058) = 3 ^ 7 * m + 1741 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_26058.1, data_15_26058.2]

/-- Complete interval computation for depth 15, residue 26059. -/
theorem bounds_15_26059 : exactInterval 15 26059 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_26059 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 26059) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_26059 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_26059 : oddCount 26059 15 = 9 ∧ acceleratedOrbit 15 26059 = 15659 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_26059 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 26059) = 3 ^ 9 * m + 15659 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_26059.1, data_15_26059.2]

/-- Complete interval computation for depth 15, residue 26060. -/
theorem bounds_15_26060 : exactInterval 15 26060 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_26060 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 26060) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_26060 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_26060 : oddCount 26060 15 = 7 ∧ acceleratedOrbit 15 26060 = 1741 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_26060 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 26060) = 3 ^ 7 * m + 1741 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_26060.1, data_15_26060.2]

/-- Complete interval computation for depth 15, residue 26061. -/
theorem bounds_15_26061 : exactInterval 15 26061 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_26061 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 26061) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_26061 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_26061 : oddCount 26061 15 = 7 ∧ acceleratedOrbit 15 26061 = 1741 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_26061 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 26061) = 3 ^ 7 * m + 1741 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_26061.1, data_15_26061.2]

/-- Complete interval computation for depth 15, residue 26062. -/
theorem bounds_15_26062 : exactInterval 15 26062 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_26062 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 26062) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_26062 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_26062 : oddCount 26062 15 = 10 ∧ acceleratedOrbit 15 26062 = 46970 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_26062 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 26062) = 3 ^ 10 * m + 46970 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_26062.1, data_15_26062.2]

/-- Complete interval computation for depth 15, residue 26063. -/
theorem bounds_15_26063 : exactInterval 15 26063 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_26063 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 26063) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_26063 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_26063 : oddCount 26063 15 = 10 ∧ acceleratedOrbit 15 26063 = 46970 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_26063 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 26063) = 3 ^ 10 * m + 46970 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_26063.1, data_15_26063.2]

/-- Complete interval computation for depth 15, residue 26064. -/
theorem bounds_15_26064 : exactInterval 15 26064 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_26064 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 26064) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_26064 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_26064 : oddCount 26064 15 = 4 ∧ acceleratedOrbit 15 26064 = 65 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_26064 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 26064) = 3 ^ 4 * m + 65 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_26064.1, data_15_26064.2]

/-- Complete interval computation for depth 15, residue 26065. -/
theorem bounds_15_26065 : exactInterval 15 26065 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_26065 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 26065) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_26065 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_26065 : oddCount 26065 15 = 7 ∧ acceleratedOrbit 15 26065 = 1741 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_26065 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 26065) = 3 ^ 7 * m + 1741 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_26065.1, data_15_26065.2]

/-- Complete interval computation for depth 15, residue 26066. -/
theorem bounds_15_26066 : exactInterval 15 26066 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_26066 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 26066) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_26066 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_26066 : oddCount 26066 15 = 11 ∧ acceleratedOrbit 15 26066 = 140939 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_26066 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 26066) = 3 ^ 11 * m + 140939 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_26066.1, data_15_26066.2]

/-- Complete interval computation for depth 15, residue 26067. -/
theorem bounds_15_26067 : exactInterval 15 26067 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_26067 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 26067) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_26067 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_26067 : oddCount 26067 15 = 11 ∧ acceleratedOrbit 15 26067 = 140939 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_26067 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 26067) = 3 ^ 11 * m + 140939 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_26067.1, data_15_26067.2]

/-- Complete interval computation for depth 15, residue 26068. -/
theorem bounds_15_26068 : exactInterval 15 26068 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_26068 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 26068) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_26068 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_26068 : oddCount 26068 15 = 4 ∧ acceleratedOrbit 15 26068 = 65 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_26068 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 26068) = 3 ^ 4 * m + 65 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_26068.1, data_15_26068.2]

/-- Complete interval computation for depth 15, residue 26069. -/
theorem bounds_15_26069 : exactInterval 15 26069 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_26069 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 26069) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_26069 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_26069 : oddCount 26069 15 = 4 ∧ acceleratedOrbit 15 26069 = 65 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_26069 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 26069) = 3 ^ 4 * m + 65 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_26069.1, data_15_26069.2]

/-- Complete interval computation for depth 15, residue 26070. -/
theorem bounds_15_26070 : exactInterval 15 26070 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_26070 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 26070) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_26070 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_26070 : oddCount 26070 15 = 8 ∧ acceleratedOrbit 15 26070 = 5221 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_26070 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 26070) = 3 ^ 8 * m + 5221 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_26070.1, data_15_26070.2]

/-- Complete interval computation for depth 15, residue 26071. -/
theorem bounds_15_26071 : exactInterval 15 26071 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_26071 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 26071) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_26071 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_26071 : oddCount 26071 15 = 8 ∧ acceleratedOrbit 15 26071 = 5221 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_26071 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 26071) = 3 ^ 8 * m + 5221 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_26071.1, data_15_26071.2]

/-- Complete interval computation for depth 15, residue 26072. -/
theorem bounds_15_26072 : exactInterval 15 26072 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_26072 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 26072) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_26072 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_26072 : oddCount 26072 15 = 8 ∧ acceleratedOrbit 15 26072 = 5224 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_26072 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 26072) = 3 ^ 8 * m + 5224 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_26072.1, data_15_26072.2]

/-- Complete interval computation for depth 15, residue 26073. -/
theorem bounds_15_26073 : exactInterval 15 26073 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_26073 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 26073) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_26073 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_26073 : oddCount 26073 15 = 8 ∧ acceleratedOrbit 15 26073 = 5224 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_26073 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 26073) = 3 ^ 8 * m + 5224 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_26073.1, data_15_26073.2]

/-- Complete interval computation for depth 15, residue 26074. -/
theorem bounds_15_26074 : exactInterval 15 26074 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_26074 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 26074) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_26074 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_26074 : oddCount 26074 15 = 8 ∧ acceleratedOrbit 15 26074 = 5224 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_26074 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 26074) = 3 ^ 8 * m + 5224 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_26074.1, data_15_26074.2]

/-- Complete interval computation for depth 15, residue 26075. -/
theorem bounds_15_26075 : exactInterval 15 26075 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_26075 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 26075) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_26075 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_26075 : oddCount 26075 15 = 7 ∧ acceleratedOrbit 15 26075 = 1741 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_26075 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 26075) = 3 ^ 7 * m + 1741 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_26075.1, data_15_26075.2]

/-- Complete interval computation for depth 15, residue 26076. -/
theorem bounds_15_26076 : exactInterval 15 26076 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_26076 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 26076) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_26076 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_26076 : oddCount 26076 15 = 8 ∧ acceleratedOrbit 15 26076 = 5224 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_26076 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 26076) = 3 ^ 8 * m + 5224 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_26076.1, data_15_26076.2]

/-- Complete interval computation for depth 15, residue 26077. -/
theorem bounds_15_26077 : exactInterval 15 26077 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_26077 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 26077) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_26077 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_26077 : oddCount 26077 15 = 8 ∧ acceleratedOrbit 15 26077 = 5224 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_26077 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 26077) = 3 ^ 8 * m + 5224 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_26077.1, data_15_26077.2]

/-- Complete interval computation for depth 15, residue 26078. -/
theorem bounds_15_26078 : exactInterval 15 26078 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_26078 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 26078) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_26078 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_26078 : oddCount 26078 15 = 12 ∧ acceleratedOrbit 15 26078 = 422981 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_26078 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 26078) = 3 ^ 12 * m + 422981 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_26078.1, data_15_26078.2]

/-- Complete interval computation for depth 15, residue 26079. -/
theorem bounds_15_26079 : exactInterval 15 26079 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_26079 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 26079) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_26079 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_26079 : oddCount 26079 15 = 12 ∧ acceleratedOrbit 15 26079 = 422981 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_26079 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 26079) = 3 ^ 12 * m + 422981 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_26079.1, data_15_26079.2]

/-- Complete interval computation for depth 15, residue 26080. -/
theorem bounds_15_26080 : exactInterval 15 26080 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_26080 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 26080) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_26080 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_26080 : oddCount 26080 15 = 6 ∧ acceleratedOrbit 15 26080 = 581 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_26080 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 26080) = 3 ^ 6 * m + 581 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_26080.1, data_15_26080.2]

/-- Complete interval computation for depth 15, residue 26081. -/
theorem bounds_15_26081 : exactInterval 15 26081 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_26081 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 26081) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_26081 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_26081 : oddCount 26081 15 = 10 ∧ acceleratedOrbit 15 26081 = 47006 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_26081 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 26081) = 3 ^ 10 * m + 47006 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_26081.1, data_15_26081.2]

/-- Complete interval computation for depth 15, residue 26082. -/
theorem bounds_15_26082 : exactInterval 15 26082 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_26082 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 26082) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_26082 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_26082 : oddCount 26082 15 = 4 ∧ acceleratedOrbit 15 26082 = 65 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_26082 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 26082) = 3 ^ 4 * m + 65 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_26082.1, data_15_26082.2]

end Collatz.Research.PassageAtlas.Batch0796
