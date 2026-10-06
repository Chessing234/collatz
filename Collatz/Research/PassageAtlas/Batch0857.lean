import Collatz.Research.DescentIntervals.Classifier

namespace Collatz.Research.PassageAtlas.Batch0857

open Collatz.Research.DescentIntervals

set_option maxRecDepth 20000
set_option maxHeartbeats 0

/-- Complete interval computation for depth 15, residue 28049. -/
theorem bounds_15_28049 : exactInterval 15 28049 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_28049 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 28049) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_28049 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_28049 : oddCount 28049 15 = 7 ∧ acceleratedOrbit 15 28049 = 1873 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_28049 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 28049) = 3 ^ 7 * m + 1873 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_28049.1, data_15_28049.2]

/-- Complete interval computation for depth 15, residue 28050. -/
theorem bounds_15_28050 : exactInterval 15 28050 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_28050 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 28050) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_28050 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_28050 : oddCount 28050 15 = 7 ∧ acceleratedOrbit 15 28050 = 1873 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_28050 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 28050) = 3 ^ 7 * m + 1873 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_28050.1, data_15_28050.2]

/-- Complete interval computation for depth 15, residue 28051. -/
theorem bounds_15_28051 : exactInterval 15 28051 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_28051 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 28051) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_28051 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_28051 : oddCount 28051 15 = 7 ∧ acceleratedOrbit 15 28051 = 1873 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_28051 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 28051) = 3 ^ 7 * m + 1873 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_28051.1, data_15_28051.2]

/-- Complete interval computation for depth 15, residue 28052. -/
theorem bounds_15_28052 : exactInterval 15 28052 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_28052 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 28052) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_28052 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_28052 : oddCount 28052 15 = 5 ∧ acceleratedOrbit 15 28052 = 209 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_28052 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 28052) = 3 ^ 5 * m + 209 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_28052.1, data_15_28052.2]

/-- Complete interval computation for depth 15, residue 28053. -/
theorem bounds_15_28053 : exactInterval 15 28053 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_28053 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 28053) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_28053 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_28053 : oddCount 28053 15 = 5 ∧ acceleratedOrbit 15 28053 = 209 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_28053 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 28053) = 3 ^ 5 * m + 209 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_28053.1, data_15_28053.2]

/-- Complete interval computation for depth 15, residue 28054. -/
theorem bounds_15_28054 : exactInterval 15 28054 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_28054 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 28054) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_28054 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_28054 : oddCount 28054 15 = 7 ∧ acceleratedOrbit 15 28054 = 1873 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_28054 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 28054) = 3 ^ 7 * m + 1873 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_28054.1, data_15_28054.2]

/-- Complete interval computation for depth 15, residue 28055. -/
theorem bounds_15_28055 : exactInterval 15 28055 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_28055 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 28055) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_28055 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_28055 : oddCount 28055 15 = 7 ∧ acceleratedOrbit 15 28055 = 1873 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_28055 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 28055) = 3 ^ 7 * m + 1873 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_28055.1, data_15_28055.2]

/-- Complete interval computation for depth 15, residue 28056. -/
theorem bounds_15_28056 : exactInterval 15 28056 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_28056 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 28056) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_28056 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_28056 : oddCount 28056 15 = 5 ∧ acceleratedOrbit 15 28056 = 209 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_28056 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 28056) = 3 ^ 5 * m + 209 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_28056.1, data_15_28056.2]

/-- Complete interval computation for depth 15, residue 28057. -/
theorem bounds_15_28057 : exactInterval 15 28057 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_28057 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 28057) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_28057 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_28057 : oddCount 28057 15 = 7 ∧ acceleratedOrbit 15 28057 = 1873 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_28057 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 28057) = 3 ^ 7 * m + 1873 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_28057.1, data_15_28057.2]

/-- Complete interval computation for depth 15, residue 28058. -/
theorem bounds_15_28058 : exactInterval 15 28058 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_28058 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 28058) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_28058 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_28058 : oddCount 28058 15 = 5 ∧ acceleratedOrbit 15 28058 = 209 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_28058 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 28058) = 3 ^ 5 * m + 209 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_28058.1, data_15_28058.2]

/-- Complete interval computation for depth 15, residue 28059. -/
theorem bounds_15_28059 : exactInterval 15 28059 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_28059 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 28059) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_28059 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_28059 : oddCount 28059 15 = 9 ∧ acceleratedOrbit 15 28059 = 16856 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_28059 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 28059) = 3 ^ 9 * m + 16856 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_28059.1, data_15_28059.2]

/-- Complete interval computation for depth 15, residue 28060. -/
theorem bounds_15_28060 : exactInterval 15 28060 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_28060 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 28060) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_28060 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_28060 : oddCount 28060 15 = 9 ∧ acceleratedOrbit 15 28060 = 16858 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_28060 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 28060) = 3 ^ 9 * m + 16858 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_28060.1, data_15_28060.2]

/-- Complete interval computation for depth 15, residue 28061. -/
theorem bounds_15_28061 : exactInterval 15 28061 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_28061 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 28061) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_28061 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_28061 : oddCount 28061 15 = 9 ∧ acceleratedOrbit 15 28061 = 16858 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_28061 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 28061) = 3 ^ 9 * m + 16858 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_28061.1, data_15_28061.2]

/-- Complete interval computation for depth 15, residue 28062. -/
theorem bounds_15_28062 : exactInterval 15 28062 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_28062 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 28062) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_28062 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_28062 : oddCount 28062 15 = 9 ∧ acceleratedOrbit 15 28062 = 16858 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_28062 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 28062) = 3 ^ 9 * m + 16858 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_28062.1, data_15_28062.2]

/-- Complete interval computation for depth 15, residue 28063. -/
theorem bounds_15_28063 : exactInterval 15 28063 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_28063 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 28063) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_28063 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_28063 : oddCount 28063 15 = 10 ∧ acceleratedOrbit 15 28063 = 50573 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_28063 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 28063) = 3 ^ 10 * m + 50573 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_28063.1, data_15_28063.2]

/-- Complete interval computation for depth 15, residue 28064. -/
theorem bounds_15_28064 : exactInterval 15 28064 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_28064 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 28064) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_28064 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_28064 : oddCount 28064 15 = 5 ∧ acceleratedOrbit 15 28064 = 209 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_28064 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 28064) = 3 ^ 5 * m + 209 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_28064.1, data_15_28064.2]

/-- Complete interval computation for depth 15, residue 28065. -/
theorem bounds_15_28065 : exactInterval 15 28065 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_28065 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 28065) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_28065 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_28065 : oddCount 28065 15 = 9 ∧ acceleratedOrbit 15 28065 = 16861 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_28065 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 28065) = 3 ^ 9 * m + 16861 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_28065.1, data_15_28065.2]

/-- Complete interval computation for depth 15, residue 28066. -/
theorem bounds_15_28066 : exactInterval 15 28066 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_28066 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 28066) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_28066 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_28066 : oddCount 28066 15 = 7 ∧ acceleratedOrbit 15 28066 = 1874 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_28066 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 28066) = 3 ^ 7 * m + 1874 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_28066.1, data_15_28066.2]

/-- Complete interval computation for depth 15, residue 28067. -/
theorem bounds_15_28067 : exactInterval 15 28067 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_28067 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 28067) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_28067 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_28067 : oddCount 28067 15 = 7 ∧ acceleratedOrbit 15 28067 = 1874 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_28067 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 28067) = 3 ^ 7 * m + 1874 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_28067.1, data_15_28067.2]

/-- Complete interval computation for depth 15, residue 28068. -/
theorem bounds_15_28068 : exactInterval 15 28068 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_28068 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 28068) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_28068 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_28068 : oddCount 28068 15 = 7 ∧ acceleratedOrbit 15 28068 = 1874 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_28068 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 28068) = 3 ^ 7 * m + 1874 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_28068.1, data_15_28068.2]

/-- Complete interval computation for depth 15, residue 28069. -/
theorem bounds_15_28069 : exactInterval 15 28069 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_28069 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 28069) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_28069 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_28069 : oddCount 28069 15 = 7 ∧ acceleratedOrbit 15 28069 = 1874 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_28069 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 28069) = 3 ^ 7 * m + 1874 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_28069.1, data_15_28069.2]

/-- Complete interval computation for depth 15, residue 28070. -/
theorem bounds_15_28070 : exactInterval 15 28070 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_28070 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 28070) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_28070 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_28070 : oddCount 28070 15 = 7 ∧ acceleratedOrbit 15 28070 = 1874 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_28070 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 28070) = 3 ^ 7 * m + 1874 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_28070.1, data_15_28070.2]

/-- Complete interval computation for depth 15, residue 28071. -/
theorem bounds_15_28071 : exactInterval 15 28071 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_28071 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 28071) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_28071 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_28071 : oddCount 28071 15 = 8 ∧ acceleratedOrbit 15 28071 = 5621 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_28071 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 28071) = 3 ^ 8 * m + 5621 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_28071.1, data_15_28071.2]

/-- Complete interval computation for depth 15, residue 28072. -/
theorem bounds_15_28072 : exactInterval 15 28072 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_28072 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 28072) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_28072 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_28072 : oddCount 28072 15 = 5 ∧ acceleratedOrbit 15 28072 = 209 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_28072 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 28072) = 3 ^ 5 * m + 209 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_28072.1, data_15_28072.2]

/-- Complete interval computation for depth 15, residue 28073. -/
theorem bounds_15_28073 : exactInterval 15 28073 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_28073 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 28073) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_28073 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_28073 : oddCount 28073 15 = 9 ∧ acceleratedOrbit 15 28073 = 16865 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_28073 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 28073) = 3 ^ 9 * m + 16865 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_28073.1, data_15_28073.2]

/-- Complete interval computation for depth 15, residue 28074. -/
theorem bounds_15_28074 : exactInterval 15 28074 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_28074 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 28074) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_28074 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_28074 : oddCount 28074 15 = 5 ∧ acceleratedOrbit 15 28074 = 209 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_28074 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 28074) = 3 ^ 5 * m + 209 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_28074.1, data_15_28074.2]

/-- Complete interval computation for depth 15, residue 28075. -/
theorem bounds_15_28075 : exactInterval 15 28075 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_28075 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 28075) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_28075 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_28075 : oddCount 28075 15 = 11 ∧ acceleratedOrbit 15 28075 = 151793 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_28075 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 28075) = 3 ^ 11 * m + 151793 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_28075.1, data_15_28075.2]

/-- Complete interval computation for depth 15, residue 28076. -/
theorem bounds_15_28076 : exactInterval 15 28076 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_28076 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 28076) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_28076 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_28076 : oddCount 28076 15 = 6 ∧ acceleratedOrbit 15 28076 = 625 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_28076 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 28076) = 3 ^ 6 * m + 625 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_28076.1, data_15_28076.2]

/-- Complete interval computation for depth 15, residue 28077. -/
theorem bounds_15_28077 : exactInterval 15 28077 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_28077 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 28077) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_28077 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_28077 : oddCount 28077 15 = 6 ∧ acceleratedOrbit 15 28077 = 625 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_28077 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 28077) = 3 ^ 6 * m + 625 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_28077.1, data_15_28077.2]

/-- Complete interval computation for depth 15, residue 28078. -/
theorem bounds_15_28078 : exactInterval 15 28078 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_28078 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 28078) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_28078 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_28078 : oddCount 28078 15 = 6 ∧ acceleratedOrbit 15 28078 = 625 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_28078 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 28078) = 3 ^ 6 * m + 625 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_28078.1, data_15_28078.2]

/-- Complete interval computation for depth 15, residue 28079. -/
theorem bounds_15_28079 : exactInterval 15 28079 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_28079 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 28079) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_28079 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_28079 : oddCount 28079 15 = 9 ∧ acceleratedOrbit 15 28079 = 16868 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_28079 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 28079) = 3 ^ 9 * m + 16868 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_28079.1, data_15_28079.2]

/-- Complete interval computation for depth 15, residue 28080. -/
theorem bounds_15_28080 : exactInterval 15 28080 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_28080 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 28080) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_28080 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_28080 : oddCount 28080 15 = 7 ∧ acceleratedOrbit 15 28080 = 1876 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_28080 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 28080) = 3 ^ 7 * m + 1876 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_28080.1, data_15_28080.2]

/-- Complete interval computation for depth 15, residue 28081. -/
theorem bounds_15_28081 : exactInterval 15 28081 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_28081 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 28081) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_28081 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_28081 : oddCount 28081 15 = 7 ∧ acceleratedOrbit 15 28081 = 1876 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_28081 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 28081) = 3 ^ 7 * m + 1876 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_28081.1, data_15_28081.2]

end Collatz.Research.PassageAtlas.Batch0857
