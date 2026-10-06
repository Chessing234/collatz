import Collatz.Research.DescentIntervals.Classifier

namespace Collatz.Research.PassageAtlas.Batch0552

open Collatz.Research.DescentIntervals

set_option maxRecDepth 20000
set_option maxHeartbeats 0

/-- Complete interval computation for depth 15, residue 18055. -/
theorem bounds_15_18055 : exactInterval 15 18055 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_18055 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 18055) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_18055 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_18055 : oddCount 18055 15 = 8 ∧ acceleratedOrbit 15 18055 = 3617 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_18055 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 18055) = 3 ^ 8 * m + 3617 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_18055.1, data_15_18055.2]

/-- Complete interval computation for depth 15, residue 18056. -/
theorem bounds_15_18056 : exactInterval 15 18056 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_18056 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 18056) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_18056 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_18056 : oddCount 18056 15 = 7 ∧ acceleratedOrbit 15 18056 = 1208 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_18056 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 18056) = 3 ^ 7 * m + 1208 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_18056.1, data_15_18056.2]

/-- Complete interval computation for depth 15, residue 18057. -/
theorem bounds_15_18057 : exactInterval 15 18057 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_18057 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 18057) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_18057 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_18057 : oddCount 18057 15 = 11 ∧ acceleratedOrbit 15 18057 = 97631 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_18057 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 18057) = 3 ^ 11 * m + 97631 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_18057.1, data_15_18057.2]

/-- Complete interval computation for depth 15, residue 18058. -/
theorem bounds_15_18058 : exactInterval 15 18058 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_18058 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 18058) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_18058 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_18058 : oddCount 18058 15 = 7 ∧ acceleratedOrbit 15 18058 = 1208 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_18058 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 18058) = 3 ^ 7 * m + 1208 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_18058.1, data_15_18058.2]

/-- Complete interval computation for depth 15, residue 18059. -/
theorem bounds_15_18059 : exactInterval 15 18059 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_18059 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 18059) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_18059 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_18059 : oddCount 18059 15 = 9 ∧ acceleratedOrbit 15 18059 = 10853 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_18059 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 18059) = 3 ^ 9 * m + 10853 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_18059.1, data_15_18059.2]

/-- Complete interval computation for depth 15, residue 18060. -/
theorem bounds_15_18060 : exactInterval 15 18060 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_18060 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 18060) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_18060 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_18060 : oddCount 18060 15 = 7 ∧ acceleratedOrbit 15 18060 = 1208 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_18060 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 18060) = 3 ^ 7 * m + 1208 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_18060.1, data_15_18060.2]

/-- Complete interval computation for depth 15, residue 18061. -/
theorem bounds_15_18061 : exactInterval 15 18061 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_18061 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 18061) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_18061 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_18061 : oddCount 18061 15 = 7 ∧ acceleratedOrbit 15 18061 = 1208 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_18061 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 18061) = 3 ^ 7 * m + 1208 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_18061.1, data_15_18061.2]

/-- Complete interval computation for depth 15, residue 18062. -/
theorem bounds_15_18062 : exactInterval 15 18062 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_18062 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 18062) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_18062 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_18062 : oddCount 18062 15 = 10 ∧ acceleratedOrbit 15 18062 = 32555 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_18062 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 18062) = 3 ^ 10 * m + 32555 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_18062.1, data_15_18062.2]

/-- Complete interval computation for depth 15, residue 18063. -/
theorem bounds_15_18063 : exactInterval 15 18063 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_18063 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 18063) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_18063 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_18063 : oddCount 18063 15 = 10 ∧ acceleratedOrbit 15 18063 = 32555 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_18063 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 18063) = 3 ^ 10 * m + 32555 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_18063.1, data_15_18063.2]

/-- Complete interval computation for depth 15, residue 18064. -/
theorem bounds_15_18064 : exactInterval 15 18064 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_18064 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 18064) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_18064 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_18064 : oddCount 18064 15 = 7 ∧ acceleratedOrbit 15 18064 = 1208 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_18064 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 18064) = 3 ^ 7 * m + 1208 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_18064.1, data_15_18064.2]

/-- Complete interval computation for depth 15, residue 18065. -/
theorem bounds_15_18065 : exactInterval 15 18065 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_18065 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 18065) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_18065 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_18065 : oddCount 18065 15 = 5 ∧ acceleratedOrbit 15 18065 = 134 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_18065 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 18065) = 3 ^ 5 * m + 134 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_18065.1, data_15_18065.2]

/-- Complete interval computation for depth 15, residue 18066. -/
theorem bounds_15_18066 : exactInterval 15 18066 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_18066 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 18066) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_18066 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_18066 : oddCount 18066 15 = 5 ∧ acceleratedOrbit 15 18066 = 134 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_18066 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 18066) = 3 ^ 5 * m + 134 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_18066.1, data_15_18066.2]

/-- Complete interval computation for depth 15, residue 18067. -/
theorem bounds_15_18067 : exactInterval 15 18067 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_18067 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 18067) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_18067 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_18067 : oddCount 18067 15 = 5 ∧ acceleratedOrbit 15 18067 = 134 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_18067 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 18067) = 3 ^ 5 * m + 134 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_18067.1, data_15_18067.2]

/-- Complete interval computation for depth 15, residue 18068. -/
theorem bounds_15_18068 : exactInterval 15 18068 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_18068 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 18068) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_18068 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_18068 : oddCount 18068 15 = 7 ∧ acceleratedOrbit 15 18068 = 1208 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_18068 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 18068) = 3 ^ 7 * m + 1208 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_18068.1, data_15_18068.2]

/-- Complete interval computation for depth 15, residue 18069. -/
theorem bounds_15_18069 : exactInterval 15 18069 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_18069 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 18069) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_18069 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_18069 : oddCount 18069 15 = 7 ∧ acceleratedOrbit 15 18069 = 1208 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_18069 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 18069) = 3 ^ 7 * m + 1208 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_18069.1, data_15_18069.2]

/-- Complete interval computation for depth 15, residue 18070. -/
theorem bounds_15_18070 : exactInterval 15 18070 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_18070 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 18070) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_18070 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_18070 : oddCount 18070 15 = 7 ∧ acceleratedOrbit 15 18070 = 1208 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_18070 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 18070) = 3 ^ 7 * m + 1208 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_18070.1, data_15_18070.2]

/-- Complete interval computation for depth 15, residue 18071. -/
theorem bounds_15_18071 : exactInterval 15 18071 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_18071 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 18071) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_18071 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_18071 : oddCount 18071 15 = 7 ∧ acceleratedOrbit 15 18071 = 1208 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_18071 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 18071) = 3 ^ 7 * m + 1208 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_18071.1, data_15_18071.2]

/-- Complete interval computation for depth 15, residue 18072. -/
theorem bounds_15_18072 : exactInterval 15 18072 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_18072 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 18072) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_18072 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_18072 : oddCount 18072 15 = 7 ∧ acceleratedOrbit 15 18072 = 1208 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_18072 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 18072) = 3 ^ 7 * m + 1208 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_18072.1, data_15_18072.2]

/-- Complete interval computation for depth 15, residue 18073. -/
theorem bounds_15_18073 : exactInterval 15 18073 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_18073 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 18073) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_18073 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_18073 : oddCount 18073 15 = 8 ∧ acceleratedOrbit 15 18073 = 3620 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_18073 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 18073) = 3 ^ 8 * m + 3620 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_18073.1, data_15_18073.2]

/-- Complete interval computation for depth 15, residue 18074. -/
theorem bounds_15_18074 : exactInterval 15 18074 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_18074 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 18074) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_18074 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_18074 : oddCount 18074 15 = 7 ∧ acceleratedOrbit 15 18074 = 1208 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_18074 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 18074) = 3 ^ 7 * m + 1208 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_18074.1, data_15_18074.2]

/-- Complete interval computation for depth 15, residue 18075. -/
theorem bounds_15_18075 : exactInterval 15 18075 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_18075 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 18075) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_18075 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_18075 : oddCount 18075 15 = 10 ∧ acceleratedOrbit 15 18075 = 32575 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_18075 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 18075) = 3 ^ 10 * m + 32575 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_18075.1, data_15_18075.2]

/-- Complete interval computation for depth 15, residue 18076. -/
theorem bounds_15_18076 : exactInterval 15 18076 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_18076 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 18076) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_18076 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_18076 : oddCount 18076 15 = 7 ∧ acceleratedOrbit 15 18076 = 1207 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_18076 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 18076) = 3 ^ 7 * m + 1207 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_18076.1, data_15_18076.2]

/-- Complete interval computation for depth 15, residue 18077. -/
theorem bounds_15_18077 : exactInterval 15 18077 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_18077 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 18077) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_18077 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_18077 : oddCount 18077 15 = 7 ∧ acceleratedOrbit 15 18077 = 1207 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_18077 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 18077) = 3 ^ 7 * m + 1207 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_18077.1, data_15_18077.2]

/-- Complete interval computation for depth 15, residue 18078. -/
theorem bounds_15_18078 : exactInterval 15 18078 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_18078 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 18078) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_18078 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_18078 : oddCount 18078 15 = 7 ∧ acceleratedOrbit 15 18078 = 1207 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_18078 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 18078) = 3 ^ 7 * m + 1207 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_18078.1, data_15_18078.2]

/-- Complete interval computation for depth 15, residue 18079. -/
theorem bounds_15_18079 : exactInterval 15 18079 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_18079 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 18079) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_18079 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_18079 : oddCount 18079 15 = 10 ∧ acceleratedOrbit 15 18079 = 32581 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_18079 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 18079) = 3 ^ 10 * m + 32581 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_18079.1, data_15_18079.2]

/-- Complete interval computation for depth 15, residue 18080. -/
theorem bounds_15_18080 : exactInterval 15 18080 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_18080 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 18080) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_18080 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_18080 : oddCount 18080 15 = 2 ∧ acceleratedOrbit 15 18080 = 5 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_18080 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 18080) = 3 ^ 2 * m + 5 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_18080.1, data_15_18080.2]

/-- Complete interval computation for depth 15, residue 18081. -/
theorem bounds_15_18081 : exactInterval 15 18081 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_18081 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 18081) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_18081 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_18081 : oddCount 18081 15 = 7 ∧ acceleratedOrbit 15 18081 = 1207 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_18081 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 18081) = 3 ^ 7 * m + 1207 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_18081.1, data_15_18081.2]

/-- Complete interval computation for depth 15, residue 18082. -/
theorem bounds_15_18082 : exactInterval 15 18082 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_18082 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 18082) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_18082 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_18082 : oddCount 18082 15 = 9 ∧ acceleratedOrbit 15 18082 = 10867 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_18082 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 18082) = 3 ^ 9 * m + 10867 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_18082.1, data_15_18082.2]

/-- Complete interval computation for depth 15, residue 18083. -/
theorem bounds_15_18083 : exactInterval 15 18083 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_18083 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 18083) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_18083 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_18083 : oddCount 18083 15 = 9 ∧ acceleratedOrbit 15 18083 = 10867 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_18083 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 18083) = 3 ^ 9 * m + 10867 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_18083.1, data_15_18083.2]

/-- Complete interval computation for depth 15, residue 18084. -/
theorem bounds_15_18084 : exactInterval 15 18084 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_18084 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 18084) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_18084 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_18084 : oddCount 18084 15 = 9 ∧ acceleratedOrbit 15 18084 = 10867 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_18084 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 18084) = 3 ^ 9 * m + 10867 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_18084.1, data_15_18084.2]

/-- Complete interval computation for depth 15, residue 18085. -/
theorem bounds_15_18085 : exactInterval 15 18085 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_18085 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 18085) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_18085 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_18085 : oddCount 18085 15 = 9 ∧ acceleratedOrbit 15 18085 = 10867 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_18085 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 18085) = 3 ^ 9 * m + 10867 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_18085.1, data_15_18085.2]

/-- Complete interval computation for depth 15, residue 18086. -/
theorem bounds_15_18086 : exactInterval 15 18086 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_18086 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 18086) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_18086 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_18086 : oddCount 18086 15 = 9 ∧ acceleratedOrbit 15 18086 = 10867 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_18086 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 18086) = 3 ^ 9 * m + 10867 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_18086.1, data_15_18086.2]

end Collatz.Research.PassageAtlas.Batch0552
