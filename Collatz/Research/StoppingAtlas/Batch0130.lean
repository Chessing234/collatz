import Collatz.Research.DescentIntervals.Classifier

namespace Collatz.Research.StoppingAtlas.Batch0130

open Collatz.Research.DescentIntervals

set_option maxRecDepth 20000
set_option maxHeartbeats 0

/-- Complete interval computation for depth 11, residue 957. -/
theorem bounds_11_957 : exactInterval 11 957 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_11_957 (m : Nat) :
    stoppingTime (2 ^ 11 * m + 957) 11 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_11_957 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_11_957 : oddCount 957 11 = 8 ∧ acceleratedOrbit 11 957 = 3077 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_11_957 (m : Nat) :
    acceleratedOrbit 11 (2 ^ 11 * m + 957) = 3 ^ 8 * m + 3077 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_11_957.1, data_11_957.2]

/-- Complete interval computation for depth 11, residue 958. -/
theorem bounds_11_958 : exactInterval 11 958 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_11_958 (m : Nat) :
    stoppingTime (2 ^ 11 * m + 958) 11 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_11_958 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_11_958 : oddCount 958 11 = 8 ∧ acceleratedOrbit 11 958 = 3077 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_11_958 (m : Nat) :
    acceleratedOrbit 11 (2 ^ 11 * m + 958) = 3 ^ 8 * m + 3077 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_11_958.1, data_11_958.2]

/-- Complete interval computation for depth 11, residue 959. -/
theorem bounds_11_959 : exactInterval 11 959 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_11_959 (m : Nat) :
    stoppingTime (2 ^ 11 * m + 959) 11 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_11_959 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_11_959 : oddCount 959 11 = 9 ∧ acceleratedOrbit 11 959 = 9227 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_11_959 (m : Nat) :
    acceleratedOrbit 11 (2 ^ 11 * m + 959) = 3 ^ 9 * m + 9227 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_11_959.1, data_11_959.2]

/-- Complete interval computation for depth 11, residue 960. -/
theorem bounds_11_960 : exactInterval 11 960 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_11_960 (m : Nat) :
    stoppingTime (2 ^ 11 * m + 960) 11 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_11_960 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_11_960 : oddCount 960 11 = 4 ∧ acceleratedOrbit 11 960 = 40 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_11_960 (m : Nat) :
    acceleratedOrbit 11 (2 ^ 11 * m + 960) = 3 ^ 4 * m + 40 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_11_960.1, data_11_960.2]

/-- Complete interval computation for depth 11, residue 961. -/
theorem bounds_11_961 : exactInterval 11 961 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_11_961 (m : Nat) :
    stoppingTime (2 ^ 11 * m + 961) 11 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_11_961 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_11_961 : oddCount 961 11 = 6 ∧ acceleratedOrbit 11 961 = 344 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_11_961 (m : Nat) :
    acceleratedOrbit 11 (2 ^ 11 * m + 961) = 3 ^ 6 * m + 344 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_11_961.1, data_11_961.2]

/-- Complete interval computation for depth 11, residue 962. -/
theorem bounds_11_962 : exactInterval 11 962 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_11_962 (m : Nat) :
    stoppingTime (2 ^ 11 * m + 962) 11 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_11_962 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_11_962 : oddCount 962 11 = 6 ∧ acceleratedOrbit 11 962 = 344 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_11_962 (m : Nat) :
    acceleratedOrbit 11 (2 ^ 11 * m + 962) = 3 ^ 6 * m + 344 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_11_962.1, data_11_962.2]

/-- Complete interval computation for depth 11, residue 963. -/
theorem bounds_11_963 : exactInterval 11 963 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_11_963 (m : Nat) :
    stoppingTime (2 ^ 11 * m + 963) 11 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_11_963 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_11_963 : oddCount 963 11 = 6 ∧ acceleratedOrbit 11 963 = 344 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_11_963 (m : Nat) :
    acceleratedOrbit 11 (2 ^ 11 * m + 963) = 3 ^ 6 * m + 344 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_11_963.1, data_11_963.2]

/-- Complete interval computation for depth 11, residue 964. -/
theorem bounds_11_964 : exactInterval 11 964 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_11_964 (m : Nat) :
    stoppingTime (2 ^ 11 * m + 964) 11 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_11_964 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_11_964 : oddCount 964 11 = 3 ∧ acceleratedOrbit 11 964 = 13 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_11_964 (m : Nat) :
    acceleratedOrbit 11 (2 ^ 11 * m + 964) = 3 ^ 3 * m + 13 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_11_964.1, data_11_964.2]

/-- Complete interval computation for depth 11, residue 965. -/
theorem bounds_11_965 : exactInterval 11 965 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_11_965 (m : Nat) :
    stoppingTime (2 ^ 11 * m + 965) 11 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_11_965 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_11_965 : oddCount 965 11 = 3 ∧ acceleratedOrbit 11 965 = 13 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_11_965 (m : Nat) :
    acceleratedOrbit 11 (2 ^ 11 * m + 965) = 3 ^ 3 * m + 13 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_11_965.1, data_11_965.2]

/-- Complete interval computation for depth 11, residue 966. -/
theorem bounds_11_966 : exactInterval 11 966 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_11_966 (m : Nat) :
    stoppingTime (2 ^ 11 * m + 966) 11 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_11_966 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_11_966 : oddCount 966 11 = 3 ∧ acceleratedOrbit 11 966 = 13 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_11_966 (m : Nat) :
    acceleratedOrbit 11 (2 ^ 11 * m + 966) = 3 ^ 3 * m + 13 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_11_966.1, data_11_966.2]

/-- Complete interval computation for depth 11, residue 967. -/
theorem bounds_11_967 : exactInterval 11 967 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_11_967 (m : Nat) :
    stoppingTime (2 ^ 11 * m + 967) 11 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_11_967 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_11_967 : oddCount 967 11 = 8 ∧ acceleratedOrbit 11 967 = 3104 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_11_967 (m : Nat) :
    acceleratedOrbit 11 (2 ^ 11 * m + 967) = 3 ^ 8 * m + 3104 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_11_967.1, data_11_967.2]

/-- Complete interval computation for depth 11, residue 968. -/
theorem bounds_11_968 : exactInterval 11 968 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_11_968 (m : Nat) :
    stoppingTime (2 ^ 11 * m + 968) 11 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_11_968 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_11_968 : oddCount 968 11 = 6 ∧ acceleratedOrbit 11 968 = 350 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_11_968 (m : Nat) :
    acceleratedOrbit 11 (2 ^ 11 * m + 968) = 3 ^ 6 * m + 350 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_11_968.1, data_11_968.2]

/-- Complete interval computation for depth 11, residue 969. -/
theorem bounds_11_969 : exactInterval 11 969 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_11_969 (m : Nat) :
    stoppingTime (2 ^ 11 * m + 969) 11 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_11_969 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_11_969 : oddCount 969 11 = 6 ∧ acceleratedOrbit 11 969 = 346 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_11_969 (m : Nat) :
    acceleratedOrbit 11 (2 ^ 11 * m + 969) = 3 ^ 6 * m + 346 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_11_969.1, data_11_969.2]

/-- Complete interval computation for depth 11, residue 970. -/
theorem bounds_11_970 : exactInterval 11 970 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_11_970 (m : Nat) :
    stoppingTime (2 ^ 11 * m + 970) 11 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_11_970 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_11_970 : oddCount 970 11 = 6 ∧ acceleratedOrbit 11 970 = 350 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_11_970 (m : Nat) :
    acceleratedOrbit 11 (2 ^ 11 * m + 970) = 3 ^ 6 * m + 350 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_11_970.1, data_11_970.2]

/-- Complete interval computation for depth 11, residue 971. -/
theorem bounds_11_971 : exactInterval 11 971 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_11_971 (m : Nat) :
    stoppingTime (2 ^ 11 * m + 971) 11 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_11_971 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_11_971 : oddCount 971 11 = 5 ∧ acceleratedOrbit 11 971 = 116 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_11_971 (m : Nat) :
    acceleratedOrbit 11 (2 ^ 11 * m + 971) = 3 ^ 5 * m + 116 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_11_971.1, data_11_971.2]

end Collatz.Research.StoppingAtlas.Batch0130
