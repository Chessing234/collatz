import Collatz.Research.DescentIntervals.Classifier

namespace Collatz.Research.StoppingAtlas.Batch0458

open Collatz.Research.DescentIntervals

set_option maxRecDepth 20000
set_option maxHeartbeats 0

/-- Complete interval computation for depth 12, residue 3947. -/
theorem bounds_12_3947 : exactInterval 12 3947 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_12_3947 (m : Nat) :
    stoppingTime (2 ^ 12 * m + 3947) 12 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_12_3947 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_12_3947 : oddCount 3947 12 = 6 ∧ acceleratedOrbit 12 3947 = 703 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_12_3947 (m : Nat) :
    acceleratedOrbit 12 (2 ^ 12 * m + 3947) = 3 ^ 6 * m + 703 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_12_3947.1, data_12_3947.2]

/-- Complete interval computation for depth 12, residue 3948. -/
theorem bounds_12_3948 : exactInterval 12 3948 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_12_3948 (m : Nat) :
    stoppingTime (2 ^ 12 * m + 3948) 12 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_12_3948 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_12_3948 : oddCount 3948 12 = 6 ∧ acceleratedOrbit 12 3948 = 704 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_12_3948 (m : Nat) :
    acceleratedOrbit 12 (2 ^ 12 * m + 3948) = 3 ^ 6 * m + 704 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_12_3948.1, data_12_3948.2]

/-- Complete interval computation for depth 12, residue 3949. -/
theorem bounds_12_3949 : exactInterval 12 3949 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_12_3949 (m : Nat) :
    stoppingTime (2 ^ 12 * m + 3949) 12 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_12_3949 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_12_3949 : oddCount 3949 12 = 6 ∧ acceleratedOrbit 12 3949 = 704 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_12_3949 (m : Nat) :
    acceleratedOrbit 12 (2 ^ 12 * m + 3949) = 3 ^ 6 * m + 704 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_12_3949.1, data_12_3949.2]

/-- Complete interval computation for depth 12, residue 3950. -/
theorem bounds_12_3950 : exactInterval 12 3950 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_12_3950 (m : Nat) :
    stoppingTime (2 ^ 12 * m + 3950) 12 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_12_3950 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_12_3950 : oddCount 3950 12 = 6 ∧ acceleratedOrbit 12 3950 = 704 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_12_3950 (m : Nat) :
    acceleratedOrbit 12 (2 ^ 12 * m + 3950) = 3 ^ 6 * m + 704 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_12_3950.1, data_12_3950.2]

/-- Complete interval computation for depth 12, residue 3951. -/
theorem bounds_12_3951 : exactInterval 12 3951 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_12_3951 (m : Nat) :
    stoppingTime (2 ^ 12 * m + 3951) 12 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_12_3951 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_12_3951 : oddCount 3951 12 = 8 ∧ acceleratedOrbit 12 3951 = 6331 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_12_3951 (m : Nat) :
    acceleratedOrbit 12 (2 ^ 12 * m + 3951) = 3 ^ 8 * m + 6331 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_12_3951.1, data_12_3951.2]

/-- Complete interval computation for depth 12, residue 3952. -/
theorem bounds_12_3952 : exactInterval 12 3952 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_12_3952 (m : Nat) :
    stoppingTime (2 ^ 12 * m + 3952) 12 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_12_3952 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_12_3952 : oddCount 3952 12 = 5 ∧ acceleratedOrbit 12 3952 = 236 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_12_3952 (m : Nat) :
    acceleratedOrbit 12 (2 ^ 12 * m + 3952) = 3 ^ 5 * m + 236 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_12_3952.1, data_12_3952.2]

/-- Complete interval computation for depth 12, residue 3953. -/
theorem bounds_12_3953 : exactInterval 12 3953 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_12_3953 (m : Nat) :
    stoppingTime (2 ^ 12 * m + 3953) 12 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_12_3953 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_12_3953 : oddCount 3953 12 = 5 ∧ acceleratedOrbit 12 3953 = 236 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_12_3953 (m : Nat) :
    acceleratedOrbit 12 (2 ^ 12 * m + 3953) = 3 ^ 5 * m + 236 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_12_3953.1, data_12_3953.2]

/-- Complete interval computation for depth 12, residue 3954. -/
theorem bounds_12_3954 : exactInterval 12 3954 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_12_3954 (m : Nat) :
    stoppingTime (2 ^ 12 * m + 3954) 12 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_12_3954 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_12_3954 : oddCount 3954 12 = 5 ∧ acceleratedOrbit 12 3954 = 235 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_12_3954 (m : Nat) :
    acceleratedOrbit 12 (2 ^ 12 * m + 3954) = 3 ^ 5 * m + 235 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_12_3954.1, data_12_3954.2]

/-- Complete interval computation for depth 12, residue 3955. -/
theorem bounds_12_3955 : exactInterval 12 3955 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_12_3955 (m : Nat) :
    stoppingTime (2 ^ 12 * m + 3955) 12 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_12_3955 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_12_3955 : oddCount 3955 12 = 5 ∧ acceleratedOrbit 12 3955 = 235 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_12_3955 (m : Nat) :
    acceleratedOrbit 12 (2 ^ 12 * m + 3955) = 3 ^ 5 * m + 235 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_12_3955.1, data_12_3955.2]

/-- Complete interval computation for depth 12, residue 3956. -/
theorem bounds_12_3956 : exactInterval 12 3956 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_12_3956 (m : Nat) :
    stoppingTime (2 ^ 12 * m + 3956) 12 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_12_3956 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_12_3956 : oddCount 3956 12 = 5 ∧ acceleratedOrbit 12 3956 = 236 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_12_3956 (m : Nat) :
    acceleratedOrbit 12 (2 ^ 12 * m + 3956) = 3 ^ 5 * m + 236 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_12_3956.1, data_12_3956.2]

/-- Complete interval computation for depth 12, residue 3957. -/
theorem bounds_12_3957 : exactInterval 12 3957 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_12_3957 (m : Nat) :
    stoppingTime (2 ^ 12 * m + 3957) 12 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_12_3957 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_12_3957 : oddCount 3957 12 = 5 ∧ acceleratedOrbit 12 3957 = 236 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_12_3957 (m : Nat) :
    acceleratedOrbit 12 (2 ^ 12 * m + 3957) = 3 ^ 5 * m + 236 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_12_3957.1, data_12_3957.2]

/-- Complete interval computation for depth 12, residue 3958. -/
theorem bounds_12_3958 : exactInterval 12 3958 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_12_3958 (m : Nat) :
    stoppingTime (2 ^ 12 * m + 3958) 12 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_12_3958 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_12_3958 : oddCount 3958 12 = 5 ∧ acceleratedOrbit 12 3958 = 235 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_12_3958 (m : Nat) :
    acceleratedOrbit 12 (2 ^ 12 * m + 3958) = 3 ^ 5 * m + 235 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_12_3958.1, data_12_3958.2]

/-- Complete interval computation for depth 12, residue 3959. -/
theorem bounds_12_3959 : exactInterval 12 3959 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_12_3959 (m : Nat) :
    stoppingTime (2 ^ 12 * m + 3959) 12 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_12_3959 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_12_3959 : oddCount 3959 12 = 5 ∧ acceleratedOrbit 12 3959 = 235 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_12_3959 (m : Nat) :
    acceleratedOrbit 12 (2 ^ 12 * m + 3959) = 3 ^ 5 * m + 235 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_12_3959.1, data_12_3959.2]

/-- Complete interval computation for depth 12, residue 3960. -/
theorem bounds_12_3960 : exactInterval 12 3960 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_12_3960 (m : Nat) :
    stoppingTime (2 ^ 12 * m + 3960) 12 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_12_3960 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_12_3960 : oddCount 3960 12 = 7 ∧ acceleratedOrbit 12 3960 = 2119 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_12_3960 (m : Nat) :
    acceleratedOrbit 12 (2 ^ 12 * m + 3960) = 3 ^ 7 * m + 2119 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_12_3960.1, data_12_3960.2]

/-- Complete interval computation for depth 12, residue 3961. -/
theorem bounds_12_3961 : exactInterval 12 3961 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_12_3961 (m : Nat) :
    stoppingTime (2 ^ 12 * m + 3961) 12 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_12_3961 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_12_3961 : oddCount 3961 12 = 7 ∧ acceleratedOrbit 12 3961 = 2116 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_12_3961 (m : Nat) :
    acceleratedOrbit 12 (2 ^ 12 * m + 3961) = 3 ^ 7 * m + 2116 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_12_3961.1, data_12_3961.2]

end Collatz.Research.StoppingAtlas.Batch0458
