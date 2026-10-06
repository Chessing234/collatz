import Collatz.Research.DescentIntervals.Classifier

namespace Collatz.Research.PassageAtlas.Batch0030

open Collatz.Research.DescentIntervals

set_option maxRecDepth 20000
set_option maxHeartbeats 0

/-- Complete interval computation for depth 15, residue 950. -/
theorem bounds_15_950 : exactInterval 15 950 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_950 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 950) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_950 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_950 : oddCount 950 15 = 7 ∧ acceleratedOrbit 15 950 = 64 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_950 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 950) = 3 ^ 7 * m + 64 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_950.1, data_15_950.2]

/-- Complete interval computation for depth 15, residue 951. -/
theorem bounds_15_951 : exactInterval 15 951 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_951 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 951) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_951 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_951 : oddCount 951 15 = 7 ∧ acceleratedOrbit 15 951 = 64 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_951 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 951) = 3 ^ 7 * m + 64 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_951.1, data_15_951.2]

/-- Complete interval computation for depth 15, residue 952. -/
theorem bounds_15_952 : exactInterval 15 952 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_952 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 952) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_952 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_952 : oddCount 952 15 = 6 ∧ acceleratedOrbit 15 952 = 22 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_952 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 952) = 3 ^ 6 * m + 22 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_952.1, data_15_952.2]

/-- Complete interval computation for depth 15, residue 953. -/
theorem bounds_15_953 : exactInterval 15 953 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_953 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 953) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_953 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_953 : oddCount 953 15 = 7 ∧ acceleratedOrbit 15 953 = 64 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_953 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 953) = 3 ^ 7 * m + 64 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_953.1, data_15_953.2]

/-- Complete interval computation for depth 15, residue 954. -/
theorem bounds_15_954 : exactInterval 15 954 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_954 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 954) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_954 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_954 : oddCount 954 15 = 6 ∧ acceleratedOrbit 15 954 = 22 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_954 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 954) = 3 ^ 6 * m + 22 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_954.1, data_15_954.2]

/-- Complete interval computation for depth 15, residue 955. -/
theorem bounds_15_955 : exactInterval 15 955 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_955 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 955) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_955 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_955 : oddCount 955 15 = 7 ∧ acceleratedOrbit 15 955 = 64 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_955 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 955) = 3 ^ 7 * m + 64 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_955.1, data_15_955.2]

/-- Complete interval computation for depth 15, residue 956. -/
theorem bounds_15_956 : exactInterval 15 956 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_956 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 956) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_956 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_956 : oddCount 956 15 = 9 ∧ acceleratedOrbit 15 956 = 577 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_956 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 956) = 3 ^ 9 * m + 577 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_956.1, data_15_956.2]

/-- Complete interval computation for depth 15, residue 957. -/
theorem bounds_15_957 : exactInterval 15 957 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_957 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 957) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_957 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_957 : oddCount 957 15 = 9 ∧ acceleratedOrbit 15 957 = 577 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_957 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 957) = 3 ^ 9 * m + 577 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_957.1, data_15_957.2]

/-- Complete interval computation for depth 15, residue 958. -/
theorem bounds_15_958 : exactInterval 15 958 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_958 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 958) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_958 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_958 : oddCount 958 15 = 9 ∧ acceleratedOrbit 15 958 = 577 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_958 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 958) = 3 ^ 9 * m + 577 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_958.1, data_15_958.2]

/-- Complete interval computation for depth 15, residue 959. -/
theorem bounds_15_959 : exactInterval 15 959 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_959 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 959) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_959 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_959 : oddCount 959 15 = 12 ∧ acceleratedOrbit 15 959 = 15572 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_959 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 959) = 3 ^ 12 * m + 15572 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_959.1, data_15_959.2]

/-- Complete interval computation for depth 15, residue 960. -/
theorem bounds_15_960 : exactInterval 15 960 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_960 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 960) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_960 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_960 : oddCount 960 15 = 5 ∧ acceleratedOrbit 15 960 = 8 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_960 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 960) = 3 ^ 5 * m + 8 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_960.1, data_15_960.2]

/-- Complete interval computation for depth 15, residue 961. -/
theorem bounds_15_961 : exactInterval 15 961 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_961 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 961) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_961 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_961 : oddCount 961 15 = 7 ∧ acceleratedOrbit 15 961 = 65 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_961 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 961) = 3 ^ 7 * m + 65 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_961.1, data_15_961.2]

/-- Complete interval computation for depth 15, residue 962. -/
theorem bounds_15_962 : exactInterval 15 962 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_962 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 962) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_962 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_962 : oddCount 962 15 = 7 ∧ acceleratedOrbit 15 962 = 65 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_962 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 962) = 3 ^ 7 * m + 65 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_962.1, data_15_962.2]

/-- Complete interval computation for depth 15, residue 963. -/
theorem bounds_15_963 : exactInterval 15 963 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_963 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 963) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_963 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_963 : oddCount 963 15 = 7 ∧ acceleratedOrbit 15 963 = 65 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_963 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 963) = 3 ^ 7 * m + 65 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_963.1, data_15_963.2]

/-- Complete interval computation for depth 15, residue 964. -/
theorem bounds_15_964 : exactInterval 15 964 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_964 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 964) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_964 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_964 : oddCount 964 15 = 5 ∧ acceleratedOrbit 15 964 = 8 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_964 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 964) = 3 ^ 5 * m + 8 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_964.1, data_15_964.2]

/-- Complete interval computation for depth 15, residue 965. -/
theorem bounds_15_965 : exactInterval 15 965 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_965 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 965) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_965 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_965 : oddCount 965 15 = 5 ∧ acceleratedOrbit 15 965 = 8 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_965 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 965) = 3 ^ 5 * m + 8 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_965.1, data_15_965.2]

/-- Complete interval computation for depth 15, residue 966. -/
theorem bounds_15_966 : exactInterval 15 966 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_966 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 966) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_966 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_966 : oddCount 966 15 = 5 ∧ acceleratedOrbit 15 966 = 8 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_966 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 966) = 3 ^ 5 * m + 8 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_966.1, data_15_966.2]

/-- Complete interval computation for depth 15, residue 967. -/
theorem bounds_15_967 : exactInterval 15 967 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_967 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 967) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_967 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_967 : oddCount 967 15 = 8 ∧ acceleratedOrbit 15 967 = 194 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_967 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 967) = 3 ^ 8 * m + 194 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_967.1, data_15_967.2]

/-- Complete interval computation for depth 15, residue 968. -/
theorem bounds_15_968 : exactInterval 15 968 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_968 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 968) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_968 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_968 : oddCount 968 15 = 9 ∧ acceleratedOrbit 15 968 = 593 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_968 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 968) = 3 ^ 9 * m + 593 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_968.1, data_15_968.2]

/-- Complete interval computation for depth 15, residue 969. -/
theorem bounds_15_969 : exactInterval 15 969 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_969 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 969) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_969 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_969 : oddCount 969 15 = 7 ∧ acceleratedOrbit 15 969 = 65 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_969 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 969) = 3 ^ 7 * m + 65 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_969.1, data_15_969.2]

/-- Complete interval computation for depth 15, residue 970. -/
theorem bounds_15_970 : exactInterval 15 970 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_970 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 970) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_970 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_970 : oddCount 970 15 = 9 ∧ acceleratedOrbit 15 970 = 593 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_970 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 970) = 3 ^ 9 * m + 593 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_970.1, data_15_970.2]

/-- Complete interval computation for depth 15, residue 971. -/
theorem bounds_15_971 : exactInterval 15 971 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_971 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 971) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_971 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_971 : oddCount 971 15 = 6 ∧ acceleratedOrbit 15 971 = 22 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_971 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 971) = 3 ^ 6 * m + 22 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_971.1, data_15_971.2]

/-- Complete interval computation for depth 15, residue 972. -/
theorem bounds_15_972 : exactInterval 15 972 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_972 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 972) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_972 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_972 : oddCount 972 15 = 9 ∧ acceleratedOrbit 15 972 = 593 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_972 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 972) = 3 ^ 9 * m + 593 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_972.1, data_15_972.2]

/-- Complete interval computation for depth 15, residue 973. -/
theorem bounds_15_973 : exactInterval 15 973 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_973 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 973) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_973 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_973 : oddCount 973 15 = 9 ∧ acceleratedOrbit 15 973 = 593 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_973 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 973) = 3 ^ 9 * m + 593 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_973.1, data_15_973.2]

/-- Complete interval computation for depth 15, residue 974. -/
theorem bounds_15_974 : exactInterval 15 974 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_974 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 974) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_974 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_974 : oddCount 974 15 = 9 ∧ acceleratedOrbit 15 974 = 587 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_974 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 974) = 3 ^ 9 * m + 587 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_974.1, data_15_974.2]

/-- Complete interval computation for depth 15, residue 975. -/
theorem bounds_15_975 : exactInterval 15 975 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_975 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 975) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_975 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_975 : oddCount 975 15 = 9 ∧ acceleratedOrbit 15 975 = 587 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_975 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 975) = 3 ^ 9 * m + 587 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_975.1, data_15_975.2]

/-- Complete interval computation for depth 15, residue 976. -/
theorem bounds_15_976 : exactInterval 15 976 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_976 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 976) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_976 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_976 : oddCount 976 15 = 5 ∧ acceleratedOrbit 15 976 = 8 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_976 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 976) = 3 ^ 5 * m + 8 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_976.1, data_15_976.2]

/-- Complete interval computation for depth 15, residue 977. -/
theorem bounds_15_977 : exactInterval 15 977 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_977 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 977) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_977 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_977 : oddCount 977 15 = 9 ∧ acceleratedOrbit 15 977 = 593 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_977 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 977) = 3 ^ 9 * m + 593 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_977.1, data_15_977.2]

/-- Complete interval computation for depth 15, residue 978. -/
theorem bounds_15_978 : exactInterval 15 978 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_978 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 978) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_978 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_978 : oddCount 978 15 = 8 ∧ acceleratedOrbit 15 978 = 197 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_978 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 978) = 3 ^ 8 * m + 197 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_978.1, data_15_978.2]

/-- Complete interval computation for depth 15, residue 979. -/
theorem bounds_15_979 : exactInterval 15 979 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_979 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 979) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_979 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_979 : oddCount 979 15 = 8 ∧ acceleratedOrbit 15 979 = 197 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_979 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 979) = 3 ^ 8 * m + 197 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_979.1, data_15_979.2]

/-- Complete interval computation for depth 15, residue 980. -/
theorem bounds_15_980 : exactInterval 15 980 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_980 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 980) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_980 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_980 : oddCount 980 15 = 5 ∧ acceleratedOrbit 15 980 = 8 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_980 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 980) = 3 ^ 5 * m + 8 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_980.1, data_15_980.2]

/-- Complete interval computation for depth 15, residue 981. -/
theorem bounds_15_981 : exactInterval 15 981 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_981 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 981) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_981 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_981 : oddCount 981 15 = 5 ∧ acceleratedOrbit 15 981 = 8 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_981 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 981) = 3 ^ 5 * m + 8 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_981.1, data_15_981.2]

/-- Complete interval computation for depth 15, residue 982. -/
theorem bounds_15_982 : exactInterval 15 982 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_982 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 982) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_982 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_982 : oddCount 982 15 = 10 ∧ acceleratedOrbit 15 982 = 1777 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_982 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 982) = 3 ^ 10 * m + 1777 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_982.1, data_15_982.2]

end Collatz.Research.PassageAtlas.Batch0030
