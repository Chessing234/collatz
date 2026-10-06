import Collatz.Research.DescentIntervals.Classifier

namespace Collatz.Research.StoppingAtlas.Batch0064

open Collatz.Research.DescentIntervals

set_option maxRecDepth 20000
set_option maxHeartbeats 0

/-- Complete interval computation for depth 10, residue 967. -/
theorem bounds_10_967 : exactInterval 10 967 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_10_967 (m : Nat) :
    stoppingTime (2 ^ 10 * m + 967) 10 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_10_967 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_10_967 : oddCount 967 10 = 7 ∧ acceleratedOrbit 10 967 = 2069 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_10_967 (m : Nat) :
    acceleratedOrbit 10 (2 ^ 10 * m + 967) = 3 ^ 7 * m + 2069 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_10_967.1, data_10_967.2]

/-- Complete interval computation for depth 10, residue 968. -/
theorem bounds_10_968 : exactInterval 10 968 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_10_968 (m : Nat) :
    stoppingTime (2 ^ 10 * m + 968) 10 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_10_968 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_10_968 : oddCount 968 10 = 5 ∧ acceleratedOrbit 10 968 = 233 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_10_968 (m : Nat) :
    acceleratedOrbit 10 (2 ^ 10 * m + 968) = 3 ^ 5 * m + 233 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_10_968.1, data_10_968.2]

/-- Complete interval computation for depth 10, residue 969. -/
theorem bounds_10_969 : exactInterval 10 969 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_10_969 (m : Nat) :
    stoppingTime (2 ^ 10 * m + 969) 10 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_10_969 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_10_969 : oddCount 969 10 = 6 ∧ acceleratedOrbit 10 969 = 692 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_10_969 (m : Nat) :
    acceleratedOrbit 10 (2 ^ 10 * m + 969) = 3 ^ 6 * m + 692 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_10_969.1, data_10_969.2]

/-- Complete interval computation for depth 10, residue 970. -/
theorem bounds_10_970 : exactInterval 10 970 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_10_970 (m : Nat) :
    stoppingTime (2 ^ 10 * m + 970) 10 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_10_970 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_10_970 : oddCount 970 10 = 5 ∧ acceleratedOrbit 10 970 = 233 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_10_970 (m : Nat) :
    acceleratedOrbit 10 (2 ^ 10 * m + 970) = 3 ^ 5 * m + 233 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_10_970.1, data_10_970.2]

/-- Complete interval computation for depth 10, residue 971. -/
theorem bounds_10_971 : exactInterval 10 971 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_10_971 (m : Nat) :
    stoppingTime (2 ^ 10 * m + 971) 10 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_10_971 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_10_971 : oddCount 971 10 = 4 ∧ acceleratedOrbit 10 971 = 77 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_10_971 (m : Nat) :
    acceleratedOrbit 10 (2 ^ 10 * m + 971) = 3 ^ 4 * m + 77 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_10_971.1, data_10_971.2]

/-- Complete interval computation for depth 10, residue 972. -/
theorem bounds_10_972 : exactInterval 10 972 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_10_972 (m : Nat) :
    stoppingTime (2 ^ 10 * m + 972) 10 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_10_972 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_10_972 : oddCount 972 10 = 5 ∧ acceleratedOrbit 10 972 = 233 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_10_972 (m : Nat) :
    acceleratedOrbit 10 (2 ^ 10 * m + 972) = 3 ^ 5 * m + 233 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_10_972.1, data_10_972.2]

/-- Complete interval computation for depth 10, residue 973. -/
theorem bounds_10_973 : exactInterval 10 973 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_10_973 (m : Nat) :
    stoppingTime (2 ^ 10 * m + 973) 10 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_10_973 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_10_973 : oddCount 973 10 = 5 ∧ acceleratedOrbit 10 973 = 233 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_10_973 (m : Nat) :
    acceleratedOrbit 10 (2 ^ 10 * m + 973) = 3 ^ 5 * m + 233 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_10_973.1, data_10_973.2]

/-- Complete interval computation for depth 10, residue 974. -/
theorem bounds_10_974 : exactInterval 10 974 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_10_974 (m : Nat) :
    stoppingTime (2 ^ 10 * m + 974) 10 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_10_974 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_10_974 : oddCount 974 10 = 6 ∧ acceleratedOrbit 10 974 = 695 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_10_974 (m : Nat) :
    acceleratedOrbit 10 (2 ^ 10 * m + 974) = 3 ^ 6 * m + 695 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_10_974.1, data_10_974.2]

/-- Complete interval computation for depth 10, residue 975. -/
theorem bounds_10_975 : exactInterval 10 975 = ⟨0, none⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_10_975 (m : Nat) :
    stoppingTime (2 ^ 10 * m + 975) 10 ↔ 0 ≤ m := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_10_975 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_10_975 : oddCount 975 10 = 6 ∧ acceleratedOrbit 10 975 = 695 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_10_975 (m : Nat) :
    acceleratedOrbit 10 (2 ^ 10 * m + 975) = 3 ^ 6 * m + 695 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_10_975.1, data_10_975.2]

/-- Complete interval computation for depth 10, residue 976. -/
theorem bounds_10_976 : exactInterval 10 976 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_10_976 (m : Nat) :
    stoppingTime (2 ^ 10 * m + 976) 10 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_10_976 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_10_976 : oddCount 976 10 = 4 ∧ acceleratedOrbit 10 976 = 80 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_10_976 (m : Nat) :
    acceleratedOrbit 10 (2 ^ 10 * m + 976) = 3 ^ 4 * m + 80 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_10_976.1, data_10_976.2]

/-- Complete interval computation for depth 10, residue 977. -/
theorem bounds_10_977 : exactInterval 10 977 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_10_977 (m : Nat) :
    stoppingTime (2 ^ 10 * m + 977) 10 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_10_977 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_10_977 : oddCount 977 10 = 5 ∧ acceleratedOrbit 10 977 = 233 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_10_977 (m : Nat) :
    acceleratedOrbit 10 (2 ^ 10 * m + 977) = 3 ^ 5 * m + 233 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_10_977.1, data_10_977.2]

/-- Complete interval computation for depth 10, residue 978. -/
theorem bounds_10_978 : exactInterval 10 978 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_10_978 (m : Nat) :
    stoppingTime (2 ^ 10 * m + 978) 10 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_10_978 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_10_978 : oddCount 978 10 = 7 ∧ acceleratedOrbit 10 978 = 2096 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_10_978 (m : Nat) :
    acceleratedOrbit 10 (2 ^ 10 * m + 978) = 3 ^ 7 * m + 2096 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_10_978.1, data_10_978.2]

/-- Complete interval computation for depth 10, residue 979. -/
theorem bounds_10_979 : exactInterval 10 979 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_10_979 (m : Nat) :
    stoppingTime (2 ^ 10 * m + 979) 10 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_10_979 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_10_979 : oddCount 979 10 = 7 ∧ acceleratedOrbit 10 979 = 2096 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_10_979 (m : Nat) :
    acceleratedOrbit 10 (2 ^ 10 * m + 979) = 3 ^ 7 * m + 2096 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_10_979.1, data_10_979.2]

/-- Complete interval computation for depth 10, residue 980. -/
theorem bounds_10_980 : exactInterval 10 980 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_10_980 (m : Nat) :
    stoppingTime (2 ^ 10 * m + 980) 10 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_10_980 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_10_980 : oddCount 980 10 = 4 ∧ acceleratedOrbit 10 980 = 80 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_10_980 (m : Nat) :
    acceleratedOrbit 10 (2 ^ 10 * m + 980) = 3 ^ 4 * m + 80 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_10_980.1, data_10_980.2]

/-- Complete interval computation for depth 10, residue 981. -/
theorem bounds_10_981 : exactInterval 10 981 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_10_981 (m : Nat) :
    stoppingTime (2 ^ 10 * m + 981) 10 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_10_981 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_10_981 : oddCount 981 10 = 4 ∧ acceleratedOrbit 10 981 = 80 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_10_981 (m : Nat) :
    acceleratedOrbit 10 (2 ^ 10 * m + 981) = 3 ^ 4 * m + 80 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_10_981.1, data_10_981.2]

/-- Complete interval computation for depth 10, residue 982. -/
theorem bounds_10_982 : exactInterval 10 982 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_10_982 (m : Nat) :
    stoppingTime (2 ^ 10 * m + 982) 10 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_10_982 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_10_982 : oddCount 982 10 = 7 ∧ acceleratedOrbit 10 982 = 2105 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_10_982 (m : Nat) :
    acceleratedOrbit 10 (2 ^ 10 * m + 982) = 3 ^ 7 * m + 2105 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_10_982.1, data_10_982.2]

end Collatz.Research.StoppingAtlas.Batch0064
