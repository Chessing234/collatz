import Collatz.Research.DescentIntervals.Classifier

namespace Collatz.Research.StoppingAtlas.Batch0264

open Collatz.Research.DescentIntervals

set_option maxRecDepth 20000
set_option maxHeartbeats 0

/-- Complete interval computation for depth 12, residue 967. -/
theorem bounds_12_967 : exactInterval 12 967 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_12_967 (m : Nat) :
    stoppingTime (2 ^ 12 * m + 967) 12 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_12_967 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_12_967 : oddCount 967 12 = 8 ∧ acceleratedOrbit 12 967 = 1552 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_12_967 (m : Nat) :
    acceleratedOrbit 12 (2 ^ 12 * m + 967) = 3 ^ 8 * m + 1552 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_12_967.1, data_12_967.2]

/-- Complete interval computation for depth 12, residue 968. -/
theorem bounds_12_968 : exactInterval 12 968 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_12_968 (m : Nat) :
    stoppingTime (2 ^ 12 * m + 968) 12 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_12_968 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_12_968 : oddCount 968 12 = 6 ∧ acceleratedOrbit 12 968 = 175 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_12_968 (m : Nat) :
    acceleratedOrbit 12 (2 ^ 12 * m + 968) = 3 ^ 6 * m + 175 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_12_968.1, data_12_968.2]

/-- Complete interval computation for depth 12, residue 969. -/
theorem bounds_12_969 : exactInterval 12 969 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_12_969 (m : Nat) :
    stoppingTime (2 ^ 12 * m + 969) 12 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_12_969 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_12_969 : oddCount 969 12 = 6 ∧ acceleratedOrbit 12 969 = 173 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_12_969 (m : Nat) :
    acceleratedOrbit 12 (2 ^ 12 * m + 969) = 3 ^ 6 * m + 173 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_12_969.1, data_12_969.2]

/-- Complete interval computation for depth 12, residue 970. -/
theorem bounds_12_970 : exactInterval 12 970 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_12_970 (m : Nat) :
    stoppingTime (2 ^ 12 * m + 970) 12 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_12_970 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_12_970 : oddCount 970 12 = 6 ∧ acceleratedOrbit 12 970 = 175 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_12_970 (m : Nat) :
    acceleratedOrbit 12 (2 ^ 12 * m + 970) = 3 ^ 6 * m + 175 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_12_970.1, data_12_970.2]

/-- Complete interval computation for depth 12, residue 971. -/
theorem bounds_12_971 : exactInterval 12 971 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_12_971 (m : Nat) :
    stoppingTime (2 ^ 12 * m + 971) 12 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_12_971 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_12_971 : oddCount 971 12 = 5 ∧ acceleratedOrbit 12 971 = 58 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_12_971 (m : Nat) :
    acceleratedOrbit 12 (2 ^ 12 * m + 971) = 3 ^ 5 * m + 58 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_12_971.1, data_12_971.2]

/-- Complete interval computation for depth 12, residue 972. -/
theorem bounds_12_972 : exactInterval 12 972 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_12_972 (m : Nat) :
    stoppingTime (2 ^ 12 * m + 972) 12 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_12_972 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_12_972 : oddCount 972 12 = 6 ∧ acceleratedOrbit 12 972 = 175 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_12_972 (m : Nat) :
    acceleratedOrbit 12 (2 ^ 12 * m + 972) = 3 ^ 6 * m + 175 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_12_972.1, data_12_972.2]

/-- Complete interval computation for depth 12, residue 973. -/
theorem bounds_12_973 : exactInterval 12 973 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_12_973 (m : Nat) :
    stoppingTime (2 ^ 12 * m + 973) 12 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_12_973 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_12_973 : oddCount 973 12 = 6 ∧ acceleratedOrbit 12 973 = 175 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_12_973 (m : Nat) :
    acceleratedOrbit 12 (2 ^ 12 * m + 973) = 3 ^ 6 * m + 175 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_12_973.1, data_12_973.2]

/-- Complete interval computation for depth 12, residue 974. -/
theorem bounds_12_974 : exactInterval 12 974 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_12_974 (m : Nat) :
    stoppingTime (2 ^ 12 * m + 974) 12 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_12_974 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_12_974 : oddCount 974 12 = 8 ∧ acceleratedOrbit 12 974 = 1565 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_12_974 (m : Nat) :
    acceleratedOrbit 12 (2 ^ 12 * m + 974) = 3 ^ 8 * m + 1565 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_12_974.1, data_12_974.2]

/-- Complete interval computation for depth 12, residue 975. -/
theorem bounds_12_975 : exactInterval 12 975 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_12_975 (m : Nat) :
    stoppingTime (2 ^ 12 * m + 975) 12 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_12_975 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_12_975 : oddCount 975 12 = 8 ∧ acceleratedOrbit 12 975 = 1565 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_12_975 (m : Nat) :
    acceleratedOrbit 12 (2 ^ 12 * m + 975) = 3 ^ 8 * m + 1565 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_12_975.1, data_12_975.2]

/-- Complete interval computation for depth 12, residue 976. -/
theorem bounds_12_976 : exactInterval 12 976 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_12_976 (m : Nat) :
    stoppingTime (2 ^ 12 * m + 976) 12 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_12_976 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_12_976 : oddCount 976 12 = 4 ∧ acceleratedOrbit 12 976 = 20 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_12_976 (m : Nat) :
    acceleratedOrbit 12 (2 ^ 12 * m + 976) = 3 ^ 4 * m + 20 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_12_976.1, data_12_976.2]

/-- Complete interval computation for depth 12, residue 977. -/
theorem bounds_12_977 : exactInterval 12 977 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_12_977 (m : Nat) :
    stoppingTime (2 ^ 12 * m + 977) 12 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_12_977 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_12_977 : oddCount 977 12 = 6 ∧ acceleratedOrbit 12 977 = 175 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_12_977 (m : Nat) :
    acceleratedOrbit 12 (2 ^ 12 * m + 977) = 3 ^ 6 * m + 175 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_12_977.1, data_12_977.2]

/-- Complete interval computation for depth 12, residue 978. -/
theorem bounds_12_978 : exactInterval 12 978 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_12_978 (m : Nat) :
    stoppingTime (2 ^ 12 * m + 978) 12 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_12_978 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_12_978 : oddCount 978 12 = 7 ∧ acceleratedOrbit 12 978 = 524 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_12_978 (m : Nat) :
    acceleratedOrbit 12 (2 ^ 12 * m + 978) = 3 ^ 7 * m + 524 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_12_978.1, data_12_978.2]

/-- Complete interval computation for depth 12, residue 979. -/
theorem bounds_12_979 : exactInterval 12 979 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_12_979 (m : Nat) :
    stoppingTime (2 ^ 12 * m + 979) 12 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_12_979 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_12_979 : oddCount 979 12 = 7 ∧ acceleratedOrbit 12 979 = 524 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_12_979 (m : Nat) :
    acceleratedOrbit 12 (2 ^ 12 * m + 979) = 3 ^ 7 * m + 524 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_12_979.1, data_12_979.2]

/-- Complete interval computation for depth 12, residue 980. -/
theorem bounds_12_980 : exactInterval 12 980 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_12_980 (m : Nat) :
    stoppingTime (2 ^ 12 * m + 980) 12 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_12_980 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_12_980 : oddCount 980 12 = 4 ∧ acceleratedOrbit 12 980 = 20 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_12_980 (m : Nat) :
    acceleratedOrbit 12 (2 ^ 12 * m + 980) = 3 ^ 4 * m + 20 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_12_980.1, data_12_980.2]

/-- Complete interval computation for depth 12, residue 981. -/
theorem bounds_12_981 : exactInterval 12 981 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_12_981 (m : Nat) :
    stoppingTime (2 ^ 12 * m + 981) 12 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_12_981 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_12_981 : oddCount 981 12 = 4 ∧ acceleratedOrbit 12 981 = 20 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_12_981 (m : Nat) :
    acceleratedOrbit 12 (2 ^ 12 * m + 981) = 3 ^ 4 * m + 20 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_12_981.1, data_12_981.2]

/-- Complete interval computation for depth 12, residue 982. -/
theorem bounds_12_982 : exactInterval 12 982 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_12_982 (m : Nat) :
    stoppingTime (2 ^ 12 * m + 982) 12 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_12_982 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_12_982 : oddCount 982 12 = 8 ∧ acceleratedOrbit 12 982 = 1579 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_12_982 (m : Nat) :
    acceleratedOrbit 12 (2 ^ 12 * m + 982) = 3 ^ 8 * m + 1579 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_12_982.1, data_12_982.2]

end Collatz.Research.StoppingAtlas.Batch0264
