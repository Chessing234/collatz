import Collatz.Research.DescentIntervals.Classifier

namespace Collatz.Research.PassageAtlas.Batch0855

open Collatz.Research.DescentIntervals

set_option maxRecDepth 20000
set_option maxHeartbeats 0

/-- Complete interval computation for depth 15, residue 27983. -/
theorem bounds_15_27983 : exactInterval 15 27983 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_27983 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 27983) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_27983 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_27983 : oddCount 27983 15 = 9 ∧ acceleratedOrbit 15 27983 = 16811 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_27983 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 27983) = 3 ^ 9 * m + 16811 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_27983.1, data_15_27983.2]

/-- Complete interval computation for depth 15, residue 27984. -/
theorem bounds_15_27984 : exactInterval 15 27984 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_27984 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 27984) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_27984 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_27984 : oddCount 27984 15 = 4 ∧ acceleratedOrbit 15 27984 = 71 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_27984 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 27984) = 3 ^ 4 * m + 71 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_27984.1, data_15_27984.2]

/-- Complete interval computation for depth 15, residue 27985. -/
theorem bounds_15_27985 : exactInterval 15 27985 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_27985 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 27985) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_27985 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_27985 : oddCount 27985 15 = 10 ∧ acceleratedOrbit 15 27985 = 50438 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_27985 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 27985) = 3 ^ 10 * m + 50438 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_27985.1, data_15_27985.2]

/-- Complete interval computation for depth 15, residue 27986. -/
theorem bounds_15_27986 : exactInterval 15 27986 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_27986 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 27986) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_27986 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_27986 : oddCount 27986 15 = 10 ∧ acceleratedOrbit 15 27986 = 50438 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_27986 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 27986) = 3 ^ 10 * m + 50438 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_27986.1, data_15_27986.2]

/-- Complete interval computation for depth 15, residue 27987. -/
theorem bounds_15_27987 : exactInterval 15 27987 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_27987 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 27987) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_27987 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_27987 : oddCount 27987 15 = 10 ∧ acceleratedOrbit 15 27987 = 50438 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_27987 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 27987) = 3 ^ 10 * m + 50438 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_27987.1, data_15_27987.2]

/-- Complete interval computation for depth 15, residue 27988. -/
theorem bounds_15_27988 : exactInterval 15 27988 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_27988 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 27988) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_27988 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_27988 : oddCount 27988 15 = 4 ∧ acceleratedOrbit 15 27988 = 71 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_27988 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 27988) = 3 ^ 4 * m + 71 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_27988.1, data_15_27988.2]

/-- Complete interval computation for depth 15, residue 27989. -/
theorem bounds_15_27989 : exactInterval 15 27989 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_27989 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 27989) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_27989 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_27989 : oddCount 27989 15 = 4 ∧ acceleratedOrbit 15 27989 = 71 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_27989 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 27989) = 3 ^ 4 * m + 71 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_27989.1, data_15_27989.2]

/-- Complete interval computation for depth 15, residue 27990. -/
theorem bounds_15_27990 : exactInterval 15 27990 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_27990 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 27990) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_27990 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_27990 : oddCount 27990 15 = 8 ∧ acceleratedOrbit 15 27990 = 5606 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_27990 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 27990) = 3 ^ 8 * m + 5606 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_27990.1, data_15_27990.2]

/-- Complete interval computation for depth 15, residue 27991. -/
theorem bounds_15_27991 : exactInterval 15 27991 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_27991 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 27991) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_27991 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_27991 : oddCount 27991 15 = 8 ∧ acceleratedOrbit 15 27991 = 5606 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_27991 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 27991) = 3 ^ 8 * m + 5606 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_27991.1, data_15_27991.2]

/-- Complete interval computation for depth 15, residue 27992. -/
theorem bounds_15_27992 : exactInterval 15 27992 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_27992 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 27992) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_27992 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_27992 : oddCount 27992 15 = 8 ∧ acceleratedOrbit 15 27992 = 5609 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_27992 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 27992) = 3 ^ 8 * m + 5609 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_27992.1, data_15_27992.2]

/-- Complete interval computation for depth 15, residue 27993. -/
theorem bounds_15_27993 : exactInterval 15 27993 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_27993 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 27993) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_27993 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_27993 : oddCount 27993 15 = 6 ∧ acceleratedOrbit 15 27993 = 623 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_27993 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 27993) = 3 ^ 6 * m + 623 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_27993.1, data_15_27993.2]

/-- Complete interval computation for depth 15, residue 27994. -/
theorem bounds_15_27994 : exactInterval 15 27994 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_27994 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 27994) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_27994 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_27994 : oddCount 27994 15 = 8 ∧ acceleratedOrbit 15 27994 = 5609 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_27994 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 27994) = 3 ^ 8 * m + 5609 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_27994.1, data_15_27994.2]

/-- Complete interval computation for depth 15, residue 27995. -/
theorem bounds_15_27995 : exactInterval 15 27995 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_27995 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 27995) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_27995 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_27995 : oddCount 27995 15 = 10 ∧ acceleratedOrbit 15 27995 = 50453 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_27995 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 27995) = 3 ^ 10 * m + 50453 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_27995.1, data_15_27995.2]

/-- Complete interval computation for depth 15, residue 27996. -/
theorem bounds_15_27996 : exactInterval 15 27996 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_27996 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 27996) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_27996 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_27996 : oddCount 27996 15 = 8 ∧ acceleratedOrbit 15 27996 = 5609 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_27996 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 27996) = 3 ^ 8 * m + 5609 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_27996.1, data_15_27996.2]

/-- Complete interval computation for depth 15, residue 27997. -/
theorem bounds_15_27997 : exactInterval 15 27997 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_27997 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 27997) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_27997 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_27997 : oddCount 27997 15 = 8 ∧ acceleratedOrbit 15 27997 = 5609 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_27997 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 27997) = 3 ^ 8 * m + 5609 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_27997.1, data_15_27997.2]

/-- Complete interval computation for depth 15, residue 27998. -/
theorem bounds_15_27998 : exactInterval 15 27998 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_27998 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 27998) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_27998 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_27998 : oddCount 27998 15 = 10 ∧ acceleratedOrbit 15 27998 = 50462 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_27998 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 27998) = 3 ^ 10 * m + 50462 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_27998.1, data_15_27998.2]

/-- Complete interval computation for depth 15, residue 27999. -/
theorem bounds_15_27999 : exactInterval 15 27999 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_27999 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 27999) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_27999 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_27999 : oddCount 27999 15 = 10 ∧ acceleratedOrbit 15 27999 = 50462 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_27999 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 27999) = 3 ^ 10 * m + 50462 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_27999.1, data_15_27999.2]

/-- Complete interval computation for depth 15, residue 28000. -/
theorem bounds_15_28000 : exactInterval 15 28000 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_28000 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 28000) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_28000 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_28000 : oddCount 28000 15 = 5 ∧ acceleratedOrbit 15 28000 = 208 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_28000 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 28000) = 3 ^ 5 * m + 208 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_28000.1, data_15_28000.2]

/-- Complete interval computation for depth 15, residue 28001. -/
theorem bounds_15_28001 : exactInterval 15 28001 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_28001 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 28001) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_28001 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_28001 : oddCount 28001 15 = 6 ∧ acceleratedOrbit 15 28001 = 623 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_28001 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 28001) = 3 ^ 6 * m + 623 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_28001.1, data_15_28001.2]

/-- Complete interval computation for depth 15, residue 28002. -/
theorem bounds_15_28002 : exactInterval 15 28002 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_28002 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 28002) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_28002 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_28002 : oddCount 28002 15 = 5 ∧ acceleratedOrbit 15 28002 = 208 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_28002 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 28002) = 3 ^ 5 * m + 208 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_28002.1, data_15_28002.2]

/-- Complete interval computation for depth 15, residue 28003. -/
theorem bounds_15_28003 : exactInterval 15 28003 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_28003 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 28003) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_28003 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_28003 : oddCount 28003 15 = 5 ∧ acceleratedOrbit 15 28003 = 208 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_28003 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 28003) = 3 ^ 5 * m + 208 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_28003.1, data_15_28003.2]

/-- Complete interval computation for depth 15, residue 28004. -/
theorem bounds_15_28004 : exactInterval 15 28004 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_28004 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 28004) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_28004 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_28004 : oddCount 28004 15 = 5 ∧ acceleratedOrbit 15 28004 = 208 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_28004 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 28004) = 3 ^ 5 * m + 208 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_28004.1, data_15_28004.2]

/-- Complete interval computation for depth 15, residue 28005. -/
theorem bounds_15_28005 : exactInterval 15 28005 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_28005 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 28005) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_28005 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_28005 : oddCount 28005 15 = 5 ∧ acceleratedOrbit 15 28005 = 208 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_28005 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 28005) = 3 ^ 5 * m + 208 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_28005.1, data_15_28005.2]

/-- Complete interval computation for depth 15, residue 28006. -/
theorem bounds_15_28006 : exactInterval 15 28006 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_28006 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 28006) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_28006 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_28006 : oddCount 28006 15 = 5 ∧ acceleratedOrbit 15 28006 = 208 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_28006 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 28006) = 3 ^ 5 * m + 208 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_28006.1, data_15_28006.2]

/-- Complete interval computation for depth 15, residue 28007. -/
theorem bounds_15_28007 : exactInterval 15 28007 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_28007 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 28007) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_28007 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_28007 : oddCount 28007 15 = 13 ∧ acceleratedOrbit 15 28007 = 1362743 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_28007 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 28007) = 3 ^ 13 * m + 1362743 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_28007.1, data_15_28007.2]

/-- Complete interval computation for depth 15, residue 28008. -/
theorem bounds_15_28008 : exactInterval 15 28008 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_28008 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 28008) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_28008 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_28008 : oddCount 28008 15 = 5 ∧ acceleratedOrbit 15 28008 = 208 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_28008 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 28008) = 3 ^ 5 * m + 208 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_28008.1, data_15_28008.2]

/-- Complete interval computation for depth 15, residue 28009. -/
theorem bounds_15_28009 : exactInterval 15 28009 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_28009 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 28009) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_28009 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_28009 : oddCount 28009 15 = 8 ∧ acceleratedOrbit 15 28009 = 5609 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_28009 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 28009) = 3 ^ 8 * m + 5609 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_28009.1, data_15_28009.2]

/-- Complete interval computation for depth 15, residue 28010. -/
theorem bounds_15_28010 : exactInterval 15 28010 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_28010 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 28010) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_28010 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_28010 : oddCount 28010 15 = 5 ∧ acceleratedOrbit 15 28010 = 208 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_28010 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 28010) = 3 ^ 5 * m + 208 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_28010.1, data_15_28010.2]

/-- Complete interval computation for depth 15, residue 28011. -/
theorem bounds_15_28011 : exactInterval 15 28011 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_28011 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 28011) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_28011 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_28011 : oddCount 28011 15 = 10 ∧ acceleratedOrbit 15 28011 = 50483 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_28011 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 28011) = 3 ^ 10 * m + 50483 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_28011.1, data_15_28011.2]

/-- Complete interval computation for depth 15, residue 28012. -/
theorem bounds_15_28012 : exactInterval 15 28012 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_28012 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 28012) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_28012 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_28012 : oddCount 28012 15 = 7 ∧ acceleratedOrbit 15 28012 = 1870 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_28012 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 28012) = 3 ^ 7 * m + 1870 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_28012.1, data_15_28012.2]

/-- Complete interval computation for depth 15, residue 28013. -/
theorem bounds_15_28013 : exactInterval 15 28013 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_28013 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 28013) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_28013 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_28013 : oddCount 28013 15 = 7 ∧ acceleratedOrbit 15 28013 = 1870 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_28013 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 28013) = 3 ^ 7 * m + 1870 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_28013.1, data_15_28013.2]

/-- Complete interval computation for depth 15, residue 28014. -/
theorem bounds_15_28014 : exactInterval 15 28014 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_28014 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 28014) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_28014 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_28014 : oddCount 28014 15 = 7 ∧ acceleratedOrbit 15 28014 = 1870 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_28014 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 28014) = 3 ^ 7 * m + 1870 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_28014.1, data_15_28014.2]

/-- Complete interval computation for depth 15, residue 28015. -/
theorem bounds_15_28015 : exactInterval 15 28015 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_28015 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 28015) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_28015 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_28015 : oddCount 28015 15 = 10 ∧ acceleratedOrbit 15 28015 = 50489 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_28015 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 28015) = 3 ^ 10 * m + 50489 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_28015.1, data_15_28015.2]

end Collatz.Research.PassageAtlas.Batch0855
