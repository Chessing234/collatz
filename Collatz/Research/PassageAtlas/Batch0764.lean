import Collatz.Research.DescentIntervals.Classifier

namespace Collatz.Research.PassageAtlas.Batch0764

open Collatz.Research.DescentIntervals

set_option maxRecDepth 20000
set_option maxHeartbeats 0

/-- Complete interval computation for depth 15, residue 25001. -/
theorem bounds_15_25001 : exactInterval 15 25001 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_25001 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 25001) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_25001 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_25001 : oddCount 25001 15 = 10 ∧ acceleratedOrbit 15 25001 = 45056 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_25001 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 25001) = 3 ^ 10 * m + 45056 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_25001.1, data_15_25001.2]

/-- Complete interval computation for depth 15, residue 25002. -/
theorem bounds_15_25002 : exactInterval 15 25002 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_25002 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 25002) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_25002 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_25002 : oddCount 25002 15 = 5 ∧ acceleratedOrbit 15 25002 = 188 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_25002 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 25002) = 3 ^ 5 * m + 188 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_25002.1, data_15_25002.2]

/-- Complete interval computation for depth 15, residue 25003. -/
theorem bounds_15_25003 : exactInterval 15 25003 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_25003 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 25003) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_25003 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_25003 : oddCount 25003 15 = 10 ∧ acceleratedOrbit 15 25003 = 45062 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_25003 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 25003) = 3 ^ 10 * m + 45062 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_25003.1, data_15_25003.2]

/-- Complete interval computation for depth 15, residue 25004. -/
theorem bounds_15_25004 : exactInterval 15 25004 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_25004 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 25004) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_25004 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_25004 : oddCount 25004 15 = 9 ∧ acceleratedOrbit 15 25004 = 15025 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_25004 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 25004) = 3 ^ 9 * m + 15025 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_25004.1, data_15_25004.2]

/-- Complete interval computation for depth 15, residue 25005. -/
theorem bounds_15_25005 : exactInterval 15 25005 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_25005 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 25005) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_25005 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_25005 : oddCount 25005 15 = 9 ∧ acceleratedOrbit 15 25005 = 15025 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_25005 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 25005) = 3 ^ 9 * m + 15025 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_25005.1, data_15_25005.2]

/-- Complete interval computation for depth 15, residue 25006. -/
theorem bounds_15_25006 : exactInterval 15 25006 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_25006 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 25006) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_25006 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_25006 : oddCount 25006 15 = 9 ∧ acceleratedOrbit 15 25006 = 15025 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_25006 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 25006) = 3 ^ 9 * m + 15025 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_25006.1, data_15_25006.2]

/-- Complete interval computation for depth 15, residue 25007. -/
theorem bounds_15_25007 : exactInterval 15 25007 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_25007 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 25007) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_25007 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_25007 : oddCount 25007 15 = 8 ∧ acceleratedOrbit 15 25007 = 5008 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_25007 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 25007) = 3 ^ 8 * m + 5008 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_25007.1, data_15_25007.2]

/-- Complete interval computation for depth 15, residue 25008. -/
theorem bounds_15_25008 : exactInterval 15 25008 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_25008 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 25008) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_25008 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_25008 : oddCount 25008 15 = 8 ∧ acceleratedOrbit 15 25008 = 5012 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_25008 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 25008) = 3 ^ 8 * m + 5012 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_25008.1, data_15_25008.2]

/-- Complete interval computation for depth 15, residue 25009. -/
theorem bounds_15_25009 : exactInterval 15 25009 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_25009 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 25009) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_25009 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_25009 : oddCount 25009 15 = 8 ∧ acceleratedOrbit 15 25009 = 5012 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_25009 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 25009) = 3 ^ 8 * m + 5012 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_25009.1, data_15_25009.2]

/-- Complete interval computation for depth 15, residue 25010. -/
theorem bounds_15_25010 : exactInterval 15 25010 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_25010 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 25010) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_25010 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_25010 : oddCount 25010 15 = 8 ∧ acceleratedOrbit 15 25010 = 5012 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_25010 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 25010) = 3 ^ 8 * m + 5012 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_25010.1, data_15_25010.2]

/-- Complete interval computation for depth 15, residue 25011. -/
theorem bounds_15_25011 : exactInterval 15 25011 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_25011 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 25011) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_25011 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_25011 : oddCount 25011 15 = 8 ∧ acceleratedOrbit 15 25011 = 5012 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_25011 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 25011) = 3 ^ 8 * m + 5012 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_25011.1, data_15_25011.2]

/-- Complete interval computation for depth 15, residue 25012. -/
theorem bounds_15_25012 : exactInterval 15 25012 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_25012 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 25012) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_25012 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_25012 : oddCount 25012 15 = 8 ∧ acceleratedOrbit 15 25012 = 5012 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_25012 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 25012) = 3 ^ 8 * m + 5012 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_25012.1, data_15_25012.2]

/-- Complete interval computation for depth 15, residue 25013. -/
theorem bounds_15_25013 : exactInterval 15 25013 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_25013 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 25013) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_25013 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_25013 : oddCount 25013 15 = 8 ∧ acceleratedOrbit 15 25013 = 5012 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_25013 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 25013) = 3 ^ 8 * m + 5012 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_25013.1, data_15_25013.2]

/-- Complete interval computation for depth 15, residue 25014. -/
theorem bounds_15_25014 : exactInterval 15 25014 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_25014 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 25014) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_25014 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_25014 : oddCount 25014 15 = 9 ∧ acceleratedOrbit 15 25014 = 15029 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_25014 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 25014) = 3 ^ 9 * m + 15029 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_25014.1, data_15_25014.2]

/-- Complete interval computation for depth 15, residue 25015. -/
theorem bounds_15_25015 : exactInterval 15 25015 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_25015 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 25015) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_25015 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_25015 : oddCount 25015 15 = 9 ∧ acceleratedOrbit 15 25015 = 15029 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_25015 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 25015) = 3 ^ 9 * m + 15029 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_25015.1, data_15_25015.2]

/-- Complete interval computation for depth 15, residue 25016. -/
theorem bounds_15_25016 : exactInterval 15 25016 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_25016 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 25016) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_25016 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_25016 : oddCount 25016 15 = 8 ∧ acceleratedOrbit 15 25016 = 5012 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_25016 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 25016) = 3 ^ 8 * m + 5012 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_25016.1, data_15_25016.2]

/-- Complete interval computation for depth 15, residue 25017. -/
theorem bounds_15_25017 : exactInterval 15 25017 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_25017 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 25017) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_25017 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_25017 : oddCount 25017 15 = 8 ∧ acceleratedOrbit 15 25017 = 5012 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_25017 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 25017) = 3 ^ 8 * m + 5012 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_25017.1, data_15_25017.2]

/-- Complete interval computation for depth 15, residue 25018. -/
theorem bounds_15_25018 : exactInterval 15 25018 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_25018 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 25018) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_25018 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_25018 : oddCount 25018 15 = 8 ∧ acceleratedOrbit 15 25018 = 5012 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_25018 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 25018) = 3 ^ 8 * m + 5012 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_25018.1, data_15_25018.2]

/-- Complete interval computation for depth 15, residue 25019. -/
theorem bounds_15_25019 : exactInterval 15 25019 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_25019 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 25019) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_25019 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_25019 : oddCount 25019 15 = 7 ∧ acceleratedOrbit 15 25019 = 1670 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_25019 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 25019) = 3 ^ 7 * m + 1670 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_25019.1, data_15_25019.2]

/-- Complete interval computation for depth 15, residue 25020. -/
theorem bounds_15_25020 : exactInterval 15 25020 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_25020 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 25020) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_25020 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_25020 : oddCount 25020 15 = 9 ∧ acceleratedOrbit 15 25020 = 15032 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_25020 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 25020) = 3 ^ 9 * m + 15032 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_25020.1, data_15_25020.2]

/-- Complete interval computation for depth 15, residue 25021. -/
theorem bounds_15_25021 : exactInterval 15 25021 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_25021 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 25021) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_25021 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_25021 : oddCount 25021 15 = 9 ∧ acceleratedOrbit 15 25021 = 15032 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_25021 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 25021) = 3 ^ 9 * m + 15032 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_25021.1, data_15_25021.2]

/-- Complete interval computation for depth 15, residue 25022. -/
theorem bounds_15_25022 : exactInterval 15 25022 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_25022 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 25022) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_25022 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_25022 : oddCount 25022 15 = 9 ∧ acceleratedOrbit 15 25022 = 15032 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_25022 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 25022) = 3 ^ 9 * m + 15032 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_25022.1, data_15_25022.2]

/-- Complete interval computation for depth 15, residue 25023. -/
theorem bounds_15_25023 : exactInterval 15 25023 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_25023 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 25023) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_25023 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_25023 : oddCount 25023 15 = 11 ∧ acceleratedOrbit 15 25023 = 135283 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_25023 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 25023) = 3 ^ 11 * m + 135283 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_25023.1, data_15_25023.2]

/-- Complete interval computation for depth 15, residue 25024. -/
theorem bounds_15_25024 : exactInterval 15 25024 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_25024 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 25024) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_25024 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_25024 : oddCount 25024 15 = 4 ∧ acceleratedOrbit 15 25024 = 62 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_25024 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 25024) = 3 ^ 4 * m + 62 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_25024.1, data_15_25024.2]

/-- Complete interval computation for depth 15, residue 25025. -/
theorem bounds_15_25025 : exactInterval 15 25025 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_25025 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 25025) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_25025 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_25025 : oddCount 25025 15 = 10 ∧ acceleratedOrbit 15 25025 = 45107 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_25025 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 25025) = 3 ^ 10 * m + 45107 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_25025.1, data_15_25025.2]

/-- Complete interval computation for depth 15, residue 25026. -/
theorem bounds_15_25026 : exactInterval 15 25026 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_25026 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 25026) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_25026 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_25026 : oddCount 25026 15 = 10 ∧ acceleratedOrbit 15 25026 = 45107 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_25026 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 25026) = 3 ^ 10 * m + 45107 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_25026.1, data_15_25026.2]

/-- Complete interval computation for depth 15, residue 25027. -/
theorem bounds_15_25027 : exactInterval 15 25027 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_25027 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 25027) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_25027 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_25027 : oddCount 25027 15 = 10 ∧ acceleratedOrbit 15 25027 = 45107 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_25027 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 25027) = 3 ^ 10 * m + 45107 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_25027.1, data_15_25027.2]

/-- Complete interval computation for depth 15, residue 25028. -/
theorem bounds_15_25028 : exactInterval 15 25028 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_25028 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 25028) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_25028 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_25028 : oddCount 25028 15 = 5 ∧ acceleratedOrbit 15 25028 = 188 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_25028 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 25028) = 3 ^ 5 * m + 188 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_25028.1, data_15_25028.2]

/-- Complete interval computation for depth 15, residue 25029. -/
theorem bounds_15_25029 : exactInterval 15 25029 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_25029 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 25029) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_25029 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_25029 : oddCount 25029 15 = 5 ∧ acceleratedOrbit 15 25029 = 188 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_25029 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 25029) = 3 ^ 5 * m + 188 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_25029.1, data_15_25029.2]

/-- Complete interval computation for depth 15, residue 25030. -/
theorem bounds_15_25030 : exactInterval 15 25030 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_25030 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 25030) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_25030 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_25030 : oddCount 25030 15 = 5 ∧ acceleratedOrbit 15 25030 = 188 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_25030 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 25030) = 3 ^ 5 * m + 188 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_25030.1, data_15_25030.2]

/-- Complete interval computation for depth 15, residue 25031. -/
theorem bounds_15_25031 : exactInterval 15 25031 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_25031 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 25031) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_25031 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_25031 : oddCount 25031 15 = 9 ∧ acceleratedOrbit 15 25031 = 15038 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_25031 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 25031) = 3 ^ 9 * m + 15038 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_25031.1, data_15_25031.2]

/-- Complete interval computation for depth 15, residue 25032. -/
theorem bounds_15_25032 : exactInterval 15 25032 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_25032 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 25032) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_25032 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_25032 : oddCount 25032 15 = 7 ∧ acceleratedOrbit 15 25032 = 1673 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_25032 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 25032) = 3 ^ 7 * m + 1673 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_25032.1, data_15_25032.2]

/-- Complete interval computation for depth 15, residue 25033. -/
theorem bounds_15_25033 : exactInterval 15 25033 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_25033 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 25033) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_25033 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_25033 : oddCount 25033 15 = 6 ∧ acceleratedOrbit 15 25033 = 557 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_25033 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 25033) = 3 ^ 6 * m + 557 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_25033.1, data_15_25033.2]

end Collatz.Research.PassageAtlas.Batch0764
