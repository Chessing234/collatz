import Collatz.Research.DescentIntervals.Classifier

namespace Collatz.Research.PassageAtlas.Batch0886

open Collatz.Research.DescentIntervals

set_option maxRecDepth 20000
set_option maxHeartbeats 0

/-- Complete interval computation for depth 15, residue 28999. -/
theorem bounds_15_28999 : exactInterval 15 28999 = ⟨0, none⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_28999 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 28999) 15 ↔ 0 ≤ m := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_28999 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_28999 : oddCount 28999 15 = 9 ∧ acceleratedOrbit 15 28999 = 17420 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_28999 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 28999) = 3 ^ 9 * m + 17420 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_28999.1, data_15_28999.2]

/-- Complete interval computation for depth 15, residue 29000. -/
theorem bounds_15_29000 : exactInterval 15 29000 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_29000 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 29000) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_29000 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_29000 : oddCount 29000 15 = 9 ∧ acceleratedOrbit 15 29000 = 17428 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_29000 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 29000) = 3 ^ 9 * m + 17428 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_29000.1, data_15_29000.2]

/-- Complete interval computation for depth 15, residue 29001. -/
theorem bounds_15_29001 : exactInterval 15 29001 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_29001 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 29001) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_29001 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_29001 : oddCount 29001 15 = 7 ∧ acceleratedOrbit 15 29001 = 1936 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_29001 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 29001) = 3 ^ 7 * m + 1936 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_29001.1, data_15_29001.2]

/-- Complete interval computation for depth 15, residue 29002. -/
theorem bounds_15_29002 : exactInterval 15 29002 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_29002 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 29002) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_29002 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_29002 : oddCount 29002 15 = 9 ∧ acceleratedOrbit 15 29002 = 17428 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_29002 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 29002) = 3 ^ 9 * m + 17428 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_29002.1, data_15_29002.2]

/-- Complete interval computation for depth 15, residue 29003. -/
theorem bounds_15_29003 : exactInterval 15 29003 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_29003 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 29003) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_29003 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_29003 : oddCount 29003 15 = 7 ∧ acceleratedOrbit 15 29003 = 1937 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_29003 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 29003) = 3 ^ 7 * m + 1937 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_29003.1, data_15_29003.2]

/-- Complete interval computation for depth 15, residue 29004. -/
theorem bounds_15_29004 : exactInterval 15 29004 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_29004 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 29004) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_29004 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_29004 : oddCount 29004 15 = 9 ∧ acceleratedOrbit 15 29004 = 17428 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_29004 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 29004) = 3 ^ 9 * m + 17428 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_29004.1, data_15_29004.2]

/-- Complete interval computation for depth 15, residue 29005. -/
theorem bounds_15_29005 : exactInterval 15 29005 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_29005 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 29005) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_29005 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_29005 : oddCount 29005 15 = 9 ∧ acceleratedOrbit 15 29005 = 17428 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_29005 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 29005) = 3 ^ 9 * m + 17428 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_29005.1, data_15_29005.2]

/-- Complete interval computation for depth 15, residue 29006. -/
theorem bounds_15_29006 : exactInterval 15 29006 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_29006 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 29006) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_29006 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_29006 : oddCount 29006 15 = 9 ∧ acceleratedOrbit 15 29006 = 17425 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_29006 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 29006) = 3 ^ 9 * m + 17425 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_29006.1, data_15_29006.2]

/-- Complete interval computation for depth 15, residue 29007. -/
theorem bounds_15_29007 : exactInterval 15 29007 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_29007 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 29007) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_29007 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_29007 : oddCount 29007 15 = 9 ∧ acceleratedOrbit 15 29007 = 17425 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_29007 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 29007) = 3 ^ 9 * m + 17425 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_29007.1, data_15_29007.2]

/-- Complete interval computation for depth 15, residue 29008. -/
theorem bounds_15_29008 : exactInterval 15 29008 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_29008 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 29008) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_29008 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_29008 : oddCount 29008 15 = 2 ∧ acceleratedOrbit 15 29008 = 8 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_29008 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 29008) = 3 ^ 2 * m + 8 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_29008.1, data_15_29008.2]

/-- Complete interval computation for depth 15, residue 29009. -/
theorem bounds_15_29009 : exactInterval 15 29009 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_29009 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 29009) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_29009 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_29009 : oddCount 29009 15 = 9 ∧ acceleratedOrbit 15 29009 = 17428 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_29009 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 29009) = 3 ^ 9 * m + 17428 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_29009.1, data_15_29009.2]

/-- Complete interval computation for depth 15, residue 29010. -/
theorem bounds_15_29010 : exactInterval 15 29010 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_29010 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 29010) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_29010 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_29010 : oddCount 29010 15 = 10 ∧ acceleratedOrbit 15 29010 = 52283 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_29010 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 29010) = 3 ^ 10 * m + 52283 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_29010.1, data_15_29010.2]

/-- Complete interval computation for depth 15, residue 29011. -/
theorem bounds_15_29011 : exactInterval 15 29011 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_29011 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 29011) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_29011 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_29011 : oddCount 29011 15 = 10 ∧ acceleratedOrbit 15 29011 = 52283 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_29011 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 29011) = 3 ^ 10 * m + 52283 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_29011.1, data_15_29011.2]

/-- Complete interval computation for depth 15, residue 29012. -/
theorem bounds_15_29012 : exactInterval 15 29012 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_29012 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 29012) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_29012 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_29012 : oddCount 29012 15 = 2 ∧ acceleratedOrbit 15 29012 = 8 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_29012 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 29012) = 3 ^ 2 * m + 8 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_29012.1, data_15_29012.2]

/-- Complete interval computation for depth 15, residue 29013. -/
theorem bounds_15_29013 : exactInterval 15 29013 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_29013 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 29013) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_29013 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_29013 : oddCount 29013 15 = 2 ∧ acceleratedOrbit 15 29013 = 8 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_29013 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 29013) = 3 ^ 2 * m + 8 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_29013.1, data_15_29013.2]

/-- Complete interval computation for depth 15, residue 29014. -/
theorem bounds_15_29014 : exactInterval 15 29014 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_29014 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 29014) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_29014 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_29014 : oddCount 29014 15 = 7 ∧ acceleratedOrbit 15 29014 = 1937 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_29014 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 29014) = 3 ^ 7 * m + 1937 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_29014.1, data_15_29014.2]

/-- Complete interval computation for depth 15, residue 29015. -/
theorem bounds_15_29015 : exactInterval 15 29015 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_29015 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 29015) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_29015 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_29015 : oddCount 29015 15 = 7 ∧ acceleratedOrbit 15 29015 = 1937 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_29015 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 29015) = 3 ^ 7 * m + 1937 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_29015.1, data_15_29015.2]

/-- Complete interval computation for depth 15, residue 29016. -/
theorem bounds_15_29016 : exactInterval 15 29016 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_29016 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 29016) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_29016 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_29016 : oddCount 29016 15 = 6 ∧ acceleratedOrbit 15 29016 = 647 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_29016 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 29016) = 3 ^ 6 * m + 647 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_29016.1, data_15_29016.2]

/-- Complete interval computation for depth 15, residue 29017. -/
theorem bounds_15_29017 : exactInterval 15 29017 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_29017 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 29017) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_29017 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_29017 : oddCount 29017 15 = 9 ∧ acceleratedOrbit 15 29017 = 17435 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_29017 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 29017) = 3 ^ 9 * m + 17435 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_29017.1, data_15_29017.2]

/-- Complete interval computation for depth 15, residue 29018. -/
theorem bounds_15_29018 : exactInterval 15 29018 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_29018 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 29018) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_29018 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_29018 : oddCount 29018 15 = 6 ∧ acceleratedOrbit 15 29018 = 647 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_29018 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 29018) = 3 ^ 6 * m + 647 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_29018.1, data_15_29018.2]

/-- Complete interval computation for depth 15, residue 29019. -/
theorem bounds_15_29019 : exactInterval 15 29019 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_29019 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 29019) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_29019 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_29019 : oddCount 29019 15 = 7 ∧ acceleratedOrbit 15 29019 = 1937 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_29019 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 29019) = 3 ^ 7 * m + 1937 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_29019.1, data_15_29019.2]

/-- Complete interval computation for depth 15, residue 29020. -/
theorem bounds_15_29020 : exactInterval 15 29020 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_29020 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 29020) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_29020 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_29020 : oddCount 29020 15 = 6 ∧ acceleratedOrbit 15 29020 = 647 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_29020 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 29020) = 3 ^ 6 * m + 647 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_29020.1, data_15_29020.2]

/-- Complete interval computation for depth 15, residue 29021. -/
theorem bounds_15_29021 : exactInterval 15 29021 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_29021 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 29021) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_29021 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_29021 : oddCount 29021 15 = 6 ∧ acceleratedOrbit 15 29021 = 647 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_29021 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 29021) = 3 ^ 6 * m + 647 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_29021.1, data_15_29021.2]

/-- Complete interval computation for depth 15, residue 29022. -/
theorem bounds_15_29022 : exactInterval 15 29022 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_29022 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 29022) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_29022 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_29022 : oddCount 29022 15 = 9 ∧ acceleratedOrbit 15 29022 = 17435 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_29022 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 29022) = 3 ^ 9 * m + 17435 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_29022.1, data_15_29022.2]

/-- Complete interval computation for depth 15, residue 29023. -/
theorem bounds_15_29023 : exactInterval 15 29023 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_29023 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 29023) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_29023 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_29023 : oddCount 29023 15 = 9 ∧ acceleratedOrbit 15 29023 = 17435 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_29023 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 29023) = 3 ^ 9 * m + 17435 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_29023.1, data_15_29023.2]

/-- Complete interval computation for depth 15, residue 29024. -/
theorem bounds_15_29024 : exactInterval 15 29024 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_29024 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 29024) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_29024 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_29024 : oddCount 29024 15 = 7 ∧ acceleratedOrbit 15 29024 = 1943 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_29024 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 29024) = 3 ^ 7 * m + 1943 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_29024.1, data_15_29024.2]

/-- Complete interval computation for depth 15, residue 29025. -/
theorem bounds_15_29025 : exactInterval 15 29025 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_29025 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 29025) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_29025 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_29025 : oddCount 29025 15 = 9 ∧ acceleratedOrbit 15 29025 = 17437 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_29025 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 29025) = 3 ^ 9 * m + 17437 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_29025.1, data_15_29025.2]

/-- Complete interval computation for depth 15, residue 29026. -/
theorem bounds_15_29026 : exactInterval 15 29026 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_29026 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 29026) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_29026 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_29026 : oddCount 29026 15 = 7 ∧ acceleratedOrbit 15 29026 = 1939 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_29026 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 29026) = 3 ^ 7 * m + 1939 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_29026.1, data_15_29026.2]

/-- Complete interval computation for depth 15, residue 29027. -/
theorem bounds_15_29027 : exactInterval 15 29027 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_29027 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 29027) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_29027 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_29027 : oddCount 29027 15 = 7 ∧ acceleratedOrbit 15 29027 = 1939 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_29027 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 29027) = 3 ^ 7 * m + 1939 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_29027.1, data_15_29027.2]

/-- Complete interval computation for depth 15, residue 29028. -/
theorem bounds_15_29028 : exactInterval 15 29028 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_29028 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 29028) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_29028 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_29028 : oddCount 29028 15 = 7 ∧ acceleratedOrbit 15 29028 = 1939 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_29028 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 29028) = 3 ^ 7 * m + 1939 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_29028.1, data_15_29028.2]

/-- Complete interval computation for depth 15, residue 29029. -/
theorem bounds_15_29029 : exactInterval 15 29029 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_29029 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 29029) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_29029 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_29029 : oddCount 29029 15 = 7 ∧ acceleratedOrbit 15 29029 = 1939 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_29029 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 29029) = 3 ^ 7 * m + 1939 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_29029.1, data_15_29029.2]

/-- Complete interval computation for depth 15, residue 29030. -/
theorem bounds_15_29030 : exactInterval 15 29030 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_29030 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 29030) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_29030 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_29030 : oddCount 29030 15 = 7 ∧ acceleratedOrbit 15 29030 = 1939 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_29030 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 29030) = 3 ^ 7 * m + 1939 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_29030.1, data_15_29030.2]

/-- Complete interval computation for depth 15, residue 29031. -/
theorem bounds_15_29031 : exactInterval 15 29031 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_29031 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 29031) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_29031 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_29031 : oddCount 29031 15 = 8 ∧ acceleratedOrbit 15 29031 = 5813 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_29031 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 29031) = 3 ^ 8 * m + 5813 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_29031.1, data_15_29031.2]

end Collatz.Research.PassageAtlas.Batch0886
