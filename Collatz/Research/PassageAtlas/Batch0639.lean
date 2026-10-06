import Collatz.Research.DescentIntervals.Classifier

namespace Collatz.Research.PassageAtlas.Batch0639

open Collatz.Research.DescentIntervals

set_option maxRecDepth 20000
set_option maxHeartbeats 0

/-- Complete interval computation for depth 15, residue 20905. -/
theorem bounds_15_20905 : exactInterval 15 20905 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_20905 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 20905) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_20905 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_20905 : oddCount 20905 15 = 10 ∧ acceleratedOrbit 15 20905 = 37675 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_20905 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 20905) = 3 ^ 10 * m + 37675 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_20905.1, data_15_20905.2]

/-- Complete interval computation for depth 15, residue 20906. -/
theorem bounds_15_20906 : exactInterval 15 20906 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_20906 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 20906) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_20906 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_20906 : oddCount 20906 15 = 4 ∧ acceleratedOrbit 15 20906 = 53 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_20906 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 20906) = 3 ^ 4 * m + 53 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_20906.1, data_15_20906.2]

/-- Complete interval computation for depth 15, residue 20907. -/
theorem bounds_15_20907 : exactInterval 15 20907 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_20907 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 20907) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_20907 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_20907 : oddCount 20907 15 = 9 ∧ acceleratedOrbit 15 20907 = 12560 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_20907 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 20907) = 3 ^ 9 * m + 12560 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_20907.1, data_15_20907.2]

/-- Complete interval computation for depth 15, residue 20908. -/
theorem bounds_15_20908 : exactInterval 15 20908 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_20908 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 20908) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_20908 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_20908 : oddCount 20908 15 = 7 ∧ acceleratedOrbit 15 20908 = 1396 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_20908 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 20908) = 3 ^ 7 * m + 1396 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_20908.1, data_15_20908.2]

/-- Complete interval computation for depth 15, residue 20909. -/
theorem bounds_15_20909 : exactInterval 15 20909 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_20909 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 20909) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_20909 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_20909 : oddCount 20909 15 = 7 ∧ acceleratedOrbit 15 20909 = 1396 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_20909 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 20909) = 3 ^ 7 * m + 1396 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_20909.1, data_15_20909.2]

/-- Complete interval computation for depth 15, residue 20910. -/
theorem bounds_15_20910 : exactInterval 15 20910 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_20910 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 20910) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_20910 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_20910 : oddCount 20910 15 = 7 ∧ acceleratedOrbit 15 20910 = 1396 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_20910 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 20910) = 3 ^ 7 * m + 1396 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_20910.1, data_15_20910.2]

/-- Complete interval computation for depth 15, residue 20911. -/
theorem bounds_15_20911 : exactInterval 15 20911 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_20911 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 20911) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_20911 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_20911 : oddCount 20911 15 = 7 ∧ acceleratedOrbit 15 20911 = 1396 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_20911 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 20911) = 3 ^ 7 * m + 1396 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_20911.1, data_15_20911.2]

/-- Complete interval computation for depth 15, residue 20912. -/
theorem bounds_15_20912 : exactInterval 15 20912 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_20912 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 20912) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_20912 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_20912 : oddCount 20912 15 = 9 ∧ acceleratedOrbit 15 20912 = 12575 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_20912 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 20912) = 3 ^ 9 * m + 12575 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_20912.1, data_15_20912.2]

/-- Complete interval computation for depth 15, residue 20913. -/
theorem bounds_15_20913 : exactInterval 15 20913 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_20913 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 20913) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_20913 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_20913 : oddCount 20913 15 = 7 ∧ acceleratedOrbit 15 20913 = 1397 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_20913 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 20913) = 3 ^ 7 * m + 1397 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_20913.1, data_15_20913.2]

/-- Complete interval computation for depth 15, residue 20914. -/
theorem bounds_15_20914 : exactInterval 15 20914 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_20914 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 20914) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_20914 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_20914 : oddCount 20914 15 = 7 ∧ acceleratedOrbit 15 20914 = 1397 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_20914 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 20914) = 3 ^ 7 * m + 1397 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_20914.1, data_15_20914.2]

/-- Complete interval computation for depth 15, residue 20915. -/
theorem bounds_15_20915 : exactInterval 15 20915 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_20915 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 20915) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_20915 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_20915 : oddCount 20915 15 = 7 ∧ acceleratedOrbit 15 20915 = 1397 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_20915 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 20915) = 3 ^ 7 * m + 1397 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_20915.1, data_15_20915.2]

/-- Complete interval computation for depth 15, residue 20916. -/
theorem bounds_15_20916 : exactInterval 15 20916 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_20916 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 20916) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_20916 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_20916 : oddCount 20916 15 = 9 ∧ acceleratedOrbit 15 20916 = 12575 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_20916 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 20916) = 3 ^ 9 * m + 12575 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_20916.1, data_15_20916.2]

/-- Complete interval computation for depth 15, residue 20917. -/
theorem bounds_15_20917 : exactInterval 15 20917 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_20917 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 20917) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_20917 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_20917 : oddCount 20917 15 = 9 ∧ acceleratedOrbit 15 20917 = 12575 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_20917 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 20917) = 3 ^ 9 * m + 12575 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_20917.1, data_15_20917.2]

/-- Complete interval computation for depth 15, residue 20918. -/
theorem bounds_15_20918 : exactInterval 15 20918 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_20918 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 20918) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_20918 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_20918 : oddCount 20918 15 = 9 ∧ acceleratedOrbit 15 20918 = 12568 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_20918 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 20918) = 3 ^ 9 * m + 12568 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_20918.1, data_15_20918.2]

/-- Complete interval computation for depth 15, residue 20919. -/
theorem bounds_15_20919 : exactInterval 15 20919 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_20919 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 20919) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_20919 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_20919 : oddCount 20919 15 = 9 ∧ acceleratedOrbit 15 20919 = 12568 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_20919 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 20919) = 3 ^ 9 * m + 12568 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_20919.1, data_15_20919.2]

/-- Complete interval computation for depth 15, residue 20920. -/
theorem bounds_15_20920 : exactInterval 15 20920 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_20920 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 20920) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_20920 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_20920 : oddCount 20920 15 = 9 ∧ acceleratedOrbit 15 20920 = 12575 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_20920 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 20920) = 3 ^ 9 * m + 12575 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_20920.1, data_15_20920.2]

/-- Complete interval computation for depth 15, residue 20921. -/
theorem bounds_15_20921 : exactInterval 15 20921 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_20921 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 20921) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_20921 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_20921 : oddCount 20921 15 = 7 ∧ acceleratedOrbit 15 20921 = 1397 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_20921 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 20921) = 3 ^ 7 * m + 1397 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_20921.1, data_15_20921.2]

/-- Complete interval computation for depth 15, residue 20922. -/
theorem bounds_15_20922 : exactInterval 15 20922 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_20922 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 20922) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_20922 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_20922 : oddCount 20922 15 = 9 ∧ acceleratedOrbit 15 20922 = 12575 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_20922 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 20922) = 3 ^ 9 * m + 12575 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_20922.1, data_15_20922.2]

/-- Complete interval computation for depth 15, residue 20923. -/
theorem bounds_15_20923 : exactInterval 15 20923 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_20923 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 20923) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_20923 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_20923 : oddCount 20923 15 = 8 ∧ acceleratedOrbit 15 20923 = 4190 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_20923 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 20923) = 3 ^ 8 * m + 4190 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_20923.1, data_15_20923.2]

/-- Complete interval computation for depth 15, residue 20924. -/
theorem bounds_15_20924 : exactInterval 15 20924 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_20924 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 20924) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_20924 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_20924 : oddCount 20924 15 = 9 ∧ acceleratedOrbit 15 20924 = 12572 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_20924 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 20924) = 3 ^ 9 * m + 12572 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_20924.1, data_15_20924.2]

/-- Complete interval computation for depth 15, residue 20925. -/
theorem bounds_15_20925 : exactInterval 15 20925 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_20925 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 20925) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_20925 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_20925 : oddCount 20925 15 = 9 ∧ acceleratedOrbit 15 20925 = 12572 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_20925 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 20925) = 3 ^ 9 * m + 12572 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_20925.1, data_15_20925.2]

/-- Complete interval computation for depth 15, residue 20926. -/
theorem bounds_15_20926 : exactInterval 15 20926 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_20926 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 20926) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_20926 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_20926 : oddCount 20926 15 = 9 ∧ acceleratedOrbit 15 20926 = 12572 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_20926 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 20926) = 3 ^ 9 * m + 12572 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_20926.1, data_15_20926.2]

/-- Complete interval computation for depth 15, residue 20927. -/
theorem bounds_15_20927 : exactInterval 15 20927 = ⟨0, none⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_20927 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 20927) 15 ↔ 0 ≤ m := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_20927 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_20927 : oddCount 20927 15 = 9 ∧ acceleratedOrbit 15 20927 = 12571 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_20927 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 20927) = 3 ^ 9 * m + 12571 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_20927.1, data_15_20927.2]

/-- Complete interval computation for depth 15, residue 20928. -/
theorem bounds_15_20928 : exactInterval 15 20928 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_20928 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 20928) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_20928 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_20928 : oddCount 20928 15 = 7 ∧ acceleratedOrbit 15 20928 = 1403 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_20928 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 20928) = 3 ^ 7 * m + 1403 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_20928.1, data_15_20928.2]

/-- Complete interval computation for depth 15, residue 20929. -/
theorem bounds_15_20929 : exactInterval 15 20929 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_20929 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 20929) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_20929 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_20929 : oddCount 20929 15 = 9 ∧ acceleratedOrbit 15 20929 = 12575 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_20929 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 20929) = 3 ^ 9 * m + 12575 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_20929.1, data_15_20929.2]

/-- Complete interval computation for depth 15, residue 20930. -/
theorem bounds_15_20930 : exactInterval 15 20930 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_20930 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 20930) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_20930 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_20930 : oddCount 20930 15 = 11 ∧ acceleratedOrbit 15 20930 = 113177 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_20930 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 20930) = 3 ^ 11 * m + 113177 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_20930.1, data_15_20930.2]

/-- Complete interval computation for depth 15, residue 20931. -/
theorem bounds_15_20931 : exactInterval 15 20931 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_20931 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 20931) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_20931 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_20931 : oddCount 20931 15 = 11 ∧ acceleratedOrbit 15 20931 = 113177 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_20931 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 20931) = 3 ^ 11 * m + 113177 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_20931.1, data_15_20931.2]

/-- Complete interval computation for depth 15, residue 20932. -/
theorem bounds_15_20932 : exactInterval 15 20932 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_20932 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 20932) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_20932 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_20932 : oddCount 20932 15 = 4 ∧ acceleratedOrbit 15 20932 = 53 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_20932 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 20932) = 3 ^ 4 * m + 53 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_20932.1, data_15_20932.2]

/-- Complete interval computation for depth 15, residue 20933. -/
theorem bounds_15_20933 : exactInterval 15 20933 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_20933 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 20933) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_20933 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_20933 : oddCount 20933 15 = 4 ∧ acceleratedOrbit 15 20933 = 53 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_20933 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 20933) = 3 ^ 4 * m + 53 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_20933.1, data_15_20933.2]

/-- Complete interval computation for depth 15, residue 20934. -/
theorem bounds_15_20934 : exactInterval 15 20934 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_20934 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 20934) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_20934 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_20934 : oddCount 20934 15 = 4 ∧ acceleratedOrbit 15 20934 = 53 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_20934 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 20934) = 3 ^ 4 * m + 53 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_20934.1, data_15_20934.2]

/-- Complete interval computation for depth 15, residue 20935. -/
theorem bounds_15_20935 : exactInterval 15 20935 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_20935 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 20935) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_20935 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_20935 : oddCount 20935 15 = 9 ∧ acceleratedOrbit 15 20935 = 12577 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_20935 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 20935) = 3 ^ 9 * m + 12577 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_20935.1, data_15_20935.2]

/-- Complete interval computation for depth 15, residue 20936. -/
theorem bounds_15_20936 : exactInterval 15 20936 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_20936 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 20936) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_20936 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_20936 : oddCount 20936 15 = 7 ∧ acceleratedOrbit 15 20936 = 1399 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_20936 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 20936) = 3 ^ 7 * m + 1399 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_20936.1, data_15_20936.2]

/-- Complete interval computation for depth 15, residue 20937. -/
theorem bounds_15_20937 : exactInterval 15 20937 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_20937 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 20937) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_20937 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_20937 : oddCount 20937 15 = 9 ∧ acceleratedOrbit 15 20937 = 12581 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_20937 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 20937) = 3 ^ 9 * m + 12581 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_20937.1, data_15_20937.2]

end Collatz.Research.PassageAtlas.Batch0639
