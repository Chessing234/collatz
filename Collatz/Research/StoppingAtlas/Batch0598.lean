import Collatz.Research.DescentIntervals.Classifier

namespace Collatz.Research.StoppingAtlas.Batch0598

open Collatz.Research.DescentIntervals

set_option maxRecDepth 20000
set_option maxHeartbeats 0

/-- Complete interval computation for depth 13, residue 2001. -/
theorem bounds_13_2001 : exactInterval 13 2001 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_13_2001 (m : Nat) :
    stoppingTime (2 ^ 13 * m + 2001) 13 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_13_2001 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_13_2001 : oddCount 2001 13 = 6 ∧ acceleratedOrbit 13 2001 = 179 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_13_2001 (m : Nat) :
    acceleratedOrbit 13 (2 ^ 13 * m + 2001) = 3 ^ 6 * m + 179 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_13_2001.1, data_13_2001.2]

/-- Complete interval computation for depth 13, residue 2002. -/
theorem bounds_13_2002 : exactInterval 13 2002 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_13_2002 (m : Nat) :
    stoppingTime (2 ^ 13 * m + 2002) 13 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_13_2002 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_13_2002 : oddCount 2002 13 = 9 ∧ acceleratedOrbit 13 2002 = 4819 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_13_2002 (m : Nat) :
    acceleratedOrbit 13 (2 ^ 13 * m + 2002) = 3 ^ 9 * m + 4819 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_13_2002.1, data_13_2002.2]

/-- Complete interval computation for depth 13, residue 2003. -/
theorem bounds_13_2003 : exactInterval 13 2003 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_13_2003 (m : Nat) :
    stoppingTime (2 ^ 13 * m + 2003) 13 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_13_2003 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_13_2003 : oddCount 2003 13 = 9 ∧ acceleratedOrbit 13 2003 = 4819 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_13_2003 (m : Nat) :
    acceleratedOrbit 13 (2 ^ 13 * m + 2003) = 3 ^ 9 * m + 4819 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_13_2003.1, data_13_2003.2]

/-- Complete interval computation for depth 13, residue 2004. -/
theorem bounds_13_2004 : exactInterval 13 2004 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_13_2004 (m : Nat) :
    stoppingTime (2 ^ 13 * m + 2004) 13 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_13_2004 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_13_2004 : oddCount 2004 13 = 6 ∧ acceleratedOrbit 13 2004 = 182 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_13_2004 (m : Nat) :
    acceleratedOrbit 13 (2 ^ 13 * m + 2004) = 3 ^ 6 * m + 182 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_13_2004.1, data_13_2004.2]

/-- Complete interval computation for depth 13, residue 2005. -/
theorem bounds_13_2005 : exactInterval 13 2005 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_13_2005 (m : Nat) :
    stoppingTime (2 ^ 13 * m + 2005) 13 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_13_2005 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_13_2005 : oddCount 2005 13 = 6 ∧ acceleratedOrbit 13 2005 = 182 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_13_2005 (m : Nat) :
    acceleratedOrbit 13 (2 ^ 13 * m + 2005) = 3 ^ 6 * m + 182 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_13_2005.1, data_13_2005.2]

/-- Complete interval computation for depth 13, residue 2006. -/
theorem bounds_13_2006 : exactInterval 13 2006 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_13_2006 (m : Nat) :
    stoppingTime (2 ^ 13 * m + 2006) 13 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_13_2006 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_13_2006 : oddCount 2006 13 = 8 ∧ acceleratedOrbit 13 2006 = 1610 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_13_2006 (m : Nat) :
    acceleratedOrbit 13 (2 ^ 13 * m + 2006) = 3 ^ 8 * m + 1610 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_13_2006.1, data_13_2006.2]

/-- Complete interval computation for depth 13, residue 2007. -/
theorem bounds_13_2007 : exactInterval 13 2007 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_13_2007 (m : Nat) :
    stoppingTime (2 ^ 13 * m + 2007) 13 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_13_2007 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_13_2007 : oddCount 2007 13 = 8 ∧ acceleratedOrbit 13 2007 = 1610 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_13_2007 (m : Nat) :
    acceleratedOrbit 13 (2 ^ 13 * m + 2007) = 3 ^ 8 * m + 1610 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_13_2007.1, data_13_2007.2]

/-- Complete interval computation for depth 13, residue 2008. -/
theorem bounds_13_2008 : exactInterval 13 2008 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_13_2008 (m : Nat) :
    stoppingTime (2 ^ 13 * m + 2008) 13 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_13_2008 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_13_2008 : oddCount 2008 13 = 8 ∧ acceleratedOrbit 13 2008 = 1619 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_13_2008 (m : Nat) :
    acceleratedOrbit 13 (2 ^ 13 * m + 2008) = 3 ^ 8 * m + 1619 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_13_2008.1, data_13_2008.2]

/-- Complete interval computation for depth 13, residue 2009. -/
theorem bounds_13_2009 : exactInterval 13 2009 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_13_2009 (m : Nat) :
    stoppingTime (2 ^ 13 * m + 2009) 13 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_13_2009 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_13_2009 : oddCount 2009 13 = 4 ∧ acceleratedOrbit 13 2009 = 20 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_13_2009 (m : Nat) :
    acceleratedOrbit 13 (2 ^ 13 * m + 2009) = 3 ^ 4 * m + 20 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_13_2009.1, data_13_2009.2]

/-- Complete interval computation for depth 13, residue 2010. -/
theorem bounds_13_2010 : exactInterval 13 2010 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_13_2010 (m : Nat) :
    stoppingTime (2 ^ 13 * m + 2010) 13 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_13_2010 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_13_2010 : oddCount 2010 13 = 8 ∧ acceleratedOrbit 13 2010 = 1619 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_13_2010 (m : Nat) :
    acceleratedOrbit 13 (2 ^ 13 * m + 2010) = 3 ^ 8 * m + 1619 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_13_2010.1, data_13_2010.2]

/-- Complete interval computation for depth 13, residue 2011. -/
theorem bounds_13_2011 : exactInterval 13 2011 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_13_2011 (m : Nat) :
    stoppingTime (2 ^ 13 * m + 2011) 13 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_13_2011 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_13_2011 : oddCount 2011 13 = 8 ∧ acceleratedOrbit 13 2011 = 1613 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_13_2011 (m : Nat) :
    acceleratedOrbit 13 (2 ^ 13 * m + 2011) = 3 ^ 8 * m + 1613 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_13_2011.1, data_13_2011.2]

/-- Complete interval computation for depth 13, residue 2012. -/
theorem bounds_13_2012 : exactInterval 13 2012 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_13_2012 (m : Nat) :
    stoppingTime (2 ^ 13 * m + 2012) 13 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_13_2012 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_13_2012 : oddCount 2012 13 = 8 ∧ acceleratedOrbit 13 2012 = 1619 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_13_2012 (m : Nat) :
    acceleratedOrbit 13 (2 ^ 13 * m + 2012) = 3 ^ 8 * m + 1619 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_13_2012.1, data_13_2012.2]

/-- Complete interval computation for depth 13, residue 2013. -/
theorem bounds_13_2013 : exactInterval 13 2013 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_13_2013 (m : Nat) :
    stoppingTime (2 ^ 13 * m + 2013) 13 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_13_2013 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_13_2013 : oddCount 2013 13 = 8 ∧ acceleratedOrbit 13 2013 = 1619 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_13_2013 (m : Nat) :
    acceleratedOrbit 13 (2 ^ 13 * m + 2013) = 3 ^ 8 * m + 1619 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_13_2013.1, data_13_2013.2]

/-- Complete interval computation for depth 13, residue 2014. -/
theorem bounds_13_2014 : exactInterval 13 2014 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_13_2014 (m : Nat) :
    stoppingTime (2 ^ 13 * m + 2014) 13 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_13_2014 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_13_2014 : oddCount 2014 13 = 8 ∧ acceleratedOrbit 13 2014 = 1615 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_13_2014 (m : Nat) :
    acceleratedOrbit 13 (2 ^ 13 * m + 2014) = 3 ^ 8 * m + 1615 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_13_2014.1, data_13_2014.2]

/-- Complete interval computation for depth 13, residue 2015. -/
theorem bounds_13_2015 : exactInterval 13 2015 = ⟨0, none⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_13_2015 (m : Nat) :
    stoppingTime (2 ^ 13 * m + 2015) 13 ↔ 0 ≤ m := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_13_2015 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_13_2015 : oddCount 2015 13 = 8 ∧ acceleratedOrbit 13 2015 = 1615 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_13_2015 (m : Nat) :
    acceleratedOrbit 13 (2 ^ 13 * m + 2015) = 3 ^ 8 * m + 1615 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_13_2015.1, data_13_2015.2]

/-- Complete interval computation for depth 13, residue 2016. -/
theorem bounds_13_2016 : exactInterval 13 2016 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_13_2016 (m : Nat) :
    stoppingTime (2 ^ 13 * m + 2016) 13 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_13_2016 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_13_2016 : oddCount 2016 13 = 6 ∧ acceleratedOrbit 13 2016 = 182 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_13_2016 (m : Nat) :
    acceleratedOrbit 13 (2 ^ 13 * m + 2016) = 3 ^ 6 * m + 182 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_13_2016.1, data_13_2016.2]

end Collatz.Research.StoppingAtlas.Batch0598
