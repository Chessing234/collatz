import Collatz.Research.DescentIntervals.Classifier

namespace Collatz.Research.PassageAtlas.Batch0062

open Collatz.Research.DescentIntervals

set_option maxRecDepth 20000
set_option maxHeartbeats 0

/-- Complete interval computation for depth 15, residue 1998. -/
theorem bounds_15_1998 : exactInterval 15 1998 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_1998 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 1998) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_1998 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_1998 : oddCount 1998 15 = 7 ∧ acceleratedOrbit 15 1998 = 134 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_1998 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 1998) = 3 ^ 7 * m + 134 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_1998.1, data_15_1998.2]

/-- Complete interval computation for depth 15, residue 1999. -/
theorem bounds_15_1999 : exactInterval 15 1999 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_1999 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 1999) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_1999 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_1999 : oddCount 1999 15 = 7 ∧ acceleratedOrbit 15 1999 = 134 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_1999 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 1999) = 3 ^ 7 * m + 134 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_1999.1, data_15_1999.2]

/-- Complete interval computation for depth 15, residue 2000. -/
theorem bounds_15_2000 : exactInterval 15 2000 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_2000 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 2000) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_2000 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_2000 : oddCount 2000 15 = 7 ∧ acceleratedOrbit 15 2000 = 137 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_2000 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 2000) = 3 ^ 7 * m + 137 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_2000.1, data_15_2000.2]

/-- Complete interval computation for depth 15, residue 2001. -/
theorem bounds_15_2001 : exactInterval 15 2001 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_2001 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 2001) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_2001 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_2001 : oddCount 2001 15 = 8 ∧ acceleratedOrbit 15 2001 = 404 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_2001 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 2001) = 3 ^ 8 * m + 404 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_2001.1, data_15_2001.2]

/-- Complete interval computation for depth 15, residue 2002. -/
theorem bounds_15_2002 : exactInterval 15 2002 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_2002 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 2002) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_2002 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_2002 : oddCount 2002 15 = 11 ∧ acceleratedOrbit 15 2002 = 10844 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_2002 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 2002) = 3 ^ 11 * m + 10844 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_2002.1, data_15_2002.2]

/-- Complete interval computation for depth 15, residue 2003. -/
theorem bounds_15_2003 : exactInterval 15 2003 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_2003 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 2003) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_2003 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_2003 : oddCount 2003 15 = 11 ∧ acceleratedOrbit 15 2003 = 10844 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_2003 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 2003) = 3 ^ 11 * m + 10844 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_2003.1, data_15_2003.2]

/-- Complete interval computation for depth 15, residue 2004. -/
theorem bounds_15_2004 : exactInterval 15 2004 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_2004 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 2004) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_2004 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_2004 : oddCount 2004 15 = 7 ∧ acceleratedOrbit 15 2004 = 137 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_2004 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 2004) = 3 ^ 7 * m + 137 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_2004.1, data_15_2004.2]

/-- Complete interval computation for depth 15, residue 2005. -/
theorem bounds_15_2005 : exactInterval 15 2005 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_2005 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 2005) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_2005 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_2005 : oddCount 2005 15 = 7 ∧ acceleratedOrbit 15 2005 = 137 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_2005 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 2005) = 3 ^ 7 * m + 137 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_2005.1, data_15_2005.2]

/-- Complete interval computation for depth 15, residue 2006. -/
theorem bounds_15_2006 : exactInterval 15 2006 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_2006 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 2006) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_2006 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_2006 : oddCount 2006 15 = 9 ∧ acceleratedOrbit 15 2006 = 1208 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_2006 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 2006) = 3 ^ 9 * m + 1208 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_2006.1, data_15_2006.2]

/-- Complete interval computation for depth 15, residue 2007. -/
theorem bounds_15_2007 : exactInterval 15 2007 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_2007 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 2007) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_2007 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_2007 : oddCount 2007 15 = 9 ∧ acceleratedOrbit 15 2007 = 1208 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_2007 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 2007) = 3 ^ 9 * m + 1208 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_2007.1, data_15_2007.2]

/-- Complete interval computation for depth 15, residue 2008. -/
theorem bounds_15_2008 : exactInterval 15 2008 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_2008 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 2008) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_2008 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_2008 : oddCount 2008 15 = 10 ∧ acceleratedOrbit 15 2008 = 3644 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_2008 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 2008) = 3 ^ 10 * m + 3644 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_2008.1, data_15_2008.2]

/-- Complete interval computation for depth 15, residue 2009. -/
theorem bounds_15_2009 : exactInterval 15 2009 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_2009 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 2009) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_2009 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_2009 : oddCount 2009 15 = 4 ∧ acceleratedOrbit 15 2009 = 5 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_2009 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 2009) = 3 ^ 4 * m + 5 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_2009.1, data_15_2009.2]

/-- Complete interval computation for depth 15, residue 2010. -/
theorem bounds_15_2010 : exactInterval 15 2010 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_2010 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 2010) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_2010 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_2010 : oddCount 2010 15 = 10 ∧ acceleratedOrbit 15 2010 = 3644 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_2010 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 2010) = 3 ^ 10 * m + 3644 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_2010.1, data_15_2010.2]

/-- Complete interval computation for depth 15, residue 2011. -/
theorem bounds_15_2011 : exactInterval 15 2011 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_2011 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 2011) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_2011 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_2011 : oddCount 2011 15 = 9 ∧ acceleratedOrbit 15 2011 = 1210 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_2011 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 2011) = 3 ^ 9 * m + 1210 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_2011.1, data_15_2011.2]

/-- Complete interval computation for depth 15, residue 2012. -/
theorem bounds_15_2012 : exactInterval 15 2012 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_2012 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 2012) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_2012 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_2012 : oddCount 2012 15 = 10 ∧ acceleratedOrbit 15 2012 = 3644 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_2012 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 2012) = 3 ^ 10 * m + 3644 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_2012.1, data_15_2012.2]

/-- Complete interval computation for depth 15, residue 2013. -/
theorem bounds_15_2013 : exactInterval 15 2013 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_2013 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 2013) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_2013 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_2013 : oddCount 2013 15 = 10 ∧ acceleratedOrbit 15 2013 = 3644 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_2013 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 2013) = 3 ^ 10 * m + 3644 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_2013.1, data_15_2013.2]

/-- Complete interval computation for depth 15, residue 2014. -/
theorem bounds_15_2014 : exactInterval 15 2014 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_2014 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 2014) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_2014 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_2014 : oddCount 2014 15 = 10 ∧ acceleratedOrbit 15 2014 = 3635 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_2014 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 2014) = 3 ^ 10 * m + 3635 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_2014.1, data_15_2014.2]

/-- Complete interval computation for depth 15, residue 2015. -/
theorem bounds_15_2015 : exactInterval 15 2015 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_2015 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 2015) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_2015 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_2015 : oddCount 2015 15 = 10 ∧ acceleratedOrbit 15 2015 = 3635 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_2015 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 2015) = 3 ^ 10 * m + 3635 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_2015.1, data_15_2015.2]

/-- Complete interval computation for depth 15, residue 2016. -/
theorem bounds_15_2016 : exactInterval 15 2016 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_2016 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 2016) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_2016 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_2016 : oddCount 2016 15 = 7 ∧ acceleratedOrbit 15 2016 = 137 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_2016 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 2016) = 3 ^ 7 * m + 137 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_2016.1, data_15_2016.2]

/-- Complete interval computation for depth 15, residue 2017. -/
theorem bounds_15_2017 : exactInterval 15 2017 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_2017 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 2017) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_2017 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_2017 : oddCount 2017 15 = 10 ∧ acceleratedOrbit 15 2017 = 3640 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_2017 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 2017) = 3 ^ 10 * m + 3640 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_2017.1, data_15_2017.2]

/-- Complete interval computation for depth 15, residue 2018. -/
theorem bounds_15_2018 : exactInterval 15 2018 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_2018 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 2018) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_2018 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_2018 : oddCount 2018 15 = 7 ∧ acceleratedOrbit 15 2018 = 137 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_2018 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 2018) = 3 ^ 7 * m + 137 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_2018.1, data_15_2018.2]

/-- Complete interval computation for depth 15, residue 2019. -/
theorem bounds_15_2019 : exactInterval 15 2019 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_2019 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 2019) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_2019 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_2019 : oddCount 2019 15 = 7 ∧ acceleratedOrbit 15 2019 = 137 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_2019 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 2019) = 3 ^ 7 * m + 137 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_2019.1, data_15_2019.2]

/-- Complete interval computation for depth 15, residue 2020. -/
theorem bounds_15_2020 : exactInterval 15 2020 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_2020 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 2020) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_2020 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_2020 : oddCount 2020 15 = 8 ∧ acceleratedOrbit 15 2020 = 407 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_2020 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 2020) = 3 ^ 8 * m + 407 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_2020.1, data_15_2020.2]

/-- Complete interval computation for depth 15, residue 2021. -/
theorem bounds_15_2021 : exactInterval 15 2021 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_2021 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 2021) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_2021 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_2021 : oddCount 2021 15 = 8 ∧ acceleratedOrbit 15 2021 = 407 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_2021 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 2021) = 3 ^ 8 * m + 407 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_2021.1, data_15_2021.2]

/-- Complete interval computation for depth 15, residue 2022. -/
theorem bounds_15_2022 : exactInterval 15 2022 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_2022 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 2022) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_2022 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_2022 : oddCount 2022 15 = 8 ∧ acceleratedOrbit 15 2022 = 407 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_2022 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 2022) = 3 ^ 8 * m + 407 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_2022.1, data_15_2022.2]

/-- Complete interval computation for depth 15, residue 2023. -/
theorem bounds_15_2023 : exactInterval 15 2023 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_2023 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 2023) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_2023 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_2023 : oddCount 2023 15 = 9 ∧ acceleratedOrbit 15 2023 = 1217 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_2023 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 2023) = 3 ^ 9 * m + 1217 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_2023.1, data_15_2023.2]

/-- Complete interval computation for depth 15, residue 2024. -/
theorem bounds_15_2024 : exactInterval 15 2024 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_2024 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 2024) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_2024 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_2024 : oddCount 2024 15 = 7 ∧ acceleratedOrbit 15 2024 = 137 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_2024 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 2024) = 3 ^ 7 * m + 137 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_2024.1, data_15_2024.2]

/-- Complete interval computation for depth 15, residue 2025. -/
theorem bounds_15_2025 : exactInterval 15 2025 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_2025 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 2025) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_2025 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_2025 : oddCount 2025 15 = 10 ∧ acceleratedOrbit 15 2025 = 3653 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_2025 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 2025) = 3 ^ 10 * m + 3653 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_2025.1, data_15_2025.2]

/-- Complete interval computation for depth 15, residue 2026. -/
theorem bounds_15_2026 : exactInterval 15 2026 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_2026 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 2026) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_2026 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_2026 : oddCount 2026 15 = 7 ∧ acceleratedOrbit 15 2026 = 137 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_2026 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 2026) = 3 ^ 7 * m + 137 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_2026.1, data_15_2026.2]

/-- Complete interval computation for depth 15, residue 2027. -/
theorem bounds_15_2027 : exactInterval 15 2027 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_2027 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 2027) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_2027 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_2027 : oddCount 2027 15 = 9 ∧ acceleratedOrbit 15 2027 = 1219 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_2027 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 2027) = 3 ^ 9 * m + 1219 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_2027.1, data_15_2027.2]

/-- Complete interval computation for depth 15, residue 2028. -/
theorem bounds_15_2028 : exactInterval 15 2028 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_2028 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 2028) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_2028 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_2028 : oddCount 2028 15 = 7 ∧ acceleratedOrbit 15 2028 = 136 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_2028 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 2028) = 3 ^ 7 * m + 136 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_2028.1, data_15_2028.2]

/-- Complete interval computation for depth 15, residue 2029. -/
theorem bounds_15_2029 : exactInterval 15 2029 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_2029 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 2029) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_2029 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_2029 : oddCount 2029 15 = 7 ∧ acceleratedOrbit 15 2029 = 136 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_2029 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 2029) = 3 ^ 7 * m + 136 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_2029.1, data_15_2029.2]

/-- Complete interval computation for depth 15, residue 2030. -/
theorem bounds_15_2030 : exactInterval 15 2030 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_2030 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 2030) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_2030 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_2030 : oddCount 2030 15 = 7 ∧ acceleratedOrbit 15 2030 = 136 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_2030 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 2030) = 3 ^ 7 * m + 136 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_2030.1, data_15_2030.2]

end Collatz.Research.PassageAtlas.Batch0062
