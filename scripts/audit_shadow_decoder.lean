import Collatz.Strategy.ShadowDecoder

open Collatz.ShadowDecoder

#print axioms fits_unique
#print axioms evenFits_unique
#print axioms approximation_fits
#print axioms closed_tolerance_ambiguous
#print axioms encode_ge_one
#print axioms encode_exact
#print axioms encode_fits
#print axioms even_block_dvd
#print axioms certificate_dvd
#print axioms certificate_unique

-- A rounded rational certificate for 7 -> 11 -> 17 -> 13 -> 5 -> 1.
-- These are samples with nonzero residuals, not an infinite-orbit assumption.
example :
    EvenFits 2 (986/100) (1429/100) ∧
    EvenFits 2 (1429/100) (2093/100) ∧
    EvenFits 4 (2093/100) (1545/100) ∧
    EvenFits 8 (1545/100) (567/100) ∧
    EvenFits 16 (567/100) 1 := by
  unfold EvenFits
  grind (splits := 32)

example : 2*11=3*7+1 ∧ 2*17=3*11+1 ∧ 4*13=3*17+1 ∧
    8*5=3*13+1 ∧ 16*1=3*5+1 := by decide
