import Collatz.Research.StoppingAtlas.Bridge

/-! First coefficient crossings can occur only after an even step. The resulting
power band explains forbidden exact stopping times without enumerating inputs. -/
namespace Collatz.Research.StoppingAtlas
open FirstLightDescent

/-- An odd step multiplies the coefficient by 3/2, so cannot be its first contraction. -/
theorem firstLight_last_even {n k : Nat} (hf : FirstLight n (k + 1)) :
    acceleratedOrbit k n % 2 = 0 := by
  have hprev := hf.2 k (by omega)
  have hlight := hf.1
  have hcount := Density.oddCount_succ_last n k
  rcases Arith.mod_two_eq_zero_or_one (acceleratedOrbit k n) with he | ho
  · exact he
  · have hc : oddCount n (k + 1) = oddCount n k + 1 := by omega
    rw [hc, Arith.three_pow_succ, Arith.two_pow_succ] at hlight
    omega

/-- A crossing at k+1 requires a power of three in the half-open band [2^k,2^(k+1)). -/
theorem firstLight_power_band {n k : Nat} (hf : FirstLight n (k + 1)) :
    2 ^ k ≤ 3 ^ oddCount n (k + 1) ∧ 3 ^ oddCount n (k + 1) < 2 ^ (k + 1) := by
  have he := firstLight_last_even hf
  have hc := Density.oddCount_succ_last n k
  have hp := hf.2 k (by omega)
  have hc' : oddCount n (k + 1) = oddCount n k := by omega
  exact ⟨by simpa only [hc'] using hp, hf.1⟩

/-- Missing powers in the band exclude first crossing for every input. -/
theorem no_firstLight_of_empty_band (k : Nat)
    (hgap : ∀ a : Fin (k + 2), ¬ (2 ^ k ≤ 3 ^ a.val ∧ 3 ^ a.val < 2 ^ (k + 1)))
    (n : Nat) : ¬ FirstLight n (k + 1) := by
  intro hf
  have hb := AffineExact.oddCount_le_self n (k + 1)
  exact hgap ⟨oddCount n (k + 1), by omega⟩ (firstLight_power_band hf)

/-- The all-empty depth-eleven census is forced by a power gap, not a sampling artifact. -/
theorem no_firstLight_eleven (n : Nat) : ¬ FirstLight n 11 :=
  no_firstLight_of_empty_band 10 (by decide) n

/-- No natural starting value has exact accelerated stopping time eleven. -/
theorem no_stopping_eleven (n : Nat) : ¬ stoppingTime n 11 := by
  intro hs
  have hn := CoefficientDescent.start_gt_one hs
  exact no_firstLight_eleven n ((stopping_iff_firstLight_le_1538 hn (by decide)).mp hs)

end Collatz.Research.StoppingAtlas
