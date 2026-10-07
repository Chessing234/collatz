import Collatz.Exploration.BalancedOffset
import Collatz.Structure.AffineBound

/-! Applying normalized error control directly to the large representative
retains its contribution to the band bound instead of discarding it. -/
namespace Collatz.Exploration.BalancedCompact
open BalancedResidue SixBandPrefixes BalancedOffset

/-- Balanced parity safety depends only on the finite parity word. -/
theorem safe_of_vector {K n r : Nat} (hv : parityVector n K = parityVector r K)
    (hs : Safe K r) : Safe K n := by
  constructor
  · intro j hj
    rw [counts_of_vector hv j hj]
    exact hs.1 j hj
  · intro j hj ho
    rw [counts_of_vector hv j (by omega)]
    exact hs.2 j hj ((bit_of_vector hv hj).symm.trans ho)

/-- Heavy coefficients guarantee no descent, including their nonnegative offsets. -/
theorem heavy_lower {j n : Nat} (hh : 2^j ≤ 3^oddCount n j) :
    n ≤ acceleratedOrbit j n := by
  obtain ⟨b,he,_⟩ := AffineBound.exists_affine_bounded n j
  have hm := Nat.mul_le_mul_right n hh
  have hp : 0 < (2:Nat)^j := Nat.pow_pos (by decide)
  have hf : 2^j*n ≤ 2^j*acceleratedOrbit j n := by omega
  exact Nat.le_of_mul_le_mul_left hf hp

/-- A linear multiple of the parity modulus absorbs every ordinary odd peak. -/
theorem compact_prefix {K n : Nat} (hs : Safe K n) (hn : 2^K*(6*K+1) ≤ n) :
    ∀ k, k ≤ K+oddCount n K → n ≤ orbit k n ∧ orbit k n ≤ 6*n := by
  have ha : ∀ j, j ≤ K → n ≤ acceleratedOrbit j n ∧ acceleratedOrbit j n ≤ 6*n := by
    intro j hj
    refine ⟨heavy_lower (hs.1 j hj).1,?_⟩
    have hl := linear_prefix_bound hs hj
    have hK : K+1 ≤ n := by
      have hp : 0 < (2:Nat)^K := Nat.pow_pos (by decide)
      have hm := Nat.le_mul_of_pos_left (6*K+1) hp
      omega
    omega
  have peaks : ∀ j, j < K → acceleratedOrbit j n % 2 = 1 →
      3*acceleratedOrbit j n+1 ≤ 6*n := by
    intro j hj ho
    let D := (2:Nat)^j
    let C := 3^oddCount n j
    have hC : C < 2*D := hs.2 j hj ho
    have hnorm := normalized_bound (fun i hi => (hs.1 i hi).1) j (by omega)
    change D*acceleratedOrbit j n ≤ C*(n+j) at hnorm
    have hmul := Nat.mul_le_mul_left 3 hnorm
    have hnorm2 : D*(3*acceleratedOrbit j n+1) ≤ (3*C)*n+((3*C)*j+D) := by
      have hleft : D*(3*acceleratedOrbit j n+1) = 3*(D*acceleratedOrbit j n)+D := by
        rw [Nat.mul_add, Nat.mul_one]
        ac_rfl
      have hright : 3*(C*(n+j))+D = (3*C)*n+((3*C)*j+D) := by
        simp only [Nat.mul_add, Nat.mul_assoc, Nat.add_assoc]
      rw [hleft, ← hright]
      omega
    have hcoef : 3*C < 6*D := by omega
    have hgap := gap_lower hcoef (Nat.le_refl n)
    have herr := Nat.mul_le_mul (show 3*C ≤ 6*D by omega) (show j ≤ K by omega)
    have he : (6*D)*K+D = D*(6*K+1) := by
      rw [Nat.mul_add, Nat.mul_one]
      ac_rfl
    have hpow : D ≤ (2:Nat)^K := Nat.pow_le_pow_right (by decide) (by omega)
    have hbudget := Nat.mul_le_mul_right (6*K+1) hpow
    have hoff : (3*C)*j+D ≤ n := by rw [← he] at hbudget; omega
    have hr : (6*D)*n = D*(6*n) := by ac_rfl
    rw [hr] at hgap
    have htotal : D*(3*acceleratedOrbit j n+1) ≤ D*(6*n) := by omega
    exact Nat.le_of_mul_le_mul_left htotal (Nat.pow_pos (by decide))
  exact expanded_coverage K n (6*n) n ha peaks

/-- Witness-size growth needs only a linear factor times 2^K. -/
theorem compact_quantitative_prefixes (K N : Nat) :
    ∃ n, N < n ∧ 1 < n ∧ n ≤ 2^K*(N+6*K+4) ∧
      ∀ k, k ≤ K+(3*K+4)/5 → n ≤ orbit k n ∧ orbit k n ≤ 6*n := by
  obtain ⟨r,hr,hs⟩ := exists_safe K
  let n := 2^K*(N+6*K+3)+r
  have hp : 0 < (2:Nat)^K := Nat.pow_pos (by decide)
  have hl := Nat.le_mul_of_pos_left (N+6*K+3) hp
  have hv := vector_class K (N+6*K+3) r hr
  have hsafe := safe_of_vector hv hs
  have hbudget := Nat.mul_le_mul_left (2^K) (show 6*K+1 ≤ N+6*K+3 by omega)
  have hc := safe_clock_lower hsafe
  refine ⟨n,by dsimp [n]; omega,by dsimp [n]; omega,?_,?_⟩
  · dsimp [n]
    rw [show N+6*K+4 = (N+6*K+3)+1 by omega]
    simp only [Nat.mul_add, Nat.mul_one]
    omega
  · intro k hk
    exact compact_prefix hsafe (by omega) k (by omega)

/-- A compact witness for every prescribed ordinary duration. -/
theorem compact_duration_witness (H N : Nat) :
    ∃ n, N < n ∧ 1 < n ∧
      n ≤ 2^((5*H+7)/8)*(N+6*((5*H+7)/8)+4) ∧
      ∀ k, k ≤ H → n ≤ orbit k n ∧ orbit k n ≤ 6*n := by
  obtain ⟨n,hN,hn,hsize,hprefix⟩ := compact_quantitative_prefixes ((5*H+7)/8) N
  refine ⟨n,hN,hn,hsize,?_⟩
  intro k hk
  apply hprefix k
  omega

/-- The improved finite-domain obstruction retains the expanded duration. -/
theorem compact_domain_obstruction (K B : Nat) (hB : 2^K*(6*K+4) ≤ B) :
    ¬ (∀ n, 1 < n → n ≤ B → ∃ k, k ≤ K+(3*K+4)/5 ∧
      (orbit k n < n ∨ 6*n < orbit k n)) := by
  intro hc
  obtain ⟨n,_,hn,hsize,hprefix⟩ := compact_quantitative_prefixes K 0
  have hnsize : n ≤ 2^K*(6*K+4) := by simpa using hsize
  obtain ⟨k,hk,hexit⟩ := hc n hn (Nat.le_trans hnsize hB)
  obtain ⟨hl,hu⟩ := hprefix k hk
  rcases hexit with h | h <;> omega

end Collatz.Exploration.BalancedCompact
