import Collatz.Exploration.SixBandPrefixes

/-! Linear affine-offset control on balanced parity prefixes. -/
namespace Collatz.Exploration.BalancedOffset
open BalancedResidue SixBandPrefixes

/-- Heavy coefficients at every earlier time bound the normalized additive error. -/
theorem normalized_bound {K r : Nat}
    (heavy : ∀ i, i ≤ K → 2^i ≤ 3^oddCount r i) (j : Nat) (hj : j ≤ K) :
    2^j * acceleratedOrbit j r ≤ 3^oddCount r j * (r+j) := by
  induction j with
  | zero => simp [oddCount, parityVector]
  | succ j ih =>
    have hi := ih (by omega)
    have hheavy := heavy j (by omega)
    have hc := Density.oddCount_succ_last r j
    rw [acceleratedOrbit_succ_step]
    rcases Arith.mod_two_eq_zero_or_one (acceleratedOrbit j r) with he | ho
    · rw [he, Nat.add_zero] at hc
      rw [hc, Nat.pow_succ]
      have hx : 2 * acceleratedStep (acceleratedOrbit j r) = acceleratedOrbit j r := by
        simp only [acceleratedStep, he, ↓reduceIte]
        omega
      have heq : (2^j*2)*acceleratedStep (acceleratedOrbit j r) =
          2^j*acceleratedOrbit j r := by rw [Nat.mul_assoc, hx]
      rw [heq]
      have hm := Nat.mul_le_mul_left (3^oddCount r j) (show r+j ≤ r+(j+1) by omega)
      exact Nat.le_trans hi hm
    · rw [ho] at hc
      rw [hc, Nat.pow_succ, Nat.pow_succ]
      have hx : 2 * acceleratedStep (acceleratedOrbit j r) = 3*acceleratedOrbit j r+1 := by
        simp only [acceleratedStep, show acceleratedOrbit j r % 2 ≠ 0 by omega, ↓reduceIte]
        omega
      have heq : (2^j*2)*acceleratedStep (acceleratedOrbit j r) =
          3*(2^j*acceleratedOrbit j r)+2^j := by
        rw [Nat.mul_assoc, hx, Nat.mul_add, Nat.mul_one]
        ac_rfl
      rw [heq]
      have hm := Nat.mul_le_mul_left 3 hi
      have ht : (3^oddCount r j*3)*(r+(j+1)) =
          3*(3^oddCount r j*(r+j))+3*3^oddCount r j := by
        rw [show r+(j+1) = (r+j)+1 by omega, Nat.mul_add, Nat.mul_one]
        simp only [Nat.mul_comm, Nat.mul_left_comm]
      rw [ht]
      omega

/-- Balanced prefixes have a linear value bound, replacing exponential step growth. -/
theorem linear_prefix_bound {K r j : Nat} (hs : Safe K r) (hj : j ≤ K) :
    acceleratedOrbit j r < 3*(r+K+1) := by
  have hn := normalized_bound (fun i hi => (hs.1 i hi).1) j hj
  have hu := (hs.1 j hj).2
  have hm := Nat.mul_le_mul_right (r+j) (Nat.le_of_lt hu)
  have ht : (3*2^j)*(r+j) = 2^j*(3*(r+j)) := by ac_rfl
  rw [ht] at hm
  have hp : 0 < (2:Nat)^j := Nat.pow_pos (by decide)
  have hv : acceleratedOrbit j r ≤ 3*(r+j) :=
    Nat.le_of_mul_le_mul_left (Nat.le_trans hn hm) hp
  omega

/-- All sufficiently large members of a balanced residue class have the desired prefix. -/
theorem linear_class_prefix {K r m : Nat} (hr : r < 2^K) (hs : Safe K r)
    (hm : r+12*(r+K+1)+1 ≤ m) :
    ∀ k, k ≤ K+oddCount r K → 2^K*m+r ≤ orbit k (2^K*m+r) ∧
      orbit k (2^K*m+r) ≤ 6*(2^K*m+r) := by
  let n := 2^K*m+r
  have ha : ∀ j, j ≤ K → n ≤ acceleratedOrbit j n ∧ acceleratedOrbit j n ≤ 6*n := by
    intro j hj
    have hb := linear_prefix_bound hs hj
    have hsl := slope_bounds hs hj
    have ht := class_trace hj m r
    change acceleratedOrbit j n = _ at ht
    refine ⟨?_,?_⟩
    · by_cases hz : j = 0
      · subst j; exact Nat.le_refl n
      · have hl := gap_lower (slope_strict_lower hs hj (by omega)) (show r ≤ m by omega)
        rw [ht]
        exact Nat.le_trans hl (Nat.le_add_right _ _)
    · have hu := gap_upper hsl.2 (show acceleratedOrbit j r < m by omega)
      rw [ht]
      dsimp [n]
      have hmul : 3*(2^K*m) ≤ 6*(2^K*m+r) := by omega
      have hh : slope K r j*m+acceleratedOrbit j r < 3*(2^K*m) := by
        simpa only [Nat.mul_assoc] using hu
      omega
  have hp : ∀ j, j < K → acceleratedOrbit j n%2 = 1 → 3*acceleratedOrbit j n+1 ≤ 6*n := by
    intro j hj ho
    have hv := vector_class K m r hr
    have hb := bit_of_vector hv hj
    have hslope := slope_before_odd hs hj (hb.symm.trans ho)
    have hraw := Nat.mul_lt_mul_of_pos_left hslope (show 0 < 3 by decide)
    have hcoef : 3*slope K r j < 6*2^K := by simpa only [← Nat.mul_assoc, Nat.reduceMul] using hraw
    have hc := linear_prefix_bound hs (Nat.le_of_lt hj)
    have hu := gap_upper hcoef (show 3*acceleratedOrbit j r+1 < m by omega)
    have ht := class_trace (Nat.le_of_lt hj) m r
    change acceleratedOrbit j n = _ at ht
    rw [ht]
    dsimp [n]
    have heq : 3*(slope K r j*m+acceleratedOrbit j r)+1 =
        (3*slope K r j)*m+(3*acceleratedOrbit j r+1) := by
      simp only [Nat.mul_add, Nat.mul_assoc, Nat.add_assoc]
    rw [heq]
    have hh : (3*slope K r j)*m+(3*acceleratedOrbit j r+1) < 6*(2^K*m) := by
      simpa only [Nat.mul_assoc] using hu
    omega
  have hc := counts_of_vector (vector_class K m r hr) K (by omega)
  intro k hk
  exact expanded_coverage K n (6*n) n ha hp k (by dsimp [n]; omega)


/-- An elementary estimate converts the linear horizon term to a square modulus. -/
theorem horizon_le_modulus (K : Nat) : K+1 ≤ (2:Nat)^K := by
  induction K with
  | zero => decide
  | succ K ih => rw [Nat.pow_succ]; omega

/-- The improved representative has size O(4^K), rather than O(8^K). -/
theorem square_size {K r : Nat} (hr : r < 2^K) :
    2^K*(r+12*(r+K+1)+2)+r ≤ 28*4^K := by
  let a := (2:Nat)^K
  have ha : 1 ≤ a := Nat.one_le_pow K 2 (by decide)
  have hk := horizon_le_modulus K
  have hb : r+12*(r+K+1)+2 ≤ 27*a := by dsimp [a]; omega
  have hm := Nat.mul_le_mul_left a hb
  have hr2 : r ≤ a*a := Nat.le_trans (show r ≤ a by dsimp [a]; omega)
    (Nat.le_mul_of_pos_left a (by omega))
  have hp : (4:Nat)^K = a*a := by
    dsimp [a]
    rw [show (4:Nat) = 2*2 from rfl, Nat.mul_pow]
  have he : a*(27*a) = 27*(a*a) := by ac_rfl
  rw [he] at hm
  change a*(r+12*(r+K+1)+2)+r ≤ 28*4^K
  rw [hp]
  omega

/-- Smaller witnesses retain the full expanded ordinary-time survival duration. -/
theorem square_quantitative_prefixes (K N : Nat) :
    ∃ n, N < n ∧ 1 < n ∧ n ≤ 2^K*N+28*4^K ∧
      ∀ k, k ≤ K+(3*K+4)/5 → n ≤ orbit k n ∧ orbit k n ≤ 6*n := by
  obtain ⟨r,hr,hs⟩ := exists_safe K
  let m := N+r+12*(r+K+1)+2
  let n := 2^K*m+r
  have hp : 0 < (2:Nat)^K := Nat.pow_pos (by decide)
  have hlarge : m ≤ n := Nat.le_trans (Nat.le_mul_of_pos_left m hp) (Nat.le_add_right _ _)
  have hsize := square_size hr
  have he : n = 2^K*N+(2^K*(r+12*(r+K+1)+2)+r) := by
    dsimp [n,m]
    simp only [Nat.mul_add]
    omega
  have hclock := safe_clock_lower hs
  refine ⟨n,Nat.lt_of_lt_of_le ?_ hlarge,Nat.lt_of_lt_of_le ?_ hlarge,?_,?_⟩
  · dsimp [m]; omega
  · dsimp [m]; omega
  · rw [he]; omega
  · intro k hk
    exact linear_class_prefix hr hs (by dsimp [m]; omega) k (by omega)

/-- A finite domain of square-modulus size already defeats the stated exit clock. -/
theorem square_domain_obstruction (K B : Nat) (hB : 28*4^K ≤ B) :
    ¬ (∀ n, 1 < n → n ≤ B → ∃ k, k ≤ K+(3*K+4)/5 ∧
      (orbit k n < n ∨ 6*n < orbit k n)) := by
  intro hc
  obtain ⟨n,_,hn,hsize,hprefix⟩ := square_quantitative_prefixes K 0
  have hnsize : n ≤ 28*4^K := by simpa using hsize
  obtain ⟨k,hk,hexit⟩ := hc n hn (Nat.le_trans hnsize hB)
  obtain ⟨hl,hu⟩ := hprefix k hk
  rcases hexit with h | h <;> omega

end Collatz.Exploration.BalancedOffset
