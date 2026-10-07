import Collatz.Exploration.BalancedCompact

/-! Explicit sub-six bands with long finite survivors. Widths depend on the
horizon; this does not classify a fixed width below six. -/
namespace Collatz.Exploration.BalancedNearSix
open BalancedResidue SixBandPrefixes BalancedOffset BalancedCompact

/-- A scaled positive margin persists when the denominator is enlarged. -/
theorem enlarge_margin {D A n x : Nat} (hD : 0 < D) (hDA : D ≤ A)
    (h : D*x+2*n ≤ 6*D*n) : A*x+2*n ≤ 6*A*n := by
  have hx : x ≤ 6*n := by
    apply Nat.le_of_mul_le_mul_left (c := D) _ hD
    have he : D*(6*n) = 6*D*n := by ac_rfl
    rw [he]
    omega
  let gap := 6*n-x
  have he : x+gap = 6*n := by dsimp [gap]; omega
  have hd : D*x+D*gap = 6*D*n := by rw [← Nat.mul_add, he]; ac_rfl
  have ha : A*x+A*gap = 6*A*n := by rw [← Nat.mul_add, he]; ac_rfl
  have hm := Nat.mul_le_mul_right gap hDA
  omega

/-- The integer coefficient gap leaves twice the source as a scaled peak margin. -/
theorem peak_margin {K n j : Nat} (hs : Safe K n) (hn : 2^K*(6*K+1) ≤ n)
    (hj : j < K) (ho : acceleratedOrbit j n % 2 = 1) :
    2^j*(3*acceleratedOrbit j n+1)+2*n ≤ 6*2^j*n := by
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
  have hgap := Nat.mul_le_mul_right n (show 3*C+3 ≤ 6*D by omega)
  rw [Nat.add_mul] at hgap
  have herr := Nat.mul_le_mul (show 3*C ≤ 6*D by omega) (show j ≤ K by omega)
  have he : (6*D)*K+D = D*(6*K+1) := by rw [Nat.mul_add, Nat.mul_one]; ac_rfl
  have hpow : D ≤ (2:Nat)^K := Nat.pow_le_pow_right (by decide) (by omega)
  have hbudget := Nat.mul_le_mul_right (6*K+1) hpow
  have hoff : (3*C)*j+D ≤ n := by rw [← he] at hbudget; omega
  change D*(3*acceleratedOrbit j n+1)+2*n ≤ 6*D*n
  omega

/-- Accelerated states have enough spare room for the same scaled margin. -/
theorem state_margin {K n j : Nat} (hs : Safe K n) (hn : 2^K*(6*K+1) ≤ n)
    (hj : j ≤ K) :
    2^K*acceleratedOrbit j n+2*n ≤ 6*2^K*n := by
  have hp : 0 < (2:Nat)^K := Nat.pow_pos (by decide)
  have hlarge := Nat.le_mul_of_pos_left (6*K+1) hp
  have hl := linear_prefix_bound hs hj
  have hx : acceleratedOrbit j n ≤ 4*n := by
    by_cases hz : j = 0
    · subst j; change n ≤ 4*n; omega
    · omega
  have hm := Nat.mul_le_mul_left (2^K) hx
  have hscale := Nat.le_mul_of_pos_left n hp
  have he : 2^K*(4*n) = 4*(2^K*n) := by ac_rfl
  rw [he] at hm
  have he2 : 6*2^K*n = 6*(2^K*n) := by ac_rfl
  rw [he2]
  omega

/-- Convert the retained margin to a rational band numerator. -/
theorem margin_band {A n x : Nat} (h : A*x+2*n ≤ 6*A*n) :
    A*x ≤ (6*A-2)*n := by
  rw [Nat.sub_mul]
  omega

/-- The same compact sources survive in width 6-2/2^K through the full duration. -/
theorem near_six_prefix {K n : Nat} (hs : Safe K n) (hn : 2^K*(6*K+1) ≤ n) :
    ∀ k, k ≤ K+oddCount n K → n ≤ orbit k n ∧
      2^K*orbit k n ≤ (6*2^K-2)*n := by
  let A := (2:Nat)^K
  let u := ((6*A-2)*n)/A
  have hA : 0 < A := Nat.pow_pos (by decide)
  have ha : ∀ j, j ≤ K → n ≤ acceleratedOrbit j n ∧ acceleratedOrbit j n ≤ u := by
    intro j hj
    refine ⟨heavy_lower (hs.1 j hj).1,?_⟩
    apply (Nat.le_div_iff_mul_le hA).mpr
    have hm := margin_band (state_margin hs hn hj)
    simpa only [Nat.mul_comm] using hm
  have peaks : ∀ j, j < K → acceleratedOrbit j n % 2 = 1 →
      3*acceleratedOrbit j n+1 ≤ u := by
    intro j hj ho
    apply (Nat.le_div_iff_mul_le hA).mpr
    have hd : 0 < (2:Nat)^j := Nat.pow_pos (by decide)
    have hDA : (2:Nat)^j ≤ A := Nat.pow_le_pow_right (by decide) (by omega)
    have hm := margin_band (enlarge_margin hd hDA (peak_margin hs hn hj ho))
    simpa only [Nat.mul_comm] using hm
  intro k hk
  obtain ⟨hl,hu⟩ := expanded_coverage K n u n ha peaks k hk
  refine ⟨hl,?_⟩
  have hm := (Nat.le_div_iff_mul_le hA).mp hu
  simpa only [Nat.mul_comm] using hm

/-- A quantitative family of strictly sub-six finite-prefix witnesses. -/
theorem near_six_witness (K N : Nat) :
    ∃ n, N < n ∧ 1 < n ∧ n ≤ 2^K*(N+6*K+4) ∧
      ∀ k, k ≤ K+(3*K+4)/5 → n ≤ orbit k n ∧
        2^K*orbit k n ≤ (6*2^K-2)*n := by
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
    exact near_six_prefix hsafe (by omega) k (by omega)

/-- No exit clock can beat these horizon-dependent narrower-band witnesses. -/
theorem no_near_six_clock (K : Nat) :
    ¬ BandClock.ExitClock (6*2^K-2) (2^K) (K+(3*K+4)/5) := by
  intro hc
  obtain ⟨n,_,hn,_,hp⟩ := near_six_witness K 0
  exact BandClock.no_band_through hc hn hp

/-- Any clock covering this duration must have width strictly below the witness width. -/
theorem clock_width_necessary {P Q H K : Nat} (hc : BandClock.ExitClock P Q H)
    (hH : H ≤ K+(3*K+4)/5) :
    P*2^K < (6*2^K-2)*Q := by
  by_cases hlt : P*2^K < (6*2^K-2)*Q
  · exact hlt
  have hcross : (6*2^K-2)*Q ≤ P*2^K := by omega
  have hnarrow := BandClock.narrower_ratio hc (Nat.pow_pos (by decide)) hcross
  obtain ⟨n,_,hn,_,hp⟩ := near_six_witness K 0
  exact False.elim (BandClock.no_band_through hnarrow hn (fun k hk => hp k (by omega)))

/-- A width deficit d/Q forces 2^K*d>2Q for every such finite clock. -/
theorem deficit_clock_necessary {Q d H K : Nat}
    (hd : d ≤ 6*Q) (hc : BandClock.ExitClock (6*Q-d) Q H)
    (hH : H ≤ K+(3*K+4)/5) : 2*Q < d*2^K := by
  have hw := clock_width_necessary hc hH
  rw [Nat.sub_mul, Nat.sub_mul] at hw
  have hq := Nat.mul_le_mul_right (2^K) hd
  have he : (6*Q)*2^K = (6*2^K)*Q := by ac_rfl
  rw [he] at hw hq
  omega

/-- Necessary width-deficit inequality stated directly in the ordinary clock duration. -/
theorem deficit_duration_necessary {Q d H : Nat}
    (hd : d ≤ 6*Q) (hc : BandClock.ExitClock (6*Q-d) Q H) :
    2*Q < d*2^((5*H+7)/8) := by
  apply deficit_clock_necessary hd hc
  omega

end Collatz.Exploration.BalancedNearSix
