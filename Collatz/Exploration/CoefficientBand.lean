import Collatz.Exploration.BalancedCompact

/-! Finite coefficient ceilings transfer to infinite residue classes in any
rational band with a positive coefficient margin. -/
namespace Collatz.Exploration.CoefficientBand
open BalancedResidue SixBandPrefixes BalancedOffset BalancedCompact

def TraceBounds (R Q K n C D : Nat) : Prop :=
  (∀ j, j ≤ K → D*2^j ≤ C*3^oddCount n j ∧
    Q*(C*3^oddCount n j) ≤ R*(D*2^j)) ∧
  (∀ j, j < K → acceleratedOrbit j n % 2 = 1 →
    3*Q*(C*3^oddCount n j) ≤ R*(D*2^j))

/-- Linear-time coefficient checker; no arithmetic search or trusted evaluator. -/
def coefficientCheck (R Q : Nat) : Nat → Nat → Nat → Nat → Bool
  | 0,_n,C,D => decide (D ≤ C ∧ Q*C ≤ R*D)
  | K+1,n,C,D =>
    decide (D ≤ C ∧ Q*C ≤ R*D ∧ (n%2=1 → 3*Q*C ≤ R*D)) &&
    coefficientCheck R Q K (acceleratedStep n) (if n%2=0 then C else 3*C) (2*D)

/-- Every checker row has its actual homogeneous coefficient and actual parity. -/
theorem checker_sound {R Q K n C D : Nat}
    (h : coefficientCheck R Q K n C D = true) : TraceBounds R Q K n C D := by
  induction K generalizing n C D with
  | zero =>
    have h0 : D ≤ C ∧ Q*C ≤ R*D := by simpa [coefficientCheck] using h
    constructor
    · intro j hj
      have hz : j = 0 := by omega
      subst j
      simpa only [Congruence.oddCount_zero, Nat.pow_zero, Nat.mul_one] using h0
    · intro j hj; omega
  | succ K ih =>
    have hh : (D ≤ C ∧ Q*C ≤ R*D ∧ (n%2=1 → 3*Q*C ≤ R*D)) ∧
        coefficientCheck R Q K (acceleratedStep n) (if n%2=0 then C else 3*C) (2*D) = true := by
      simpa only [coefficientCheck, Bool.and_eq_true, decide_eq_true_eq] using h
    have ht := ih hh.2
    constructor
    · intro j hj
      cases j with
      | zero =>
        simpa only [Congruence.oddCount_zero, Nat.pow_zero, Nat.mul_one] using
          (show D ≤ C ∧ Q*C ≤ R*D from ⟨hh.1.1,hh.1.2.1⟩)
      | succ j =>
        have hb := ht.1 j (by omega)
        rcases Arith.mod_two_eq_zero_or_one n with he | ho
        · simp only [he, ↓reduceIte] at hb
          rw [Congruence.oddCount_succ_of_even he]
          simpa only [Nat.pow_succ, Nat.mul_assoc, Nat.mul_left_comm, Nat.mul_comm] using hb
        · simp only [show n%2 ≠ 0 by omega, ↓reduceIte] at hb
          rw [Congruence.oddCount_succ_of_odd ho]
          simpa only [Nat.pow_succ, Nat.mul_assoc, Nat.mul_left_comm, Nat.mul_comm] using hb
    · intro j hj hodd
      cases j with
      | zero =>
        have h0 : n%2=1 := hodd
        simpa only [Congruence.oddCount_zero, Nat.pow_zero, Nat.mul_one] using hh.1.2.2 h0
      | succ j =>
        change acceleratedOrbit j (acceleratedStep n)%2=1 at hodd
        have hb := ht.2 j (by omega) hodd
        rcases Arith.mod_two_eq_zero_or_one n with he | ho
        · simp only [he, ↓reduceIte] at hb
          rw [Congruence.oddCount_succ_of_even he]
          simpa only [Nat.pow_succ, Nat.mul_assoc, Nat.mul_left_comm, Nat.mul_comm] using hb
        · simp only [show n%2 ≠ 0 by omega, ↓reduceIte] at hb
          rw [Congruence.oddCount_succ_of_odd ho]
          simpa only [Nat.pow_succ, Nat.mul_assoc, Nat.mul_left_comm, Nat.mul_comm] using hb

/-- Bounds transfer with the finite parity word, including every odd-peak ceiling. -/
theorem trace_of_vector {R Q K n r : Nat} (hv : parityVector n K = parityVector r K)
    (ht : TraceBounds R Q K r 1 1) : TraceBounds R Q K n 1 1 := by
  constructor
  · intro j hj
    rw [counts_of_vector hv j hj]
    exact ht.1 j hj
  · intro j hj ho
    rw [counts_of_vector hv j (by omega)]
    exact ht.2 j hj ((bit_of_vector hv hj).symm.trans ho)

/-- A positive rational coefficient gap absorbs the complete additive error. -/
theorem absorb_offset {D A R G Q K n j y : Nat} (hD : 0 < D) (hj : j ≤ K)
    (hy : D*y ≤ A*(n+j)+D) (hcoef : Q*A ≤ R*D)
    (hbudget : R*K+Q ≤ G*n) : Q*y ≤ (R+G)*n := by
  have hyQ := Nat.mul_le_mul_left Q hy
  have hmain := Nat.mul_le_mul_right n hcoef
  have herr := Nat.mul_le_mul hcoef hj
  have hpay := Nat.mul_le_mul_left D hbudget
  have he0 : Q*(D*y) = D*(Q*y) := by ac_rfl
  have he1 : Q*(A*(n+j)+D) = (Q*A)*n+(Q*A)*j+D*Q := by
    simp only [Nat.mul_add]
    ac_rfl
  have he2 : D*(R*K+Q) = (R*D)*K+D*Q := by rw [Nat.mul_add]; ac_rfl
  have he3 : D*(G*n) = (G*D)*n := by ac_rfl
  have he4 : D*((R+G)*n) = (R*D)*n+(G*D)*n := by rw [Nat.add_mul, Nat.mul_add]; ac_rfl
  rw [he0,he1] at hyQ
  rw [he2,he3] at hpay
  apply Nat.le_of_mul_le_mul_left (c := D) _ hD
  rw [he4]
  omega

/-- A certified coefficient ceiling gives the full ordinary rational band prefix. -/
theorem profile_prefix {R Q G K n : Nat} (ht : TraceBounds R Q K n 1 1)
    (hQ : 0 < Q) (hbudget : R*K+Q ≤ G*n) :
    ∀ k, k ≤ K+oddCount n K → n ≤ orbit k n ∧ Q*orbit k n ≤ (R+G)*n := by
  have heavy : ∀ j, j ≤ K → 2^j ≤ 3^oddCount n j := by
    intro j hj
    simpa only [Nat.one_mul] using (ht.1 j hj).1
  let u := ((R+G)*n)/Q
  have states : ∀ j, j ≤ K → n ≤ acceleratedOrbit j n ∧ acceleratedOrbit j n ≤ u := by
    intro j hj
    refine ⟨heavy_lower (heavy j hj),?_⟩
    have hnorm := normalized_bound heavy j hj
    have hcoef : Q*3^oddCount n j ≤ R*2^j := by simpa only [Nat.one_mul] using (ht.1 j hj).2
    have hu := absorb_offset (Nat.pow_pos (by decide)) hj (Nat.le_trans hnorm (Nat.le_add_right _ _)) hcoef hbudget
    apply (Nat.le_div_iff_mul_le hQ).mpr
    simpa only [Nat.mul_comm] using hu
  have peaks : ∀ j, j < K → acceleratedOrbit j n%2=1 → 3*acceleratedOrbit j n+1 ≤ u := by
    intro j hj ho
    have hnorm := Nat.mul_le_mul_left 3 (normalized_bound heavy j (by omega))
    have he0 : 2^j*(3*acceleratedOrbit j n+1) = 3*(2^j*acceleratedOrbit j n)+2^j := by
      rw [Nat.mul_add, Nat.mul_one]; ac_rfl
    have he1 : (3*3^oddCount n j)*(n+j) = 3*(3^oddCount n j*(n+j)) := by ac_rfl
    have hraw : 2^j*(3*acceleratedOrbit j n+1) ≤ (3*3^oddCount n j)*(n+j)+2^j := by
      rw [he0,he1]; omega
    have hcoef : Q*(3*3^oddCount n j) ≤ R*2^j := by
      have hb := ht.2 j hj ho
      simpa only [Nat.one_mul, Nat.mul_comm, Nat.mul_left_comm, Nat.mul_assoc] using hb
    have hu := absorb_offset (Nat.pow_pos (by decide)) (Nat.le_of_lt hj) hraw hcoef hbudget
    apply (Nat.le_div_iff_mul_le hQ).mpr
    simpa only [Nat.mul_comm] using hu
  intro k hk
  obtain ⟨hl,hu⟩ := expanded_coverage K n u n states peaks k hk
  refine ⟨hl,?_⟩
  have hm := (Nat.le_div_iff_mul_le hQ).mp hu
  simpa only [Nat.mul_comm] using hm

/-- Every sufficiently large representative of a certified parity class survives. -/
theorem certified_class_prefix {R Q G K r m : Nat} (hr : r < 2^K)
    (hc : coefficientCheck R Q K r 1 1 = true) (hQ : 0 < Q) (hG : 0 < G)
    (hm : R*K+Q ≤ m) :
    ∀ k, k ≤ K+oddCount r K → 2^K*m+r ≤ orbit k (2^K*m+r) ∧
      Q*orbit k (2^K*m+r) ≤ (R+G)*(2^K*m+r) := by
  have hv := vector_class K m r hr
  have ht := trace_of_vector hv (checker_sound hc)
  have hp : 0 < (2:Nat)^K := Nat.pow_pos (by decide)
  have hlarge := Nat.le_trans (Nat.le_mul_of_pos_left m hp) (Nat.le_add_right (2^K*m) r)
  have hpay := Nat.le_mul_of_pos_left (2^K*m+r) hG
  have hbudget : R*K+Q ≤ G*(2^K*m+r) := Nat.le_trans hm (Nat.le_trans hlarge hpay)
  have hcount := counts_of_vector hv K (by omega)
  intro k hk
  exact profile_prefix ht hQ hbudget k (by omega)

/-- A finite coefficient certificate implies an unbounded family of explicit witnesses. -/
theorem certified_witness {R Q G K r : Nat} (hr : r < 2^K)
    (hc : coefficientCheck R Q K r 1 1 = true) (hQ : 0 < Q) (hG : 0 < G) (N : Nat) :
    ∃ n, N < n ∧ 1 < n ∧ n ≤ 2^K*(N+R*K+Q+3) ∧
      ∀ k, k ≤ K+oddCount r K → n ≤ orbit k n ∧ Q*orbit k n ≤ (R+G)*n := by
  let m := N+R*K+Q+2
  let n := 2^K*m+r
  have hp : 0 < (2:Nat)^K := Nat.pow_pos (by decide)
  have hl := Nat.le_mul_of_pos_left m hp
  refine ⟨n,by dsimp [n,m] at *; omega,by dsimp [n,m] at *; omega,?_,?_⟩
  · dsimp [n,m]
    rw [show N+R*K+Q+3 = (N+R*K+Q+2)+1 by omega]
    simp only [Nat.mul_add, Nat.mul_one]
    omega
  · exact certified_class_prefix hr hc hQ hG (by dsimp [m]; omega)

/-- A linear-time parity count for auditing long finite certificates. -/
def prefixOdds : Nat → Nat → Nat
  | 0,_ => 0
  | K+1,n => n%2+prefixOdds K (acceleratedStep n)

theorem prefixOdds_eq (K n : Nat) : prefixOdds K n = oddCount n K := by
  induction K generalizing n with
  | zero => simp [prefixOdds]
  | succ K ih =>
    rw [prefixOdds, ih]
    rcases Arith.mod_two_eq_zero_or_one n with he | ho
    · rw [Congruence.oddCount_succ_of_even he, he]; omega
    · rw [Congruence.oddCount_succ_of_odd ho, ho]; omega

end Collatz.Exploration.CoefficientBand
