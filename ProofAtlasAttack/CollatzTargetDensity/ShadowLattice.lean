import CollatzTargetDensity.ShadowOscillation

/-! Bounded shadows cannot approach any fixed rational lattice. The result
allows completely nonperiodic choices of lattice points. -/
namespace CollatzTargetDensity.ShadowLattice
open Erdos1135 OrbitReciprocals InverseBoundary BoundaryLinearization ShadowOscillation
noncomputable section

/-- Finite form of the denominator obstruction. -/
theorem integer_block_dvd (L : ℕ) (a b : ℕ → ℕ)
    (ha : ∀ i < L, 1 ≤ a i)
    (hstep : ∀ i < L, 2 ^ a i * b (i + 1) = 3 * b i) : 2 ^ L ∣ b 0 := by
  induction L generalizing a b with
  | zero => simp
  | succ L ih =>
    have ht := ih (fun i => a (i + 1)) (fun i => b (i + 1))
      (fun i hi => ha (i + 1) (by omega))
      (fun i hi => hstep (i + 1) (by omega))
    have htwo : (2 : ℕ) ∣ 2 ^ a 0 := by
      simpa using (pow_dvd_pow 2 (ha 0 (by omega)) : (2 : ℕ) ^ 1 ∣ 2 ^ a 0)
    have hm := Nat.mul_dvd_mul ht htwo
    rw [← pow_succ, Nat.mul_comm (b 1), hstep 0 (by omega)] at hm
    exact ((by decide : Nat.Coprime 2 3).pow_left (L + 1)).dvd_of_dvd_mul_left hm

/-- Integer multiplicative coordinates cannot stay positive forever. -/
theorem no_integer_multiplicative_orbit (a b : ℕ → ℕ) (hb : 0 < b 0)
    (ha : ∀ i, 1 ≤ a i) (hstep : ∀ i, 2 ^ a i * b (i + 1) = 3 * b i) : False := by
  have hdiv (j : ℕ) : ∀ i, 2 ^ j ∣ b i := by
    induction j with
    | zero => intro i; simp
    | succ j ih =>
      intro i
      have htwo : (2 : ℕ) ∣ 2 ^ a i := by
        simpa using (pow_dvd_pow 2 (ha i) : (2 : ℕ) ^ 1 ∣ 2 ^ a i)
      have hm := Nat.mul_dvd_mul (ih (i + 1)) htwo
      rw [← pow_succ, Nat.mul_comm (b (i + 1)), hstep i] at hm
      exact ((by decide : Nat.Coprime 2 3).pow_left (j + 1)).dvd_of_dvd_mul_left hm
  have hle := Nat.le_of_dvd hb (hdiv (b 0) 0)
  have hlt := Nat.lt_two_pow_self (n := b 0)
  omega

/-- An approximate rational-grid recurrence becomes an exact integer
recurrence once its residual is less than one. -/
theorem integer_relation_of_approx {c q m r : ℕ} {u v ε C : ℝ}
    (hs : (c : ℝ) * v = 3 * u - q) (hc : (c : ℝ) ≤ C)
    (hε : 0 < ε) (hbudget : (C + 3) * ε < 1)
    (hu : |u - (m : ℝ)| < ε) (hv : |v - (r : ℝ)| < ε) :
    c * r + q = 3 * m := by
  have he : (((c * r + q : ℕ) : ℝ) - ((3 * m : ℕ) : ℝ)) =
      (c : ℝ) * ((r : ℝ) - v) + 3 * (u - (m : ℝ)) := by
    push_cast
    nlinarith
  have hv' : |(r : ℝ) - v| < ε := by simpa only [abs_sub_comm] using hv
  have hd : |((c * r + q : ℕ) : ℝ) - ((3 * m : ℕ) : ℝ)| < 1 := by
    rw [he]
    calc
      _ ≤ |(c : ℝ) * ((r : ℝ) - v)| + |3 * (u - (m : ℝ))| := abs_add_le _ _
      _ = (c : ℝ) * |(r : ℝ) - v| + 3 * |u - (m : ℝ)| := by
        rw [abs_mul, abs_mul, abs_of_nonneg (Nat.cast_nonneg c), abs_of_pos (by norm_num : (0 : ℝ) < 3)]
      _ < (c : ℝ) * ε + 3 * ε :=
        add_lt_add_of_le_of_lt (mul_le_mul_of_nonneg_left hv'.le (Nat.cast_nonneg c))
          (mul_lt_mul_of_pos_left hu (by norm_num))
      _ ≤ (C + 3) * ε := by
        have h := mul_le_mul_of_nonneg_right hc hε.le
        nlinarith
      _ < 1 := hbudget
  have hl : c * r + q < 3 * m + 1 := by
    exact_mod_cast (show ((c * r + q : ℕ) : ℝ) < ((3 * m : ℕ) : ℝ) + 1 by
      have := (abs_lt.mp hd).2; linarith)
  have hr : 3 * m < c * r + q + 1 := by
    exact_mod_cast (show ((3 * m : ℕ) : ℝ) < ((c * r + q : ℕ) : ℝ) + 1 by
      have := (abs_lt.mp hd).1; linarith)
  omega

/-- A finite shadow near a fixed rational grid has a logarithmic length
barrier. This theorem uses only the displayed finite integer and real
recurrences; it assumes no infinite orbit, summability, or Collatz conjecture. -/
theorem finite_grid_barrier (L : ℕ) (a x m : ℕ → ℕ) (E : ℕ → ℝ)
    {q : ℕ} (hq : 0 < q) (hx0 : 0 < x 0) {M : ℝ} (hM : 1 ≤ M)
    (ha : ∀ i < L, 1 ≤ a i)
    (hplus : ∀ i < L, 2 ^ a i * x (i + 1) = 3 * x i + 1)
    (hminus : ∀ i < L, (2 : ℝ) ^ a i * E (i + 1) = 3 * E i - 1)
    (hlow : ∀ i ≤ L, 1 ≤ E i) (hupp : ∀ i ≤ L, E i ≤ M)
    (happrox : ∀ i ≤ L, |(q : ℝ) * E i - (m i : ℝ)| < 1 / (6 * (M + 1))) :
    (2 : ℝ) ^ L < (q : ℝ) * ((x 0 : ℝ) + M) + 1 := by
  let b (i : ℕ) : ℕ := q * x i + m i
  have hε : (0 : ℝ) < 1 / (6 * (M + 1)) := by positivity
  have hεone : (1 / (6 * (M + 1)) : ℝ) < 1 := by
    apply (div_lt_iff₀ (by linarith : (0 : ℝ) < 6 * (M + 1))).2
    linarith
  have hbudget : (3 * M + 3) * (1 / (6 * (M + 1))) < 1 := by
    rw [mul_one_div]
    apply (div_lt_iff₀ (by linarith : (0 : ℝ) < 6 * (M + 1))).2
    linarith
  have hstep (i : ℕ) (hi : i < L) : 2 ^ a i * b (i + 1) = 3 * b i := by
    have hs := hminus i hi
    have hl := hlow (i + 1) (by omega)
    have hu := hupp i (by omega)
    have hc : ((2 ^ a i : ℕ) : ℝ) ≤ 3 * M := by
      push_cast
      have hp : (0 : ℝ) ≤ 2 ^ a i := by positivity
      have hh := mul_le_mul_of_nonneg_left hl hp
      nlinarith
    have hscaled : ((2 ^ a i : ℕ) : ℝ) * ((q : ℝ) * E (i + 1)) =
        3 * ((q : ℝ) * E i) - q := by
      push_cast
      have hh := congrArg (fun t : ℝ => (q : ℝ) * t) hs
      nlinarith
    have hg := integer_relation_of_approx hscaled hc hε hbudget
      (happrox i (by omega)) (happrox (i + 1) (by omega))
    have hxq := congrArg (fun t : ℕ => q * t) (hplus i hi)
    dsimp [b]
    nlinarith
  have hb : 0 < b 0 := by
    have hp := Nat.mul_pos hq hx0
    dsimp [b]
    omega
  have hd := Nat.le_of_dvd hb (integer_block_dvd L a b ha hstep)
  have hdR : (2 : ℝ) ^ L ≤ (b 0 : ℝ) := by exact_mod_cast hd
  have hm := (abs_lt.mp (happrox 0 (by omega))).1
  have hqM := mul_le_mul_of_nonneg_left (hupp 0 (by omega)) (Nat.cast_nonneg q : (0 : ℝ) ≤ q)
  have hupper : (b 0 : ℝ) < (q : ℝ) * ((x 0 : ℝ) + M) + 1 := by
    dsimp [b]
    push_cast
    nlinarith
  exact hdR.trans_lt hupper

theorem not_uniform_lattice_approximation {n : ℕ} (hn : Odd n)
    (hi : Function.Injective (orbit n)) {M : ℝ} (hM : 1 ≤ M)
    (hbound : ∀ k, shadow (orbit n k) ≤ M) {q : ℕ} (hq : 0 < q) :
    ¬ ∀ k, ∃ m : ℕ, |(q : ℝ) * shadow (orbit n k) - (m : ℝ)| < 1 / (6 * (M + 1)) := by
  intro h
  choose m hm using h
  let b (k : ℕ) : ℕ := q * orbit n k + m k
  have hε : (0 : ℝ) < 1 / (6 * (M + 1)) := by positivity
  have hbudget : (3 * M + 3) * (1 / (6 * (M + 1))) < 1 := by
    rw [mul_one_div]
    apply (div_lt_iff₀ (by linarith : (0 : ℝ) < 6 * (M + 1))).2
    linarith
  have hstep (k : ℕ) : 2 ^ Tao.syracuseExponent (orbit n k) * b (k + 1) = 3 * b k := by
    have hs := shadow_step (orbit_pos hn.pos k) (injective_shift hi k)
    rw [orbit_succ] at hs
    have hl := shadow_ge_one (orbit_odd hn (k + 1)) (injective_shift hi (k + 1))
    have hb := hbound k
    have hc : ((2 ^ Tao.syracuseExponent (orbit n k) : ℕ) : ℝ) ≤ 3 * M := by
      push_cast
      have hp : (0 : ℝ) ≤ 2 ^ Tao.syracuseExponent (orbit n k) := by positivity
      have hh := mul_le_mul_of_nonneg_left hl hp
      nlinarith
    have hscaled : ((2 ^ Tao.syracuseExponent (orbit n k) : ℕ) : ℝ) *
        ((q : ℝ) * shadow (orbit n (k + 1))) = 3 * ((q : ℝ) * shadow (orbit n k)) - q := by
      push_cast
      have hh := congrArg (fun t : ℝ => (q : ℝ) * t) hs
      nlinarith
    have hg := integer_relation_of_approx hscaled hc hε hbudget (hm k) (hm (k + 1))
    have hx := Tao.two_pow_syracuseExponent_mul_syracuse (orbit n k)
    rw [orbit_succ] at hx
    have hxq := congrArg (fun t : ℕ => q * t) hx
    dsimp [b]
    nlinarith
  apply no_integer_multiplicative_orbit (fun k => Tao.syracuseExponent (orbit n k)) b
    (by
      have hp := Nat.mul_pos hq (orbit_pos hn.pos 0)
      dsimp [b]
      omega)
    (fun k => Tao.syracuseExponent_pos_of_odd (orbit_odd hn k)) hstep

/-- Every tail contains a shadow value a definite distance from the entire
fixed rational grid. In units of E the separation is 1/(6q(M+1)). -/
theorem rational_lattice_separation {n : ℕ} (hn : Odd n)
    (hi : Function.Injective (orbit n)) {M : ℝ} (hM : 1 ≤ M)
    (hbound : ∀ k, shadow (orbit n k) ≤ M) {q : ℕ} (hq : 0 < q) (N : ℕ) :
    ∃ k ≥ N, ∀ m : ℕ, 1 / (6 * (M + 1)) ≤ |(q : ℝ) * shadow (orbit n k) - (m : ℝ)| := by
  by_contra! h
  apply not_uniform_lattice_approximation (orbit_odd hn N) (injective_shift hi N) hM
    (fun k => by simpa only [orbit_shift] using hbound (k + N)) hq
  intro k
  simpa only [orbit_shift] using h (k + N) (by omega)

end
end CollatzTargetDensity.ShadowLattice
