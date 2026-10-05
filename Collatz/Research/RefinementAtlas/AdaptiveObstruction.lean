import Collatz.Research.RefinementAtlas.Core

/-! A simultaneous returning witness defeats bounded adaptive horizons.
This theorem concerns ranks monotone inside each residue class. It does not
exclude unbounded stopping times, or ranks that genuinely decrease inside a class.
-/
namespace Collatz.Research.RefinementAtlas
/-- Positive odd-run witnesses, proved directly to keep this module small. -/
theorem power_run_value (j : Nat) (p : Nat) (hp : 0 < p) :
    acceleratedOrbit j (2 ^ j * p - 1) + 1 = 3 ^ j * p := by
  induction j generalizing p with
  | zero => simp; omega
  | succ j ih =>
    have ha : 0 < 2 ^ j * p := Nat.mul_pos (Arith.two_pow_pos j) hp
    have he : 2 ^ (j + 1) * p = 2 * (2 ^ j * p) := by
      rw [Arith.two_pow_succ, Nat.mul_assoc]
    have ho : (2 ^ (j + 1) * p - 1) % 2 ≠ 0 := by rw [he]; omega
    have hstep : acceleratedStep (2 ^ (j + 1) * p - 1) = 2 ^ j * (3 * p) - 1 := by
      rw [acceleratedStep, if_neg ho, he]
      have hm : 2 ^ j * (3 * p) = 3 * (2 ^ j * p) := by
        rw [← Nat.mul_assoc, Nat.mul_comm (2 ^ j) 3, Nat.mul_assoc]
      rw [hm]
      omega
    rw [acceleratedOrbit_succ, hstep, ih (3 * p) (by omega), Arith.three_pow_succ]
    rw [← Nat.mul_assoc, Nat.mul_comm (3 ^ j) 3, Nat.mul_assoc]

private theorem pred_mod_of_dvd {d x : Nat} (hd : 0 < d) (h : d ∣ x + 1) :
    x % d = d - 1 := by
  obtain ⟨c, hc⟩ := h
  have hpos : 0 < c := by
    by_cases hz : c = 0
    · simp [hz] at hc
    · omega
  have hx : x = d - 1 + d * (c - 1) := by
    have he : c = (c - 1) + 1 := by omega
    rw [he, Nat.mul_add, Nat.mul_one] at hc
    omega
  rw [hx, Nat.add_mul_mod_self_left, Nat.mod_eq_of_lt (by omega)]

private theorem two_pow_lt_three_pow (j : Nat) (hj : 0 < j) : 2 ^ j < 3 ^ j := by
  induction j with
  | zero => omega
  | succ j ih =>
    by_cases hz : j = 0
    · subst hz; decide
    · have hh := ih (by omega)
      rw [Arith.two_pow_succ, Arith.three_pow_succ]
      omega

/-- One positive integer grows and returns to its residue at every positive
horizon up to K. The extra factor two keeps the witness strictly above one. -/
theorem simultaneous_returns {m K : Nat} (hm : 0 < m) (hK : 0 < K) :
    ∃ n : Nat, 1 < n ∧ ∀ j : Nat, 0 < j → j ≤ K →
      n < acceleratedOrbit j n ∧ n % m = acceleratedOrbit j n % m := by
  let n := 2 ^ K * (2 * m) - 1
  have htwo : 2 ≤ 2 ^ K := Arith.two_le_two_pow hK
  have hsize : 4 ≤ 2 ^ K * (2 * m) := by
    have hh := Nat.mul_le_mul htwo (show 2 ≤ 2 * m by omega)
    omega
  have hn : n + 1 = 2 ^ K * (2 * m) := by dsimp [n]; omega
  refine ⟨n, by dsimp [n]; omega, ?_⟩
  intro j hj hjK
  have hsplit : n + 1 = 2 ^ ((K - j) + j) * (2 * m) := by
    rw [Nat.sub_add_cancel hjK]
    exact hn
  let p := 2 ^ (K - j) * (2 * m)
  have hp : 0 < p := Nat.mul_pos (Arith.two_pow_pos _) (by omega)
  have hn' : n + 1 = 2 ^ j * p := by
    rw [hsplit, Nat.pow_add]
    dsimp [p]
    rw [Nat.mul_comm (2 ^ (K - j)) (2 ^ j), Nat.mul_assoc]
  have heqn : n = 2 ^ j * p - 1 := by omega
  have hv : acceleratedOrbit j n + 1 = 3 ^ j * p := by
    rw [heqn]
    exact power_run_value j p hp
  have hlt := Nat.mul_lt_mul_of_pos_right (two_pow_lt_three_pow j hj) hp
  have hg : n < acceleratedOrbit j n := by omega
  have hd1 : m ∣ n + 1 := by
    refine ⟨2 ^ K * 2, ?_⟩
    rw [hn]
    simp [Nat.mul_comm, Nat.mul_assoc, Nat.mul_left_comm]
  have hd2 : m ∣ acceleratedOrbit j n + 1 := by
    refine ⟨3 ^ j * (2 ^ (K - j) * 2), ?_⟩
    rw [hv]
    dsimp [p]
    simp [Nat.mul_comm, Nat.mul_assoc, Nat.mul_left_comm]
  exact ⟨hg, by rw [pred_mod_of_dvd hm hd1, pred_mod_of_dvd hm hd2]⟩

/-- No bounded positive choice of horizon makes a rank decrease if the rank
is nondecreasing with size inside each residue class. The choice may inspect
the whole integer; it need not be determined by its residue. -/
theorem no_bounded_adaptive_rank {m K : Nat} (hm : 0 < m) (hK : 0 < K)
    (rank : Nat → Nat) (choose : Nat → Nat)
    (hchoose : ∀ n, 1 < n → 0 < choose n ∧ choose n ≤ K)
    (hmono : ∀ x y, x ≤ y → x % m = y % m → rank x ≤ rank y) :
    ¬ (∀ n, 1 < n → rank (acceleratedOrbit (choose n) n) < rank n) := by
  intro hdec
  obtain ⟨n, hn, hreturn⟩ := simultaneous_returns hm hK
  obtain ⟨hcpos, hcle⟩ := hchoose n hn
  obtain ⟨hg, hr⟩ := hreturn (choose n) hcpos hcle
  have hmrank := hmono n (acceleratedOrbit (choose n) n) (Nat.le_of_lt hg) hr
  have hd := hdec n hn
  omega

/-- A nonnegative linear height plus a residue correction is such a rank. -/
theorem no_affine_residue_adaptive_rank {m K : Nat} (hm : 0 < m) (hK : 0 < K)
    (a : Nat) (correction : Nat → Nat) (choose : Nat → Nat)
    (hchoose : ∀ n, 1 < n → 0 < choose n ∧ choose n ≤ K) :
    ¬ (∀ n, 1 < n →
      a * acceleratedOrbit (choose n) n + correction (acceleratedOrbit (choose n) n % m) <
        a * n + correction (n % m)) := by
  apply no_bounded_adaptive_rank hm hK (fun n => a * n + correction (n % m)) choose hchoose
  intro x y hxy hmod
  rw [hmod]
  exact Nat.add_le_add_right (Nat.mul_le_mul_left a hxy) _

end Collatz.Research.RefinementAtlas
