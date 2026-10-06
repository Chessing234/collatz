import Collatz.Accelerated

/-!
# Obstruction to residue-monotone descent heights

For any modulus M > 0 and any finite horizon B, there are arbitrarily large
positive integers whose first B iterates all have the same residue modulo M
as the start, and are strictly larger than the start at every positive time.
The witness is M*q*2^(B+1)-1. Consequently a height increasing within each
residue class cannot furnish a universally bounded descent schedule.

The same-modulus returning family already appears in AnyModulusRanking.
Here it is strengthened to a whole rising run, arbitrary cutoffs, and heights
that need not be constant on residue classes. It does not
exclude unbounded stopping schedules or heights that decrease within a class.
No historical novelty is asserted.
-/

namespace Collatz.ResidueMonotoneObstruction

/-- Exact all-odd run with an arbitrary positive multiplier. -/
theorem orbit_mul_pow_pred (q k : Nat) (hq : 0 < q) :
    ∀ i, i ≤ k →
      acceleratedOrbit i (q * 2^k - 1) = q * 3^i * 2^(k-i) - 1 := by
  intro i
  induction i generalizing q k with
  | zero => simp
  | succ i ih =>
    intro hik
    have hp : 0 < q * 2^(k-1) := Nat.mul_pos hq (Nat.pow_pos (by decide))
    have he : 2^k = 2^(k-1)*2 := by
      rw [← Nat.pow_succ]
      congr 1
      omega
    have hs : acceleratedStep (q*2^k-1) = (q*3)*2^(k-1)-1 := by
      rw [he]
      have hm : q*(2^(k-1)*2) = 2*(q*2^(k-1)) := by
        simp [Nat.mul_comm, Nat.mul_left_comm]
      have ht : q*3*2^(k-1) = 3*(q*2^(k-1)) := by
        simp [Nat.mul_comm, Nat.mul_left_comm, Nat.mul_assoc]
      rw [hm, ht]
      simp only [acceleratedStep]
      rw [if_neg (by omega : ¬(2*(q*2^(k-1))-1)%2=0)]
      omega
    rw [acceleratedOrbit_succ, hs, ih (q*3) (k-1) (by omega) (by omega)]
    have hk : k-1-i = k-(i+1) := by omega
    rw [hk, Nat.pow_succ]
    simp [Nat.mul_comm, Nat.mul_left_comm, Nat.mul_assoc]

/-- Multiples minus one all represent the same residue. -/
theorem mul_pred_mod (M q : Nat) (hM : 0 < M) (hq : 0 < q) :
    (M*q-1)%M = M-1 := by
  have he : M*q-1 = M*(q-1)+(M-1) := by
    have hp : M*(q-1)+M = M*q := by
      rw [← Nat.mul_succ]
      congr 1
      omega
    omega
  rw [he, Nat.add_mod, Nat.mul_mod_right, Nat.zero_add,
    Nat.mod_eq_of_lt (by omega : M-1<M)]
  exact Nat.mod_eq_of_lt (by omega)

/-- A whole finite run grows while staying in one residue class. -/
theorem same_residue_rising_run (M q B : Nat) (hM : 0 < M) (hq : 0 < q) :
    ∀ i, 0 < i → i ≤ B →
      M*q*2^(B+1)-1 < acceleratedOrbit i (M*q*2^(B+1)-1) ∧
      acceleratedOrbit i (M*q*2^(B+1)-1)%M = (M*q*2^(B+1)-1)%M := by
  intro i hi hiB
  rw [orbit_mul_pow_pred (M*q) (B+1) (Nat.mul_pos hM hq) i (by omega)]
  have hp : 0 < M*q*2^(B+1-i) :=
    Nat.mul_pos (Nat.mul_pos hM hq) (Nat.pow_pos (by decide))
  have he : 2^(B+1) = 2^i*2^(B+1-i) := by
    rw [← Nat.pow_add]
    congr 1
    omega
  constructor
  · have hlt : (2:Nat)^i < 3^i := Nat.pow_lt_pow_left (by decide) (by omega)
    have hm := Nat.mul_lt_mul_of_pos_left hlt hp
    have ha : 0 < M*q*2^(B+1) :=
      Nat.mul_pos (Nat.mul_pos hM hq) (Nat.pow_pos (by decide))
    rw [he] at ha ⊢
    have hc : M*q*(2^i*2^(B+1-i)) < M*q*3^i*2^(B+1-i) := by
      simpa [Nat.mul_comm, Nat.mul_left_comm, Nat.mul_assoc] using hm
    omega
  · have ha : 0 < q*3^i*2^(B+1-i) :=
      Nat.mul_pos (Nat.mul_pos hq (Nat.pow_pos (by decide))) (Nat.pow_pos (by decide))
    have hb : 0 < q*2^(B+1) := Nat.mul_pos hq (Nat.pow_pos (by decide))
    simpa only [Nat.mul_assoc] using
      (mul_pred_mod M (q*3^i*2^(B+1-i)) hM ha).trans
        (mul_pred_mod M (q*2^(B+1)) hM hb).symm

/-- Arbitrarily large witnesses; finite exceptional starting ranges do not help. -/
theorem arbitrarily_large_rising_run (M B cutoff : Nat) (hM : 0 < M) :
    ∃ n, cutoff < n ∧ 1 < n ∧ ∀ i, 0 < i → i ≤ B →
      n < acceleratedOrbit i n ∧ acceleratedOrbit i n % M = n % M := by
  refine ⟨M*(cutoff+3)*2^(B+1)-1, ?_, ?_,
    same_residue_rising_run M (cutoff+3) B hM (by omega)⟩
  all_goals
    have hm : cutoff+3 ≤ M*(cutoff+3) := by
      simpa using Nat.mul_le_mul_right (cutoff+3) hM
    have hp : 1 ≤ (2:Nat)^(B+1) := Nat.one_le_pow _ _ (by decide)
    have ht : M*(cutoff+3) ≤ M*(cutoff+3)*2^(B+1) := by
      simpa using Nat.mul_le_mul_left (M*(cutoff+3)) hp
    omega

/-- A height is residue-monotone if it increases with size inside each class.
No relation is required between heights in different classes. -/
def ResidueMonotone (M : Nat) (height : Nat → Nat) : Prop :=
  ∀ x y, x < y → x % M = y % M → height x < height y

/-- No finite horizon works for a residue-monotone height, even eventually. -/
theorem no_bounded_height_descent (M B cutoff : Nat) (hM : 0 < M)
    (height : Nat → Nat) (hheight : ResidueMonotone M height) :
    ¬ (∀ n, cutoff < n → 1 < n → ∃ i, 0 < i ∧ i ≤ B ∧
      height (acceleratedOrbit i n) < height n) := by
  intro h
  obtain ⟨n, hcut, hn, hrun⟩ := arbitrarily_large_rising_run M B cutoff hM
  obtain ⟨i, hi, hiB, hd⟩ := h n hcut hn
  obtain ⟨hg, hr⟩ := hrun i hi hiB
  have := hheight n (acceleratedOrbit i n) hg hr.symm
  omega

/-- Residue-dependent positive linear slopes and arbitrary natural offsets
are included, even if crossing residue classes changes the height abruptly. -/
theorem affine_height_residue_monotone (M : Nat) (slope offset : Nat → Nat)
    (hpos : ∀ r, 0 < slope r) :
    ResidueMonotone M (fun n => slope (n%M)*n + offset (n%M)) := by
  intro x y hxy hr
  change slope (x%M)*x + offset (x%M) < slope (y%M)*y + offset (y%M)
  rw [hr]
  exact Nat.add_lt_add_right (Nat.mul_lt_mul_of_pos_left hxy (hpos _)) _

/-- A finite table of possible stopping lengths cannot evade the obstruction
by choosing a different entry for each starting value. -/
theorem no_finite_menu_descent (M cutoff : Nat) (hM : 0 < M)
    (height : Nat → Nat) (hheight : ResidueMonotone M height)
    (menu : List Nat) :
    ¬ (∀ n, cutoff < n → 1 < n → ∃ i, i ∈ menu ∧ 0 < i ∧
      height (acceleratedOrbit i n) < height n) := by
  intro h
  apply no_bounded_height_descent M menu.sum cutoff hM height hheight
  intro n hcut hn
  obtain ⟨i, him, hi, hd⟩ := h n hcut hn
  refine ⟨i, hi, ?_, hd⟩
  clear h hheight hd hcut hn
  induction menu with
  | nil => simp at him
  | cons a rest ih =>
    simp only [List.mem_cons] at him
    simp only [List.sum_cons]
    rcases him with rfl | hm
    · omega
    · have := ih hm
      omega

/-- Only eventual nondecrease within residue classes is needed. This includes
class-constant ranks as well as increasing ranks, and permits arbitrary
behavior on the finite exceptional range up to the cutoff. -/
theorem no_eventual_nondecreasing_height_descent (M B cutoff : Nat) (hM : 0 < M)
    (height : Nat → Nat)
    (hheight : ∀ x y, cutoff < x → x ≤ y → x%M = y%M → height x ≤ height y) :
    ¬ (∀ n, cutoff < n → 1 < n → ∃ i, 0 < i ∧ i ≤ B ∧
      height (acceleratedOrbit i n) < height n) := by
  intro h
  obtain ⟨n, hcut, hn, hrun⟩ := arbitrarily_large_rising_run M B cutoff hM
  obtain ⟨i, hi, hiB, hd⟩ := h n hcut hn
  obtain ⟨hg, hr⟩ := hrun i hi hiB
  have := hheight n (acceleratedOrbit i n) hcut (Nat.le_of_lt hg) hr.symm
  omega

end Collatz.ResidueMonotoneObstruction
