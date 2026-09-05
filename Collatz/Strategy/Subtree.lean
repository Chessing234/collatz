import Collatz.Strategy.TreeBranching

/-!
# Subtree counts rooted at an arbitrary fertile node

For a root `a` and a bound `Y`, `S a Y` counts the odd `n ≤ Y` prime to `3`
whose accelerated orbit hits `a` within `Y` steps.  The recursion
`S_rec` bounds `S a Y` below by the sum of the subtree counts of the six
fertile children `fch a i`, via `TreeBranching.family_count` with the identity
maps: the images are disjoint because no `n` can reach two distinct children
of a node `a ≥ 5` that reaches `1` (`no_common_subtree`).
-/

namespace Collatz
namespace Subtree

open TreeCount TreeBranching Collatz.Sum Papers.KrasikovLagarias2003

/-! ## 1. Reaching a target within a step budget -/

/-- `reachesBy n a B = true` iff the orbit of `n` hits `a` within `B` steps. -/
def reachesBy (n a : Nat) : Nat → Bool
  | 0 => decide (acceleratedOrbit 0 n = a)
  | B + 1 => reachesBy n a B || decide (acceleratedOrbit (B + 1) n = a)

theorem reachesBy_of_orbit {n a j : Nat} (h : acceleratedOrbit j n = a) :
    ∀ B, j ≤ B → reachesBy n a B = true := by
  intro B
  induction B with
  | zero =>
    intro hj
    have hj0 : j = 0 := by omega
    subst hj0
    show decide (acceleratedOrbit 0 n = a) = true
    exact decide_eq_true h
  | succ B ih =>
    intro hj
    show (reachesBy n a B || decide (acceleratedOrbit (B + 1) n = a)) = true
    rw [Bool.or_eq_true]
    by_cases hjB : j ≤ B
    · left; exact ih hjB
    · right
      have : j = B + 1 := by omega
      subst this
      exact decide_eq_true h

theorem reachesBy_iff (n a : Nat) : ∀ B,
    reachesBy n a B = true ↔ ∃ j, j ≤ B ∧ acceleratedOrbit j n = a := by
  intro B
  constructor
  · induction B with
    | zero =>
      intro h
      exact ⟨0, Nat.le_refl 0, of_decide_eq_true h⟩
    | succ B ih =>
      intro h
      have h' : (reachesBy n a B || decide (acceleratedOrbit (B + 1) n = a)) = true := h
      rw [Bool.or_eq_true] at h'
      rcases h' with h' | h'
      · obtain ⟨j, hj, hj1⟩ := ih h'
        exact ⟨j, by omega, hj1⟩
      · exact ⟨B + 1, Nat.le_refl _, of_decide_eq_true h'⟩
  · intro ⟨j, hj, hj1⟩
    exact reachesBy_of_orbit hj1 B hj

theorem reachesBy_mono {n a B B' : Nat} (h : B ≤ B') (hB : reachesBy n a B = true) :
    reachesBy n a B' = true := by
  obtain ⟨j, hj, hj1⟩ := (reachesBy_iff n a B).1 hB
  exact reachesBy_of_orbit hj1 B' (Nat.le_trans hj h)

theorem reachesBy_trans {n b a B v : Nat} (hb : reachesBy n b B = true)
    (hv : acceleratedOrbit v b = a) : reachesBy n a (B + v) = true := by
  obtain ⟨j, hj, hj1⟩ := (reachesBy_iff n b B).1 hb
  apply reachesBy_of_orbit (j := v + j)
  · rw [← acceleratedOrbit_add, hj1, hv]
  · omega

/-! ## 2. The subtree count -/

/-- The number of fertile `n ≤ Y` reaching `a` within `Y` steps. -/
def S (a Y : Nat) : Nat := countUpTo (fun n => TreeCount.Good n ∧ reachesBy n a Y = true) Y

theorem S_mono {a Y Y' : Nat} (h : Y ≤ Y') : S a Y ≤ S a Y' := by
  unfold S
  apply Nat.le_trans (countUpTo_le_of_le (p := fun n => Good n ∧ reachesBy n a Y = true) h)
  apply countUpTo_mono
  intro n _ _ ⟨hg, hr⟩
  exact ⟨hg, reachesBy_mono h hr⟩

theorem S_pos {a Y : Nat} (ha : TreeCount.Good a) (hY : a ≤ Y) : 1 ≤ S a Y := by
  unfold S
  apply le_countUpTo_of_inj (g := fun _ => a)
  · intro _ _; have := ha.1; omega
  · intro _ _; exact hY
  · intro _ _
    exact ⟨ha, reachesBy_of_orbit (acceleratedOrbit_zero a) Y (Nat.zero_le _)⟩
  · intro i j hi hj _; omega

/-! ## 3. Periodic points that reach `1` -/

theorem orbit_one (j : Nat) : acceleratedOrbit j 1 = 1 ∨ acceleratedOrbit j 1 = 2 := by
  induction j with
  | zero => left; rfl
  | succ j ih =>
    rw [acceleratedOrbit_succ_step]
    rcases ih with h | h
    · rw [h]; right; decide
    · rw [h]; left; decide

theorem orbit_mul_periodic {a s : Nat} (hper : acceleratedOrbit s a = a) :
    ∀ u, acceleratedOrbit (s * u) a = a := by
  intro u
  induction u with
  | zero => rw [Nat.mul_zero]; rfl
  | succ u ih =>
    rw [Nat.mul_add, Nat.mul_one, ← acceleratedOrbit_add, hper, ih]

theorem eq_one_or_two_of_periodic {a s t : Nat} (hs : 1 ≤ s) (hper : acceleratedOrbit s a = a)
    (ht : acceleratedOrbit t a = 1) : a = 1 ∨ a = 2 := by
  have h1 := orbit_mul_periodic hper t
  have hle : t ≤ s * t := by
    have := Nat.mul_le_mul_right t hs
    rw [Nat.one_mul] at this
    exact this
  have h2 := acceleratedOrbit_add (s * t - t) t a
  rw [ht, Nat.sub_add_cancel hle, h1] at h2
  rw [← h2]
  exact orbit_one _

/-- Two arrivals at `a` at different times make `a` periodic. -/
theorem periodic_of_two_arrivals {c a p q : Nat} (hp : acceleratedOrbit p c = a)
    (hq : acceleratedOrbit q c = a) (hpq : p < q) : acceleratedOrbit (q - p) a = a := by
  have h := acceleratedOrbit_add (q - p) p c
  rw [hp, Nat.sub_add_cancel (Nat.le_of_lt hpq), hq] at h
  exact h

/-! ## 4. The ray from a child back to its parent -/

theorem fch_ne_self {a i : Nat} (ha : TreeCount.Good a) (h5 : 5 ≤ a) :
    TreeBranching.fch a i ≠ a := by
  intro h
  have h3 := three_fch ha i
  rw [h] at h3
  have hv := fval_pos a i
  rcases Nat.lt_or_ge (fval a i) 2 with hlt | hge
  · have : fval a i = 1 := by omega
    rw [this, Nat.pow_one] at h3
    omega
  · have hp : 2 ^ 2 ≤ 2 ^ fval a i := Nat.pow_le_pow_right (by decide) hge
    have h4 : 2 ^ 2 * a ≤ 2 ^ fval a i * a := Nat.mul_le_mul_right a hp
    have e : (2:Nat) ^ 2 = 4 := rfl
    rw [e] at h4
    omega

theorem step_fch {a : Nat} (ha : Good a) (i : Nat) :
    acceleratedStep (fch a i) = 2 ^ (fval a i - 1) * a := by
  have h3 := three_fch ha i
  have hodd := (fch_good ha i).1
  have hv := fval_pos a i
  obtain ⟨w, hw⟩ : ∃ w, fval a i = w + 1 := ⟨fval a i - 1, by omega⟩
  rw [hw] at h3
  rw [hw, Nat.add_sub_cancel, acceleratedStep, if_neg (by omega)]
  have hm := two_pow_succ_mul w a
  omega

/-- After `w + 1 ≤ fval a i` steps the child sits at `2 ^ (fval a i − w − 1) · a`. -/
theorem orbit_fch_ray {a : Nat} (ha : Good a) (i w : Nat) (hw : w + 1 ≤ fval a i) :
    acceleratedOrbit (w + 1) (fch a i) = 2 ^ (fval a i - (w + 1)) * a := by
  rw [acceleratedOrbit_succ, step_fch ha i]
  have e : fval a i - 1 = w + (fval a i - (w + 1)) := by omega
  rw [e, Nat.pow_add, Nat.mul_assoc]
  exact ReverseTree.orbit_two_pow_mul w _

/-! ## 5. Disjointness of the children's subtrees -/

theorem no_common_aux {a n i j t ti tj : Nat} (ha : Good a) (h5 : 5 ≤ a)
    (h1 : acceleratedOrbit t a = 1) (hij : i ≠ j) (hle : ti ≤ tj)
    (hi : acceleratedOrbit ti n = fch a i) (hj : acceleratedOrbit tj n = fch a j) : False := by
  have hu : acceleratedOrbit (tj - ti) (fch a i) = fch a j := by
    have h := acceleratedOrbit_add (tj - ti) ti n
    rw [hi, Nat.sub_add_cancel hle, hj] at h
    exact h
  have hvi := orbit_fch ha i
  have hvj : acceleratedOrbit (fval a j + (tj - ti)) (fch a i) = a := by
    rw [← acceleratedOrbit_add, hu]
    exact orbit_fch ha j
  have hnot : ¬ (a = 1 ∨ a = 2) := by omega
  have hvj1 := fval_pos a j
  rcases Nat.lt_trichotomy (fval a i) (fval a j + (tj - ti)) with hlt | heq | hgt
  · exact hnot (eq_one_or_two_of_periodic (by omega) (periodic_of_two_arrivals hvi hvj hlt) h1)
  · rcases Nat.eq_zero_or_pos (tj - ti) with h0 | hpos
    · rw [h0] at hu
      have hu' : fch a i = fch a j := hu
      exact hij (fch_inj ha ha hu').2
    · obtain ⟨w, hw⟩ : ∃ w, tj - ti = w + 1 := ⟨tj - ti - 1, by omega⟩
      rw [hw] at hu
      rw [orbit_fch_ray ha i w (by omega)] at hu
      have e : fval a i - (w + 1) = (fval a j - 1) + 1 := by omega
      rw [e, two_pow_succ_mul] at hu
      have hodd := (fch_good ha j).1
      omega
  · exact hnot (eq_one_or_two_of_periodic (by omega) (periodic_of_two_arrivals hvj hvi hgt) h1)

theorem no_common_subtree {a n i j t : Nat} (ha : TreeCount.Good a) (h5 : 5 ≤ a)
    (h1 : acceleratedOrbit t a = 1) (hij : i ≠ j)
    (hi : ∃ ti, acceleratedOrbit ti n = TreeBranching.fch a i)
    (hj : ∃ tj, acceleratedOrbit tj n = TreeBranching.fch a j) : False := by
  obtain ⟨ti, hi⟩ := hi
  obtain ⟨tj, hj⟩ := hj
  rcases Nat.le_total ti tj with h | h
  · exact no_common_aux ha h5 h1 hij h hi hj
  · exact no_common_aux ha h5 h1 (fun e => hij e.symm) h hj hi

/-! ## 6. The recursion -/

theorem S_rec {a Y : Nat} (Yi : Nat → Nat) (ha : TreeCount.Good a) (h5 : 5 ≤ a)
    (h1 : ∃ t, acceleratedOrbit t a = 1) (hY : ∀ i, i < 6 → Yi i + 18 ≤ Y) :
    Collatz.Sum.sumRange 6 (fun i => S (TreeBranching.fch a i) (Yi i)) ≤ S a Y := by
  obtain ⟨t, ht⟩ := h1
  unfold S
  apply family_count (f := fun _ n => n)
    (P := fun i n => Good n ∧ reachesBy n (fch a i) (Yi i) = true)
    (Y := Yi) 6 (fun n => Good n ∧ reachesBy n a Y = true)
  · intro i _ n m _ _ _ _ _ _ h
    exact h
  · intro i j _ _ hij n m _ _ _ _ hPn hPm h
    have hnm : n = m := h
    subst hnm
    obtain ⟨ti, _, hti⟩ := (reachesBy_iff n (fch a i) (Yi i)).1 hPn.2
    obtain ⟨tj, _, htj⟩ := (reachesBy_iff n (fch a j) (Yi j)).1 hPm.2
    exact no_common_subtree ha h5 ht hij ⟨ti, hti⟩ ⟨tj, htj⟩
  · intro i hi n hn1 hnY hPn
    have hYi := hY i hi
    refine ⟨hn1, by omega, hPn.1, ?_⟩
    have hb := reachesBy_trans hPn.2 (orbit_fch ha i)
    apply reachesBy_mono _ hb
    have hfv : fval a i ≤ tmpl i := fval_le_tmpl a i
    have htm : tmpl i ≤ 18 := tmpl_le_18 hi
    omega

/-! ## 7. The subtree of `5` lands in the Krasikov–Lagarias count -/

theorem S_five_le_count (Y : Nat) :
    S 5 Y ≤ Papers.KrasikovLagarias2003.reachesOneUpToCount (Y + 4) := by
  unfold S reachesOneUpToCount
  apply Nat.le_trans
    (countUpTo_le_of_le (p := fun n => Good n ∧ reachesBy n 5 Y = true) (by omega : Y ≤ Y + 4))
  apply countUpTo_mono
  intro n hn1 hnY ⟨_, hr⟩
  refine ⟨by omega, hnY, ?_⟩
  obtain ⟨j, hj, hj5⟩ := (reachesBy_iff n 5 Y).1 hr
  apply reachesOneBy_of_orbit (j := 4 + j)
  · rw [← acceleratedOrbit_add, hj5]
    decide
  · omega

end Subtree
end Collatz
