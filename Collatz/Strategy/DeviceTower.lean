import Collatz.Structure.OddRuns
import Collatz.Strategy.ScaleLadder

/-!
# The scale tower — the connection `π_k`, and why compactness misses it

Finite-scale never-dropping is a condition on *real sizes*, not on residues
modulo `2 ^ k`.  This file records the connection that lifts the condition from
horizon `k` to horizon `k + 1`, identifies the coordinate the residue tower
discards, and proves the exact reason compactness cannot produce an infinite
non-dropping orbit from the finite-horizon data:

> each cylinder `X_k` is nonempty, and already a two-point subset of it has
> Euclidean diameter `2 ^ (k + 2)`, which tends to infinity with `k`.

No statement about the intersection `⋂ X_k` is made.  That intersection is the
set of infinite non-droppers; deciding it is the conjecture, and is not claimed.
-/

namespace Collatz
namespace DeviceTower

open Reach
open OddRuns
open ScaleLadder

/-! ## Horizons and the drop window -/

/-- The `k`-horizon: the orbit of `n` has not dropped below `n` in the first
`k` accelerated steps. -/
def Horiz (k n : Nat) : Prop := ∀ j : Nat, j ≤ k → n ≤ acceleratedOrbit j n

/-- The **drop window** at start `n`: even values in `[n, 2n)`.  An even current
value in this interval is exactly the obstruction to lifting `Horiz k` to
`Horiz (k + 1)`. -/
def DropWindow (n v : Nat) : Prop :=
  v % 2 = 0 ∧ n ≤ v ∧ v < 2 * n

/-- An odd accelerated step does not decrease. -/
theorem le_step_of_odd {v : Nat} (h : v % 2 = 1) :
    v ≤ acceleratedStep v := by
  rw [acceleratedStep, if_neg (by omega)]
  omega

/-- The even branch is exact division by two. -/
theorem step_of_even {v : Nat} (h : v % 2 = 0) :
    acceleratedStep v = v / 2 := by
  rw [acceleratedStep, if_pos h]

/-- After an even step, staying above `n` is the comparison `v ≥ 2n`. -/
theorem even_step_ge_iff {v n : Nat} (h : v % 2 = 0) :
    n ≤ acceleratedStep v ↔ 2 * n ≤ v := by
  rw [step_of_even h]
  omega

/-! ## Device 14 — the connection `π_k` -/

/-- The inverse-system projection: a `(k + 1)`-horizon is a `k`-horizon.
This is inclusion of sets `X_{k+1} ⊆ X_k`. -/
theorem pi {k n : Nat} (h : Horiz (k + 1) n) : Horiz k n :=
  fun j hj => h j (by omega)

/-- **The lift law.**  A `k`-horizon lifts to a `(k + 1)`-horizon if and only if
the current value is odd, or even and at least twice the start.  No residue
modulo `2 ^ k` appears. -/
theorem lift_iff {k n : Nat} (h : Horiz k n) :
    Horiz (k + 1) n ↔
      (acceleratedOrbit k n % 2 = 1 ∨ 2 * n ≤ acceleratedOrbit k n) := by
  constructor
  · intro hsucc
    have hge : n ≤ acceleratedOrbit (k + 1) n := hsucc (k + 1) (Nat.le_refl _)
    rw [acceleratedOrbit_succ_step] at hge
    rcases Arith.mod_two_eq_zero_or_one (acceleratedOrbit k n) with he | ho
    · refine Or.inr ?_
      exact (even_step_ge_iff he).mp hge
    · exact Or.inl ho
  · intro hcond
    intro j hj
    rcases Nat.lt_or_ge j (k + 1) with hlt | hgej
    · exact h j (by omega)
    · have hjk : j = k + 1 := by omega
      subst hjk
      rw [acceleratedOrbit_succ_step]
      have hcur : n ≤ acceleratedOrbit k n := h k (Nat.le_refl _)
      rcases hcond with ho | hbig
      · exact Nat.le_trans hcur (le_step_of_odd ho)
      · rcases Arith.mod_two_eq_zero_or_one (acceleratedOrbit k n) with he | ho
        · exact (even_step_ge_iff he).mpr hbig
        · exact Nat.le_trans hcur (le_step_of_odd ho)

/-- Odd current values always lift. -/
theorem odd_lifts {k n : Nat} (h : Horiz k n)
    (ho : acceleratedOrbit k n % 2 = 1) : Horiz (k + 1) n :=
  (lift_iff h).mpr (Or.inl ho)

/-- **The fibre is the drop window.**  Failing to lift is exactly landing on an
even value in `[n, 2n)`. -/
theorem blocked_iff_drop_window {k n : Nat} (h : Horiz k n) :
    ¬ Horiz (k + 1) n ↔ DropWindow n (acceleratedOrbit k n) := by
  constructor
  · intro hfail
    have hcur : n ≤ acceleratedOrbit k n := h k (Nat.le_refl _)
    have hnot : ¬ (acceleratedOrbit k n % 2 = 1 ∨ 2 * n ≤ acceleratedOrbit k n) := by
      intro hc
      exact hfail ((lift_iff h).mpr hc)
    rcases Arith.mod_two_eq_zero_or_one (acceleratedOrbit k n) with he | ho
    · have hn2 : ¬ 2 * n ≤ acceleratedOrbit k n := by
        intro h2
        exact hnot (Or.inr h2)
      exact ⟨he, hcur, Nat.lt_of_not_ge hn2⟩
    · exact absurd (Or.inl ho) hnot
  · intro ⟨he, _, hlt⟩
    intro hsucc
    have hcond := (lift_iff h).mp hsucc
    rcases hcond with ho | hbig
    · omega
    · omega

/-! ## Free continuation past the start's own scale -/

/-- A floor at a scale already above the start makes every later value at least
the start: the drop window sits below the floor, so every later lift is free. -/
theorem continuation_free {n i a : Nat}
    (hf : Floor n i a) (hle : n ≤ 2 ^ a) :
    ∀ j : Nat, i ≤ j → n ≤ acceleratedOrbit j n :=
  fun j hj => Nat.le_trans hle (hf j hj)

/-- Finite horizon up to the floor, plus a floor at a scale `≥ n`, is an
infinite horizon.  Not a Collatz claim: the floor hypothesis is extra. -/
theorem horiz_all_of_floor {n i a : Nat}
    (hh : Horiz i n) (hf : Floor n i a) (hle : n ≤ 2 ^ a) :
    ∀ j : Nat, n ≤ acceleratedOrbit j n := by
  intro j
  rcases Nat.lt_or_ge j i with hlt | hge
  · exact hh j (Nat.le_of_lt hlt)
  · exact continuation_free hf hle j hge

/-! ## Device 15 — nonempty cylinders of unbounded real diameter -/

/-- Horizons are antitone in the length: the inverse-system maps `π`. -/
theorem horiz_mono {k k' n : Nat} (h : Horiz k' n) (hle : k ≤ k') : Horiz k n :=
  fun j hj => h j (Nat.le_trans hj hle)

/-- Along an odd run of length `m` the orbit is a nondecreasing `m`-horizon. -/
theorem horiz_of_oddRun {x m : Nat} (h : OddRun x m) : Horiz m x := by
  intro j hj
  induction j with
  | zero => exact Nat.le_refl x
  | succ j ih =>
    have hodd : acceleratedOrbit j x % 2 = 1 := h j (by omega)
    rw [acceleratedOrbit_succ_step]
    exact Nat.le_trans (ih (by omega)) (le_step_of_odd hodd)

/-- The Mersenne number `2 ^ m − 1` is an `m`-horizon. -/
theorem mersenne_horiz (m : Nat) : Horiz m (2 ^ m - 1) :=
  horiz_of_oddRun (oddRun_two_pow_sub_one m)

/-- **Cylinders are nonempty.**  `2 ^ (k + 2) − 1` is a `k`-horizon. -/
theorem cylinder_nonempty (k : Nat) : Horiz k (2 ^ (k + 2) - 1) :=
  horiz_mono (mersenne_horiz (k + 2)) (by omega)

/-- The next Mersenne number is still a `k`-horizon. -/
theorem cylinder_nonempty_succ (k : Nat) : Horiz k (2 ^ (k + 3) - 1) :=
  horiz_mono (mersenne_horiz (k + 3)) (by omega)

/-- **Constructive diameter.**  Both `2^(k+2)−1` and `2^(k+3)−1` lie in `X_k`,
and their difference is `2^(k+2)`.  Finite-scale non-drop cylinders are
nonempty, and already this two-point subset has Euclidean diameter tending to
infinity — the exact reason compactness in `ℝ` does not apply. -/
theorem cylinder_diameter (k : Nat) :
    Horiz k (2 ^ (k + 2) - 1) ∧
    Horiz k (2 ^ (k + 3) - 1) ∧
    (2 ^ (k + 3) - 1) - (2 ^ (k + 2) - 1) = 2 ^ (k + 2) := by
  refine ⟨cylinder_nonempty k, cylinder_nonempty_succ k, ?_⟩
  have hpos : 0 < 2 ^ (k + 2) := Arith.two_pow_pos (k + 2)
  have hle : 2 ^ (k + 2) ≤ 2 ^ (k + 3) :=
    Arith.two_pow_le_two_pow (by omega)
  have hs : (2 : Nat) ^ (k + 3) = 2 ^ (k + 2) * 2 := Nat.pow_succ 2 (k + 2)
  have h1 : 1 ≤ 2 ^ (k + 2) := Arith.one_le_two_pow (k + 2)
  have h3 : 1 ≤ 2 ^ (k + 3) := Arith.one_le_two_pow (k + 3)
  have hsub : (2 ^ (k + 3) - 1) - (2 ^ (k + 2) - 1) = 2 ^ (k + 3) - 2 ^ (k + 2) := by
    omega
  rw [hsub, hs]
  omega

/-- Every bound is exceeded by some point of `X_k`.  Equivalent form: `X_k` is
unbounded in `ℕ ⊂ ℝ`, so `diam_ℝ(X_k) = ∞`. -/
theorem cylinder_unbounded (k B : Nat) :
    ∃ x : Nat, B < x ∧ Horiz k x := by
  refine ⟨2 ^ (k + B + 2) - 1, ?_, ?_⟩
  · have hlt : k + B + 2 < 2 ^ (k + B + 2) := Arith.lt_two_pow_self (k + B + 2)
    have hle : B + 1 ≤ k + B + 2 := by omega
    have : B + 1 < 2 ^ (k + B + 2) := Nat.lt_of_le_of_lt hle hlt
    have hpos : 0 < 2 ^ (k + B + 2) := Arith.two_pow_pos (k + B + 2)
    omega
  · exact horiz_mono (mersenne_horiz (k + B + 2)) (by omega)

/-- The constructive section `s(k) = 2^(k+2)−1` escapes every bounded interval
of `ℝ`.  No compact of `ℝ` contains a section of the tower at all scales. -/
theorem no_compact_section (B : Nat) :
    ∃ K : Nat, ∀ k : Nat, K ≤ k → B < 2 ^ (k + 2) - 1 := by
  refine ⟨B, fun k hk => ?_⟩
  have hlt : k + 2 < 2 ^ (k + 2) := Arith.lt_two_pow_self (k + 2)
  have hle : B + 1 ≤ k + 2 := by omega
  have : B + 1 < 2 ^ (k + 2) := Nat.lt_of_le_of_lt hle hlt
  have hpos : 0 < 2 ^ (k + 2) := Arith.two_pow_pos (k + 2)
  omega

/-! ## The missing coordinate: Archimedean size, not a residue -/

/-- The Archimedean size — the coordinate discarded by `n ↦ n % 2 ^ k`.
Never-dropping inequalities are comparisons of this value against orbit values,
as points of `ℕ ⊂ ℝ`. -/
def ArchSize (n : Nat) : Nat := n

/-- Same residue modulo `2 ^ 2`, different size, different horizon: `1` lifts
through two steps and `5` does not.  The connection `π_k` is not a function of
the residue. -/
theorem size_splits_fibre :
    1 % 2 ^ 2 = 5 % 2 ^ 2 ∧ Horiz 2 1 ∧ ¬ Horiz 2 5 := by
  refine ⟨by decide, ?_, ?_⟩
  · intro j hj
    have h0 : acceleratedOrbit 0 1 = 1 := rfl
    have h1 : acceleratedOrbit 1 1 = 2 := by decide
    have h2 : acceleratedOrbit 2 1 = 1 := by decide
    rcases (show j = 0 ∨ j = 1 ∨ j = 2 from by omega) with h | h | h
    · subst h; rw [h0]; exact Nat.le_refl _
    · subst h; rw [h1]; omega
    · subst h; rw [h2]; exact Nat.le_refl _
  · intro h
    have hge : 5 ≤ acceleratedOrbit 2 5 := h 2 (Nat.le_refl _)
    have h2 : acceleratedOrbit 2 5 = 4 := by decide
    omega

/-! ## The inverse limit, named and not decided -/

/-- A thread through the tower: an integer that is a `k`-horizon at every
finite scale. -/
def InverseLimit (n : Nat) : Prop := ∀ k : Nat, Horiz k n

/-- The inverse limit is exactly the infinite non-dropping condition.  This is
an identification of predicates, not a cardinality claim. -/
theorem inverseLimit_iff (n : Nat) :
    InverseLimit n ↔ ∀ j : Nat, n ≤ acceleratedOrbit j n := by
  constructor
  · intro h j
    exact h j j (Nat.le_refl _)
  · intro h k j hj
    exact h j

end DeviceTower
end Collatz
