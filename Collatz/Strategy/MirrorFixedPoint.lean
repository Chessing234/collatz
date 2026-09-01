import Collatz.Strategy.SwapForm

/-!
# F2, sharpened: the sign of the translation selects the regime

Scratch file. Companion to `SwapForm.fixed_point_iff` (Collatz, `c = +1`), proving
the mirror analogue (`c = -1`) and the sign consequence for cycles.  NOT wired into
the repo — verification only.
-/

namespace Collatz
namespace MirrorFixedPoint

open SwapForm

/-- **`3^(a-1) ≥ 2^a + 2` for every `a ≥ 4`.**  The gap between the swapped `3`-part
and the `2`-part is at least `2` once `a` exceeds the crossover, so `a = 3` is the
*only* place the mirror's fixed-point equation can have a solution. -/
theorem three_pow_gap (a : Nat) (ha : 4 ≤ a) : 2 ^ a + 2 ≤ 3 ^ (a - 1) := by
  induction a with
  | zero => omega
  | succ a ih =>
    rcases Nat.lt_or_ge a 4 with hlt | hge
    · have ha4 : a = 3 := by omega
      subst ha4; decide
    · have hprev := ih hge
      have hstep : (2 : Nat) ^ (a + 1) = 2 * 2 ^ a := by rw [← Nat.pow_succ']
      have h3 : (3 : Nat) ^ (a + 1 - 1) = 3 * 3 ^ (a - 1) := by
        have he : a + 1 - 1 = (a - 1) + 1 := by omega
        rw [he, ← Nat.pow_succ']
      have hpow : 0 < 2 ^ a := Nat.pow_pos (by omega)
      rw [hstep, h3]
      omega

/-- **The mirror's fixed points, classified.**  `3^(a-1)·w = 2^a·w + 1` (the mirror
block map's fixed-point equation, `c = -1` cleared of subtraction) forces `w = 1` and
`a = 3` — exactly the block collapsing the real cycle `10 → 5 → 7 → 10`.  Contrast
`SwapForm.fixed_point_iff`: same shape of equation, opposite sign on the `1`, and the
solution sits in the *expanding* regime (`a ≥ 3`) instead of the contracting one
(`a ≤ 2`). -/
theorem mirror_fixed_point_iff {a w : Nat} (ha : 0 < a) (hw : w % 2 = 1) :
    3 ^ (a - 1) * w = 2 ^ a * w + 1 ↔ (w = 1 ∧ a = 3) := by
  constructor
  · intro h
    rcases Nat.lt_or_ge a 4 with hlt | hge
    · -- a ∈ {1, 2, 3}: for a ≤ 2 the swap can't reach the `+1`; a = 3 is forced.
      have h123 : a = 1 ∨ a = 2 ∨ a = 3 := by omega
      rcases h123 with h1 | h2 | h3
      · exfalso
        subst h1
        have e1 : (3 : Nat) ^ (1 - 1) = 1 := by decide
        have e2 : (2 : Nat) ^ 1 = 2 := by decide
        rw [e1, e2] at h
        omega
      · exfalso
        subst h2
        have e1 : (3 : Nat) ^ (2 - 1) = 3 := by decide
        have e2 : (2 : Nat) ^ 2 = 4 := by decide
        rw [e1, e2] at h
        omega
      · subst h3
        have e1 : (3 : Nat) ^ (3 - 1) = 9 := by decide
        have e2 : (2 : Nat) ^ 3 = 8 := by decide
        rw [e1, e2] at h
        exact ⟨by omega, rfl⟩
    · exfalso
      have hgap := three_pow_gap a hge
      have hmul : (2 ^ a + 2) * w ≤ 3 ^ (a - 1) * w := Nat.mul_le_mul_right w hgap
      rw [Nat.add_mul] at hmul
      have hwpos : 0 < w := by omega
      omega
  · rintro ⟨rfl, rfl⟩; decide

/-- **The sign consequence for a single-block cycle.**  A fixed point of the block
map with `c = +1` (Collatz) forces the multiplier `3^(a-1)/2^a < 1`; with `c = -1`
(mirror) it forces `3^(a-1)/2^a > 1`.  Stated multiplier-free, as the comparison of
`3^(a-1)` against `2^a` that the affine identity `U(1-λ) = c` reduces to. -/
theorem collatz_fixed_point_subunit {a w : Nat} (ha : 0 < a) (hw : w % 2 = 1)
    (h : 3 ^ (a - 1) * w + 1 = 2 ^ a * w) : 3 ^ (a - 1) < 2 ^ a := by
  have hw1 : w = 1 := (SwapForm.fixed_point_iff ha hw).1 h |>.1
  subst hw1
  omega

theorem mirror_fixed_point_superunit {a w : Nat} (ha : 0 < a) (hw : w % 2 = 1)
    (h : 3 ^ (a - 1) * w = 2 ^ a * w + 1) : 2 ^ a < 3 ^ (a - 1) := by
  have hw1 : w = 1 := (mirror_fixed_point_iff ha hw).1 h |>.1
  subst hw1
  omega

/-- **Kill test: `expStep` has no fixed point at all**, contracting or expanding —
its block map `2^a·w ↦ 3^a·w` (`c = 0`) has `w·(2^a - 3^a) = 0` forcing `2^a = 3^a`,
which never happens for `a ≥ 1` (and `a = 0` puts `w` outside the odd domain trivially
— `1 = 1` is the only fixed instance and it is not a genuine block, `a` must be
positive to be a swap at all). So the sign dichotomy above is a genuine consequence of
`c = ±1`, not an artifact that would also show up for `c = 0`. -/
theorem two_pow_lt_three_pow_strict : ∀ a : Nat, 0 < a → 2 ^ a < 3 ^ a := by
  intro a
  induction a with
  | zero => omega
  | succ a ih =>
    intro _
    have h2 : (2 : Nat) ^ (a + 1) = 2 * 2 ^ a := by rw [← Nat.pow_succ']
    have h3 : (3 : Nat) ^ (a + 1) = 3 * 3 ^ a := by rw [← Nat.pow_succ']
    rcases Nat.eq_zero_or_pos a with ha0 | hapos
    · subst ha0; rw [h2, h3]; decide
    · have hprev := ih hapos
      rw [h2, h3]
      omega

theorem expStep_no_fixed_point {a w : Nat} (ha : 0 < a) (hw : w % 2 = 1) :
    3 ^ a * w ≠ 2 ^ a * w := by
  intro h
  have hwpos : 0 < w := by omega
  have hlt : 2 ^ a < 3 ^ a := two_pow_lt_three_pow_strict a ha
  have hmul : 2 ^ a * w < 3 ^ a * w := (Nat.mul_lt_mul_right hwpos).2 hlt
  omega

end MirrorFixedPoint
end Collatz
