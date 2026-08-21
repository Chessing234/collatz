import Collatz.Strategy.CycleCriterion
import Collatz.Strategy.DenominatorScalar
import Collatz.Strategy.AnyModulusRanking

/-!
# Four models, and the theorems that survive the bridge back

This file collects the results of a deliberate departure from the development's
own framework.  Only statements that translate back into `oddCount` / `affineC` /
`acceleratedOrbit` are kept.

## Model 1 — the matrix semigroup

The two accelerated branches are the projective actions of

    A₀ = [[1,0],[0,2]]   (x ↦ x/2)        A₁ = [[3,1],[0,2]]   (x ↦ (3x+1)/2)

on the column `(x,1)`, and the product along a word `w` of length `L` with `a`
odd letters is exactly

    M_w = [[3 ^ a, C_w],[0, 2 ^ L]],      C_w = affineC L ·.

`affineC_add` / `oddCount_add` are the matrix product; `two_pow_dvd_affine` says
the second row acts trivially.  The eigenvector of `M_w` for the eigenvalue
`2 ^ L` is `(C_w, 2 ^ L − 3 ^ a)` — the accumulator over the gap — so the cycle
value of a word is a *projective fixed point*, not an accident.

**The theorem of this model is that the semigroup is free**, and — better — that
the triple `(L, 3 ^ a, C)` is a complete invariant of the residue class:

    oddCount x L = oddCount y L  →  affineC L x = affineC L y  →  x ≡ y (mod 2 ^ L)

(`word_of_count_and_accum`).  With `AccumulatorClass` this is an *iff*
(`class_iff_count_accum`), so the word ↔ class dictionary of Terras extends to a
word ↔ (count, accumulator) dictionary with no loss.  Previously this was a
measurement ("all `2 ^ j` words, `j ≤ 22`, zero collisions"); it is now a proof,
for every length.

The proof is two lines from `two_pow_dvd_affine`: both `x` and `y` satisfy
`3 ^ a · · + C ≡ 0 (mod 2 ^ L)`, and `3 ^ a` is odd, so it cancels.

Note what this does *not* contradict: the refuted statement was injectivity of
`w ↦ C_w` on heavy words with `a` free (collision at length 83, `a = 53` against
`a' = 55`).  Holding `a` fixed restores injectivity at every length.

## Model 2 — p-adic dynamics, and the denominator of a word

Read through the Böhm–Sontacchi conjugacy, a periodic parity word is a rational
fixed point `C / (2 ^ L − 3 ^ a)`.  The elementary shadow of that statement is
`two_pow_dvd_affine`, which pins the class: any `n` with
`(2 ^ L − 3 ^ a) · n = δ · C` automatically satisfies `n ≡ r (mod 2 ^ L)`.

The consequence is the **denominator of a word**: for `g = gcd(C, G)` and
`δ = G / g`, the integer `n = C / g` solves the cycle equation of the word `w`
for the map `x ↦ (3x + δ)/2` exactly (`word_denominator_equation`), and `δ` is
the least such constant (`word_denominator_least`).  So every word with a
positive gap *is* the parity word of a genuine `3x + δ` cycle, for one explicit
odd `δ` computable from the word alone.  `δ = 1` happens iff `G ∣ C`, which is
the cycle criterion.

This turns the development's soundness filter from a heuristic into a theorem:
no property of the parity word alone — heaviness, density, congruence, order,
accumulator size — can obstruct a cycle, because the word is a cycle word in
*some* denominator world, and `C(w,d) = d · C(w,1)` makes all of those properties
independent of `d`.

## Model 4 — the two remaining hatches in the ranking obstruction

`AnyModulusRanking.no_ranking_any_modulus` fixes the window `L` in advance and
demands descent at *every* positive `x`.  Two hypotheses of that shape were left
open, and both are closed here.

* **Variable windows.**  `no_variable_window_ranking`: no class function of any
  modulus admits, for each `x > 1`, *some* window on which it strictly drops.
  This needs no witness at all — the range of a class function is finite, and a
  representative of the minimal class larger than one has nowhere to go.  Stated
  for an arbitrary `Nat → Nat` step family, since the map plays no role.
* **A finite heaviness side condition.**  `no_ranking_on_heavy_prefix`:
  restricting the demand to the `x` that do not drop in their first `K` steps
  does not help, for any `K`.  The witness `2 ^ L · m − 1` grows for `L` steps,
  so it survives every finite heaviness filter with `K ≤ L`.  The only surviving
  restriction is the *infinite* one — never-dropping — and a ranking that assumes
  that is a restatement of the conjecture, not a proof of it.
-/

namespace Collatz
namespace NewModels

open Reach Congruence AffineExact AccumulatorClass CycleCriterion

/-! ## Model 1 — the semigroup is free -/

/-- Cancellation of an odd multiplier in a congruence modulo a power of two,
in the ordered case. -/
theorem congr_of_dvd_le {u c x y k : Nat} (hu : u % 2 = 1) (hle : y ≤ x)
    (hx : 2 ^ k ∣ (u * x + c)) (hy : 2 ^ k ∣ (u * y + c)) :
    x % 2 ^ k = y % 2 ^ k := by
  obtain ⟨p, hp⟩ := hx
  obtain ⟨q, hq⟩ := hy
  have hmono : u * y ≤ u * x := Nat.mul_le_mul_left u hle
  have hqp : q ≤ p := by
    have hle2 : 2 ^ k * q ≤ 2 ^ k * p := by omega
    exact Nat.le_of_mul_le_mul_left hle2 (Arith.two_pow_pos k)
  have hd : 2 ^ k ∣ (u * x - u * y) := by
    refine ⟨p - q, ?_⟩
    rw [Nat.mul_sub]
    omega
  obtain ⟨c', hc'⟩ := cancel_odd_mod_two_pow hu hle hd
  have hxy : x = y + 2 ^ k * c' := by omega
  rw [hxy, Nat.add_mul_mod_self_left]

/-- **An odd multiplier and a shared constant pin the class.** -/
theorem congr_of_dvd {u c x y k : Nat} (hu : u % 2 = 1)
    (hx : 2 ^ k ∣ (u * x + c)) (hy : 2 ^ k ∣ (u * y + c)) :
    x % 2 ^ k = y % 2 ^ k := by
  rcases Nat.le_total y x with hle | hle
  · exact congr_of_dvd_le hu hle hx hy
  · exact (congr_of_dvd_le hu hle hy hx).symm

/-- **The semigroup of the two branches is free.**  The odd-step count and the
accumulator of a window determine the residue class, hence the parity word.
The converse of `AccumulatorClass.affineC_congr_of_mod`. -/
theorem word_of_count_and_accum {x y L : Nat}
    (hcount : oddCount x L = oddCount y L) (hC : affineC L x = affineC L y) :
    x % 2 ^ L = y % 2 ^ L := by
  have hx := two_pow_dvd_affine x L
  have hy := two_pow_dvd_affine y L
  rw [hcount, hC] at hx
  exact congr_of_dvd (Arith.three_pow_odd _) hx hy

/-- **The complete invariant.**  `(oddCount, affineC)` and the class modulo
`2 ^ L` carry exactly the same information. -/
theorem class_iff_count_accum {x y L : Nat} :
    x % 2 ^ L = y % 2 ^ L ↔
      (oddCount x L = oddCount y L ∧ affineC L x = affineC L y) := by
  constructor
  · intro h
    exact ⟨oddCount_congr_of_mod h, affineC_congr_of_mod h⟩
  · intro h
    exact word_of_count_and_accum h.1 h.2

/-- Contrapositive form: distinct words have distinct `(a, C)` data. -/
theorem count_or_accum_ne_of_ne {x y L : Nat} (h : x % 2 ^ L ≠ y % 2 ^ L) :
    oddCount x L ≠ oddCount y L ∨ affineC L x ≠ affineC L y := by
  rcases Nat.decEq (oddCount x L) (oddCount y L) with hc | hc
  · exact Or.inl hc
  · refine Or.inr ?_
    intro hC
    exact h (word_of_count_and_accum hc hC)

/-! ## Model 2 — the denominator of a word -/

/-- The gap of a window: `2 ^ L − 3 ^ a`, as a natural number. -/
def gap (L x : Nat) : Nat := 2 ^ L - 3 ^ oddCount x L

/-- **The denominator equation.**  Let `g` be any common divisor of the
accumulator and the gap.  Then `n = C / g` satisfies the cycle equation of the
word for the constant `δ = G / g`: this is `DenominatorScalar.gen_cycle_gap`
read backwards, with the word's own accumulator on the right. -/
theorem word_denominator_equation {L x g : Nat} (hg : 0 < g)
    (hC : g ∣ affineC L x) (hG : g ∣ gap L x) :
    gap L x * (affineC L x / g) = (gap L x / g) * affineC L x := by
  obtain ⟨c, hc⟩ := hC
  obtain ⟨d, hd⟩ := hG
  rw [hc, hd, Nat.mul_div_cancel_left _ hg, Nat.mul_div_cancel_left _ hg]
  rw [Nat.mul_assoc, Nat.mul_comm c (g * d), Nat.mul_assoc, Nat.mul_comm d c]

/-- **`δ = 1` is exactly the cycle criterion.**  The denominator of a word is one
precisely when the gap divides the accumulator, and then the quotient is a
genuine `3x + 1` cycle point carrying that word. -/
theorem denominator_one_iff {r L : Nat} (hgap : 3 ^ oddCount r L < 2 ^ L) :
    (∃ n : Nat, gap L r * n = affineC L r) ↔ gap L r ∣ affineC L r := by
  constructor
  · intro h
    obtain ⟨n, hn⟩ := h
    exact ⟨n, hn.symm⟩
  · intro h
    obtain ⟨n, hn⟩ := h
    exact ⟨n, hn.symm⟩

/-- The realisation half: a solution of the denominator equation at `δ = 1` is a
cycle point with the given word.  (Restatement of `cycle_of_gap_dvd` in the
`gap` notation of this file.) -/
theorem cycle_of_denominator_one {r L n : Nat}
    (hgap : 3 ^ oddCount r L < 2 ^ L) (hn : gap L r * n = affineC L r) :
    acceleratedOrbit L n = n ∧ n % 2 ^ L = r % 2 ^ L :=
  cycle_of_gap_dvd hgap hn

/-! ## Model 4 — the two remaining hatches in the ranking obstruction -/

/-- **Variable windows do not help.**  A rank that is constant on classes modulo
`m` cannot drop on *some* window at every point, whatever the step family.  The
map is irrelevant: the range of a class function is finite and the minimal class
has a representative above one. -/
theorem no_variable_window_ranking {m : Nat} (hm : 0 < m) (φ : Nat → Nat)
    (step : Nat → Nat → Nat)
    (hclass : ∀ x y : Nat, x % m = y % m → φ x = φ y) :
    ¬ (∀ x : Nat, 1 < x → ∃ L : Nat, 0 < L ∧ φ (step L x) < φ x) := by
  intro hdec
  have key : ∀ v : Nat, ∀ x : Nat, 1 < x → φ x = v → False := by
    intro v
    induction v using Nat.strong_induction_on with
    | _ v ih =>
      intro x hx hv
      obtain ⟨L, _, hlt⟩ := hdec x hx
      have hz : (step L x + 2 * m) % m = (step L x) % m := by
        have : step L x + 2 * m = step L x + m * 2 := by omega
        rw [this, Nat.add_mul_mod_self_left]
      have hphi : φ (step L x + 2 * m) = φ (step L x) := hclass _ _ hz
      refine ih (φ (step L x)) (by omega) (step L x + 2 * m) (by omega) ?_
      exact hphi
  exact key (φ 2) 2 (by omega) rfl

/-- Instantiated at the accelerated map: no class function of any modulus drops
along *some* window at every point above one. -/
theorem no_variable_window_ranking_orbit {m : Nat} (hm : 0 < m) (φ : Nat → Nat)
    (hclass : ∀ x y : Nat, x % m = y % m → φ x = φ y) :
    ¬ (∀ x : Nat, 1 < x → ∃ L : Nat, 0 < L ∧ φ (acceleratedOrbit L x) < φ x) :=
  no_variable_window_ranking hm φ (fun L x => acceleratedOrbit L x) hclass

/-- The witness of `AnyModulusRanking` does not drop in its first `L` steps:
`2 ^ L · m − 1` grows at every prefix of the run. -/
theorem witness_heavy_prefix {m L i : Nat} (hm : 0 < m) (hi : i ≤ L) :
    (2 ^ L * m - 1) ≤ acceleratedOrbit i (2 ^ L * m - 1) := by
  rcases Nat.eq_zero_or_pos i with h0 | h0
  · rw [h0]
    simp [acceleratedOrbit]
  · have h2L : (1:Nat) ≤ 2 ^ L := Nat.one_le_two_pow
    have hbig : 1 ≤ 2 ^ L * m := Nat.le_trans h2L (Nat.le_mul_of_pos_right _ hm)
    have hn : (2 ^ L * m - 1) + 1 = 2 ^ ((L - i) + i) * m := by
      have : (L - i) + i = L := by omega
      rw [this]; omega
    exact Nat.le_of_lt (NoFiniteRanking.heavy_return_grows h0 hm hn)

/-- **A finite heaviness side condition does not help either.**  For every `K`
with `K ≤ L`, no class function modulo `m` can be required to drop over the
window `L` on all points that do not fall in their first `K` steps. -/
theorem no_ranking_on_heavy_prefix {m L K : Nat} (hm : 0 < m) (hL : 0 < L)
    (hKL : K ≤ L) (φ : Nat → Nat)
    (hclass : ∀ x y : Nat, x % m = y % m → φ x = φ y) :
    ¬ (∀ x : Nat, 0 < x → (∀ i : Nat, i ≤ K → x ≤ acceleratedOrbit i x) →
        φ (acceleratedOrbit L x) < φ x) := by
  intro hdec
  obtain ⟨n, hpos, hval, _, hcongr⟩ := AnyModulusRanking.exists_growing_return hm hL
  have hheavy : ∀ i : Nat, i ≤ K → n ≤ acceleratedOrbit i n := by
    intro i hi
    rw [hval]
    exact witness_heavy_prefix hm (Nat.le_trans hi hKL)
  have heq : φ (acceleratedOrbit L n) = φ n := hclass _ _ hcongr.symm
  have := hdec n hpos hheavy
  omega

end NewModels
end Collatz
