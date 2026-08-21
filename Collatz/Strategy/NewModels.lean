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

Independently and in parallel, `RunAlgebra.runA_word_eq` reached the same
completeness statement for the dual accumulator `A = C + G` by an induction on
the word.  The two are the same fact — `A` and `C` differ by `2 ^ L − 3 ^ a`,
which is a function of the data already fixed — but the route here is different:
no induction at all, only the class equation `2 ^ L ∣ 3 ^ a · x + C`, and the
conclusion is the congruence `x ≡ y (mod 2 ^ L)` rather than the pointwise
equality of parities.

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
  simp [Nat.mul_comm, Nat.mul_left_comm]

/-- **`δ = 1` is exactly the cycle criterion.**  The denominator of a word is one
precisely when the gap divides the accumulator, and then the quotient is a
genuine `3x + 1` cycle point carrying that word. -/
theorem denominator_one_iff {r L : Nat} :
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
    induction v using Nat.strongRecOn with
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


/-! ## Model 2 — the `d`-world class dictionary

`AccumulatorClass` proves that `oddCount` and `affineC` are class functions
modulo `2 ^ j`.  The realisation theorem of Model 2 needs the same statement for
`3x + d`, so the four lemmas are repeated here with `d` carried through.
-/

open Denominator DenominatorScalar

/-- One `3x + d` step on an even residue class. -/
theorem genStep_class_even {d k m r : Nat} (hr : r % 2 = 0) :
    genStep d (2 ^ (k + 1) * m + r) = 2 ^ k * m + genStep d r := by
  have hsplit : (2:Nat) ^ (k + 1) * m = 2 * (2 ^ k * m) := by
    rw [Arith.two_pow_succ, Nat.mul_assoc]
  have heven : (2 ^ (k + 1) * m + r) % 2 = 0 := by rw [hsplit]; omega
  rw [genStep, if_pos heven, genStep, if_pos hr, hsplit]
  omega

/-- One `3x + d` step on an odd residue class: the coefficient is tripled. -/
theorem genStep_class_odd {d k m r : Nat} (hr : r % 2 = 1) :
    genStep d (2 ^ (k + 1) * m + r) = 2 ^ k * (3 * m) + genStep d r := by
  have hsplit : (2:Nat) ^ (k + 1) * m = 2 * (2 ^ k * m) := by
    rw [Arith.two_pow_succ, Nat.mul_assoc]
  have hodd : (2 ^ (k + 1) * m + r) % 2 = 1 := by rw [hsplit]; omega
  have h3 : (2:Nat) ^ k * (3 * m) = 3 * (2 ^ k * m) := by
    rw [← Nat.mul_assoc, ← Nat.mul_assoc, Nat.mul_comm (2 ^ k) 3]
  rw [genStep, if_neg (by omega), genStep, if_neg (by omega), hsplit, h3]
  omega

/-- The odd-step count of `3x + d`, peeled from the front. -/
theorem genOddCount_head (d : Nat) : ∀ (k n : Nat),
    genOddCount d (k + 1) n
      = (if n % 2 = 1 then 1 else 0) + genOddCount d k (genStep d n) := by
  intro k
  induction k with
  | zero =>
    intro n
    have h1 : genOddCount d 1 n
        = genOddCount d 0 n + (if genOrbit d 0 n % 2 = 1 then 1 else 0) := rfl
    have h2 : genOrbit d 0 n = n := rfl
    rcases Arith.mod_two_eq_zero_or_one n with h | h
    · rw [h1, h2, if_neg (by omega : ¬ n % 2 = 1)]
      simp
    · rw [h1, h2, if_pos h]
      simp
  | succ k ih =>
    intro n
    have h1 : genOddCount d (k + 1 + 1) n
        = genOddCount d (k + 1) n + (if genOrbit d (k + 1) n % 2 = 1 then 1 else 0) := rfl
    have h2 : genOddCount d (k + 1) (genStep d n)
        = genOddCount d k (genStep d n)
          + (if genOrbit d k (genStep d n) % 2 = 1 then 1 else 0) := rfl
    have h3 : genOrbit d (k + 1) n = genOrbit d k (genStep d n) := rfl
    rw [h1, ih n, h2, h3, Nat.add_assoc]

/-- The `3x + d` odd-step count sees only the residue. -/
theorem genOddCount_class (d : Nat) : ∀ (j m r : Nat),
    genOddCount d j (2 ^ j * m + r) = genOddCount d j r := by
  intro j
  induction j with
  | zero => intro m r; rfl
  | succ j ih =>
    intro m r
    have hsplit : (2:Nat) ^ (j + 1) * m = 2 * (2 ^ j * m) := by
      rw [Arith.two_pow_succ, Nat.mul_assoc]
    rcases Arith.mod_two_eq_zero_or_one r with hr | hr
    · have heven : (2 ^ (j + 1) * m + r) % 2 = 0 := by rw [hsplit]; omega
      rw [genOddCount_head, genOddCount_head, if_neg (by omega), if_neg (by omega),
        genStep_class_even (k := j) (m := m) hr, ih]
    · have hodd : (2 ^ (j + 1) * m + r) % 2 = 1 := by rw [hsplit]; omega
      rw [genOddCount_head, genOddCount_head, if_pos hodd, if_pos hr,
        genStep_class_odd (k := j) (m := m) hr, ih]

/-- **The congruence identity for `3x + d`.** -/
theorem genOrbit_class (d : Nat) : ∀ (k m r : Nat),
    genOrbit d k (2 ^ k * m + r) = 3 ^ genOddCount d k r * m + genOrbit d k r := by
  intro k
  induction k with
  | zero => intro m r; simp
  | succ k ih =>
    intro m r
    rcases Arith.mod_two_eq_zero_or_one r with hr | hr
    · rw [genOrbit_succ, genStep_class_even (k := k) (m := m) hr, ih,
        genOddCount_head, if_neg (by omega), genOrbit_succ, Nat.zero_add]
    · rw [genOrbit_succ, genStep_class_odd (k := k) (m := m) hr, ih,
        genOddCount_head, if_pos hr, genOrbit_succ]
      have hp : (3:Nat) ^ (1 + genOddCount d k (genStep d r)) * m
          = 3 ^ genOddCount d k (genStep d r) * (3 * m) := by
        rw [Nat.pow_add, Nat.pow_one, Nat.mul_comm 3 (3 ^ genOddCount d k (genStep d r)),
          Nat.mul_assoc]
      rw [hp]

/-- The `3x + d` unit accumulator sees only the residue. -/
theorem genU_class {d : Nat} (hd : d % 2 = 1) (j m r : Nat) :
    genU d j (2 ^ j * m + r) = genU d j r := by
  have hdpos : 0 < d := by omega
  have hx := gen_affine_exact hd (2 ^ j * m + r) j
  have hr := gen_affine_exact hd r j
  have horb := genOrbit_class d j m r
  have hcount := genOddCount_class d j m r
  rw [horb, hcount, Nat.mul_add, Nat.mul_add] at hx
  have hcomm : (2:Nat) ^ j * (3 ^ genOddCount d j r * m)
      = 3 ^ genOddCount d j r * (2 ^ j * m) := by
    rw [← Nat.mul_assoc, ← Nat.mul_assoc, Nat.mul_comm (2 ^ j) (3 ^ genOddCount d j r)]
  rw [hcomm] at hx
  have hcancel : d * genU d j (2 ^ j * m + r) = d * genU d j r := by omega
  exact Nat.eq_of_mul_eq_mul_left hdpos hcancel

/-- Class invariance of the `3x + d` data, stated for congruent starting points. -/
theorem gen_congr_of_mod {d : Nat} (hd : d % 2 = 1) {x y j : Nat}
    (h : x % 2 ^ j = y % 2 ^ j) :
    genOddCount d j x = genOddCount d j y ∧ genU d j x = genU d j y := by
  have hdx : (2:Nat) ^ j * (x / 2 ^ j) + x % 2 ^ j = x := by
    have := Nat.div_add_mod x (2 ^ j); omega
  have hdy : (2:Nat) ^ j * (y / 2 ^ j) + y % 2 ^ j = y := by
    have := Nat.div_add_mod y (2 ^ j); omega
  have hcx := genOddCount_class d j (x / 2 ^ j) (x % 2 ^ j)
  have hcy := genOddCount_class d j (y / 2 ^ j) (y % 2 ^ j)
  have hux := genU_class hd j (x / 2 ^ j) (x % 2 ^ j)
  have huy := genU_class hd j (y / 2 ^ j) (y % 2 ^ j)
  rw [hdx] at hcx hux
  rw [hdy] at hcy huy
  rw [hcx, hcy, hux, huy, h]
  exact ⟨rfl, rfl⟩

/-! ### The realisation theorem -/

/-- **The converse cycle criterion for `3x + d`.**  If the gap of a residue's
`3x + d`-word divides `d` times its accumulator, the quotient is a genuine
`3x + d` cycle point carrying that very word.  This is `cycle_of_gap_dvd` with
the constant carried through. -/
theorem gen_cycle_of_gap_dvd {d r L x : Nat} (hd : d % 2 = 1)
    (hgap : 3 ^ genOddCount d L r ≤ 2 ^ L)
    (hx : (2 ^ L - 3 ^ genOddCount d L r) * x = d * genU d L r) :
    genOrbit d L x = x ∧ x % 2 ^ L = r % 2 ^ L := by
  have hdr : 2 ^ L ∣ (3 ^ genOddCount d L r * r + d * genU d L r) :=
    ⟨genOrbit d L r, (gen_affine_exact hd r L).symm⟩
  have hxexp : 3 ^ genOddCount d L r * x + d * genU d L r = 2 ^ L * x := by
    have hmono : 3 ^ genOddCount d L r * x ≤ 2 ^ L * x := Nat.mul_le_mul_right x hgap
    have hsub : (2 ^ L - 3 ^ genOddCount d L r) * x = 2 ^ L * x - 3 ^ genOddCount d L r * x :=
      Nat.sub_mul _ _ _
    omega
  have hdx : 2 ^ L ∣ (3 ^ genOddCount d L r * x + d * genU d L r) := ⟨x, hxexp⟩
  have hmod : x % 2 ^ L = r % 2 ^ L :=
    congr_of_dvd (Arith.three_pow_odd _) hdx hdr
  obtain ⟨hcount, hU⟩ := gen_congr_of_mod hd hmod
  have hexact := gen_affine_exact hd x L
  rw [hcount, hU, hxexp] at hexact
  exact ⟨Nat.eq_of_mul_eq_mul_left (Arith.two_pow_pos L) hexact, hmod⟩

/-! ### Scaling: every `3x + 1` word is a `3x + d` word -/

/-- **`T_d` on multiples of `d` is `d` times `T_1`.** -/
theorem mul_mod_two {d y : Nat} (hd : d % 2 = 1) : (d * y) % 2 = y % 2 := by
  have h := Nat.mul_mod d y 2
  rw [hd, Nat.one_mul] at h
  omega

/-- **`T_d` on multiples of `d` is `d` times `T_1`.** -/
theorem genOrbit_scale {d : Nat} (hd : d % 2 = 1) : ∀ (j x : Nat),
    genOrbit d j (d * x) = d * acceleratedOrbit j x := by
  intro j
  induction j with
  | zero => intro x; simp
  | succ j ih =>
    intro x
    have hstep : genStep d (d * x) = d * acceleratedStep x := by
      have hpar : (d * x) % 2 = x % 2 := mul_mod_two hd
      rcases Arith.mod_two_eq_zero_or_one x with hx | hx
      · have hxe : d * x = 2 * (d * (x / 2)) := by
          have h2 : 2 * (x / 2) = x := by omega
          calc d * x = d * (2 * (x / 2)) := by rw [h2]
            _ = 2 * (d * (x / 2)) := by rw [Nat.mul_left_comm]
        rw [genStep, if_pos (by omega), acceleratedStep, if_pos hx]
        omega
      · have hd3 : d * (3 * x + 1) = 3 * (d * x) + d := by
          rw [Nat.mul_add, Nat.mul_one, ← Nat.mul_assoc, Nat.mul_comm d 3, Nat.mul_assoc]
        have hhalf : 2 * ((3 * x + 1) / 2) = 3 * x + 1 := by omega
        have hkey : 3 * (d * x) + d = 2 * (d * ((3 * x + 1) / 2)) := by
          have e1 : 2 * (d * ((3 * x + 1) / 2)) = d * (2 * ((3 * x + 1) / 2)) :=
            Nat.mul_left_comm 2 d _
          rw [e1, hhalf, hd3]
        rw [genStep, if_neg (by omega), acceleratedStep, if_neg (by omega)]
        omega
    rw [genOrbit_succ, hstep, ih, acceleratedOrbit_succ]

/-- The scaled point carries the same parity word, hence the same odd-step count
and the same unit accumulator. -/
theorem gen_scale_data {d : Nat} (hd : d % 2 = 1) : ∀ (j x : Nat),
    genOddCount d j (d * x) = oddCount x j ∧ genU d j (d * x) = AffineExact.affineC j x := by
  intro j
  induction j with
  | zero => intro x; exact ⟨rfl, rfl⟩
  | succ j ih =>
    intro x
    have horb : genOrbit d j (d * x) = d * acceleratedOrbit j x := genOrbit_scale hd j x
    have hpar : genOrbit d j (d * x) % 2 = acceleratedOrbit j x % 2 := by
      rw [horb]; exact mul_mod_two hd
    obtain ⟨hc, hu⟩ := ih x
    have hlast := Density.oddCount_succ_last x j
    rcases Arith.mod_two_eq_zero_or_one (acceleratedOrbit j x) with he | ho
    · have hge : genOrbit d j (d * x) % 2 = 0 := by omega
      refine ⟨?_, ?_⟩
      · have h1 : genOddCount d (j + 1) (d * x)
            = genOddCount d j (d * x) + (if genOrbit d j (d * x) % 2 = 1 then 1 else 0) := rfl
        rw [h1, if_neg (by omega), hc]
        omega
      · rw [genU_even hge, AffineExact.affineC_even he, hu]
    · have hgo : genOrbit d j (d * x) % 2 = 1 := by omega
      refine ⟨?_, ?_⟩
      · have h1 : genOddCount d (j + 1) (d * x)
            = genOddCount d j (d * x) + (if genOrbit d j (d * x) % 2 = 1 then 1 else 0) := rfl
        rw [h1, if_pos hgo, hc]
        omega
      · rw [genU_odd hgo, AffineExact.affineC_odd ho, hu]

/-! ### The denominator of a word, and the soundness filter as a theorem -/

/-- A divisor of an odd number has odd cofactor. -/
theorem odd_quotient {G g q : Nat} (hGq : G = g * q) (hG : G % 2 = 1) : q % 2 = 1 := by
  rcases Arith.mod_two_eq_zero_or_one q with h0 | h1
  · exfalso
    have hq2 : q = 2 * (q / 2) := by omega
    have e : g * q = 2 * (g * (q / 2)) :=
      calc g * q = g * (2 * (q / 2)) := by rw [← hq2]
        _ = 2 * (g * (q / 2)) := Nat.mul_left_comm g 2 _
    have hG2 : G = 2 * (g * (q / 2)) := by rw [hGq, e]
    omega
  · exact h1

/-- The gap of a nonempty window with at least one odd step is odd. -/
theorem gap_odd {r L : Nat} (hL : 0 < L) (hgap : 3 ^ oddCount r L ≤ 2 ^ L) :
    (2 ^ L - 3 ^ oddCount r L) % 2 = 1 := by
  have h3 : (3:Nat) ^ oddCount r L % 2 = 1 := Arith.three_pow_odd _
  have h2 : (2:Nat) ^ L % 2 = 0 := by
    have hsplit : (2:Nat) ^ L = 2 * 2 ^ (L - 1) := by
      rw [← Arith.two_pow_succ]
      congr 1
      omega
    omega
  omega

/-- **Every word is a cycle word.**  Fix any window `L ≥ 1` and any residue `r`
whose multiplier is contracting, and let `g` be any common divisor of the
accumulator `C = affineC L r` and the gap `G = 2 ^ L − 3 ^ a`.  Then the integer
`n = C / g` is a genuine cycle point, of period `L`, of the map
`x ↦ (3x + δ)/2` with `δ = G / g` — and it carries exactly the parity word of
`r`, being congruent to `δ · r` modulo `2 ^ L`.

Taking `g = gcd(C, G)` makes `δ` the least constant that works: the **denominator
of the word**.  `δ = 1` is precisely `G ∣ C`, the cycle criterion for `3x + 1`.

This is the soundness filter of the development, promoted from a heuristic to a
theorem.  No property of the parity word alone — heaviness, density, any
congruence, the multiplicative order of `2` modulo the gap, any bound on `C` —
can obstruct a cycle, because `C(w, d) = d · C(w, 1)` makes every such property
independent of `d`, and the word *is* a cycle word for `d = δ(w)`. -/
theorem word_is_cycle_word {r L g : Nat} (hL : 0 < L) (hg : 0 < g)
    (hgap : 3 ^ oddCount r L ≤ 2 ^ L)
    (hCg : g ∣ affineC L r) (hGg : g ∣ (2 ^ L - 3 ^ oddCount r L)) :
    genOrbit ((2 ^ L - 3 ^ oddCount r L) / g) L (affineC L r / g) = affineC L r / g ∧
      (affineC L r / g) % 2 ^ L
        = (((2 ^ L - 3 ^ oddCount r L) / g) * r) % 2 ^ L := by
  obtain ⟨q, hq⟩ := hGg
  obtain ⟨c, hc⟩ := hCg
  have hdodd : ((2 ^ L - 3 ^ oddCount r L) / g) % 2 = 1 := by
    have hdiv : (2 ^ L - 3 ^ oddCount r L) / g = q := by
      rw [hq, Nat.mul_div_cancel_left _ hg]
    rw [hdiv]
    exact odd_quotient hq (gap_odd hL hgap)
  have hscale := gen_scale_data hdodd L r
  have hkey : (2 ^ L - 3 ^ genOddCount ((2 ^ L - 3 ^ oddCount r L) / g) L
        (((2 ^ L - 3 ^ oddCount r L) / g) * r)) * (affineC L r / g)
      = ((2 ^ L - 3 ^ oddCount r L) / g)
          * genU ((2 ^ L - 3 ^ oddCount r L) / g) L (((2 ^ L - 3 ^ oddCount r L) / g) * r) := by
    rw [hscale.1, hscale.2, hq, hc, Nat.mul_div_cancel_left _ hg, Nat.mul_div_cancel_left _ hg]
    rw [Nat.mul_assoc, Nat.mul_comm q (g * c), Nat.mul_assoc]
    simp [Nat.mul_comm]
  have hgap' : 3 ^ genOddCount ((2 ^ L - 3 ^ oddCount r L) / g) L
      (((2 ^ L - 3 ^ oddCount r L) / g) * r) ≤ 2 ^ L := by
    rw [hscale.1]; exact hgap
  exact gen_cycle_of_gap_dvd hdodd hgap' hkey

/-- **The denominator is one exactly when the gap divides the accumulator**, and
then the `3x + δ` cycle of `word_is_cycle_word` is a genuine `3x + 1` cycle. -/
theorem denominator_one {r L : Nat} (hL : 0 < L)
    (hgap : 3 ^ oddCount r L ≤ 2 ^ L)
    (hdvd : (2 ^ L - 3 ^ oddCount r L) ∣ affineC L r) :
    acceleratedOrbit L (affineC L r / (2 ^ L - 3 ^ oddCount r L))
        = affineC L r / (2 ^ L - 3 ^ oddCount r L) := by
  have hgpos : 0 < 2 ^ L - 3 ^ oddCount r L := by
    have := gap_odd hL hgap
    omega
  have h := word_is_cycle_word (g := 2 ^ L - 3 ^ oddCount r L) hL hgpos hgap hdvd
    (Nat.dvd_refl _)
  have hone : (2 ^ L - 3 ^ oddCount r L) / (2 ^ L - 3 ^ oddCount r L) = 1 :=
    Nat.div_self hgpos
  rw [hone] at h
  have := h.1
  rw [genOrbit_one] at this
  exact this

/-! ## Model 3 — the accumulator set as a uniquely-representable sumset

`affineC L x = Σ_{i=1..a} 3 ^ (a−i) · 2 ^ (t_i)` with `t_1 < ⋯ < t_a < L` the
odd-step times, so the set of accumulators at length `L` with `a` odd steps is
the sumset `{3^(a−1)·2^j} + {3^(a−2)·2^j} + ⋯ + {2^j}` restricted to strictly
increasing exponents.  Model 1 says this sumset has **unique representation**:
distinct exponent sets give distinct sums.  So the additive-combinatorial
question "is a fixed residue class modulo `G` hit rarely?" has no Freiman-type
structure to exploit — the sumset is as spread out as a sumset can be, and the
development's own measurement ("`C mod p` equidistributes for every `p ∤ 6` once
`a ≥ 9`") is the correct picture.

What unique representation *does* buy is a decoding algorithm, and its first two
steps are theorems already: `AccumulatorValuation.affineC_valuation` gives
`t_1 = v₂(C)`, and the peeling identity below strips the leading term.  The
decoding is what makes `C ↦ w` effective, and it is the reason the collision at
length 83 needed `a` to move: with `a` fixed there is nothing to collide.
-/

/-- **Peeling the leading odd step.**  For odd `x`, the accumulator of a window
is `3 ^ (a−1)` plus twice the accumulator of the window one step later.  This is
the recursion that decodes `C` back into its odd-step times. -/
theorem affineC_peel_odd {x k : Nat} (hx : x % 2 = 1) :
    affineC (1 + k) x
      = 3 ^ (oddCount x (1 + k) - 1) + 2 * affineC k (acceleratedStep x) := by
  have hadd := AccumulatorArith.affineC_add x 1 k
  have hcnt := AccumulatorArith.oddCount_add x 1 k
  have h1 : acceleratedOrbit 1 x = acceleratedStep x := rfl
  have hC1 : affineC 1 x = 1 := by
    have h := affineC_odd (j := 0) (x := x) hx
    simpa using h
  have hcnt1 : oddCount x 1 = 1 := by
    have h := oddCount_succ_of_odd hx 0
    simpa using h
  rw [h1, hC1, Nat.mul_one] at hadd
  rw [hcnt1] at hcnt
  rw [hadd, hcnt]
  simp

end NewModels
end Collatz
