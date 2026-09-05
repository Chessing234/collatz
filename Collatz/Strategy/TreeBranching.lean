import Collatz.Strategy.TreeCount

/-!
# Counting the inverse tree, second pass: every child charged its own size

**Novelty tag: FORMALIZATION-OF-KNOWN** (the size-aware branching count of
Crandall 1978 / Sander 1990; still far below Krasikov–Lagarias 2003, `0.84`).

`TreeCount` charged every child the size of the largest of three, and got the
exponent `log 2 / log 22 = 0.224`.  This file does two things better.

1. **All fertile children, each at its own size.**  The admissible valuations of
   an odd `a` prime to `3` are `v₀ + 2j`, `j ≥ 0`, and the child is fertile
   (prime to `3`) exactly when `j ≢ phase a (mod 3)`, where `phase a ∈ {0,1,2}`
   is read off `2 ^ v₀ · a mod 9`.  So the `i`-th fertile child (`i ≥ 0`) sits
   at `j_i = i + ⌊(i + 2 − phase)/2⌋` and its valuation is at most the
   *template* `tmpl i = 2 + 2i + 2⌊(i+2)/2⌋ = 4, 6, 10, 12, 16, 18, …`.
   The `i`-th child is therefore below `2 ^ tmpl i · a / 3`.

2. **A disjoint-family counting principle** (`family_count`): if maps
   `f i` are injective on `{a ≤ Y i : P i a}`, have pairwise disjoint images,
   and land in `{n ≤ X : Q n}`, then `Σ_i countUpTo (P i) (Y i) ≤ countUpTo Q X`.

Together: with `NF X` the number of odd `n ≤ X` prime to `3` that reach `1`
within `X` steps,

    NF_rec : 64 ≤ X → Σ_{i<6} NF (3X / 2 ^ tmpl i) ≤ NF X.

## Closing the recursion without real numbers

On the two-type lattice `f k = NF (2 ^ k)`, `h k = NF (3 · 2 ^ k)` the recursion
is exact in one direction (`3 · 2 ^ k / 2 ^ t = 3 · 2 ^ (k−t)`) and loses a
factor `9/8` in the other (`9 · 2 ^ (k−t) ≥ 2 ^ (k−t+3)`).  A growth rate
`λ = 13/10` is then certified by the *joint* induction

    2 · 13 ^ k ≤ 10 ^ k · 200 · f k,      3 · 13 ^ k ≤ 10 ^ k · 200 · h k,

whose inductive steps reduce to two integer inequalities checked by `decide`
(`I1`, `I2`: `3 Σ (10/13) ^ tmpl i ≥ 2` and `2 Σ (10/13) ^ (tmpl i − 3) ≥ 3`),
and whose base cases (`k < 18`) use only `NF ≥ 1`.  Since `13 ^ 8 > 8 · 10 ^ 8`,
`λ ≥ 2 ^ (3/8)`, giving

    count_pow_eight : 1 ≤ N → N ^ 3 < 8 · 10 ^ 16 · (reachesOneUpToCount N) ^ 8,

i.e. at least `N ^ (3/8) / 131` integers up to `N` reach `1`.  The scalar moves
from `1/5` to `3/8`.

## What is left on the table

The true root of this recursion is `≈ 0.388`; `3/8 = 0.375` is what the
rational `13/10` certifies.  Tracking residues of the parent modulo `9`, `27`, …
(the children's residues modulo `3 ^ k` depend on the parent modulo `3 ^ (k+1)`,
so the system never closes and needs the difference-inequality device) is the
Krasikov–Lagarias route to `0.84`.  Pure counting cannot reach density `1`.
-/

namespace Collatz
namespace TreeBranching

open Reach TreeCount Collatz.Sum Papers.KrasikovLagarias2003

/-! ## 1. Every fertile child, indexed by rank -/

/-- The residue class of `j` modulo `3` at which `4 ^ j · base a ≡ 1 (mod 9)`. -/
def phase (a : Nat) : Nat :=
  if base a % 9 = 1 then 0 else if base a % 9 = 7 then 1 else 2

theorem phase_le_two (a : Nat) : phase a ≤ 2 := by
  unfold phase
  split
  · omega
  · split <;> omega

/-- The index `j` of the `i`-th fertile child among the admissible valuations
`v₀ + 2j`: skip every `j ≡ phase a (mod 3)`. -/
def jidx (a i : Nat) : Nat := i + (i + 2 - phase a) / 2

/-- The valuation of the `i`-th fertile child. -/
def fval (a i : Nat) : Nat := v0 a + 2 * jidx a i

/-- The template bound on `fval`: `4, 6, 10, 12, 16, 18, …`. -/
def tmpl (i : Nat) : Nat := 2 + 2 * i + 2 * ((i + 2) / 2)

theorem tmpl_ge_four (i : Nat) : 4 ≤ tmpl i := by
  unfold tmpl; omega

theorem tmpl_le_18 {i : Nat} (hi : i < 6) : tmpl i ≤ 18 := by
  unfold tmpl; omega

theorem jidx_mod_three (a i : Nat) : jidx a i % 3 ≠ phase a := by
  unfold jidx
  have := phase_le_two a
  omega

theorem fval_pos (a i : Nat) : 1 ≤ fval a i := by
  unfold fval
  have := v0_ge_one a
  omega

theorem fval_le_tmpl (a i : Nat) : fval a i ≤ tmpl i := by
  unfold fval jidx tmpl
  have := v0_le_two a
  have := phase_le_two a
  omega

theorem fval_inj {a i j : Nat} (h : fval a i = fval a j) : i = j := by
  unfold fval jidx at h
  have := phase_le_two a
  omega

/-- `4 ^ j` modulo `9` cycles through `1, 4, 7` with `j mod 3`. -/
theorem four_pow_mod_nine : ∀ j : Nat,
    (4 ^ j % 9 = 1 ∧ j % 3 = 0) ∨ (4 ^ j % 9 = 4 ∧ j % 3 = 1) ∨
    (4 ^ j % 9 = 7 ∧ j % 3 = 2) := by
  intro j
  induction j with
  | zero => left; exact ⟨rfl, rfl⟩
  | succ j ih =>
    rw [Nat.pow_succ]
    omega

theorem two_pow_fval_mul (a i : Nat) : 2 ^ fval a i * a = 4 ^ jidx a i * base a := by
  unfold fval base
  rw [Nat.pow_add, Nat.pow_mul, show (2:Nat) ^ 2 = 4 from rfl,
    Nat.mul_comm (2 ^ v0 a) (4 ^ jidx a i), Nat.mul_assoc]

/-- **Every `fval a i` is admissible and fertile.** -/
theorem fval_admissible {a : Nat} (ha : Good a) (i : Nat) :
    (2 ^ fval a i * a) % 3 = 1 ∧ (2 ^ fval a i * a) % 9 ≠ 1 := by
  rw [two_pow_fval_mul]
  have hb := base_mod_three ha.2
  have hj := jidx_mod_three a i
  have h4 := four_pow_mod_nine (jidx a i)
  have hu : base a % 9 = 1 ∨ base a % 9 = 4 ∨ base a % 9 = 7 := by omega
  have hx : (4 ^ jidx a i * base a) % 9 = (4 ^ jidx a i % 9 * (base a % 9)) % 9 :=
    Nat.mul_mod _ _ _
  unfold phase at hj
  rcases hu with hu | hu | hu <;> rw [hu] at hx hj <;>
    rcases h4 with ⟨h4, h4'⟩ | ⟨h4, h4'⟩ | ⟨h4, h4'⟩ <;> rw [h4] at hx <;>
    simp at hj <;> omega

/-- The `i`-th fertile child of `a`. -/
def fch (a i : Nat) : Nat := child a (fval a i)

theorem fch_good {a : Nat} (ha : Good a) (i : Nat) : Good (fch a i) := by
  obtain ⟨h3, h9⟩ := fval_admissible ha i
  exact ⟨child_odd (fval_pos a i) h3, child_mod_three h3 h9⟩

theorem fch_pos {a : Nat} (ha : Good a) (i : Nat) : 0 < fch a i :=
  child_pos (by have := ha.1; omega) (fval_pos a i) (fval_admissible ha i).1

theorem orbit_fch {a : Nat} (ha : Good a) (i : Nat) :
    acceleratedOrbit (fval a i) (fch a i) = a :=
  orbit_child (fval_pos a i) (fval_admissible ha i).1

theorem three_fch {a : Nat} (ha : Good a) (i : Nat) :
    3 * fch a i + 1 = 2 ^ fval a i * a :=
  child_eq (fval_admissible ha i).1

/-- A child remembers its parent and its rank. -/
theorem fch_inj {a b i j : Nat} (ha : Good a) (hb : Good b) (h : fch a i = fch b j) :
    a = b ∧ i = j := by
  obtain ⟨hv, hab⟩ :=
    child_inj ha.1 hb.1 (fval_admissible ha i).1 (fval_admissible hb j).1 h
  subst hab
  exact ⟨rfl, fval_inj hv⟩

/-- **Size.**  A parent at most `3X / 2 ^ tmpl i` has its `i`-th child below `X`. -/
theorem fch_lt {a i X : Nat} (ha : Good a) (hX : a ≤ 3 * X / 2 ^ tmpl i) :
    fch a i < X := by
  have h := three_fch ha i
  have h1 : 2 ^ fval a i ≤ 2 ^ tmpl i := Nat.pow_le_pow_right (by decide) (fval_le_tmpl a i)
  have h2 : 2 ^ fval a i * a ≤ 2 ^ tmpl i * a := Nat.mul_le_mul_right a h1
  have h3 : 2 ^ tmpl i * a ≤ 2 ^ tmpl i * (3 * X / 2 ^ tmpl i) := Nat.mul_le_mul_left _ hX
  have h4 : 2 ^ tmpl i * (3 * X / 2 ^ tmpl i) ≤ 3 * X := Nat.mul_div_le (3 * X) (2 ^ tmpl i)
  omega

/-! ## 2. Step budgets -/

theorem reachesOneBy_iff (n : Nat) : ∀ B,
    reachesOneBy n B = true ↔ ∃ j, j ≤ B ∧ acceleratedOrbit j n = 1 := by
  intro B
  constructor
  · induction B with
    | zero =>
      intro h
      exact ⟨0, Nat.le_refl 0, of_decide_eq_true h⟩
    | succ B ih =>
      intro h
      have h' : (reachesOneBy n B || decide (acceleratedOrbit (B + 1) n = 1)) = true := h
      rw [Bool.or_eq_true] at h'
      rcases h' with h' | h'
      · obtain ⟨j, hj, hj1⟩ := ih h'
        exact ⟨j, by omega, hj1⟩
      · exact ⟨B + 1, Nat.le_refl _, of_decide_eq_true h'⟩
  · intro ⟨j, hj, hj1⟩
    exact reachesOneBy_of_orbit hj1 B hj

theorem reachesOneBy_mono {n B B' : Nat} (h : B ≤ B') (hB : reachesOneBy n B = true) :
    reachesOneBy n B' = true := by
  obtain ⟨j, hj, hj1⟩ := (reachesOneBy_iff n B).1 hB
  exact reachesOneBy_of_orbit hj1 B' (Nat.le_trans hj h)

theorem reachesOneBy_fch {a i B : Nat} (ha : Good a) (hB : reachesOneBy a B = true) :
    reachesOneBy (fch a i) (B + fval a i) = true := by
  obtain ⟨j, hj, hj1⟩ := (reachesOneBy_iff a B).1 hB
  apply reachesOneBy_of_orbit (j := j + fval a i)
  · rw [← acceleratedOrbit_add, orbit_fch ha, hj1]
  · omega

/-! ## 3. Counting a disjoint family of injective images -/

/-- Removing one counted element lowers the count by exactly one. -/
theorem countUpTo_remove {Q : Nat → Prop} [∀ a, Decidable (Q a)] {y : Nat}
    (hy : 1 ≤ y) (hQ : Q y) :
    ∀ X, y ≤ X → countUpTo Q X = countUpTo (fun n => Q n ∧ n ≠ y) X + 1 := by
  intro X
  induction X with
  | zero => intro h; omega
  | succ X ih =>
    intro hyX
    show countUpTo Q X + (if Q (X + 1) then 1 else 0)
        = countUpTo (fun n => Q n ∧ n ≠ y) X + (if Q (X + 1) ∧ X + 1 ≠ y then 1 else 0) + 1
    by_cases hyX' : y = X + 1
    · have hc : countUpTo Q X = countUpTo (fun n => Q n ∧ n ≠ y) X := by
        apply countUpTo_congr
        intro n _ h2
        constructor
        · intro h; exact ⟨h, by omega⟩
        · intro h; exact h.1
      rw [hc, if_pos (hyX' ▸ hQ), if_neg (fun h => h.2 hyX'.symm)]
    · rw [ih (by omega)]
      by_cases hQ' : Q (X + 1)
      · rw [if_pos hQ', if_pos ⟨hQ', fun h => hyX' h.symm⟩]
      · rw [if_neg hQ', if_neg (fun h => hQ' h.1)]

/-- **Image counting.**  An injection of `{a ∈ [1, Y] : P a}` into
`{n ∈ [1, X] : Q n}` bounds one count by the other. -/
theorem image_count {f : Nat → Nat} {P : Nat → Prop} [∀ a, Decidable (P a)] {X : Nat} :
    ∀ (Y : Nat) (Q : Nat → Prop) [∀ a, Decidable (Q a)],
      (∀ a b, 1 ≤ a → a ≤ Y → 1 ≤ b → b ≤ Y → P a → P b → f a = f b → a = b) →
      (∀ a, 1 ≤ a → a ≤ Y → P a → 1 ≤ f a ∧ f a ≤ X ∧ Q (f a)) →
      countUpTo P Y ≤ countUpTo Q X := by
  intro Y
  induction Y with
  | zero => intro Q _ _ _; exact Nat.zero_le _
  | succ Y ih =>
    intro Q _ hinj hinto
    show countUpTo P Y + (if P (Y + 1) then 1 else 0) ≤ countUpTo Q X
    by_cases hP : P (Y + 1)
    · rw [if_pos hP]
      obtain ⟨hy1, hyX, hQy⟩ := hinto (Y + 1) (by omega) (Nat.le_refl _) hP
      have hrem := countUpTo_remove hy1 hQy X hyX
      have hle := ih (fun n => Q n ∧ n ≠ f (Y + 1))
        (fun a b ha1 haY hb1 hbY hPa hPb h =>
          hinj a b ha1 (by omega) hb1 (by omega) hPa hPb h)
        (fun a ha1 haY hPa => by
          obtain ⟨h1, h2, h3⟩ := hinto a ha1 (by omega) hPa
          refine ⟨h1, h2, h3, fun heq => ?_⟩
          have := hinj a (Y + 1) ha1 (by omega) (by omega) (Nat.le_refl _) hPa hP heq
          omega)
      omega
    · rw [if_neg hP]
      exact ih Q
        (fun a b ha1 haY hb1 hbY hPa hPb h =>
          hinj a b ha1 (by omega) hb1 (by omega) hPa hPb h)
        (fun a ha1 haY hPa => hinto a ha1 (by omega) hPa)

/-- Membership in the image of `f` over `{a ∈ [1, Y] : P a}`, as a Boolean. -/
def imgB (f : Nat → Nat) (P : Nat → Prop) [∀ a, Decidable (P a)] : Nat → Nat → Bool
  | 0, _ => false
  | Y + 1, n => imgB f P Y n || (decide (P (Y + 1)) && decide (f (Y + 1) = n))

theorem imgB_iff (f : Nat → Nat) (P : Nat → Prop) [∀ a, Decidable (P a)] :
    ∀ Y n, imgB f P Y n = true ↔ ∃ a, 1 ≤ a ∧ a ≤ Y ∧ P a ∧ f a = n := by
  intro Y
  induction Y with
  | zero =>
    intro n
    constructor
    · intro h; exact absurd h (by simp [imgB])
    · intro ⟨a, ha1, haY, _, _⟩; omega
  | succ Y ih =>
    intro n
    show (imgB f P Y n || (decide (P (Y + 1)) && decide (f (Y + 1) = n))) = true ↔ _
    rw [Bool.or_eq_true, Bool.and_eq_true, ih, decide_eq_true_iff, decide_eq_true_iff]
    constructor
    · intro h
      rcases h with ⟨a, ha1, haY, hPa, hfa⟩ | ⟨hP, hf⟩
      · exact ⟨a, ha1, by omega, hPa, hfa⟩
      · exact ⟨Y + 1, by omega, Nat.le_refl _, hP, hf⟩
    · intro ⟨a, ha1, haY, hPa, hfa⟩
      by_cases haY' : a = Y + 1
      · right; subst haY'; exact ⟨hPa, hfa⟩
      · left; exact ⟨a, ha1, by omega, hPa, hfa⟩

/-- A count splits along any Boolean test. -/
theorem countUpTo_split {Q : Nat → Prop} [∀ a, Decidable (Q a)] (R : Nat → Bool) :
    ∀ X, countUpTo Q X
      = countUpTo (fun n => Q n ∧ R n = true) X + countUpTo (fun n => Q n ∧ R n = false) X := by
  intro X
  induction X with
  | zero => rfl
  | succ X ih =>
    show countUpTo Q X + (if Q (X + 1) then 1 else 0)
      = (countUpTo (fun n => Q n ∧ R n = true) X + (if Q (X + 1) ∧ R (X + 1) = true then 1 else 0))
        + (countUpTo (fun n => Q n ∧ R n = false) X + (if Q (X + 1) ∧ R (X + 1) = false then 1 else 0))
    rw [ih]
    by_cases hQ : Q (X + 1)
    · cases hR : R (X + 1)
      · rw [if_pos hQ, if_neg (fun h => absurd h.2 (by decide)), if_pos ⟨hQ, rfl⟩]
        omega
      · rw [if_pos hQ, if_pos ⟨hQ, rfl⟩, if_neg (fun h => absurd h.2 (by decide))]
        omega
    · rw [if_neg hQ, if_neg (fun h => hQ h.1), if_neg (fun h => hQ h.1)]
      omega

/-- **The disjoint-family counting principle.** -/
theorem family_count {f : Nat → Nat → Nat} {P : Nat → Nat → Prop}
    [∀ i a, Decidable (P i a)] {Y : Nat → Nat} {X : Nat} :
    ∀ (m : Nat) (Q : Nat → Prop) [∀ a, Decidable (Q a)],
      (∀ i, i < m → ∀ a b, 1 ≤ a → a ≤ Y i → 1 ≤ b → b ≤ Y i →
        P i a → P i b → f i a = f i b → a = b) →
      (∀ i j, i < m → j < m → i ≠ j → ∀ a b, 1 ≤ a → a ≤ Y i → 1 ≤ b → b ≤ Y j →
        P i a → P j b → f i a ≠ f j b) →
      (∀ i, i < m → ∀ a, 1 ≤ a → a ≤ Y i → P i a → 1 ≤ f i a ∧ f i a ≤ X ∧ Q (f i a)) →
      sumRange m (fun i => countUpTo (P i) (Y i)) ≤ countUpTo Q X := by
  intro m
  induction m with
  | zero => intro Q _ _ _ _; exact Nat.zero_le _
  | succ m ih =>
    intro Q _ hinj hdisj hinto
    rw [sumRange_succ]
    have hsplit := countUpTo_split (Q := Q) (imgB (f m) (P m) (Y m)) X
    have h1 : sumRange m (fun i => countUpTo (P i) (Y i))
        ≤ countUpTo (fun n => Q n ∧ imgB (f m) (P m) (Y m) n = false) X := by
      apply ih
      · intro i hi; exact hinj i (by omega)
      · intro i j hi hj; exact hdisj i j (by omega) (by omega)
      · intro i hi a ha1 haY hPa
        obtain ⟨h1, h2, h3⟩ := hinto i (by omega) a ha1 haY hPa
        refine ⟨h1, h2, h3, ?_⟩
        cases hR : imgB (f m) (P m) (Y m) (f i a) with
        | false => rfl
        | true =>
          exfalso
          obtain ⟨b, hb1, hbY, hPb, hfb⟩ := (imgB_iff (f m) (P m) (Y m) (f i a)).1 hR
          exact hdisj m i (Nat.lt_succ_self m) (by omega) (by omega) b a hb1 hbY ha1 haY hPb hPa hfb
    have h2 : countUpTo (P m) (Y m)
        ≤ countUpTo (fun n => Q n ∧ imgB (f m) (P m) (Y m) n = true) X := by
      apply image_count (Y m)
      · exact hinj m (Nat.lt_succ_self m)
      · intro a ha1 haY hPa
        obtain ⟨h1, h2, h3⟩ := hinto m (Nat.lt_succ_self m) a ha1 haY hPa
        exact ⟨h1, h2, h3, (imgB_iff _ _ _ _).2 ⟨a, ha1, haY, hPa, rfl⟩⟩
    omega

/-! ## 4. The fertile count and its recursion -/

instance (n : Nat) : Decidable (Good n) := by
  unfold Good; infer_instance

/-- The number of odd `n ≤ X` prime to `3` reaching `1` within `X` steps. -/
def NF (X : Nat) : Nat := countUpTo (fun n => Good n ∧ reachesOneBy n X = true) X

theorem countUpTo_le_succ {p : Nat → Prop} [∀ a, Decidable (p a)] (X : Nat) :
    countUpTo p X ≤ countUpTo p (X + 1) := by
  show countUpTo p X ≤ countUpTo p X + (if p (X + 1) then 1 else 0)
  split <;> omega

theorem countUpTo_le_of_le {p : Nat → Prop} [∀ a, Decidable (p a)] {X X' : Nat} (h : X ≤ X') :
    countUpTo p X ≤ countUpTo p X' := by
  induction X' with
  | zero => have : X = 0 := by omega
            subst this; exact Nat.le_refl _
  | succ X' ih =>
    by_cases hX : X ≤ X'
    · exact Nat.le_trans (ih hX) (countUpTo_le_succ X')
    · have : X = X' + 1 := by omega
      subst this; exact Nat.le_refl _

theorem NF_le_count (X : Nat) : NF X ≤ reachesOneUpToCount X := by
  unfold NF reachesOneUpToCount
  apply countUpTo_mono
  intro n h1 h2 ⟨hg, hr⟩
  exact ⟨by omega, h2, hr⟩

theorem NF_mono {X X' : Nat} (h : X ≤ X') : NF X ≤ NF X' := by
  unfold NF
  apply Nat.le_trans (countUpTo_le_of_le (p := fun n => Good n ∧ reachesOneBy n X = true) h)
  apply countUpTo_mono
  intro n _ _ ⟨hg, hr⟩
  exact ⟨hg, reachesOneBy_mono h hr⟩

theorem NF_pos {X : Nat} (hX : 1 ≤ X) : 1 ≤ NF X := by
  have h1 : NF 1 = 1 := by
    show (countUpTo _ 0 + if (Good 1 ∧ reachesOneBy 1 1 = true) then 1 else 0) = 1
    rw [if_pos ⟨⟨rfl, by decide⟩, by decide⟩]
    rfl
  rw [← h1]
  exact NF_mono hX

/-- **The size-aware recursion.** -/
theorem NF_rec {X : Nat} (hX : 64 ≤ X) :
    sumRange 6 (fun i => NF (3 * X / 2 ^ tmpl i)) ≤ NF X := by
  unfold NF
  apply family_count (f := fun i a => fch a i)
    (P := fun i a => Good a ∧ reachesOneBy a (3 * X / 2 ^ tmpl i) = true)
    (Y := fun i => 3 * X / 2 ^ tmpl i) 6 (fun n => Good n ∧ reachesOneBy n X = true)
  · intro i _ a b _ _ _ _ hPa hPb h
    exact (fch_inj hPa.1 hPb.1 h).1
  · intro i j _ _ hij a b _ _ _ _ hPa hPb h
    exact hij (fch_inj hPa.1 hPb.1 h).2
  · intro i hi a _ haY hPa
    refine ⟨fch_pos hPa.1 i, Nat.le_of_lt (fch_lt hPa.1 haY), fch_good hPa.1 i, ?_⟩
    have hb := reachesOneBy_fch (i := i) hPa.1 hPa.2
    apply reachesOneBy_mono _ hb
    have h16 : 2 ^ 4 ≤ 2 ^ tmpl i := Nat.pow_le_pow_right (by decide) (tmpl_ge_four i)
    have hdiv : 3 * X / 2 ^ tmpl i ≤ 3 * X / 2 ^ 4 := Nat.div_le_div_left h16 (by decide)
    have hfv : fval a i ≤ tmpl i := fval_le_tmpl a i
    have htm : tmpl i ≤ 18 := tmpl_le_18 hi
    have h4 : (2:Nat) ^ 4 = 16 := rfl
    rw [h4] at hdiv
    omega

/-! ## 5. The two-type lattice -/

/-- `f k = NF (2 ^ k)`. -/
def fs (k : Nat) : Nat := NF (2 ^ k)

/-- `h k = NF (3 · 2 ^ k)`. -/
def hs (k : Nat) : Nat := NF (3 * 2 ^ k)

theorem fs_rec {k : Nat} (hk18 : 18 ≤ k) : sumRange 6 (fun i => hs (k - tmpl i)) ≤ fs k := by
  have h64 : 64 ≤ 2 ^ k := by
    have : 2 ^ 6 ≤ 2 ^ k := Nat.pow_le_pow_right (by decide) (by omega)
    exact this
  have h := NF_rec h64
  have e : ∀ i, i < 6 → 3 * 2 ^ k / 2 ^ tmpl i = 3 * 2 ^ (k - tmpl i) := by
    intro i hi
    have ht := tmpl_le_18 hi
    have hsplit : 2 ^ k = 2 ^ (k - tmpl i) * 2 ^ tmpl i := by
      rw [← Nat.pow_add, Nat.sub_add_cancel (by omega)]
    rw [hsplit, ← Nat.mul_assoc, Nat.mul_div_cancel _ (Nat.two_pow_pos _)]
  unfold fs hs
  have e' : sumRange 6 (fun i => NF (3 * 2 ^ (k - tmpl i)))
      = sumRange 6 (fun i => NF (3 * 2 ^ k / 2 ^ tmpl i)) :=
    sumRange_congr (fun i hi => by rw [e i hi])
  rw [e']
  exact h

theorem hs_rec {k : Nat} (hk15 : 15 ≤ k) :
    sumRange 6 (fun i => fs (k + 3 - tmpl i)) ≤ hs k := by
  have h64 : 64 ≤ 3 * 2 ^ k := by
    have : 2 ^ 6 ≤ 2 ^ k := Nat.pow_le_pow_right (by decide) (by omega)
    omega
  have h := NF_rec h64
  unfold fs hs
  apply Nat.le_trans _ h
  apply sumRange_le
  intro i hi
  apply NF_mono
  have ht := tmpl_le_18 hi
  rw [Nat.le_div_iff_mul_le (Nat.two_pow_pos _), ← Nat.pow_add,
    Nat.sub_add_cancel (by omega : tmpl i ≤ k + 3), Nat.pow_add]
  have : (2:Nat) ^ 3 = 8 := rfl
  rw [this]
  omega

/-! ## 6. The rational-ratio induction -/

/-- The `f`-claim: `f k ≥ (13/10) ^ k / 100`. -/
def claimF (k : Nat) : Prop := 2 * 13 ^ k ≤ 10 ^ k * 200 * fs k

/-- The `h`-claim: `h k ≥ 3 (13/10) ^ k / 200`. -/
def claimH (k : Nat) : Prop := 3 * 13 ^ k ≤ 10 ^ k * 200 * hs k

theorem base_bound_f : ∀ k, k ≤ 17 → 2 * 13 ^ k ≤ 200 * 10 ^ k := by decide

theorem base_bound_h : ∀ k, k ≤ 14 → 3 * 13 ^ k ≤ 200 * 10 ^ k := by decide

theorem base_f {k : Nat} (h17 : k ≤ 17) : claimF k := by
  unfold claimF fs
  have h1 := base_bound_f k h17
  rw [Nat.mul_comm 200] at h1
  have h2 : 1 ≤ NF (2 ^ k) := NF_pos (Nat.two_pow_pos k)
  have h3 : 10 ^ k * 200 * 1 ≤ 10 ^ k * 200 * NF (2 ^ k) := Nat.mul_le_mul_left _ h2
  rw [Nat.mul_one] at h3
  omega

theorem base_h {k : Nat} (h14 : k ≤ 14) : claimH k := by
  unfold claimH hs
  have h1 := base_bound_h k h14
  rw [Nat.mul_comm 200] at h1
  have h2 : 1 ≤ NF (3 * 2 ^ k) := NF_pos (by have := Nat.two_pow_pos k; omega)
  have h3 : 10 ^ k * 200 * 1 ≤ 10 ^ k * 200 * NF (3 * 2 ^ k) := Nat.mul_le_mul_left _ h2
  rw [Nat.mul_one] at h3
  omega

/-- The certified inequality behind the `f`-step: `3 Σ (10/13) ^ tmpl i ≥ 2`. -/
theorem I1 : 2 * 13 ^ 18 ≤ 3 * sumRange 6 (fun i => 10 ^ tmpl i * 13 ^ (18 - tmpl i)) := by
  decide

/-- The certified inequality behind the `h`-step: `2 Σ (10/13) ^ (tmpl i − 3) ≥ 3`. -/
theorem I2 : 3 * 13 ^ 15 ≤ 2 * sumRange 6 (fun i => 10 ^ (tmpl i - 3) * 13 ^ (18 - tmpl i)) := by
  decide

theorem rearr (x y A B : Nat) : x * (y * (A * B)) = A * (y * (x * B)) := by
  rw [Nat.mul_left_comm x y, Nat.mul_left_comm x A, Nat.mul_left_comm y A]

theorem step_f {k : Nat} (h18 : 18 ≤ k) (H : ∀ i, i < 6 → claimH (k - tmpl i)) : claimF k := by
  unfold claimF
  have hrec := fs_rec h18
  have h1 : 10 ^ k * 200 * sumRange 6 (fun i => hs (k - tmpl i)) ≤ 10 ^ k * 200 * fs k :=
    Nat.mul_le_mul_left _ hrec
  rw [← sumRange_const_mul] at h1
  have h2 : sumRange 6 (fun i => 10 ^ tmpl i * (3 * 13 ^ (k - tmpl i)))
      ≤ sumRange 6 (fun i => 10 ^ k * 200 * hs (k - tmpl i)) := by
    apply sumRange_le
    intro i hi
    have ht := tmpl_le_18 hi
    have hH := H i hi
    unfold claimH at hH
    have e : 10 ^ k = 10 ^ tmpl i * 10 ^ (k - tmpl i) := by
      rw [← Nat.pow_add, Nat.add_sub_cancel' (by omega)]
    rw [e, Nat.mul_assoc, Nat.mul_assoc]
    apply Nat.mul_le_mul_left
    rw [← Nat.mul_assoc]
    exact hH
  have h3 : sumRange 6 (fun i => 10 ^ tmpl i * (3 * 13 ^ (k - tmpl i)))
      = 13 ^ (k - 18) * (3 * sumRange 6 (fun i => 10 ^ tmpl i * 13 ^ (18 - tmpl i))) := by
    rw [← sumRange_const_mul, ← sumRange_const_mul]
    apply sumRange_congr
    intro i hi
    have ht := tmpl_le_18 hi
    have e : 13 ^ (k - tmpl i) = 13 ^ (k - 18) * 13 ^ (18 - tmpl i) := by
      rw [← Nat.pow_add]
      congr 1
      omega
    rw [e]
    exact rearr _ _ _ _
  have h4 : 13 ^ (k - 18) * (2 * 13 ^ 18)
      ≤ 13 ^ (k - 18) * (3 * sumRange 6 (fun i => 10 ^ tmpl i * 13 ^ (18 - tmpl i))) :=
    Nat.mul_le_mul_left _ I1
  have h5 : 13 ^ (k - 18) * (2 * 13 ^ 18) = 2 * 13 ^ k := by
    rw [Nat.mul_left_comm, ← Nat.pow_add]
    congr 2
    omega
  omega

theorem step_h {k : Nat} (h15 : 15 ≤ k) (H : ∀ i, i < 6 → claimF (k + 3 - tmpl i)) : claimH k := by
  unfold claimH
  have hrec := hs_rec h15
  have h1 : 10 ^ k * 200 * sumRange 6 (fun i => fs (k + 3 - tmpl i)) ≤ 10 ^ k * 200 * hs k :=
    Nat.mul_le_mul_left _ hrec
  rw [← sumRange_const_mul] at h1
  have h2 : sumRange 6 (fun i => 10 ^ (tmpl i - 3) * (2 * 13 ^ (k + 3 - tmpl i)))
      ≤ sumRange 6 (fun i => 10 ^ k * 200 * fs (k + 3 - tmpl i)) := by
    apply sumRange_le
    intro i hi
    have ht := tmpl_le_18 hi
    have ht4 := tmpl_ge_four i
    have hH := H i hi
    unfold claimF at hH
    have e : 10 ^ k = 10 ^ (tmpl i - 3) * 10 ^ (k + 3 - tmpl i) := by
      rw [← Nat.pow_add]
      congr 1
      omega
    rw [e, Nat.mul_assoc, Nat.mul_assoc]
    apply Nat.mul_le_mul_left
    rw [← Nat.mul_assoc]
    exact hH
  have h3 : sumRange 6 (fun i => 10 ^ (tmpl i - 3) * (2 * 13 ^ (k + 3 - tmpl i)))
      = 13 ^ (k - 15) * (2 * sumRange 6 (fun i => 10 ^ (tmpl i - 3) * 13 ^ (18 - tmpl i))) := by
    rw [← sumRange_const_mul, ← sumRange_const_mul]
    apply sumRange_congr
    intro i hi
    have ht := tmpl_le_18 hi
    have e : 13 ^ (k + 3 - tmpl i) = 13 ^ (k - 15) * 13 ^ (18 - tmpl i) := by
      rw [← Nat.pow_add]
      congr 1
      omega
    rw [e]
    exact rearr _ _ _ _
  have h4 : 13 ^ (k - 15) * (3 * 13 ^ 15)
      ≤ 13 ^ (k - 15) * (2 * sumRange 6 (fun i => 10 ^ (tmpl i - 3) * 13 ^ (18 - tmpl i))) :=
    Nat.mul_le_mul_left _ I2
  have h5 : 13 ^ (k - 15) * (3 * 13 ^ 15) = 3 * 13 ^ k := by
    rw [Nat.mul_left_comm, ← Nat.pow_add]
    congr 2
    omega
  omega

/-- **Both claims hold at every `k`.** -/
theorem claims : ∀ n, ∀ k, k ≤ n → claimF k ∧ claimH k := by
  intro n
  induction n with
  | zero =>
    intro k hs
    have : k = 0 := by omega
    subst this
    exact ⟨base_f (by omega), base_h (by omega)⟩
  | succ n ih =>
    intro k hs
    by_cases hkn : k ≤ n
    · exact ih k hkn
    · have hs' : k = n + 1 := by omega
      subst hs'
      constructor
      · by_cases h18 : 18 ≤ n + 1
        · exact step_f h18 (fun i _ => (ih (n + 1 - tmpl i) (by have := tmpl_ge_four i; omega)).2)
        · exact base_f (by omega)
      · by_cases h15 : 15 ≤ n + 1
        · exact step_h h15 (fun i _ => (ih (n + 1 + 3 - tmpl i) (by have := tmpl_ge_four i; omega)).1)
        · exact base_h (by omega)

theorem growth (k : Nat) : 2 * 13 ^ k ≤ 10 ^ k * 200 * fs k :=
  (claims k k (Nat.le_refl k)).1

/-! ## 7. The exponent `3/8` -/

theorem exists_bracket_two : ∀ N, 1 ≤ N → ∃ k, 2 ^ k ≤ N ∧ N < 2 ^ (k + 1) := by
  intro N
  induction N with
  | zero => intro h; omega
  | succ N ih =>
    intro _
    by_cases hN : N = 0
    · subst hN; exact ⟨0, by decide, by decide⟩
    · obtain ⟨k, hk1, hk2⟩ := ih (by omega)
      by_cases hlt : N + 1 < 2 ^ (k + 1)
      · exact ⟨k, by omega, hlt⟩
      · refine ⟨k + 1, by omega, ?_⟩
        rw [Nat.pow_succ 2 (k + 1)]
        have : 1 ≤ 2 ^ (k + 1) := Nat.pow_pos (by decide)
        omega

theorem thirteen_pow_eight : 8 * 10 ^ 8 ≤ 13 ^ 8 := by decide

/-- `(13 ^ 8) ^ k ≥ 8 ^ k · 10 ^ (8k)`. -/
theorem thirteen_pow_ge (k : Nat) : 8 ^ k * 10 ^ (8 * k) ≤ 13 ^ (8 * k) := by
  rw [Nat.pow_mul, Nat.pow_mul, ← Nat.mul_pow]
  exact Nat.pow_le_pow_left thirteen_pow_eight k

/-- **The main theorem of this file.**  For every `N ≥ 1`,
`N ^ 3 < 8 · 10 ^ 16 · (reachesOneUpToCount N) ^ 8`: at least `N ^ (3/8) / 131`
integers in `[1, N]` reach `1` within `N` accelerated steps. -/
theorem count_pow_eight {N : Nat} (hN : 1 ≤ N) :
    N ^ 3 < 8 * 10 ^ 16 * reachesOneUpToCount N ^ 8 := by
  obtain ⟨k, hk1, hk2⟩ := exists_bracket_two N hN
  have hg := growth k
  have hf : fs k ≤ reachesOneUpToCount N := Nat.le_trans (NF_mono hk1) (NF_le_count N)
  have hc : 2 * 13 ^ k ≤ 10 ^ k * 200 * reachesOneUpToCount N :=
    Nat.le_trans hg (Nat.mul_le_mul_left _ hf)
  have h8 : (2 * 13 ^ k) ^ 8 ≤ (10 ^ k * 200 * reachesOneUpToCount N) ^ 8 :=
    Nat.pow_le_pow_left hc 8
  rw [Nat.mul_pow, Nat.mul_pow, Nat.mul_pow, ← Nat.pow_mul, ← Nat.pow_mul,
    Nat.mul_comm k 8] at h8
  -- h8 : 2 ^ 8 * 13 ^ (8 * k) ≤ 10 ^ (8 * k) * 200 ^ 8 * c ^ 8
  have h13 := thirteen_pow_ge k
  have hL : 2 ^ 8 * (8 ^ k * 10 ^ (8 * k)) ≤ 2 ^ 8 * 13 ^ (8 * k) := Nat.mul_le_mul_left _ h13
  have hR : 10 ^ (8 * k) * 200 ^ 8 * reachesOneUpToCount N ^ 8
      = 10 ^ (8 * k) * (200 ^ 8 * reachesOneUpToCount N ^ 8) := Nat.mul_assoc _ _ _
  have hL' : 2 ^ 8 * (8 ^ k * 10 ^ (8 * k)) = 10 ^ (8 * k) * (2 ^ 8 * 8 ^ k) := by
    rw [Nat.mul_comm (8 ^ k), ← Nat.mul_assoc, Nat.mul_comm (2 ^ 8), Nat.mul_assoc]
  rw [hL'] at hL
  rw [hR] at h8
  have hcancel : 2 ^ 8 * 8 ^ k ≤ 200 ^ 8 * reachesOneUpToCount N ^ 8 :=
    Nat.le_of_mul_le_mul_left (Nat.le_trans hL h8) (Nat.pow_pos (by decide))
  have h200 : (200:Nat) ^ 8 = 2 ^ 8 * 10 ^ 16 := by decide
  rw [h200, Nat.mul_assoc] at hcancel
  have hcancel' : 8 ^ k ≤ 10 ^ 16 * reachesOneUpToCount N ^ 8 :=
    Nat.le_of_mul_le_mul_left hcancel (by decide)
  have hN3 : N ^ 3 < (2 ^ (k + 1)) ^ 3 := Nat.pow_lt_pow_left hk2 (by decide)
  have h2k : (2 ^ (k + 1)) ^ 3 = 8 * 8 ^ k := by
    rw [← Nat.pow_mul, Nat.mul_comm, Nat.pow_mul, show (2:Nat) ^ 3 = 8 from rfl, Nat.pow_succ,
      Nat.mul_comm]
  rw [h2k] at hN3
  have : 8 * 8 ^ k ≤ 8 * (10 ^ 16 * reachesOneUpToCount N ^ 8) := Nat.mul_le_mul_left 8 hcancel'
  rw [← Nat.mul_assoc] at this
  omega

end TreeBranching
end Collatz
