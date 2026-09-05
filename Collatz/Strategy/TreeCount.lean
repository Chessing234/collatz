import Collatz.Strategy.ReverseTree
import Collatz.Papers.KrasikovLagarias2003

/-!
# Counting the inverse tree: an explicit branching family

**Novelty tag: FORMALIZATION-OF-KNOWN.**  The argument is the elementary
branching bound of R. E. Crandall (*On the "3x+1" problem*, Math. Comp. 32,
1978) in the form later sharpened by Sander, Applegate–Lagarias and
Krasikov–Lagarias (Acta Arith. 109, 2003, exponent `0.84`).  The repository
recorded the Krasikov–Lagarias theorem as a bare proposition
(`Papers.KrasikovLagarias2003.krasikovLagariasLowerBound`) with no proof
claimed; standing problem G6 (inverse-tree coverage) had no kernel-checked
content at all.  This file supplies the first exponent.  It is far below the
literature — that is the point of recording it as a scalar that later rounds
must move.

## The construction

Work with the accelerated map `T`.  Every odd `a` prime to `3` has odd
preimages at every valuation `v` with `2 ^ v · a ≡ 1 (mod 3)`, namely

    child a v = (2 ^ v · a − 1) / 3,      T ^ v (child a v) = a.

Those valuations form one parity class; take three consecutive ones
`v₀, v₀ + 2, v₀ + 4` with `v₀ ∈ {1, 2}`.  Multiplying by `4` cycles
`2 ^ v · a` through the residues `1, 4, 7 (mod 9)`, and the child is prime to
`3` exactly when that residue is not `1`.  So **exactly two of the three
children are again odd and prime to `3`** (`sel0_spec`, `sel1_spec`), and
both lie below `22 · a` (`child_lt`, from `2 ^ 6 / 3 < 22`).

Iterating from `1` gives an explicit enumeration `enum k : Nat → Nat` whose
first `2 ^ k` values are pairwise distinct (`enum_inj`, from the fact that
`(a, v) ↦ child a v` is injective on odd `a`), all at most `22 ^ k`
(`enum_le`), and all reach `1` within `6k` accelerated steps
(`enum_reaches`).

## The theorems

* `two_pow_le_count`: `22 ^ k ≤ N → 2 ^ k ≤ reachesOneUpToCount N`.
* `count_pow_five`: for every `N ≥ 1`, `N < 22 · (reachesOneUpToCount N) ^ 5`
  — at least `(N/22) ^ (1/5)` integers up to `N` reach `1`, with the count
  taken in the repository's own computable form (reaching `1` within `N`
  steps).
* `krasikovLagariasLowerBound_holds`: the recorded proposition, in its
  corrected form `N ^ p ≤ (count N) ^ q`, with `p = 1`, `q = 5`, `N₀ = 22 ^ 9`.

## What it is not

The exponent `log 2 / log 22 = 0.2243…` is a worst-case bound: it charges
every child the size of the largest of the three, `2 ^ (v₀ + 4) · a / 3`.
Charging each child its own size gives the recursion
`N(X) ≥ N(3X / 16) + N(3X / 64)` and exponent `≈ 0.30`; tracking the residue
class of `a` modulo `9` and beyond is the Krasikov–Lagarias method.  Neither
is done here.  Positive density is open; Tao's almost-all theorem does not
give it.
-/

namespace Collatz
namespace TreeCount

open Reach

/-! ## 1. The odd child at a prescribed valuation -/

/-- The odd preimage of `a` with `v` halvings in front of it. -/
def child (a v : Nat) : Nat := (2 ^ v * a - 1) / 3

/-- The defining equation, valid whenever the valuation is admissible. -/
theorem child_eq {a v : Nat} (h3 : (2 ^ v * a) % 3 = 1) :
    3 * child a v + 1 = 2 ^ v * a := by
  unfold child
  omega

theorem two_pow_succ_mul (w a : Nat) : 2 ^ (w + 1) * a = 2 * (2 ^ w * a) := by
  rw [Nat.pow_succ, Nat.mul_comm (2 ^ w) 2, Nat.mul_assoc]

theorem two_pow_add_two_mul (v a : Nat) : 2 ^ (v + 2) * a = 4 * (2 ^ v * a) := by
  rw [Nat.pow_add, show (2:Nat) ^ 2 = 4 from rfl, Nat.mul_comm (2 ^ v) 4, Nat.mul_assoc]

theorem two_pow_add_four_mul (v a : Nat) : 2 ^ (v + 4) * a = 16 * (2 ^ v * a) := by
  rw [Nat.pow_add, show (2:Nat) ^ 4 = 16 from rfl, Nat.mul_comm (2 ^ v) 16, Nat.mul_assoc]

/-- A child at positive valuation is odd. -/
theorem child_odd {a v : Nat} (hv : 1 ≤ v) (h3 : (2 ^ v * a) % 3 = 1) :
    child a v % 2 = 1 := by
  have h := child_eq h3
  obtain ⟨w, rfl⟩ : ∃ w, v = w + 1 := ⟨v - 1, by omega⟩
  have hm := two_pow_succ_mul w a
  omega

/-- A child is positive as soon as `a` is. -/
theorem child_pos {a v : Nat} (ha : 0 < a) (hv : 1 ≤ v) (h3 : (2 ^ v * a) % 3 = 1) :
    0 < child a v := by
  have h := child_eq h3
  obtain ⟨w, rfl⟩ : ∃ w, v = w + 1 := ⟨v - 1, by omega⟩
  have hm := two_pow_succ_mul w a
  have hp : 0 < 2 ^ w * a := Nat.mul_pos (Nat.two_pow_pos w) ha
  omega

/-- **Fertility.**  The child is prime to `3` exactly when `2 ^ v · a` is not
`1` modulo `9`. -/
theorem child_mod_three {a v : Nat} (h3 : (2 ^ v * a) % 3 = 1)
    (h9 : (2 ^ v * a) % 9 ≠ 1) : child a v % 3 ≠ 0 := by
  unfold child
  omega

/-- The child really climbs back to `a` in exactly `v` accelerated steps. -/
theorem orbit_child {a v : Nat} (hv : 1 ≤ v) (h3 : (2 ^ v * a) % 3 = 1) :
    acceleratedOrbit v (child a v) = a := by
  obtain ⟨w, rfl⟩ : ∃ w, v = w + 1 := ⟨v - 1, by omega⟩
  have hm := two_pow_succ_mul w a
  have heq := child_eq h3
  have hodd : child a (w + 1) % 2 = 1 := child_odd (by omega) h3
  have hstep : acceleratedStep (child a (w + 1)) = 2 ^ w * a := by
    rw [acceleratedStep, if_neg (by omega)]
    omega
  rw [acceleratedOrbit_succ, hstep]
  exact ReverseTree.orbit_two_pow_mul w a

/-- Valuations up to `6` keep the child below `22 · a`. -/
theorem child_lt {a v : Nat} (hv : v ≤ 6) (h3 : (2 ^ v * a) % 3 = 1) :
    child a v < 22 * a := by
  have h := child_eq h3
  have hle : 2 ^ v * a ≤ 64 * a := by
    have h1 : 2 ^ v ≤ 2 ^ 6 := Nat.pow_le_pow_right (by decide) hv
    have h64 : (2:Nat) ^ 6 = 64 := rfl
    rw [h64] at h1
    exact Nat.mul_le_mul_right a h1
  omega

/-! ## 2. Injectivity: a child remembers its parent and its valuation -/

/-- `2 ^ v · a` with `a` odd determines both `v` and `a`. -/
theorem two_pow_mul_odd_inj {v v' a a' : Nat} (ha : a % 2 = 1) (ha' : a' % 2 = 1)
    (h : 2 ^ v * a = 2 ^ v' * a') : v = v' ∧ a = a' := by
  rcases Nat.lt_trichotomy v v' with hlt | heq | hgt
  · exfalso
    obtain ⟨d, rfl⟩ : ∃ d, v' = v + (d + 1) := ⟨v' - v - 1, by omega⟩
    rw [Nat.pow_add, Nat.mul_assoc] at h
    have h2 := Nat.eq_of_mul_eq_mul_left (Nat.two_pow_pos v) h
    have hm := two_pow_succ_mul d a'
    omega
  · subst heq
    exact ⟨rfl, Nat.eq_of_mul_eq_mul_left (Nat.two_pow_pos v) h⟩
  · exfalso
    obtain ⟨d, rfl⟩ : ∃ d, v = v' + (d + 1) := ⟨v - v' - 1, by omega⟩
    rw [Nat.pow_add, Nat.mul_assoc] at h
    have h2 := Nat.eq_of_mul_eq_mul_left (Nat.two_pow_pos v') h.symm
    have hm := two_pow_succ_mul d a
    omega

/-- Two admissible children coincide only if parent and valuation coincide. -/
theorem child_inj {a a' v v' : Nat} (ha : a % 2 = 1) (ha' : a' % 2 = 1)
    (h3 : (2 ^ v * a) % 3 = 1) (h3' : (2 ^ v' * a') % 3 = 1)
    (h : child a v = child a' v') : v = v' ∧ a = a' := by
  have e := child_eq h3
  have e' := child_eq h3'
  exact two_pow_mul_odd_inj ha ha' (by omega)

/-! ## 3. Selecting two fertile children -/

/-- The least admissible valuation: `2` when `a ≡ 1`, `1` when `a ≡ 2 (mod 3)`. -/
def v0 (a : Nat) : Nat := if a % 3 = 1 then 2 else 1

/-- `2 ^ v₀ · a`, the first admissible multiple. -/
def base (a : Nat) : Nat := 2 ^ v0 a * a

/-- The first selected valuation. -/
def sel0 (a : Nat) : Nat := if base a % 9 = 1 then v0 a + 2 else v0 a

/-- The second selected valuation. -/
def sel1 (a : Nat) : Nat := if base a % 9 = 4 then v0 a + 2 else v0 a + 4

theorem v0_ge_one (a : Nat) : 1 ≤ v0 a := by
  unfold v0
  split <;> omega

theorem v0_le_two (a : Nat) : v0 a ≤ 2 := by
  unfold v0
  split <;> omega

/-- The base multiple is `1` modulo `3` whenever `a` is prime to `3`. -/
theorem base_mod_three {a : Nat} (h : a % 3 ≠ 0) : base a % 3 = 1 := by
  unfold base v0
  by_cases h1 : a % 3 = 1
  · rw [if_pos h1, show (2:Nat) ^ 2 = 4 from rfl]
    omega
  · rw [if_neg h1, Nat.pow_one]
    omega

theorem base_shift_two (a : Nat) : 2 ^ (v0 a + 2) * a = 4 * base a :=
  two_pow_add_two_mul (v0 a) a

theorem base_shift_four (a : Nat) : 2 ^ (v0 a + 4) * a = 16 * base a :=
  two_pow_add_four_mul (v0 a) a

/-- The first selection is admissible, fertile, and at most `6`. -/
theorem sel0_spec {a : Nat} (h : a % 3 ≠ 0) :
    1 ≤ sel0 a ∧ sel0 a ≤ 6 ∧ (2 ^ sel0 a * a) % 3 = 1 ∧ (2 ^ sel0 a * a) % 9 ≠ 1 := by
  have hb := base_mod_three h
  have h1 := v0_ge_one a
  have h2 := v0_le_two a
  unfold sel0
  by_cases h9 : base a % 9 = 1
  · rw [if_pos h9, base_shift_two]
    refine ⟨by omega, by omega, by omega, by omega⟩
  · rw [if_neg h9]
    refine ⟨by omega, by omega, hb, h9⟩

/-- The second selection is admissible, fertile, and at most `6`. -/
theorem sel1_spec {a : Nat} (h : a % 3 ≠ 0) :
    1 ≤ sel1 a ∧ sel1 a ≤ 6 ∧ (2 ^ sel1 a * a) % 3 = 1 ∧ (2 ^ sel1 a * a) % 9 ≠ 1 := by
  have hb := base_mod_three h
  have h1 := v0_ge_one a
  have h2 := v0_le_two a
  unfold sel1
  by_cases h9 : base a % 9 = 4
  · rw [if_pos h9, base_shift_two]
    refine ⟨by omega, by omega, by omega, by omega⟩
  · rw [if_neg h9, base_shift_four]
    refine ⟨by omega, by omega, by omega, by omega⟩

/-- The two selections are distinct valuations. -/
theorem sel0_lt_sel1 (a : Nat) : sel0 a < sel1 a := by
  unfold sel0 sel1
  by_cases h9 : base a % 9 = 1
  · rw [if_pos h9, if_neg (by omega)]
    omega
  · rw [if_neg h9]
    split <;> omega

/-! ## 4. The enumeration -/

/-- Odd and prime to three: the fertile nodes of the inverse tree. -/
def Good (n : Nat) : Prop := n % 2 = 1 ∧ n % 3 ≠ 0

theorem good_child0 {a : Nat} (ha : Good a) : Good (child a (sel0 a)) := by
  obtain ⟨h1, _, h3, h9⟩ := sel0_spec ha.2
  exact ⟨child_odd h1 h3, child_mod_three h3 h9⟩

theorem good_child1 {a : Nat} (ha : Good a) : Good (child a (sel1 a)) := by
  obtain ⟨h1, _, h3, h9⟩ := sel1_spec ha.2
  exact ⟨child_odd h1 h3, child_mod_three h3 h9⟩

/-- Level `k` of the tree, indexed by the binary word `i` of choices. -/
def enum : Nat → Nat → Nat
  | 0, _ => 1
  | k + 1, i =>
    if i % 2 = 0 then child (enum k (i / 2)) (sel0 (enum k (i / 2)))
    else child (enum k (i / 2)) (sel1 (enum k (i / 2)))

theorem enum_zero (i : Nat) : enum 0 i = 1 := rfl

theorem enum_succ (k i : Nat) :
    enum (k + 1) i =
      if i % 2 = 0 then child (enum k (i / 2)) (sel0 (enum k (i / 2)))
      else child (enum k (i / 2)) (sel1 (enum k (i / 2))) := rfl

/-- Every node of the enumeration is odd and prime to three. -/
theorem enum_good : ∀ k i, Good (enum k i) := by
  intro k
  induction k with
  | zero => intro i; exact ⟨rfl, by show (1:Nat) % 3 ≠ 0; decide⟩
  | succ k ih =>
    intro i
    rw [enum_succ]
    split
    · exact good_child0 (ih _)
    · exact good_child1 (ih _)

theorem enum_pos (k i : Nat) : 0 < enum k i := by
  have := (enum_good k i).1
  omega

/-- Every node at level `k` is at most `22 ^ k`. -/
theorem enum_le : ∀ k i, enum k i ≤ 22 ^ k := by
  intro k
  induction k with
  | zero => intro i; exact Nat.le_refl 1
  | succ k ih =>
    intro i
    rw [enum_succ, Nat.pow_succ]
    have hg := enum_good k (i / 2)
    have hpos := enum_pos k (i / 2)
    have hle := ih (i / 2)
    split
    · obtain ⟨_, h6, h3, _⟩ := sel0_spec hg.2
      have := child_lt h6 h3
      have h22 : 22 * enum k (i / 2) ≤ 22 ^ k * 22 := by
        rw [Nat.mul_comm (22 ^ k) 22]
        exact Nat.mul_le_mul_left 22 hle
      omega
    · obtain ⟨_, h6, h3, _⟩ := sel1_spec hg.2
      have := child_lt h6 h3
      have h22 : 22 * enum k (i / 2) ≤ 22 ^ k * 22 := by
        rw [Nat.mul_comm (22 ^ k) 22]
        exact Nat.mul_le_mul_left 22 hle
      omega

/-- Every node at level `k` reaches `1` within `6k` accelerated steps. -/
theorem enum_reaches : ∀ k i, ∃ j, j ≤ 6 * k ∧ acceleratedOrbit j (enum k i) = 1 := by
  intro k
  induction k with
  | zero => intro i; exact ⟨0, Nat.le_refl 0, rfl⟩
  | succ k ih =>
    intro i
    obtain ⟨j, hj, hj1⟩ := ih (i / 2)
    have hg := enum_good k (i / 2)
    rw [enum_succ]
    split
    · obtain ⟨h1, h6, h3, _⟩ := sel0_spec hg.2
      refine ⟨j + sel0 (enum k (i / 2)), by omega, ?_⟩
      rw [← acceleratedOrbit_add, orbit_child h1 h3, hj1]
    · obtain ⟨h1, h6, h3, _⟩ := sel1_spec hg.2
      refine ⟨j + sel1 (enum k (i / 2)), by omega, ?_⟩
      rw [← acceleratedOrbit_add, orbit_child h1 h3, hj1]

/-- **Injectivity.**  The first `2 ^ k` nodes at level `k` are pairwise distinct. -/
theorem enum_inj : ∀ k i j, i < 2 ^ k → j < 2 ^ k → enum k i = enum k j → i = j := by
  intro k
  induction k with
  | zero =>
    intro i j hi hj _
    have : (2:Nat) ^ 0 = 1 := rfl
    omega
  | succ k ih =>
    intro i j hi hj h
    have h2 : (2:Nat) ^ (k + 1) = 2 * 2 ^ k := by rw [Nat.pow_succ, Nat.mul_comm]
    have hi' : i / 2 < 2 ^ k := by omega
    have hj' : j / 2 < 2 ^ k := by omega
    have ga := enum_good k (i / 2)
    have gb := enum_good k (j / 2)
    obtain ⟨_, _, a0, _⟩ := sel0_spec ga.2
    obtain ⟨_, _, a1, _⟩ := sel1_spec ga.2
    obtain ⟨_, _, b0, _⟩ := sel0_spec gb.2
    obtain ⟨_, _, b1, _⟩ := sel1_spec gb.2
    have hlt_a := sel0_lt_sel1 (enum k (i / 2))
    rw [enum_succ, enum_succ] at h
    by_cases hi2 : i % 2 = 0 <;> by_cases hj2 : j % 2 = 0
    · rw [if_pos hi2, if_pos hj2] at h
      obtain ⟨_, hab⟩ := child_inj ga.1 gb.1 a0 b0 h
      have := ih _ _ hi' hj' hab
      omega
    · rw [if_pos hi2, if_neg hj2] at h
      obtain ⟨hv, hab⟩ := child_inj ga.1 gb.1 a0 b1 h
      have := ih _ _ hi' hj' hab
      rw [this] at hv hlt_a
      omega
    · rw [if_neg hi2, if_pos hj2] at h
      obtain ⟨hv, hab⟩ := child_inj ga.1 gb.1 a1 b0 h
      have := ih _ _ hi' hj' hab
      rw [this] at hv hlt_a
      omega
    · rw [if_neg hi2, if_neg hj2] at h
      obtain ⟨_, hab⟩ := child_inj ga.1 gb.1 a1 b1 h
      have := ih _ _ hi' hj' hab
      omega

/-! ## 5. Counting an injective family with `countUpTo` -/

/-- `hitB g m x` says that `x` is one of `g 0, …, g (m − 1)`. -/
def hitB (g : Nat → Nat) : Nat → Nat → Bool
  | 0, _ => false
  | m + 1, x => hitB g m x || decide (g m = x)

theorem hitB_iff (g : Nat → Nat) : ∀ m x, hitB g m x = true ↔ ∃ i, i < m ∧ g i = x := by
  intro m
  induction m with
  | zero =>
    intro x
    constructor
    · intro h; exact absurd h (by simp [hitB])
    · intro ⟨i, hi, _⟩; omega
  | succ m ih =>
    intro x
    show (hitB g m x || decide (g m = x)) = true ↔ _
    rw [Bool.or_eq_true, ih, decide_eq_true_iff]
    constructor
    · intro h
      rcases h with ⟨i, hi, hx⟩ | hx
      · exact ⟨i, by omega, hx⟩
      · exact ⟨m, by omega, hx⟩
    · intro ⟨i, hi, hx⟩
      by_cases him : i = m
      · right; rw [← him]; exact hx
      · left; exact ⟨i, by omega, hx⟩

/-- Two predicates agreeing on `[1, N]` have the same count. -/
theorem countUpTo_congr {p q : Nat → Prop} [∀ a, Decidable (p a)] [∀ a, Decidable (q a)] :
    ∀ N, (∀ x, 1 ≤ x → x ≤ N → (p x ↔ q x)) → countUpTo p N = countUpTo q N := by
  intro N
  induction N with
  | zero => intro _; rfl
  | succ N ih =>
    intro h
    show countUpTo p N + (if p (N + 1) then 1 else 0)
        = countUpTo q N + (if q (N + 1) then 1 else 0)
    rw [ih (fun x hx hxN => h x hx (by omega))]
    have hpq := h (N + 1) (by omega) (Nat.le_refl _)
    by_cases hp : p (N + 1)
    · rw [if_pos hp, if_pos (hpq.1 hp)]
    · rw [if_neg hp, if_neg (fun hq => hp (hpq.2 hq))]

/-- A pointwise implication on `[1, N]` is monotone for the count. -/
theorem countUpTo_mono {p q : Nat → Prop} [∀ a, Decidable (p a)] [∀ a, Decidable (q a)] :
    ∀ N, (∀ x, 1 ≤ x → x ≤ N → p x → q x) → countUpTo p N ≤ countUpTo q N := by
  intro N
  induction N with
  | zero => intro _; exact Nat.le_refl 0
  | succ N ih =>
    intro h
    show countUpTo p N + (if p (N + 1) then 1 else 0)
        ≤ countUpTo q N + (if q (N + 1) then 1 else 0)
    have h1 := ih (fun x hx hxN => h x hx (by omega))
    by_cases hp : p (N + 1)
    · rw [if_pos hp, if_pos (h (N + 1) (by omega) (Nat.le_refl _) hp)]
      omega
    · rw [if_neg hp]
      split <;> omega

/-- Adjoining one fresh value in `[1, N]` raises the count by exactly one. -/
theorem countUpTo_or_eq {q : Nat → Bool} {y : Nat} (hy : 0 < y) (hq : q y = false) :
    ∀ N, y ≤ N →
      countUpTo (fun x => (q x || decide (y = x)) = true) N
        = countUpTo (fun x => q x = true) N + 1 := by
  intro N
  induction N with
  | zero => intro h; omega
  | succ N ih =>
    intro hyN
    show countUpTo (fun x => (q x || decide (y = x)) = true) N
          + (if (q (N + 1) || decide (y = N + 1)) = true then 1 else 0)
        = countUpTo (fun x => q x = true) N + (if q (N + 1) = true then 1 else 0) + 1
    by_cases hyN' : y = N + 1
    · have hc : countUpTo (fun x => (q x || decide (y = x)) = true) N
          = countUpTo (fun x => q x = true) N := by
        apply countUpTo_congr
        intro x hx hxN
        have hne : ¬ (y = x) := by omega
        rw [Bool.or_eq_true, decide_eq_true_iff]
        constructor
        · intro h; rcases h with h | h
          · exact h
          · exact absurd h hne
        · intro h; left; exact h
      rw [hc]
      have hq' : q (N + 1) = false := by rw [← hyN']; exact hq
      rw [hq']
      have h1 : (false || decide (y = N + 1)) = true := by
        rw [Bool.false_or, decide_eq_true_iff]; exact hyN'
      rw [if_pos h1, if_neg (by decide : ¬ (false = true))]
    · rw [ih (by omega)]
      have hne : decide (y = N + 1) = false := by
        rw [decide_eq_false_iff_not]; exact hyN'
      rw [hne, Bool.or_false]
      omega

/-- The empty predicate counts nothing. -/
theorem countUpTo_false : ∀ N, countUpTo (fun _ => False) N = 0 := by
  intro N
  induction N with
  | zero => rfl
  | succ N ih =>
    show countUpTo (fun _ => False) N + (if False then 1 else 0) = 0
    rw [ih, if_neg id]

/-- The count of the first `m` values of an injective family, all in `[1, N]`,
is exactly `m`. -/
theorem countUpTo_hitB {g : Nat → Nat} {N : Nat} :
    ∀ m, (∀ i, i < m → 0 < g i) → (∀ i, i < m → g i ≤ N) →
      (∀ i j, i < m → j < m → g i = g j → i = j) →
      countUpTo (fun x => hitB g m x = true) N = m := by
  intro m
  induction m with
  | zero =>
    intro _ _ _
    have : ∀ x, 1 ≤ x → x ≤ N → (hitB g 0 x = true ↔ False) := by
      intro x _ _
      simp [hitB]
    rw [countUpTo_congr N this, countUpTo_false]
  | succ m ih =>
    intro hpos hle hinj
    have hfresh : hitB g m (g m) = false := by
      cases h : hitB g m (g m) with
      | false => rfl
      | true =>
        exfalso
        obtain ⟨i, hi, hgi⟩ := (hitB_iff g m (g m)).1 h
        have := hinj i m (by omega) (Nat.lt_succ_self m) hgi
        omega
    have hrec := ih (fun i hi => hpos i (by omega)) (fun i hi => hle i (by omega))
      (fun i j hi hj h => hinj i j (by omega) (by omega) h)
    have hstep := countUpTo_or_eq (q := hitB g m) (y := g m) (hpos m (Nat.lt_succ_self m))
      hfresh N (hle m (Nat.lt_succ_self m))
    show countUpTo (fun x => (hitB g m x || decide (g m = x)) = true) N = m + 1
    rw [hstep, hrec]

/-- **The counting principle.**  An injective family of `m` values in `[1, N]`,
all satisfying `p`, forces `countUpTo p N ≥ m`. -/
theorem le_countUpTo_of_inj {p : Nat → Prop} [∀ a, Decidable (p a)] {N m : Nat}
    {g : Nat → Nat} (hpos : ∀ i, i < m → 0 < g i) (hle : ∀ i, i < m → g i ≤ N)
    (hp : ∀ i, i < m → p (g i)) (hinj : ∀ i j, i < m → j < m → g i = g j → i = j) :
    m ≤ countUpTo p N := by
  rw [← countUpTo_hitB m hpos hle hinj]
  apply countUpTo_mono
  intro x _ _ hx
  obtain ⟨i, hi, rfl⟩ := (hitB_iff g m x).1 hx
  exact hp i hi

/-! ## 6. The lower bound on the Krasikov–Lagarias count -/

open Papers.KrasikovLagarias2003

/-- An orbit hitting `1` at time `j ≤ B` is detected by `reachesOneBy n B`. -/
theorem reachesOneBy_of_orbit {n j : Nat} (h : acceleratedOrbit j n = 1) :
    ∀ B, j ≤ B → reachesOneBy n B = true := by
  intro B
  induction B with
  | zero =>
    intro hj
    have hj0 : j = 0 := by omega
    subst hj0
    show decide (acceleratedOrbit 0 n = 1) = true
    exact decide_eq_true h
  | succ B ih =>
    intro hj
    show (reachesOneBy n B || decide (acceleratedOrbit (B + 1) n = 1)) = true
    rw [Bool.or_eq_true]
    by_cases hjB : j ≤ B
    · left; exact ih hjB
    · right
      have : j = B + 1 := by omega
      subst this
      exact decide_eq_true h

theorem six_mul_le_pow (k : Nat) : 6 * k ≤ 22 ^ k := by
  induction k with
  | zero => decide
  | succ k ih =>
    rw [Nat.pow_succ]
    have : 1 ≤ 22 ^ k := Nat.pow_pos (by decide)
    omega

/-- **Level `k` of the tree lands in the count.**  Whenever `22 ^ k ≤ N`, at least
`2 ^ k` integers in `[1, N]` reach `1` within `N` accelerated steps. -/
theorem two_pow_le_count {k N : Nat} (hN : 22 ^ k ≤ N) :
    2 ^ k ≤ reachesOneUpToCount N := by
  unfold reachesOneUpToCount
  apply le_countUpTo_of_inj (g := enum k)
  · intro i _; exact enum_pos k i
  · intro i _; exact Nat.le_trans (enum_le k i) hN
  · intro i _
    refine ⟨enum_pos k i, Nat.le_trans (enum_le k i) hN, ?_⟩
    obtain ⟨j, hj, hj1⟩ := enum_reaches k i
    exact reachesOneBy_of_orbit hj1 N (Nat.le_trans hj (Nat.le_trans (six_mul_le_pow k) hN))
  · intro i j hi hj h; exact enum_inj k i j hi hj h

/-- Every `N ≥ 1` sits in a bracket `22 ^ k ≤ N < 22 ^ (k + 1)`. -/
theorem exists_bracket : ∀ N, 1 ≤ N → ∃ k, 22 ^ k ≤ N ∧ N < 22 ^ (k + 1) := by
  intro N
  induction N with
  | zero => intro h; omega
  | succ N ih =>
    intro _
    by_cases hN : N = 0
    · subst hN; exact ⟨0, by decide, by decide⟩
    · obtain ⟨k, hk1, hk2⟩ := ih (by omega)
      by_cases hlt : N + 1 < 22 ^ (k + 1)
      · exact ⟨k, by omega, hlt⟩
      · refine ⟨k + 1, by omega, ?_⟩
        rw [Nat.pow_succ (22) (k + 1)]
        have : 1 ≤ 22 ^ (k + 1) := Nat.pow_pos (by decide)
        omega

theorem thirtytwo_pow_ge (k : Nat) : 22 ^ k ≤ 32 ^ k :=
  Nat.pow_le_pow_left (by decide) k

theorem two_pow_five_mul (k : Nat) : (2 ^ k) ^ 5 = 32 ^ k := by
  rw [← Nat.pow_mul, Nat.mul_comm, Nat.pow_mul]

/-- **The unconditional bound.**  For every `N ≥ 1`,
`N < 22 · (reachesOneUpToCount N) ^ 5`: at least `(N / 22) ^ (1/5)` integers in
`[1, N]` reach `1` within `N` accelerated steps. -/
theorem count_pow_five {N : Nat} (hN : 1 ≤ N) :
    N < 22 * reachesOneUpToCount N ^ 5 := by
  obtain ⟨k, hk1, hk2⟩ := exists_bracket N hN
  have hc := two_pow_le_count hk1
  have h5 : (2 ^ k) ^ 5 ≤ reachesOneUpToCount N ^ 5 := Nat.pow_le_pow_left hc 5
  rw [two_pow_five_mul] at h5
  have h32 := thirtytwo_pow_ge k
  rw [Nat.pow_succ, Nat.mul_comm] at hk2
  have : 22 * 22 ^ k ≤ 22 * reachesOneUpToCount N ^ 5 :=
    Nat.mul_le_mul_left 22 (Nat.le_trans h32 h5)
  omega

/-- `32 ^ k ≥ 22 ^ (k + 1)` from `k = 9` on. -/
theorem thirtytwo_pow_ge_succ : ∀ k, 9 ≤ k → 22 ^ (k + 1) ≤ 32 ^ k := by
  intro k
  induction k with
  | zero => intro h; omega
  | succ k ih =>
    intro h
    by_cases h9 : 9 ≤ k
    · have := ih h9
      rw [Nat.pow_succ, Nat.pow_succ 32 k]
      have h2 : 22 ^ (k + 1) * 22 ≤ 32 ^ k * 22 := Nat.mul_le_mul_right 22 this
      have h3 : 32 ^ k * 22 ≤ 32 ^ k * 32 := Nat.mul_le_mul_left _ (by decide)
      exact Nat.le_trans h2 h3
    · have hk : k = 8 := by omega
      subst hk
      decide

/-- **The recorded proposition, corrected and discharged.**  The file
`Papers/KrasikovLagarias2003` records the Krasikov–Lagarias bound as
`N ^ p ≤ reachesOneUpToCount N * N ^ q` — which is vacuous at `p = q`.  The
definition has been corrected to `N ^ p ≤ (reachesOneUpToCount N) ^ q` and is
proved here with `p = 1`, `q = 5`, `N₀ = 22 ^ 9`. -/
theorem krasikovLagariasLowerBound_holds : krasikovLagariasLowerBound := by
  unfold krasikovLagariasLowerBound
  refine ⟨1, 5, by decide, by decide, 22 ^ 9, ?_⟩
  intro N hN0 hN
  rw [Nat.pow_one]
  obtain ⟨k, hk1, hk2⟩ := exists_bracket N hN
  have hk9 : 9 ≤ k := by
    rcases Nat.lt_or_ge k 9 with hlt | hge
    · exfalso
      have hk : k + 1 ≤ 9 := by omega
      have : 22 ^ (k + 1) ≤ 22 ^ 9 := Nat.pow_le_pow_right (by decide) hk
      omega
    · exact hge
  have hc := two_pow_le_count hk1
  have h5 : (2 ^ k) ^ 5 ≤ reachesOneUpToCount N ^ 5 := Nat.pow_le_pow_left hc 5
  rw [two_pow_five_mul] at h5
  have := thirtytwo_pow_ge_succ k hk9
  omega

end TreeCount
end Collatz
