import Collatz.Strategy.ClassChild
import Collatz.Strategy.LiftExponentThree

/-!
# Backward mixing modulo `3 ^ k`: one node's children cover every class, once

**Novelty tag: NEW (structural).**  The gap list of Round LXXVI named

    ∀ k a, a % 3 ≠ 0 → ∀ i j, i < 3 ^ k → j < 3 ^ k →
      child a (v0 a + 2 * i) % 3 ^ k = child a (v0 a + 2 * j) % 3 ^ k → i = j

as an open Lean statement, and Round LXXVI's next-round list asked for "the
exact order of `4` modulo `3 ^ (k+1)`, completing `LiftExponentThree`, as the
first lemma of backward mixing".  This file proves both, and the surjective
half as well, so the statement becomes a *bijection*:

> **Every fertile odd `a` has, among its admissible backward valuations
> `v₀ a + 2j` with `j < 3 ^ k`, exactly one child in each residue class
> modulo `3 ^ k` — and the class sequence is `3 ^ k`-periodic in `j`.**

Removing the `3 ^ (k-1)` infertile classes: the fertile children of any node,
listed in order of increasing valuation, hit each of the `2 · 3 ^ (k-1)`
fertile classes modulo `3 ^ k` exactly once per period of `2 · 3 ^ (k-1)`.

So the inverse Syracuse tree is *exactly* 3-adically equidistributed at every
node, at every level, and the 3-adic imbalance that costs the
Krasikov–Lagarias system its exponent (`Devices/StochasticTree.md`) is
entirely a **truncation** effect: a node below `X` contributes only its first
`O(1)` children, and a period costs valuation `2 · 3 ^ k`.

## The mechanism

`child a v` modulo `3 ^ k` is decided by `2 ^ v · a` modulo `3 ^ (k+1)`
(`ClassChild.child_mod_pow`), and the admissible valuations are `v₀ a + 2j`,
so the whole child-class sequence is the geometric progression
`base a · 4 ^ j` modulo `3 ^ (k+1)`.  Now `4` generates the index-`2`
subgroup `{u : u ≡ 1 mod 3}` of `(ℤ/3 ^ (k+1))ˣ`, of order `3 ^ k`, and
`s ↦ (s − 1)/3` maps that subgroup bijectively onto `ℤ/3 ^ k`.  The order of
`4` is exactly `3 ^ k` by lifting the exponent: `4 ^ (3 ^ j) = 1 + 3 ^ (j+1) c`
with `c ≡ 1 (mod 3)`.

No Mathlib: the exponent lift is the repository's `cube_three`, the
cancellation of `base a` is a hand-rolled `3 ∤ B → 3 ^ m ∣ B * M → 3 ^ m ∣ M`,
and the pigeonhole (`inj_on_range_surj`) is proved here from scratch.
-/

namespace Collatz
namespace BackwardMixing

open TreeCount Arith LiftExponentThree

/-! ## 1. Lifting the exponent at `3`, sharply -/

/-- The cube expansion used by the lift, in the form the induction needs. -/
theorem nine_expand (x : Nat) :
    9 * x * (3 * (x * x) + 3 * x + 1) = 27 * (x * x * x) + 27 * (x * x) + 9 * x := by
  have h1 : 9 * x * (3 * (x * x)) = 27 * (x * x * x) := by
    rw [← Nat.mul_assoc, Nat.mul_right_comm 9 x 3, show (9:Nat) * 3 = 27 from rfl,
        Nat.mul_assoc 27 x (x * x), Nat.mul_assoc x x x]
  have h2 : 9 * x * (3 * x) = 27 * (x * x) := by
    rw [← Nat.mul_assoc, Nat.mul_right_comm 9 x 3, show (9:Nat) * 3 = 27 from rfl,
        Nat.mul_assoc 27 x x]
  rw [Nat.mul_add, Nat.mul_add, Nat.mul_one, h1, h2]

/-- `4 ^ (3 ^ j) = 3 ^ (j+1) * c + 1` with `c ≡ 1 (mod 3)`: the `3`-adic
valuation of `4 ^ (3 ^ j) − 1` is exactly `j + 1`. -/
theorem four_pow_three_pow :
    ∀ j : Nat, ∃ c : Nat, 4 ^ 3 ^ j = 3 ^ (j + 1) * c + 1 ∧ c % 3 = 1 := by
  intro j
  induction j with
  | zero => exact ⟨1, by decide, by decide⟩
  | succ j ih =>
    obtain ⟨c, hc, hc3⟩ := ih
    refine ⟨c * (3 * (3 ^ j * c * (3 ^ j * c)) + 3 * (3 ^ j * c) + 1), ?_, ?_⟩
    · have hpow : (4:Nat) ^ 3 ^ (j + 1) = 4 ^ 3 ^ j * 4 ^ 3 ^ j * 4 ^ 3 ^ j := by
        rw [Nat.pow_succ, Nat.pow_mul, Nat.pow_succ, Nat.pow_succ, Nat.pow_one]
      have hx : 4 ^ 3 ^ j = 3 * (3 ^ j * c) + 1 := by
        rw [hc, three_pow_succ, Nat.mul_assoc]
      have h1 : (3:Nat) ^ (j + 1 + 1) = 9 * 3 ^ j := by
        rw [three_pow_succ, three_pow_succ]; omega
      have h2 : 3 ^ (j + 1 + 1) * (c * (3 * (3 ^ j * c * (3 ^ j * c)) + 3 * (3 ^ j * c) + 1))
          = 27 * (3 ^ j * c * (3 ^ j * c) * (3 ^ j * c)) + 27 * (3 ^ j * c * (3 ^ j * c))
            + 9 * (3 ^ j * c) := by
        rw [h1, Nat.mul_assoc 9 (3 ^ j) _, ← Nat.mul_assoc (3 ^ j) c _,
            ← Nat.mul_assoc 9 (3 ^ j * c) _, nine_expand]
      rw [hpow, hx, cube_three, h2]
    · have hb : (3 * (3 ^ j * c * (3 ^ j * c)) + 3 * (3 ^ j * c) + 1) % 3 = 1 := by omega
      rw [Nat.mul_mod, hc3, hb]

/-- The binomial expansion to second order: `(A+1) ^ e = e·A + A²·w + 1`. -/
theorem one_add_pow (A : Nat) : ∀ e : Nat, ∃ w, (A + 1) ^ e = e * A + A * A * w + 1 := by
  intro e
  induction e with
  | zero => exact ⟨0, by simp⟩
  | succ e ih =>
    obtain ⟨w, hw⟩ := ih
    refine ⟨e + w * A + w, ?_⟩
    rw [Nat.pow_succ, hw]
    simp [Nat.mul_add, Nat.mul_comm, Nat.mul_left_comm]
    omega

/-- Every positive `d` factors as `3 ^ t * e` with `3 ∤ e`. -/
theorem three_factor : ∀ d : Nat, 0 < d → ∃ t e, d = 3 ^ t * e ∧ e % 3 ≠ 0 := by
  intro d
  induction d using Nat.strongRecOn with
  | _ d ih =>
    intro hd
    by_cases h : d % 3 = 0
    · have hlt : d / 3 < d := by omega
      have hpos : 0 < d / 3 := by omega
      obtain ⟨t, e, he, he3⟩ := ih (d / 3) hlt hpos
      refine ⟨t + 1, e, ?_, he3⟩
      rw [three_pow_succ, Nat.mul_assoc, ← he]
      omega
    · exact ⟨0, d, by simp, h⟩

/-- `3` is prime, in the only form used here. -/
theorem three_dvd_right {B M : Nat} (hB : B % 3 ≠ 0) (h : (B * M) % 3 = 0) : M % 3 = 0 := by
  have hm := Nat.mul_mod B M 3
  have hb : B % 3 = 1 ∨ B % 3 = 2 := by omega
  have hmm : M % 3 = 0 ∨ M % 3 = 1 ∨ M % 3 = 2 := by omega
  rcases hb with hb | hb <;> rcases hmm with hmm | hmm | hmm <;> rw [hb, hmm] at hm <;> omega

/-- A factor prime to `3` can be cancelled from a power of `3`. -/
theorem cancel_three_pow {B : Nat} (hB : B % 3 ≠ 0) :
    ∀ m M : Nat, (B * M) % 3 ^ m = 0 → M % 3 ^ m = 0 := by
  intro m
  induction m with
  | zero => intro M _; rw [Nat.pow_zero]; exact Nat.mod_one M
  | succ m ih =>
    intro M hM
    obtain ⟨q, hq⟩ : (3:Nat) ^ (m + 1) ∣ B * M := Nat.dvd_of_mod_eq_zero hM
    have hBM3 : (B * M) % 3 = 0 := by
      rw [hq, three_pow_succ, Nat.mul_assoc]; omega
    have h3 : M % 3 = 0 := three_dvd_right hB hBM3
    obtain ⟨M', hM'⟩ : ∃ M', M = 3 * M' := ⟨M / 3, by omega⟩
    have hsplit : B * M = 3 * (B * M') := by rw [hM', Nat.mul_left_comm]
    have key : (B * M') % 3 ^ m = 0 := by
      rw [hsplit, three_pow_succ, Nat.mul_mod_mul_left] at hM
      omega
    have hM'0 : M' % 3 ^ m = 0 := ih M' key
    rw [hM', three_pow_succ, Nat.mul_mod_mul_left, hM'0]

/-! ## 2. The order of `4` modulo `3 ^ (k+1)` is exactly `3 ^ k` -/

/-- The sharp lift: for `0 < d`, `4 ^ d = 3 ^ (t+1) * U + 1` with `3 ∤ U` and
`3 ^ t ≤ d`, where `3 ^ t` is the exact power of `3` dividing `d`. -/
theorem four_pow_exact {d : Nat} (hd : 0 < d) :
    ∃ t U, 4 ^ d = 3 ^ (t + 1) * U + 1 ∧ U % 3 ≠ 0 ∧ 3 ^ t ≤ d := by
  obtain ⟨t, e, hde, he3⟩ := three_factor d hd
  obtain ⟨c, hc, hc3⟩ := four_pow_three_pow t
  obtain ⟨w, hw⟩ := one_add_pow (3 ^ (t + 1) * c) e
  refine ⟨t, e * c + 3 ^ (t + 1) * (c * c * w), ?_, ?_, ?_⟩
  · have hsplit : (4:Nat) ^ d = (4 ^ 3 ^ t) ^ e := by rw [hde, Nat.pow_mul]
    have hbase : (4:Nat) ^ 3 ^ t = 3 ^ (t + 1) * c + 1 := hc
    rw [hsplit, hbase, hw]
    have e1 : e * (3 ^ (t + 1) * c) = 3 ^ (t + 1) * (e * c) := by
      rw [Nat.mul_left_comm]
    have e2 : 3 ^ (t + 1) * c * (3 ^ (t + 1) * c) * w
        = 3 ^ (t + 1) * (3 ^ (t + 1) * (c * c * w)) := by
      rw [Nat.mul_assoc (3 ^ (t + 1)) c (3 ^ (t + 1) * c),
          Nat.mul_left_comm c (3 ^ (t + 1)) c, ← Nat.mul_assoc,
          Nat.mul_assoc (3 ^ (t + 1) * 3 ^ (t + 1)) (c * c) w,
          Nat.mul_assoc (3 ^ (t + 1)) (3 ^ (t + 1)) (c * c * w)]
    rw [e1, e2, ← Nat.mul_add]
  · have hcm : (e * c) % 3 ≠ 0 := by
      have hm := Nat.mul_mod e c 3
      have : c % 3 = 1 := hc3
      rw [this, Nat.mul_one] at hm
      omega
    have h9 : (3 ^ (t + 1) * (c * c * w)) % 3 = 0 := by
      rw [three_pow_succ, Nat.mul_assoc]; omega
    omega
  · rw [hde]
    have : 1 ≤ e := by omega
    exact Nat.le_mul_of_pos_right _ (by omega)

/-- **The order of `4` modulo `3 ^ (k+1)` is exactly `3 ^ k`.**  Combined with
`LiftExponentThree.two_pow_three_pow` (`4 ^ (3 ^ k) ≡ 1`), this is the exact
order statement asked for in Round LXXVI. -/
theorem four_pow_ne_one {k d : Nat} (h0 : 0 < d) (hd : d < 3 ^ k) :
    4 ^ d % 3 ^ (k + 1) ≠ 1 := by
  obtain ⟨t, U, hU, hU3, hte⟩ := four_pow_exact h0
  intro hcon
  have htk : t < k := by
    rcases Nat.lt_or_ge t k with h | h
    · exact h
    · have : (3:Nat) ^ k ≤ 3 ^ t := three_pow_le_three_pow h
      omega
  -- `3 ^ (k+1) ∣ 4 ^ d − 1 = 3 ^ (t+1) * U`
  have hdvd : (3 ^ (t + 1) * U) % 3 ^ (k + 1) = 0 := by
    have h1 : 4 ^ d % 3 ^ (k + 1) = 1 := hcon
    have hpos : 0 < 3 ^ (k + 1) := three_pow_pos _
    have := Nat.div_add_mod (4 ^ d) (3 ^ (k + 1))
    have hq : 3 ^ (t + 1) * U = 3 ^ (k + 1) * (4 ^ d / 3 ^ (k + 1)) := by omega
    rw [hq]
    exact Nat.mul_mod_right _ _
  -- cancel `3 ^ (t+1)` from both sides: `3 ^ (k−t) ∣ U`
  have hsplit : (3:Nat) ^ (k + 1) = 3 ^ (t + 1) * 3 ^ (k - t) := by
    rw [← three_pow_add]
    have : t + 1 + (k - t) = k + 1 := by omega
    rw [this]
  rw [hsplit, Nat.mul_mod_mul_left] at hdvd
  have hpos : 0 < (3:Nat) ^ (t + 1) := three_pow_pos _
  have hUmod : U % 3 ^ (k - t) = 0 := by
    rcases Nat.mul_eq_zero.mp hdvd with h | h
    · omega
    · exact h
  have hkt : 1 ≤ k - t := by omega
  have h3dvd : (3:Nat) ∣ 3 ^ (k - t) := ⟨3 ^ (k - t - 1), by
    rw [← three_pow_succ]
    have : k - t - 1 + 1 = k - t := by omega
    rw [this]⟩
  obtain ⟨q, hq⟩ : (3:Nat) ^ (k - t) ∣ U := Nat.dvd_of_mod_eq_zero hUmod
  obtain ⟨r, hr⟩ := h3dvd
  rw [hq, hr] at hU3
  exact hU3 (by rw [Nat.mul_assoc]; omega)

/-! ## 3. Two utilities: cancelling an additive shift, and pigeonhole -/

/-- If `X + B` and `B` agree modulo `m`, then `m` divides `X`. -/
theorem mod_cancel_add {X B m : Nat} (hm : 0 < m) (h : (X + B) % m = B % m) : X % m = 0 := by
  rw [Nat.add_mod] at h
  have hx : X % m < m := Nat.mod_lt _ hm
  have hb : B % m < m := Nat.mod_lt _ hm
  rcases Nat.lt_or_ge (X % m + B % m) m with hlt | hge
  · rw [Nat.mod_eq_of_lt hlt] at h; omega
  · rw [Nat.mod_eq_sub_mod hge, Nat.mod_eq_of_lt (by omega)] at h; omega

/-- Deleting one value from an initial segment is injective off that value. -/
theorem shrink_inj {m x y : Nat} (hx : x ≠ m) (hy : y ≠ m)
    (h : (if x < m then x else x - 1) = (if y < m then y else y - 1)) : x = y := by
  split at h <;> split at h <;> omega

/-- **Pigeonhole.**  A map of `{0,…,n−1}` into itself that is injective is onto. -/
theorem inj_on_range_surj :
    ∀ n : Nat, ∀ f : Nat → Nat,
      (∀ i, i < n → f i < n) → (∀ i j, i < n → j < n → f i = f j → i = j) →
      ∀ r, r < n → ∃ i, i < n ∧ f i = r := by
  intro n
  induction n with
  | zero => intro _ _ _ r hr; omega
  | succ n ih =>
    intro f hlt hinj r hr
    have hfn : f n < n + 1 := hlt n (by omega)
    have hne : ∀ i, i < n → f i ≠ f n := by
      intro i hi hh
      have := hinj i n (by omega) (by omega) hh
      omega
    have hg : ∀ i, i < n → (if f i < f n then f i else f i - 1) < n := by
      intro i hi
      have h1 : f i < n + 1 := hlt i (by omega)
      have h2 := hne i hi
      split <;> omega
    have hginj : ∀ i j, i < n → j < n →
        (if f i < f n then f i else f i - 1) = (if f j < f n then f j else f j - 1) → i = j := by
      intro i j hi hj h
      exact hinj i j (by omega) (by omega) (shrink_inj (hne i hi) (hne j hj) h)
    by_cases hrf : r = f n
    · exact ⟨n, by omega, hrf.symm⟩
    · have hr' : (if r < f n then r else r - 1) < n := by split <;> omega
      obtain ⟨i, hi, hfi⟩ :=
        ih (fun i => if f i < f n then f i else f i - 1) hg hginj _ hr'
      exact ⟨i, by omega, shrink_inj (hne i hi) hrf hfi⟩

/-! ## 4. The child classes of one node -/

/-- The admissible multiples of `a` form the geometric progression
`4 ^ i · base a`. -/
theorem two_pow_step (a i : Nat) : 2 ^ (v0 a + 2 * i) * a = 4 ^ i * base a := by
  unfold base
  rw [Nat.pow_add, Nat.pow_mul, show (2:Nat) ^ 2 = 4 from rfl]
  rw [Nat.mul_comm (2 ^ v0 a) (4 ^ i), Nat.mul_assoc]

theorem step_mod_three {a : Nat} (ha : a % 3 ≠ 0) (i : Nat) :
    (2 ^ (v0 a + 2 * i) * a) % 3 = 1 := by
  rw [two_pow_step, Nat.mul_mod, base_mod_three ha, Nat.mul_one]
  have h4 : (4:Nat) ^ i % 3 = 1 := by
    induction i with
    | zero => decide
    | succ i ih => rw [Nat.pow_succ, Nat.mul_mod, ih]
  rw [h4]

theorem step_mod_three_pow_ne {a : Nat} (ha : a % 3 ≠ 0) (i : Nat) :
    (4 ^ i * base a) % 3 ≠ 0 := by
  have := step_mod_three ha i
  rw [two_pow_step] at this
  omega

/-- If a geometric step returns to its start modulo `3 ^ (k+1)`, the ratio is `1`. -/
theorem four_pow_eq_one_of_mul {B d k : Nat} (hB : B % 3 ≠ 0)
    (h : (B * 4 ^ d) % 3 ^ (k + 1) = B % 3 ^ (k + 1)) : 4 ^ d % 3 ^ (k + 1) = 1 := by
  have h3 : (1:Nat) < 3 ^ (k + 1) := by
    have := three_le_three_pow (k := k + 1) (by omega); omega
  rcases Nat.eq_zero_or_pos d with hd | hd
  · rw [hd, Nat.pow_zero, Nat.mod_eq_of_lt h3]
  obtain ⟨t, U, hU, hU3, _⟩ := four_pow_exact hd
  have expand : B * 4 ^ d = B * (3 ^ (t + 1) * U) + B := by
    rw [hU, Nat.mul_add, Nat.mul_one]
  have hBY : (B * (3 ^ (t + 1) * U)) % 3 ^ (k + 1) = 0 := by
    apply mod_cancel_add (three_pow_pos _)
    rw [← expand]
    exact h
  have hY : (3 ^ (t + 1) * U) % 3 ^ (k + 1) = 0 := cancel_three_pow hB _ _ hBY
  rw [hU, Nat.add_mod, hY, Nat.mod_eq_of_lt h3, Nat.zero_add]
  exact Nat.mod_eq_of_lt h3

/-! ## 5. Backward mixing -/

/-- `4 ^ i * B` is prime to `3` whenever `B` is. -/
theorem four_pow_mul_ne {B : Nat} (hB : B % 3 ≠ 0) (i : Nat) : (4 ^ i * B) % 3 ≠ 0 := by
  have h4 : (4:Nat) ^ i % 3 = 1 := by
    induction i with
    | zero => decide
    | succ i ih => rw [Nat.pow_succ, Nat.mul_mod, ih]
  rw [Nat.mul_mod, h4, Nat.one_mul, Nat.mod_mod_of_dvd _ (Nat.dvd_refl 3)]
  exact hB

/-- **The geometric progression `4 ^ i · B` is injective modulo `3 ^ (k+1)`
for `i < 3 ^ k`**, for every `B` prime to `3`.  One direction, indices ordered. -/
theorem class_eq_imp_eq {B : Nat} (hB : B % 3 ≠ 0) {k i j : Nat} (hij : i ≤ j) (hj : j < 3 ^ k)
    (h : (4 ^ i * B) % 3 ^ (k + 1) = (4 ^ j * B) % 3 ^ (k + 1)) : i = j := by
  have hsplit : (4:Nat) ^ j * B = (4 ^ i * B) * 4 ^ (j - i) := by
    have he : i + (j - i) = j := by omega
    have hji : (4:Nat) ^ j = 4 ^ i * 4 ^ (j - i) := by rw [← Nat.pow_add, he]
    rw [hji, Nat.mul_right_comm]
  rw [hsplit] at h
  have hone := four_pow_eq_one_of_mul (four_pow_mul_ne hB i) h.symm
  rcases Nat.eq_zero_or_pos (j - i) with hd | hd
  · omega
  · exact absurd hone (four_pow_ne_one hd (by omega))

/-- **Backward mixing, injective half** — the gap-list statement of Round LXXVI:
the children of one node at the admissible valuations `v₀ a + 2i`, `i < 3 ^ k`,
have pairwise distinct classes modulo `3 ^ k`. -/
theorem child_class_inj {a : Nat} (ha : a % 3 ≠ 0) (k : Nat) {i j : Nat}
    (hi : i < 3 ^ k) (hj : j < 3 ^ k)
    (h : child a (v0 a + 2 * i) % 3 ^ k = child a (v0 a + 2 * j) % 3 ^ k) : i = j := by
  have hdvd : (3:Nat) ∣ 3 ^ (k + 1) := ⟨3 ^ k, three_pow_succ k⟩
  have hs : ∀ l : Nat, (2 ^ (v0 a + 2 * l) * a) % 3 ^ (k + 1) % 3 = 1 := by
    intro l
    rw [Nat.mod_mod_of_dvd _ hdvd]
    exact step_mod_three ha l
  rw [ClassChild.child_mod_pow (step_mod_three ha i) k,
      ClassChild.child_mod_pow (step_mod_three ha j) k] at h
  have hsi := hs i
  have hsj := hs j
  have heq : (2 ^ (v0 a + 2 * i) * a) % 3 ^ (k + 1)
      = (2 ^ (v0 a + 2 * j) * a) % 3 ^ (k + 1) := by omega
  rw [two_pow_step, two_pow_step] at heq
  have hbase : base a % 3 ≠ 0 := by rw [base_mod_three ha]; omega
  rcases Nat.le_total i j with hij | hij
  · exact class_eq_imp_eq hbase hij hj heq
  · exact (class_eq_imp_eq hbase hij hi heq.symm).symm

/-- **Backward mixing, surjective half.**  Every class modulo `3 ^ k` is the
class of one of the first `3 ^ k` children. -/
theorem child_class_surj {a : Nat} (ha : a % 3 ≠ 0) (k : Nat) {r : Nat} (hr : r < 3 ^ k) :
    ∃ i, i < 3 ^ k ∧ child a (v0 a + 2 * i) % 3 ^ k = r :=
  inj_on_range_surj (3 ^ k) (fun i => child a (v0 a + 2 * i) % 3 ^ k)
    (fun _ _ => Nat.mod_lt _ (three_pow_pos _))
    (fun _ _ hi hj hh => child_class_inj ha k hi hj hh) r hr

/-- **The class sequence is `3 ^ k`-periodic in the slot index.** -/
theorem child_class_period {a : Nat} (ha : a % 3 ≠ 0) (k i : Nat) :
    child a (v0 a + 2 * (i + 3 ^ k)) % 3 ^ k = child a (v0 a + 2 * i) % 3 ^ k := by
  obtain ⟨c, hc⟩ := two_pow_three_pow k
  have hfour : (4:Nat) ^ 3 ^ k = 3 ^ (k + 1) * c + 1 := by
    rw [← hc, show (4:Nat) = 2 ^ 2 from rfl, ← Nat.pow_mul]
  have hstep : (4:Nat) ^ (i + 3 ^ k) * base a
      = 4 ^ i * base a + 3 ^ (k + 1) * (4 ^ i * base a * c) := by
    have hprod : 4 ^ i * (3 ^ (k + 1) * c) * base a = 3 ^ (k + 1) * (4 ^ i * base a * c) := by
      simp [Nat.mul_comm, Nat.mul_left_comm, Nat.mul_assoc]
    rw [Nat.pow_add, hfour, Nat.mul_add, Nat.mul_one, Nat.add_mul, hprod]
    omega
  have heq : (2 ^ (v0 a + 2 * (i + 3 ^ k)) * a) % 3 ^ (k + 1)
      = (2 ^ (v0 a + 2 * i) * a) % 3 ^ (k + 1) := by
    rw [two_pow_step, two_pow_step, hstep, Nat.add_mul_mod_self_left]
  rw [ClassChild.child_mod_pow (step_mod_three ha (i + 3 ^ k)) k,
      ClassChild.child_mod_pow (step_mod_three ha i) k, heq]

/-- **Perfect local 3-adic equidistribution.**  For every fertile odd `a` and
every `k`, the map `i ↦ child a (v₀ a + 2i) mod 3 ^ k` is a bijection of
`{0, …, 3 ^ k − 1}` onto `ℤ/3 ^ k`, and it is `3 ^ k`-periodic.  Reading off
the `3 ^ (k−1)` classes divisible by `3`: the *fertile* children of any node,
listed by increasing valuation, hit each of the `2 · 3 ^ (k−1)` fertile classes
modulo `3 ^ k` exactly once per period. -/
theorem backward_mixing {a : Nat} (ha : a % 3 ≠ 0) (k : Nat) :
    (∀ i j, i < 3 ^ k → j < 3 ^ k →
        child a (v0 a + 2 * i) % 3 ^ k = child a (v0 a + 2 * j) % 3 ^ k → i = j)
    ∧ (∀ r, r < 3 ^ k → ∃ i, i < 3 ^ k ∧ child a (v0 a + 2 * i) % 3 ^ k = r)
    ∧ (∀ i, child a (v0 a + 2 * (i + 3 ^ k)) % 3 ^ k = child a (v0 a + 2 * i) % 3 ^ k) :=
  ⟨fun _ _ hi hj h => child_class_inj ha k hi hj h,
   fun _ hr => child_class_surj ha k hr,
   fun i => child_class_period ha k i⟩

/-! ## 5b. The same theorem, as a fact about `c ↦ 4 c + 1`

The next admissible child is `4c + 1` — the classical "`n` and `4n+1` have the
same Syracuse successor" — so a node's children *are* the forward orbit of the
affine map `τ c = 4c + 1`, and `backward_mixing` says exactly:

> **`τ c = 4 c + 1` acts on `ℤ/3^k` as a single `3^k`-cycle**, from any
> starting point. -/

/-- The next admissible child is `4c + 1`. -/
theorem child_succ {a v : Nat} (h : (2 ^ v * a) % 3 = 1) :
    child a (v + 2) = 4 * child a v + 1 := by
  have e3 : (2:Nat) ^ (v + 2) * a = 4 * (2 ^ v * a) := by
    rw [Nat.pow_add, show (2:Nat) ^ 2 = 4 from rfl, Nat.mul_right_comm,
        Nat.mul_comm (2 ^ v * a) 4]
  have h2 : (2 ^ (v + 2) * a) % 3 = 1 := by rw [e3, Nat.mul_mod, h]
  have e1 : 3 * child a (v + 2) + 1 = 2 ^ (v + 2) * a := child_eq h2
  have e2 : 3 * child a v + 1 = 2 ^ v * a := child_eq h
  omega

/-- `τ c = 4c + 1`, iterated. -/
def tauIter : Nat → Nat → Nat
  | 0, c => c
  | (i + 1), c => 4 * tauIter i c + 1

theorem three_tau_iter (c : Nat) : ∀ i, 3 * tauIter i c + 1 = 4 ^ i * (3 * c + 1) := by
  intro i
  induction i with
  | zero => simp [tauIter]
  | succ i ih =>
    show 3 * (4 * tauIter i c + 1) + 1 = 4 ^ (i + 1) * (3 * c + 1)
    rw [Nat.pow_succ, Nat.mul_comm (4 ^ i) 4, Nat.mul_assoc, ← ih]
    omega

/-- `3 x + 1` modulo `3 ^ (k+1)` sees `x` only modulo `3 ^ k`. -/
theorem three_mul_mod (x k : Nat) : (3 * x + 1) % 3 ^ (k + 1) = 3 * (x % 3 ^ k) + 1 := by
  have hp : 0 < (3:Nat) ^ k := three_pow_pos k
  have hr : x % 3 ^ k < 3 ^ k := Nat.mod_lt _ hp
  have hd := Nat.div_add_mod x (3 ^ k)
  have hsplit : 3 * x + 1 = 3 ^ (k + 1) * (x / 3 ^ k) + (3 * (x % 3 ^ k) + 1) := by
    rw [three_pow_succ, Nat.mul_assoc]
    omega
  rw [hsplit, Nat.mul_add_mod, Nat.mod_eq_of_lt]
  rw [three_pow_succ]
  omega

/-- **`τ c = 4c + 1` acts on `ℤ/3^k` as a single `3^k`-cycle**, from any start. -/
theorem tau_cycle (c k : Nat) :
    (∀ i j, i < 3 ^ k → j < 3 ^ k → tauIter i c % 3 ^ k = tauIter j c % 3 ^ k → i = j)
    ∧ (∀ r, r < 3 ^ k → ∃ i, i < 3 ^ k ∧ tauIter i c % 3 ^ k = r) := by
  have hB : (3 * c + 1) % 3 ≠ 0 := by omega
  have inj : ∀ i j, i < 3 ^ k → j < 3 ^ k →
      tauIter i c % 3 ^ k = tauIter j c % 3 ^ k → i = j := by
    intro i j hi hj h
    have key : (4 ^ i * (3 * c + 1)) % 3 ^ (k + 1) = (4 ^ j * (3 * c + 1)) % 3 ^ (k + 1) := by
      rw [← three_tau_iter c i, ← three_tau_iter c j, three_mul_mod, three_mul_mod, h]
    rcases Nat.le_total i j with hij | hij
    · exact class_eq_imp_eq hB hij hj key
    · exact (class_eq_imp_eq hB hij hi key.symm).symm
  exact ⟨inj, fun r hr => inj_on_range_surj (3 ^ k) (fun i => tauIter i c % 3 ^ k)
    (fun _ _ => Nat.mod_lt _ (three_pow_pos _)) inj r hr⟩

/-- `τ` iterated is `3 ^ k`-periodic modulo `3 ^ k`. -/
theorem tau_period (c k i : Nat) :
    tauIter (i + 3 ^ k) c % 3 ^ k = tauIter i c % 3 ^ k := by
  obtain ⟨d, hd⟩ := two_pow_three_pow k
  have hfour : (4:Nat) ^ 3 ^ k = 3 ^ (k + 1) * d + 1 := by
    rw [← hd, show (4:Nat) = 2 ^ 2 from rfl, ← Nat.pow_mul]
  have hB : (4:Nat) ^ (i + 3 ^ k) * (3 * c + 1)
      = (4 ^ i * (3 * c + 1)) * (3 ^ (k + 1) * d + 1) := by
    rw [Nat.pow_add, hfour]
    simp [Nat.mul_comm, Nat.mul_left_comm]
  have hexp : ∀ B : Nat, B * (3 ^ (k + 1) * d + 1) = B + 3 ^ (k + 1) * (d * B) := by
    intro B
    rw [Nat.mul_add, Nat.mul_one, Nat.mul_comm B (3 ^ (k + 1) * d), Nat.mul_assoc]
    omega
  have hmul : 4 ^ (i + 3 ^ k) * (3 * c + 1)
      = 4 ^ i * (3 * c + 1) + 3 ^ (k + 1) * (d * (4 ^ i * (3 * c + 1))) := by
    rw [hB, hexp]
  have h1 : (3 * tauIter (i + 3 ^ k) c + 1) % 3 ^ (k + 1)
      = (3 * tauIter i c + 1) % 3 ^ (k + 1) := by
    rw [three_tau_iter, three_tau_iter, hmul, Nat.add_mul_mod_self_left]
  rw [three_mul_mod, three_mul_mod] at h1
  omega

theorem tau_mod_index (c k : Nat) : ∀ i, tauIter i c % 3 ^ k = tauIter (i % 3 ^ k) c % 3 ^ k := by
  intro i
  induction i using Nat.strongRecOn with
  | _ i ih =>
    rcases Nat.lt_or_ge i (3 ^ k) with h | h
    · rw [Nat.mod_eq_of_lt h]
    · have hp : 0 < (3:Nat) ^ k := three_pow_pos k
      have hlt : i - 3 ^ k < i := by omega
      have he : i - 3 ^ k + 3 ^ k = i := by omega
      have hmod : (i - 3 ^ k) % 3 ^ k = i % 3 ^ k := (Nat.mod_eq_sub_mod h).symm
      have step : tauIter i c % 3 ^ k = tauIter (i - 3 ^ k) c % 3 ^ k := by
        have hp2 := tau_period c k (i - 3 ^ k)
        rw [he] at hp2
        exact hp2
      rw [step, ih _ hlt, hmod]

/-- **`τ` is a perfect equidistribution sequence modulo `3 ^ k`**: two iterates
share a class exactly when their indices agree modulo `3 ^ k`.  Consequently,
among any `L` consecutive iterates each class is hit `⌊L/3 ^ k⌋` or
`⌈L/3 ^ k⌉` times — discrepancy strictly below `1`, at every level. -/
theorem tau_class_eq_iff (c k i j : Nat) :
    tauIter i c % 3 ^ k = tauIter j c % 3 ^ k ↔ i % 3 ^ k = j % 3 ^ k := by
  constructor
  · intro h
    rw [tau_mod_index c k i, tau_mod_index c k j] at h
    exact (tau_cycle c k).1 _ _ (Nat.mod_lt _ (three_pow_pos k)) (Nat.mod_lt _ (three_pow_pos k)) h
  · intro h
    rw [tau_mod_index c k i, tau_mod_index c k j, h]

/-! ## 6. The `2`-adic mirror: anti-mixing

The `3`-adic statement above is as strong as it could be.  The `2`-adic one is
as weak as it could be, and for the same reason — `3 · child + 1 = 2 ^ v · a`.
Modulo `2 ^ M` the right-hand side vanishes as soon as `v ≥ M`, so the child's
class is pinned to the single solution of `3 c ≡ −1 (mod 2 ^ M)`, *for every
node at once*.  A node's children therefore occupy at most `⌈(M − v₀)/2⌉ + 1`
classes modulo `2 ^ M` — the ones at `v < M`, plus that one universal class —
against all `3 ^ k` classes modulo `3 ^ k`.  This is why G1 (mixing modulo
`2 ^ M`) is a different kind of problem from backward mixing modulo `3 ^ k`:
mod `3` the spread is per-node and immediate, mod `2` it can only come from
depth. -/

/-- **2-adic anti-mixing.**  Every child taken at valuation `≥ M`, from any
node whatever, lies in one and the same class modulo `2 ^ M`. -/
theorem deep_child_congr {n m v w M : Nat}
    (hn : (2 ^ v * n) % 3 = 1) (hm : (2 ^ w * m) % 3 = 1)
    (hv : M ≤ v) (hw : M ≤ w) :
    child n v % 2 ^ M = child m w % 2 ^ M := by
  have hP : 0 < (2:Nat) ^ M := two_pow_pos M
  -- `3 c + 1 ≡ 0 (mod 2 ^ M)` for both children
  have key : ∀ x y : Nat, (2 ^ x * y) % 3 = 1 → M ≤ x →
      (3 * (child y x % 2 ^ M) + 1) % 2 ^ M = 0 := by
    intro x y hxy hx
    have hc : 3 * child y x + 1 = 2 ^ x * y := child_eq hxy
    have hsplit : (2:Nat) ^ x = 2 ^ M * 2 ^ (x - M) := by
      rw [← two_pow_add]
      have : M + (x - M) = x := by omega
      rw [this]
    have h0 : (3 * child y x + 1) % 2 ^ M = 0 := by
      rw [hc, hsplit, Nat.mul_assoc]
      exact Nat.mul_mod_right _ _
    rw [Nat.add_mod, Nat.mul_mod, Nat.mod_mod_of_dvd _ (Nat.dvd_refl _), ← Nat.mul_mod,
        ← Nat.add_mod]
    exact h0
  -- both residues solve `3 A + 1 = 2 ^ M · q` with `q ∈ {1, 2}`
  have step : ∀ A : Nat, A < 2 ^ M → (3 * A + 1) % 2 ^ M = 0 →
      3 * A + 1 = 2 ^ M ∨ 3 * A + 1 = 2 * 2 ^ M := by
    intro A hA h0
    obtain ⟨q, hq⟩ : (2:Nat) ^ M ∣ (3 * A + 1) := Nat.dvd_of_mod_eq_zero h0
    have hq2 : q ≤ 2 := by
      rcases Nat.lt_or_ge q 3 with h | h
      · omega
      · have : (2:Nat) ^ M * 3 ≤ 2 ^ M * q := Nat.mul_le_mul_left _ h
        omega
    have hq0 : q ≠ 0 := by
      intro h
      rw [h, Nat.mul_zero] at hq
      omega
    have hqv : q = 1 ∨ q = 2 := by omega
    rcases hqv with h | h <;> rw [h] at hq <;> omega
  have hA : child n v % 2 ^ M < 2 ^ M := Nat.mod_lt _ hP
  have hB : child m w % 2 ^ M < 2 ^ M := Nat.mod_lt _ hP
  rcases step _ hA (key v n hn hv) with h1 | h1 <;>
    rcases step _ hB (key w m hm hw) with h2 | h2 <;> omega

end BackwardMixing
end Collatz
