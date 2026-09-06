import Collatz.Strategy.LocalBlindness
import Collatz.Strategy.ClassChild

/-!
# The inverse tree is critical at exponent `1`, at every class level

**Novelty tag: NEW (structural; Round LXXVII).**  Searched: Krasikov–Lagarias
2003 §2–3 (the linear programs `L_k^{NT}`), Applegate–Lagarias 1995 II; neither
identifies the averaged system below or its stochasticity.  Repository:
`grep -rniE "stochastic|column.sum|Haar|stationary" RESEARCH.md CLOSURE.md
Devices/` finds only the 2-adic Haar remark of `Devices/FutureCone.md` and an
early heuristic ("counting saturates at exponent exactly 1", Round I) with no
theorem behind it.

## The two systems

The Krasikov–Lagarias certificate (`Devices/AbsoluteBound.md`) lives on the
fertile classes `r mod 3^(k+1)`.  A parent class `r` has, at each valuation
`v` with `2^v r ≡ 1 (mod 3)`, a child class

    childClass k v r = ((2^v r) mod 3^(k+1) − 1) / 3      (< 3^k),

one level *coarser* than the parent (`ClassChild.child_mod_pow`).  The
certificate weighs the child by the **minimum** of the weight over the three
lifts of `childClass` to `3^(k+1)`, because the parent's class does not decide
which lift the child is in.  Replace that minimum by the **average** over the
three lifts and put the exponent at `1` (weight `3 / 2^v` per child, the child's
relative size): the resulting linear map is **column-stochastic**.  The reason
is the bijection proved here:

* `parent_bijection`: for every child class `ℓ < 3^k` and every valuation `v`,
  **exactly one** parent class `r < 3^(k+1)` has `2^v r ≡ 1 (mod 3)` and
  `childClass k v r = ℓ` — namely `r ≡ 2^(−v) (3ℓ + 1)`.

So every column of the averaged matrix sums to `Σ_v 3·2^(−v)·(1/3) = 1`, and
its spectral radius is exactly `1` at every level: **the averaged system
certifies exponent `1` at every finite level, and the entire gap between the
published `0.84` / this repository's `0.852` and `1` is the min-over-lifts
relaxation** — that is, the 3-adic non-equidistribution of the inverse tree
across lifts, and nothing else.  Measured (`scripts/kl_spectrum.py`): the
min-system's growth at exponent `1` is `1 − ρ_k ≈ 1.1 / k` for `k = 3 … 12`,
so the K–L exponents tend to `1` polynomially, not to a ceiling.

## What is kernel-checked here

`mass_conservation` is the stochastic identity in exact integers, for every
level `k`, every valuation cutoff `V` and every weight table `w`: summing
the averaged transfer (weights `2^(V−1−i)` for valuation `i+1`, cleared by
`2^V`, and *before* the division by three lifts) over all parent classes
returns `(2^V − 1) · Σ_ℓ w ℓ`.  Dividing by `3` for the lifts and by `2^V` for
the clearing gives column sums `1 − 2^(−V)`, i.e. `1` in the limit `V → ∞`.

No real numbers, no eigenvalues: the finite identity is what the spectral
statement rests on, and it is the part a kernel can check.
-/

namespace Collatz
namespace TreeStochastic

open Collatz.Sum

/-! ## 1. Sums: exchange, single hit, unit indicator, re-indexing -/

/-- Exchanging two finite sums. -/
theorem sumRange_comm (n m : Nat) (f : Nat → Nat → Nat) :
    sumRange n (fun i => sumRange m (fun j => f i j))
      = sumRange m (fun j => sumRange n (fun i => f i j)) := by
  induction n with
  | zero =>
    have h : sumRange m (fun j => sumRange 0 (fun i => f i j)) = sumRange m (fun _ => 0) :=
      sumRange_congr (fun _ _ => rfl)
    rw [h, sumRange_const, Nat.mul_zero]
    rfl
  | succ n ih =>
    rw [sumRange_succ, ih, ← sumRange_add]
    exact sumRange_congr (fun j _ => rfl)

/-- A sum with a single nonzero index. -/
theorem sumRange_single {B ℓ₀ : Nat} (g : Nat → Nat) (h : ℓ₀ < B) :
    sumRange B (fun ℓ => if ℓ = ℓ₀ then g ℓ else 0) = g ℓ₀ := by
  induction B with
  | zero => omega
  | succ B ih =>
    rw [sumRange_succ]
    by_cases hB : ℓ₀ < B
    · rw [ih hB, if_neg (by omega), Nat.add_zero]
    · have hEq : ℓ₀ = B := by omega
      subst hEq
      rw [if_pos rfl]
      have h0 : sumRange ℓ₀ (fun ℓ => if ℓ = ℓ₀ then g ℓ else 0) = sumRange ℓ₀ (fun _ => 0) :=
        sumRange_congr (fun i hi => if_neg (by omega))
      rw [h0, sumRange_const, Nat.mul_zero, Nat.zero_add]

/-- The indicator of a predicate with exactly one witness below `n` sums to `1`. -/
theorem sumRange_indicator_one {n : Nat} (Q : Nat → Prop) [DecidablePred Q] {i₀ : Nat}
    (hi₀ : i₀ < n) (hQ : Q i₀) (huniq : ∀ i, i < n → Q i → i = i₀) :
    sumRange n (fun i => if Q i then 1 else 0) = 1 := by
  induction n with
  | zero => omega
  | succ n ih =>
    rw [sumRange_succ]
    by_cases hn : i₀ < n
    · rw [ih hn (fun i hi hQi => huniq i (by omega) hQi)]
      rw [if_neg (fun hQn => by have := huniq n (by omega) hQn; omega)]
    · have hEq : i₀ = n := by omega
      subst hEq
      rw [if_pos hQ]
      have h0 : sumRange i₀ (fun i => if Q i then 1 else 0) = sumRange i₀ (fun _ => 0) :=
        sumRange_congr (fun i hi => if_neg (fun hQi => by have := huniq i (by omega) hQi; omega))
      rw [h0, sumRange_const, Nat.mul_zero, Nat.zero_add]

/-- **Re-indexing along a bijection.**  If `f` maps the indices below `n`
satisfying `P` bijectively onto `[0, B)`, a sum of `w ∘ f` over those indices
is the sum of `w` over `[0, B)`. -/
theorem sumRange_reindex {n B : Nat} (P : Nat → Prop) [DecidablePred P]
    (f w : Nat → Nat)
    (hf : ∀ r, r < n → P r → f r < B)
    (hbij : ∀ ℓ, ℓ < B → ∃ r, r < n ∧ P r ∧ f r = ℓ ∧
      ∀ r', r' < n → P r' → f r' = ℓ → r' = r) :
    sumRange n (fun r => if P r then w (f r) else 0) = sumRange B w := by
  have h1 : ∀ r, r < n → (if P r then w (f r) else 0)
      = sumRange B (fun ℓ => if P r ∧ f r = ℓ then w ℓ else 0) := by
    intro r hr
    by_cases hP : P r
    · rw [if_pos hP]
      have h2 : sumRange B (fun ℓ => if P r ∧ f r = ℓ then w ℓ else 0)
          = sumRange B (fun ℓ => if ℓ = f r then w ℓ else 0) :=
        sumRange_congr (fun ℓ _ => by
          by_cases h : ℓ = f r
          · rw [if_pos ⟨hP, h.symm⟩, if_pos h]
          · rw [if_neg (fun h' => h h'.2.symm), if_neg h])
      rw [h2, sumRange_single w (hf r hr hP)]
    · rw [if_neg hP]
      have h2 : sumRange B (fun ℓ => if P r ∧ f r = ℓ then w ℓ else 0)
          = sumRange B (fun _ => 0) :=
        sumRange_congr (fun ℓ _ => if_neg (fun h => hP h.1))
      rw [h2, sumRange_const, Nat.mul_zero]
  calc sumRange n (fun r => if P r then w (f r) else 0)
      = sumRange n (fun r => sumRange B (fun ℓ => if P r ∧ f r = ℓ then w ℓ else 0)) :=
        sumRange_congr h1
    _ = sumRange B (fun ℓ => sumRange n (fun r => if P r ∧ f r = ℓ then w ℓ else 0)) :=
        sumRange_comm n B _
    _ = sumRange B w := by
        refine sumRange_congr (fun ℓ hℓ => ?_)
        have h2 : sumRange n (fun r => if P r ∧ f r = ℓ then w ℓ else 0)
            = sumRange n (fun r => w ℓ * (if P r ∧ f r = ℓ then 1 else 0)) :=
          sumRange_congr (fun r _ => by
            by_cases h : P r ∧ f r = ℓ
            · rw [if_pos h, if_pos h, Nat.mul_one]
            · rw [if_neg h, if_neg h, Nat.mul_zero])
        rw [h2, sumRange_const_mul]
        obtain ⟨r, hr, hP, hfr, huniq⟩ := hbij ℓ hℓ
        rw [sumRange_indicator_one (fun r => P r ∧ f r = ℓ) hr ⟨hP, hfr⟩
          (fun r' hr' h => huniq r' hr' h.1 h.2), Nat.mul_one]

/-- `2^(V−1) + 2^(V−2) + ⋯ + 1 = 2^V − 1`. -/
theorem sum_two_pow (V : Nat) : sumRange V (fun i => 2 ^ (V - 1 - i)) = 2 ^ V - 1 := by
  induction V with
  | zero => rfl
  | succ V ih =>
    rw [sumRange_succ]
    have h : sumRange V (fun i => 2 ^ (V + 1 - 1 - i)) = sumRange V (fun i => 2 * 2 ^ (V - 1 - i)) :=
      sumRange_congr (fun i hi => by
        have e : V + 1 - 1 - i = (V - 1 - i) + 1 := by omega
        rw [e, Nat.pow_succ]
        omega)
    rw [h, sumRange_const_mul, ih]
    have e : V + 1 - 1 - V = 0 := by omega
    rw [e, Nat.pow_zero, Nat.pow_succ]
    have := Nat.pow_pos (n := V) (by decide : 0 < 2)
    omega

/-! ## 2. The parent of a child class is unique -/

/-- `2 ^ e ≡ 1 (mod 3 ^ m)` for some `e > 0` (pigeonhole on the powers of `2`). -/
theorem two_pow_one_mod (m : Nat) : ∃ e, 0 < e ∧ 2 ^ e % 3 ^ m = 1 % 3 ^ m :=
  LocalBlindness.exists_pow_one_mod (Nat.pow_pos (by decide)) (by decide)
    (Nat.Coprime.pow_right m (by decide))

/-- The child class of a parent class `r` at valuation `v`, one level coarser. -/
def childClass (k v r : Nat) : Nat := ((2 ^ v * r) % 3 ^ (k + 1) - 1) / 3

theorem childClass_lt {k v r : Nat} : childClass k v r < 3 ^ k := by
  unfold childClass
  have h3P : (3:Nat) ^ (k + 1) = 3 * 3 ^ k := Nat.pow_succ' (n := k) (m := 3)
  have := Nat.mod_lt (2 ^ v * r) (Nat.pow_pos (by decide) : 0 < 3 ^ (k + 1))
  omega

/-- **Existence.**  Every `3ℓ + 1 < 3^(k+1)` is `2^v r mod 3^(k+1)` for some
parent class `r`: multiply by the inverse of `2^v`. -/
theorem parent_exists (k v ℓ : Nat) (hℓ : ℓ < 3 ^ k) :
    ∃ r, r < 3 ^ (k + 1) ∧ (2 ^ v * r) % 3 ^ (k + 1) = 3 * ℓ + 1 := by
  obtain ⟨e, he, hmod⟩ := two_pow_one_mod (k + 1)
  have hM : 0 < 3 ^ (k + 1) := Nat.pow_pos (by decide)
  have h3P : (3:Nat) ^ (k + 1) = 3 * 3 ^ k := Nat.pow_succ' (n := k) (m := 3)
  have hev : v + (e * v - v) = e * v := by
    have : v ≤ e * v := Nat.le_mul_of_pos_left v he
    omega
  refine ⟨(2 ^ (e * v - v) * (3 * ℓ + 1)) % 3 ^ (k + 1), Nat.mod_lt _ hM, ?_⟩
  calc (2 ^ v * ((2 ^ (e * v - v) * (3 * ℓ + 1)) % 3 ^ (k + 1))) % 3 ^ (k + 1)
      = (2 ^ v * (2 ^ (e * v - v) * (3 * ℓ + 1))) % 3 ^ (k + 1) := by
        rw [Nat.mul_mod, Nat.mod_mod, ← Nat.mul_mod]
    _ = (2 ^ (e * v) * (3 * ℓ + 1)) % 3 ^ (k + 1) := by
        rw [← Nat.mul_assoc, ← Nat.pow_add, hev]
    _ = ((2 ^ e % 3 ^ (k + 1)) ^ v % 3 ^ (k + 1) * ((3 * ℓ + 1) % 3 ^ (k + 1))) % 3 ^ (k + 1) := by
        rw [Nat.pow_mul, Nat.mul_mod, Nat.pow_mod]
    _ = ((1 % 3 ^ (k + 1)) ^ v % 3 ^ (k + 1) * ((3 * ℓ + 1) % 3 ^ (k + 1))) % 3 ^ (k + 1) := by
        rw [hmod]
    _ = (1 ^ v % 3 ^ (k + 1) * ((3 * ℓ + 1) % 3 ^ (k + 1))) % 3 ^ (k + 1) := by
        rw [← Nat.pow_mod]
    _ = (3 * ℓ + 1) % 3 ^ (k + 1) := by
        rw [Nat.one_pow, ← Nat.mul_mod, Nat.one_mul]
    _ = 3 * ℓ + 1 := Nat.mod_eq_of_lt (by omega)

/-- Cancelling `2 ^ v` modulo a power of three. -/
theorem parent_unique_aux {M v r r' : Nat} (hcop : Nat.Coprime M (2 ^ v)) (hr : r < M)
    (h : (2 ^ v * r) % M = (2 ^ v * r') % M) : r ≤ r' := by
  have hd : M ∣ 2 ^ v * r - 2 ^ v * r' :=
    Nat.dvd_of_mod_eq_zero (Nat.sub_mod_eq_zero_of_mod_eq h)
  rw [← Nat.mul_sub] at hd
  have hd' : M ∣ r - r' := Nat.Coprime.dvd_of_dvd_mul_left hcop hd
  have : r - r' = 0 := Nat.eq_zero_of_dvd_of_lt hd' (by omega)
  omega

/-- **Uniqueness.**  Two parent classes with the same `2^v r mod 3^(k+1)` coincide. -/
theorem parent_unique {k v r r' : Nat} (hr : r < 3 ^ (k + 1)) (hr' : r' < 3 ^ (k + 1))
    (h : (2 ^ v * r) % 3 ^ (k + 1) = (2 ^ v * r') % 3 ^ (k + 1)) : r = r' := by
  have hcop : Nat.Coprime (3 ^ (k + 1)) (2 ^ v) :=
    Nat.Coprime.pow_right v (Nat.Coprime.pow_left (k + 1) (by decide))
  have h1 := parent_unique_aux hcop hr h
  have h2 := parent_unique_aux hcop hr' h.symm
  omega

/-- **The parent bijection.**  For each child class `ℓ < 3^k` and valuation
`v`, exactly one parent class `r < 3^(k+1)` has `2^v r ≡ 1 (mod 3)` and
`childClass k v r = ℓ`. -/
theorem parent_bijection (k v ℓ : Nat) (hℓ : ℓ < 3 ^ k) :
    ∃ r, r < 3 ^ (k + 1) ∧ (2 ^ v * r) % 3 = 1 ∧ childClass k v r = ℓ ∧
      ∀ r', r' < 3 ^ (k + 1) → (2 ^ v * r') % 3 = 1 → childClass k v r' = ℓ → r' = r := by
  obtain ⟨r, hr, hmod⟩ := parent_exists k v ℓ hℓ
  have h3 : (3:Nat) ∣ 3 ^ (k + 1) := ⟨3 ^ k, Nat.pow_succ' (n := k) (m := 3)⟩
  refine ⟨r, hr, ?_, ?_, ?_⟩
  · rw [← Nat.mod_mod_of_dvd (2 ^ v * r) h3, hmod]
    omega
  · unfold childClass
    rw [hmod]
    omega
  · intro r' hr' h1 h2
    apply parent_unique hr' hr
    rw [hmod]
    unfold childClass at h2
    have h1' : (2 ^ v * r') % 3 ^ (k + 1) % 3 = 1 := by
      rw [Nat.mod_mod_of_dvd (2 ^ v * r') h3]
      exact h1
    omega

/-! ## 3. Mass conservation: the averaged system has constant column sums -/

/-- **Mass conservation, general weights.**  For every level `k`, every cutoff
`V`, every valuation weight `t : ℕ → ℕ` (`t i` for valuation `i+1`) and every
table `w` on the child classes `ℓ < 3^k`: summing `t i · w(childClass)` over
all parent classes `r < 3^(k+1)` and all valuations returns
`(Σ_{i<V} t i) · Σ_ℓ w(ℓ)`.  So every column of the lift-averaged transfer
with weights `t` sums to the same number `(1/3) Σ_i t i`, whatever the
exponent: with `t i = (3/2^(i+1))^α` (cleared) that common column sum is
`3^(α−1)/(2^α − 1)`, and it is the spectral radius. -/
theorem mass_conservation_weighted (k V : Nat) (t w : Nat → Nat) :
    sumRange (3 ^ (k + 1)) (fun r => sumRange V (fun i =>
        if (2 ^ (i + 1) * r) % 3 = 1 then t i * w (childClass k (i + 1) r) else 0))
      = sumRange V t * sumRange (3 ^ k) w := by
  have hinner : ∀ i, i < V →
      sumRange (3 ^ (k + 1)) (fun r =>
        if (2 ^ (i + 1) * r) % 3 = 1 then t i * w (childClass k (i + 1) r) else 0)
      = t i * sumRange (3 ^ k) w := by
    intro i _
    have h1 : sumRange (3 ^ (k + 1)) (fun r =>
        if (2 ^ (i + 1) * r) % 3 = 1 then t i * w (childClass k (i + 1) r) else 0)
        = sumRange (3 ^ (k + 1)) (fun r => t i *
            (if (2 ^ (i + 1) * r) % 3 = 1 then w (childClass k (i + 1) r) else 0)) :=
      sumRange_congr (fun r _ => by
        by_cases h : (2 ^ (i + 1) * r) % 3 = 1
        · rw [if_pos h, if_pos h]
        · rw [if_neg h, if_neg h, Nat.mul_zero])
    rw [h1, sumRange_const_mul]
    congr 1
    exact sumRange_reindex (fun r => (2 ^ (i + 1) * r) % 3 = 1) (childClass k (i + 1)) w
      (fun r _ _ => childClass_lt) (fun ℓ hℓ => parent_bijection k (i + 1) ℓ hℓ)
  calc sumRange (3 ^ (k + 1)) (fun r => sumRange V (fun i =>
        if (2 ^ (i + 1) * r) % 3 = 1 then t i * w (childClass k (i + 1) r) else 0))
      = sumRange V (fun i => sumRange (3 ^ (k + 1)) (fun r =>
        if (2 ^ (i + 1) * r) % 3 = 1 then t i * w (childClass k (i + 1) r) else 0)) :=
        sumRange_comm _ _ _
    _ = sumRange V (fun i => t i * sumRange (3 ^ k) w) := sumRange_congr hinner
    _ = sumRange V (fun i => sumRange (3 ^ k) w * t i) :=
        sumRange_congr (fun i _ => Nat.mul_comm _ _)
    _ = sumRange V t * sumRange (3 ^ k) w := by
        rw [sumRange_const_mul, Nat.mul_comm]

/-- **Mass conservation at exponent `1`.**  Weights `2^(V−1−i)` for valuation
`i+1` (the size ratio `3/2^(i+1)`, cleared by `2^V` and by the factor `3`
that becomes the average over the three lifts) return `(2^V − 1) · Σ_ℓ w ℓ`.
Every column of the averaged matrix sums to `1 − 2^(−V)`, and to `1` as
`V → ∞`: the lift-averaged Krasikov–Lagarias system has spectral radius
exactly `1` at exponent `1`, at every level. -/
theorem mass_conservation (k V : Nat) (w : Nat → Nat) :
    sumRange (3 ^ (k + 1)) (fun r => sumRange V (fun i =>
        if (2 ^ (i + 1) * r) % 3 = 1 then 2 ^ (V - 1 - i) * w (childClass k (i + 1) r) else 0))
      = (2 ^ V - 1) * sumRange (3 ^ k) w := by
  rw [mass_conservation_weighted k V (fun i => 2 ^ (V - 1 - i)) w, sum_two_pow]

/-- The identity at level `1` (parents mod `9`, children mod `3`), cutoff `4`,
weights `1, 2, 3`, closed by the kernel — a check that the general theorem
says what it should on an instance small enough to see. -/
example : sumRange 9 (fun r => sumRange 4 (fun i =>
      if (2 ^ (i + 1) * r) % 3 = 1 then 2 ^ (4 - 1 - i) * (childClass 1 (i + 1) r + 1) else 0))
    = 15 * 6 := by decide

end TreeStochastic
end Collatz
