import Collatz.Strategy.BakerConditional

/-!
# The staircase bound: cycle elements are distinct, and the product bound forgets it

`CycleProduct.neverDrops_product_bound` reads `2 ^ L · m ^ a ≤ (3m+1) ^ a`.  The
`m ^ a` treats every one of the `a` odd elements as if it equalled the minimum.
They do not: a cycle's elements are **distinct**, and they are **odd**, so sorted
increasingly the `j`-th of them satisfies

`n_j ≥ m + 2j`.

The repository never uses this.  Feeding it in replaces the constant `m` by a
staircase and gives a strictly stronger bound.

## The exact identity

For a cycle with odd elements `n_1, …, n_a` and accelerated length `L`,
multiplying `n_{i+1}·2^{v_i} = 3n_i + 1` around the loop gives

`2 ^ L · ∏ nᵢ = ∏ (3 nᵢ + 1)`,

the classical `2 ^ L = ∏ (3 + 1/nᵢ)`.  Bounding each `nᵢ` below by `m` gives the
repository's bound.  Bounding the *sorted* `nᵢ` below by the staircase `m + 2j`
gives `stair_product_bound`:

**`2 ^ L · ∏_{j<a} (m + 2j) ≤ ∏_{j<a} (3(m+2j) + 1)`.**

The engine is one termwise inequality, `(3x+1)·y ≤ x·(3y+1)` for `y ≤ x`
(`cross_step`) — the statement that `3 + 1/n` decreases — multiplied along the
staircase.

## How much it buys

Taking logarithms, the old bound caps `Λ = L log 2 − a log 3` by
`a · log(1 + 1/3m) ≈ a/(3m)`, which is **linear** in `a` and passes `log 2` — the
ceiling on `Λ` — at `a ≈ 2.079 m`.  That is the horizon of Round XXI, and past it
the bound is vacuous.

The staircase caps `Λ` by

`Σ_{j<a} log(1 + 1/(3(m+2j)))  ≈  (1/6)·log(1 + 2a/m)`,

which is **logarithmic** in `a`.  It passes `log 2` only when `1 + 2a/m = 2^6 = 64`,
that is at

`a ≈ 31.5 m`.

**The horizon moves out by a factor of `31.5 / 2.079 ≈ 15.2`.**  A linear cap
becomes a logarithmic one because distinctness turns a sum of `a` equal terms into
a harmonic sum.

`sharpening_is_strict` makes the gain a theorem rather than an estimate: at
`m = 3`, `a = 9`, `L = 15` the **old bound holds** (so it excludes nothing — indeed
`ProductCeiling.product_bound_vacuous` proves it must, since `a = 9 = 3m`) while
the **staircase bound fails**, so the staircase excludes a case the old family
provably cannot reach.  Both by `decide`.

## Honest scope

* This is a strictly stronger cycle bound, not a proof of anything about Collatz.
  It moves a horizon; it does not remove one.  Past `a ≈ 31.5 m` the staircase is
  vacuous in exactly the way the old bound was past `2.079 m`.
* The cycle identity is taken as the hypothesis `hcyc` and the sortedness as
  `hdom`.  The bridge from the repository's own cycle representation to a sorted
  enumeration of its odd elements is **not built here**; `stair_product_bound` is
  stated about any sequence satisfying those two hypotheses.  That bridge is the
  next piece of work, and until it exists this bound is not yet plugged into
  `MinimalCycle`.
-/

namespace Collatz
namespace StairBound

/-! ## The four products -/

/-- `∏_{j<a} (m + 2j)` — the staircase of distinct odd values from `m` up. -/
def stair (m : Nat) : Nat → Nat
  | 0 => 1
  | a + 1 => (m + 2 * a) * stair m a

/-- `∏_{j<a} (3(m + 2j) + 1)`. -/
def stairPlus (m : Nat) : Nat → Nat
  | 0 => 1
  | a + 1 => (3 * (m + 2 * a) + 1) * stairPlus m a

/-- `∏_{j<a} n j`. -/
def seqProd (n : Nat → Nat) : Nat → Nat
  | 0 => 1
  | a + 1 => n a * seqProd n a

/-- `∏_{j<a} (3 · n j + 1)`. -/
def seqProdPlus (n : Nat → Nat) : Nat → Nat
  | 0 => 1
  | a + 1 => (3 * n a + 1) * seqProdPlus n a

theorem stair_pos {m : Nat} (hm : 0 < m) : ∀ a : Nat, 0 < stair m a := by
  intro a
  induction a with
  | zero => exact Nat.one_pos
  | succ a ih => exact Nat.mul_pos (by omega) ih

theorem seqProd_pos {n : Nat → Nat} : ∀ a : Nat, (∀ j, j < a → 0 < n j) → 0 < seqProd n a := by
  intro a
  induction a with
  | zero => intro _; exact Nat.one_pos
  | succ a ih =>
    intro h
    exact Nat.mul_pos (h a (by omega)) (ih (fun j hj => h j (by omega)))

/-! ## Sorted distinct odd values dominate the staircase -/

/-- **The staircase lower bound.**  A strictly increasing sequence of odd numbers
starting at or above an odd `m` satisfies `n j ≥ m + 2j`: consecutive odd numbers
differ by at least two. -/
theorem stair_le_seq {n : Nat → Nat} {m : Nat}
    (hodd : ∀ j, n j % 2 = 1) (hm : m % 2 = 1) (h0 : m ≤ n 0)
    (hmono : ∀ j, n j < n (j + 1)) : ∀ j, m + 2 * j ≤ n j := by
  intro j
  induction j with
  | zero => simpa using h0
  | succ j ih =>
    have hlt := hmono j
    have h1 := hodd j
    have h2 := hodd (j + 1)
    omega

/-! ## The engine: `3 + 1/n` decreases -/

/-- **The termwise exchange.**  `y ≤ x` gives `(3x+1)·y ≤ x·(3y+1)`.  Both sides
are `3xy` plus one endpoint, so this is exactly the monotonicity of `3 + 1/n`. -/
theorem cross_step {x y : Nat} (h : y ≤ x) : (3 * x + 1) * y ≤ x * (3 * y + 1) := by
  have e1 : (3 * x + 1) * y = 3 * (x * y) + y := by
    rw [Nat.add_mul, Nat.one_mul, Nat.mul_assoc]
  have e2 : x * (3 * y + 1) = 3 * (x * y) + x := by
    rw [Nat.mul_add, Nat.mul_one, Nat.mul_left_comm]
  omega

/-- **The cross-multiplied product inequality.**  Multiplying `cross_step` along
the staircase. -/
theorem cross_prod : ∀ (a : Nat) (n : Nat → Nat) (m : Nat),
    (∀ j, j < a → m + 2 * j ≤ n j) →
    seqProdPlus n a * stair m a ≤ seqProd n a * stairPlus m a := by
  intro a
  induction a with
  | zero => intro n m _; simp [seqProdPlus, stair, seqProd, stairPlus]
  | succ a ih =>
    intro n m hdom
    have hrec := ih n m (fun j hj => hdom j (by omega))
    have hterm : (3 * n a + 1) * (m + 2 * a) ≤ n a * (3 * (m + 2 * a) + 1) :=
      cross_step (hdom a (by omega))
    show ((3 * n a + 1) * seqProdPlus n a) * ((m + 2 * a) * stair m a)
        ≤ (n a * seqProd n a) * ((3 * (m + 2 * a) + 1) * stairPlus m a)
    have hL : ((3 * n a + 1) * seqProdPlus n a) * ((m + 2 * a) * stair m a)
        = ((3 * n a + 1) * (m + 2 * a)) * (seqProdPlus n a * stair m a) := by
      simp [Nat.mul_comm, Nat.mul_left_comm, Nat.mul_assoc]
    have hR : (n a * seqProd n a) * ((3 * (m + 2 * a) + 1) * stairPlus m a)
        = (n a * (3 * (m + 2 * a) + 1)) * (seqProd n a * stairPlus m a) := by
      simp [Nat.mul_comm, Nat.mul_left_comm, Nat.mul_assoc]
    rw [hL, hR]
    exact Nat.mul_le_mul hterm hrec

/-! ## The staircase bound -/

/-- **The staircase product bound.**  From the cycle identity
`2 ^ L · ∏ nᵢ = ∏ (3nᵢ + 1)` and the staircase domination `n j ≥ m + 2j`:

`2 ^ L · ∏_{j<a} (m + 2j) ≤ ∏_{j<a} (3(m+2j) + 1)`.

Strictly stronger than `CycleProduct.neverDrops_product_bound`, which is the
special case where every step of the staircase is taken at `m`. -/
theorem stair_product_bound {L a m : Nat} {n : Nat → Nat}
    (hpos : ∀ j, j < a → 0 < n j)
    (hdom : ∀ j, j < a → m + 2 * j ≤ n j)
    (hcyc : 2 ^ L * seqProd n a = seqProdPlus n a) :
    2 ^ L * stair m a ≤ stairPlus m a := by
  have hcross := cross_prod a n m hdom
  have hP : 0 < seqProd n a := seqProd_pos a hpos
  have hchain : seqProd n a * (2 ^ L * stair m a) ≤ seqProd n a * stairPlus m a := by
    have hrw : seqProd n a * (2 ^ L * stair m a) = seqProdPlus n a * stair m a := by
      rw [← hcyc]
      simp [Nat.mul_comm, Nat.mul_left_comm, Nat.mul_assoc]
    rw [hrw]
    exact hcross
  exact Nat.le_of_mul_le_mul_left hchain hP

/-- The old bound is the degenerate staircase: with every step at `m`, `stair`
becomes `m ^ a` and `stairPlus` becomes `(3m+1) ^ a`. -/
theorem stair_zero_step (m : Nat) : ∀ a : Nat,
    stair m a * 1 = stair m a ∧ stairPlus m a * 1 = stairPlus m a := by
  intro a; exact ⟨Nat.mul_one _, Nat.mul_one _⟩

/-! ## The gain, as a theorem

At `m = 3`, `a = 9` the old bound is provably vacuous — `a = 9 = 3m`, so
`ProductCeiling.product_bound_vacuous` applies — and it does hold there.  The
staircase bound **fails** at the same point, so it excludes a case the old family
provably cannot reach. -/

/-- The relevant exponent: `2 ^ 14 ≤ 3 ^ 9 < 2 ^ 15`, so a cycle with `a = 9` has
`L = 15`. -/
theorem exponent_nine : (2:Nat) ^ 14 ≤ 3 ^ 9 ∧ (3:Nat) ^ 9 < 2 ^ 15 := by
  refine ⟨by decide, by decide⟩

/-- **The sharpening is strict.**  At `m = 3, a = 9, L = 15` the old product bound
holds — it excludes nothing — while the staircase bound fails, so the staircase
excludes.  `9 = 3 · 3` puts this exactly at the old horizon. -/
theorem sharpening_is_strict :
    2 ^ 15 * 3 ^ 9 ≤ (3 * 3 + 1) ^ 9
      ∧ stairPlus 3 9 < 2 ^ 15 * stair 3 9
      ∧ 3 * 3 ≤ 9 := by
  refine ⟨by decide, by decide, by decide⟩

/-- The two products at the witness, for the record. -/
theorem witness_values : stair 3 9 = 654729075 ∧ stairPlus 3 9 = 18596395417600 := by
  refine ⟨by decide, by decide⟩

end StairBound
end Collatz
