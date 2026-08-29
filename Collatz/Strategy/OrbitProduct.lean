import Collatz.Strategy.CycleLemma
import Collatz.Strategy.AffineExact

/-!
# The orbit's odd elements, as a list, with the exact product identity

Two things are currently blocked on the same missing object: plumbing the
Halbeisen–Hungerbühler chain into `AccIsCycleOf`, and extending the staircase
bounds of Rounds XXIII–XXIV from cycles to never-droppers.  Both need the odd
elements of an orbit prefix as an actual list, together with the identity that
telescopes the map along it.  This file supplies both.

## The identity

Collecting the odd values of `x, T(x), …, T^{k−1}(x)` into `oddElems x k` and
telescoping `n ↦ (3n+1)/2` and `n ↦ n/2` gives

**`2^k · T^k(x) · ∏ nᵢ = x · ∏ (3nᵢ + 1)`**  (`orbit_product`).

For a cycle `T^L(x) = x` this is the classical `2^L = ∏(3 + 1/nᵢ)`.  For a
never-dropper, `T^k(x) ≥ x` turns it into

**`2^k · ∏ nᵢ ≤ ∏ (3nᵢ + 1)`**  (`neverDrops_prod_le`),

which is the product bound in the form the staircase argument consumes — no
constant `m` baked in, the actual elements present.

## Why this matters for the divergence half

`CycleProduct.neverDrops_product_bound` bounds every odd element below by the
minimum, giving `2^k · m^a ≤ (3m+1)^a` and hence a density deficit of order
`1/m` — a *constant*.  With the elements themselves in hand, and the fact that a
non-periodic orbit's values are **distinct**, the same staircase that Round XXIII
applied to cycles applies here, and the deficit becomes of order `log k / k`,
which **tends to zero**.

That is a genuine strengthening of the divergence-half toolkit rather than the
cycle-half one: it replaces a constant obstruction by a vanishing one.  What it
does *not* do is close the divergence half, because a divergent orbit is free to
send `k log 2 − a log 3` to `−∞`, and every bound here is an upper bound on that
quantity.

## Scope

`orbit_product` and `neverDrops_prod_le` are proved.  Distinctness of the elements
and the sorted staircase step are **not** done here; distinctness needs
non-periodicity, and the sorted step needs the list ordered.  Both are named at
the end of the file as the next targets.
-/

namespace Collatz
namespace OrbitProduct

open Reach AffineExact

/-! ## The odd elements of a prefix -/

/-- The odd values among `x, T(x), …, T^{k−1}(x)`, most recent first. -/
def oddElems (x : Nat) : Nat → List Nat
  | 0 => []
  | k + 1 =>
      if acceleratedOrbit k x % 2 = 1 then acceleratedOrbit k x :: oddElems x k
      else oddElems x k

@[simp] theorem oddElems_zero (x : Nat) : oddElems x 0 = [] := rfl

/-- Its length is the odd-step count. -/
theorem oddElems_length (x : Nat) : ∀ k : Nat, (oddElems x k).length = oddCount x k := by
  intro k
  induction k with
  | zero => rfl
  | succ k ih =>
    have hlast := Density.oddCount_succ_last x k
    rcases Arith.mod_two_eq_zero_or_one (acceleratedOrbit k x) with he | ho
    · show (if acceleratedOrbit k x % 2 = 1 then _ else oddElems x k).length = _
      rw [if_neg (by omega), ih]
      omega
    · show (if acceleratedOrbit k x % 2 = 1 then
        acceleratedOrbit k x :: oddElems x k else _).length = _
      rw [if_pos ho]
      show (oddElems x k).length + 1 = oddCount x (k + 1)
      rw [ih]
      omega

/-- Every listed element is odd. -/
theorem oddElems_odd (x : Nat) : ∀ k : Nat, ∀ y ∈ oddElems x k, y % 2 = 1 := by
  intro k
  induction k with
  | zero => intro y hy; cases hy
  | succ k ih =>
    intro y hy
    rcases Arith.mod_two_eq_zero_or_one (acceleratedOrbit k x) with he | ho
    · have hy' : y ∈ oddElems x k := by
        have : oddElems x (k + 1) = oddElems x k := by
          show (if acceleratedOrbit k x % 2 = 1 then _ else oddElems x k) = _
          rw [if_neg (by omega)]
        rw [this] at hy; exact hy
      exact ih y hy'
    · have hsplit : oddElems x (k + 1) = acceleratedOrbit k x :: oddElems x k := by
        show (if acceleratedOrbit k x % 2 = 1 then _ else _) = _
        rw [if_pos ho]
      rw [hsplit] at hy
      rcases List.mem_cons.mp hy with h | h
      · rw [h]; exact ho
      · exact ih y h

/-- Under never-dropping every listed element is at least the start. -/
theorem oddElems_ge {x : Nat} (hnd : ∀ i : Nat, x ≤ acceleratedOrbit i x) :
    ∀ k : Nat, ∀ y ∈ oddElems x k, x ≤ y := by
  intro k
  induction k with
  | zero => intro y hy; cases hy
  | succ k ih =>
    intro y hy
    rcases Arith.mod_two_eq_zero_or_one (acceleratedOrbit k x) with he | ho
    · have hy' : y ∈ oddElems x k := by
        have : oddElems x (k + 1) = oddElems x k := by
          show (if acceleratedOrbit k x % 2 = 1 then _ else oddElems x k) = _
          rw [if_neg (by omega)]
        rw [this] at hy; exact hy
      exact ih y hy'
    · have hsplit : oddElems x (k + 1) = acceleratedOrbit k x :: oddElems x k := by
        show (if acceleratedOrbit k x % 2 = 1 then _ else _) = _
        rw [if_pos ho]
      rw [hsplit] at hy
      rcases List.mem_cons.mp hy with h | h
      · rw [h]; exact hnd k
      · exact ih y h

/-! ## The telescoping identity -/

/-- `∏ (3nᵢ + 1)` over the listed elements. -/
def shiftProd (l : List Nat) : Nat := (l.map (fun n => 3 * n + 1)).prod

@[simp] theorem shiftProd_nil : shiftProd [] = 1 := rfl

theorem shiftProd_cons (n : Nat) (l : List Nat) :
    shiftProd (n :: l) = (3 * n + 1) * shiftProd l := rfl

/-- **The orbit product identity.**  `2^k · T^k(x) · ∏ nᵢ = x · ∏ (3nᵢ + 1)`.
For a cycle it is `2^L = ∏(3 + 1/nᵢ)`; for a prefix it is the same telescoping
with the endpoint left in. -/
theorem orbit_product (x : Nat) : ∀ k : Nat,
    2 ^ k * acceleratedOrbit k x * (oddElems x k).prod = x * shiftProd (oddElems x k) := by
  intro k
  induction k with
  | zero => simp [acceleratedOrbit]
  | succ k ih =>
    have hstep : acceleratedOrbit (k + 1) x = acceleratedStep (acceleratedOrbit k x) :=
      acceleratedOrbit_succ_step k x
    rcases Arith.mod_two_eq_zero_or_one (acceleratedOrbit k x) with he | ho
    · -- even step: the list is unchanged and the halving cancels a factor of two
      have hlist : oddElems x (k + 1) = oddElems x k := by
        show (if acceleratedOrbit k x % 2 = 1 then _ else oddElems x k) = _
        rw [if_neg (by omega)]
      have hval : acceleratedStep (acceleratedOrbit k x) = acceleratedOrbit k x / 2 := by
        rw [acceleratedStep, if_pos he]
      have hhalf : 2 * (acceleratedOrbit k x / 2) = acceleratedOrbit k x := by omega
      have hkey : 2 ^ (k + 1) * acceleratedOrbit (k + 1) x
          = 2 ^ k * acceleratedOrbit k x := by
        rw [hstep, hval, Arith.two_pow_succ, Nat.mul_assoc, Nat.mul_left_comm, hhalf]
      rw [hlist, hkey]
      exact ih
    · -- odd step: the new element enters both products
      have hlist : oddElems x (k + 1) = acceleratedOrbit k x :: oddElems x k := by
        show (if acceleratedOrbit k x % 2 = 1 then _ else _) = _
        rw [if_pos ho]
      have hval : acceleratedStep (acceleratedOrbit k x)
          = (3 * acceleratedOrbit k x + 1) / 2 := by
        rw [acceleratedStep, if_neg (by omega)]
      have hpar : 2 * ((3 * acceleratedOrbit k x + 1) / 2) = 3 * acceleratedOrbit k x + 1 := by
        omega
      have hkey : 2 ^ (k + 1) * acceleratedOrbit (k + 1) x
          = 2 ^ k * (3 * acceleratedOrbit k x + 1) := by
        rw [hstep, hval, Arith.two_pow_succ, Nat.mul_assoc, Nat.mul_left_comm, hpar]
      rw [hlist, hkey, shiftProd_cons]
      show 2 ^ k * (3 * acceleratedOrbit k x + 1)
          * (acceleratedOrbit k x * (oddElems x k).prod)
        = x * ((3 * acceleratedOrbit k x + 1) * shiftProd (oddElems x k))
      calc 2 ^ k * (3 * acceleratedOrbit k x + 1)
            * (acceleratedOrbit k x * (oddElems x k).prod)
          = (3 * acceleratedOrbit k x + 1)
              * (2 ^ k * acceleratedOrbit k x * (oddElems x k).prod) := by
            simp [Nat.mul_comm, Nat.mul_left_comm, Nat.mul_assoc]
        _ = (3 * acceleratedOrbit k x + 1) * (x * shiftProd (oddElems x k)) := by rw [ih]
        _ = x * ((3 * acceleratedOrbit k x + 1) * shiftProd (oddElems x k)) := by
            rw [Nat.mul_left_comm]

/-! ## The product bound with the actual elements -/

/-- **The never-dropper product bound, element by element.**  No constant `m` is
baked in: the bound is stated against the elements the orbit actually visits,
which is what a staircase refinement needs. -/
theorem neverDrops_prod_le {x : Nat} (hx : 0 < x)
    (hnd : ∀ i : Nat, x ≤ acceleratedOrbit i x) (k : Nat) :
    2 ^ k * (oddElems x k).prod ≤ shiftProd (oddElems x k) := by
  have hid := orbit_product x k
  have hmono : 2 ^ k * x * (oddElems x k).prod
      ≤ 2 ^ k * acceleratedOrbit k x * (oddElems x k).prod := by
    have h1 : 2 ^ k * x ≤ 2 ^ k * acceleratedOrbit k x := Nat.mul_le_mul_left _ (hnd k)
    exact Nat.mul_le_mul_right _ h1
  have hrw : 2 ^ k * x * (oddElems x k).prod
      = x * (2 ^ k * (oddElems x k).prod) := by
    simp [Nat.mul_comm, Nat.mul_left_comm, Nat.mul_assoc]
  rw [hrw, hid] at hmono
  exact Nat.le_of_mul_le_mul_left hmono hx

/-- The same for a cycle, where the endpoint cancels exactly. -/
theorem cycle_prod_eq {x L : Nat} (hx : 0 < x) (hcyc : acceleratedOrbit L x = x) :
    2 ^ L * (oddElems x L).prod = shiftProd (oddElems x L) := by
  have hid := orbit_product x L
  rw [hcyc] at hid
  have hrw : 2 ^ L * x * (oddElems x L).prod = x * (2 ^ L * (oddElems x L).prod) := by
    simp [Nat.mul_comm, Nat.mul_left_comm, Nat.mul_assoc]
  rw [hrw] at hid
  exact Nat.eq_of_mul_eq_mul_left hx hid

/-! ## What this unblocks, and what is still missing

`neverDrops_prod_le` and `cycle_prod_eq` are the hypotheses that
`StairThree.seq_product_bound` consumes, once two further facts are supplied:

* **distinctness** — the orbit values of a non-periodic orbit are pairwise
  distinct, so `oddElems` has no duplicates;
* **ordering** — the staircase argument compares against the *sorted* elements,
  so the list must be sorted, or the comparison recast as a counting statement.

Neither is deep, and both are the same obstruction that has blocked the cycle-half
plumbing since Round XXIII.  With them, the never-dropper density deficit improves
from a constant `O(1/m)` to a vanishing `O(log k / k)`. -/

end OrbitProduct
end Collatz
