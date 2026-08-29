import Collatz.Strategy.SortedStair

/-!
# Insertion sort, and the staircase bound with the orbit's own elements

The last mechanical step.  `OrbitProduct` supplies the orbit's odd elements and
the telescoping identity; `SortedStair` supplies the staircase comparison for a
*strictly increasing* list and the duplicate-freeness of the elements.  What was
missing is the sort itself.

Only the two products have to survive sorting — `prod` and `shiftProd` — not the
list up to permutation, so no `List.Perm` machinery appears here.  Each invariance
is a single induction (`insertSorted_prod`, `insertSorted_shiftProd`), and strict
sortedness of the output follows from duplicate-freeness of the input
(`sortList_sorted`).

## The payoff

**`neverDrops_staircase`**: for an odd never-dropper `x` whose orbit is injective
on `[0, k)`, with `a = oddCount x k`,

`2 ^ k · ∏_{j<a} (x + 2j)  ≤  ∏_{j<a} (3(x + 2j) + 1)`.

**`cycle_staircase`**: the same for a cycle of minimal period.

Both replace `CycleProduct.neverDrops_product_bound`'s `2^k · x^a ≤ (3x+1)^a`,
which bounds every element below by the minimum.  The staircase uses the fact that
the elements are *distinct*, which the constant bound throws away.

## What it changes, quantitatively

The old bound caps `Λ = k log 2 − a log 3` by `a·log(1 + 1/3x) ≈ a/(3x)`, **linear**
in `a`; that constant deficit of order `1/x` is exactly what produces the
`ProductCeiling` horizon at `2.079 x`.  The staircase caps it by
`Σ_{j<a} log(1 + 1/(3(x+2j))) ≈ (1/6)·log(1 + 2a/x)`, **logarithmic** in `a`, so the
density deficit is of order `log k / k` and **tends to zero**.

For the cycle half this is subsumed by Halbeisen–Hungerbühler (Round XXV).  For the
**divergence** half it is not: nothing in that literature applies the distinctness
of a never-dropping orbit's elements, because those results are about cycles.

## Honest scope

This does not close either half.  Every bound here is an *upper* bound on `Λ`, and
a divergent orbit is free to send `Λ → −∞`; the improvement is in how tightly the
density is pinned from below, not in excluding divergence.  The injectivity
hypothesis is discharged for free by divergence and by minimal periodicity, but is
left explicit here rather than assumed.
-/

namespace Collatz
namespace SortStair

open Reach StairBound OrbitProduct SortedStair

/-! ## Insertion sort -/

/-- Insert `y` into a list, before the first strictly larger element. -/
def insertSorted (y : Nat) : List Nat → List Nat
  | [] => [y]
  | z :: t => if y < z then y :: z :: t else z :: insertSorted y t

/-- Insertion sort. -/
def sortList : List Nat → List Nat
  | [] => []
  | y :: t => insertSorted y (sortList t)

/-! ## The two products survive -/

theorem insertSorted_prod (y : Nat) : ∀ l : List Nat,
    (insertSorted y l).prod = y * l.prod := by
  intro l
  induction l with
  | nil => simp [insertSorted]
  | cons z t ih =>
    show (if y < z then y :: z :: t else z :: insertSorted y t).prod = y * (z :: t).prod
    split
    · rfl
    · show z * (insertSorted y t).prod = y * (z * t.prod)
      rw [ih]
      simp [Nat.mul_comm, Nat.mul_left_comm, Nat.mul_assoc]

theorem insertSorted_shiftProd (y : Nat) : ∀ l : List Nat,
    shiftProd (insertSorted y l) = (3 * y + 1) * shiftProd l := by
  intro l
  induction l with
  | nil => simp [insertSorted, shiftProd]
  | cons z t ih =>
    show shiftProd (if y < z then y :: z :: t else z :: insertSorted y t)
        = (3 * y + 1) * shiftProd (z :: t)
    split
    · rw [shiftProd_cons]
    · rw [shiftProd_cons, ih, shiftProd_cons]
      simp [Nat.mul_comm, Nat.mul_left_comm, Nat.mul_assoc]

theorem insertSorted_length (y : Nat) : ∀ l : List Nat,
    (insertSorted y l).length = l.length + 1 := by
  intro l
  induction l with
  | nil => rfl
  | cons z t ih =>
    show (if y < z then y :: z :: t else z :: insertSorted y t).length = (z :: t).length + 1
    split
    · rfl
    · show (insertSorted y t).length + 1 = t.length + 1 + 1
      rw [ih]

theorem insertSorted_mem (y : Nat) : ∀ (l : List Nat) (w : Nat),
    w ∈ insertSorted y l ↔ w = y ∨ w ∈ l := by
  intro l
  induction l with
  | nil => intro w; simp [insertSorted]
  | cons z t ih =>
    intro w
    show w ∈ (if y < z then y :: z :: t else z :: insertSorted y t) ↔ _
    split
    · exact List.mem_cons
    · constructor
      · intro h
        rcases List.mem_cons.mp h with h1 | h1
        · exact Or.inr (List.mem_cons.mpr (Or.inl h1))
        · rcases (ih w).mp h1 with h2 | h2
          · exact Or.inl h2
          · exact Or.inr (List.mem_cons.mpr (Or.inr h2))
      · intro h
        rcases h with h1 | h1
        · exact List.mem_cons.mpr (Or.inr ((ih w).mpr (Or.inl h1)))
        · rcases List.mem_cons.mp h1 with h2 | h2
          · exact List.mem_cons.mpr (Or.inl h2)
          · exact List.mem_cons.mpr (Or.inr ((ih w).mpr (Or.inr h2)))

theorem sortList_prod : ∀ l : List Nat, (sortList l).prod = l.prod := by
  intro l
  induction l with
  | nil => rfl
  | cons y t ih =>
    show (insertSorted y (sortList t)).prod = y * t.prod
    rw [insertSorted_prod, ih]

theorem sortList_shiftProd : ∀ l : List Nat, shiftProd (sortList l) = shiftProd l := by
  intro l
  induction l with
  | nil => rfl
  | cons y t ih =>
    show shiftProd (insertSorted y (sortList t)) = shiftProd (y :: t)
    rw [insertSorted_shiftProd, ih, shiftProd_cons]

theorem sortList_length : ∀ l : List Nat, (sortList l).length = l.length := by
  intro l
  induction l with
  | nil => rfl
  | cons y t ih =>
    show (insertSorted y (sortList t)).length = t.length + 1
    rw [insertSorted_length, ih]

theorem sortList_mem : ∀ (l : List Nat) (w : Nat), w ∈ sortList l ↔ w ∈ l := by
  intro l
  induction l with
  | nil => intro w; rfl
  | cons y t ih =>
    intro w
    show w ∈ insertSorted y (sortList t) ↔ w ∈ y :: t
    rw [insertSorted_mem, ih w, List.mem_cons]

/-! ## The output is strictly increasing -/

theorem insertSorted_sorted (y : Nat) : ∀ l : List Nat,
    StrictSorted l → (y ∉ l) → StrictSorted (insertSorted y l) := by
  intro l
  induction l with
  | nil =>
    intro _ _
    refine ⟨?_, trivial⟩
    intro z hz
    simp at hz
  | cons z t ih =>
    intro hs hy
    have hyz : y ≠ z := by
      intro h; exact hy (by rw [h]; exact List.mem_cons_self)
    have hyt : y ∉ t := fun h => hy (List.mem_cons_of_mem _ h)
    show StrictSorted (if y < z then y :: z :: t else z :: insertSorted y t)
    split
    · rename_i hlt
      refine ⟨?_, hs⟩
      intro w hw
      rcases List.mem_cons.mp hw with h | h
      · omega
      · exact Nat.lt_trans hlt (hs.1 w h)
    · rename_i hnlt
      refine ⟨?_, ih hs.2 hyt⟩
      intro w hw
      rcases (insertSorted_mem y t w).mp hw with h | h
      · omega
      · exact hs.1 w h

theorem sortList_sorted : ∀ l : List Nat, l.Nodup → StrictSorted (sortList l) := by
  intro l
  induction l with
  | nil => intro _; trivial
  | cons y t ih =>
    intro hnd
    have hsplit := List.nodup_cons.mp hnd
    have hnot : y ∉ sortList t := fun h => hsplit.1 ((sortList_mem t y).mp h)
    exact insertSorted_sorted y (sortList t) (ih hsplit.2) hnot

/-! ## Products are positive -/

theorem prod_pos : ∀ l : List Nat, (∀ y ∈ l, 0 < y) → 0 < l.prod := by
  intro l
  induction l with
  | nil => intro _; exact Nat.one_pos
  | cons y t ih =>
    intro h
    exact Nat.mul_pos (h y List.mem_cons_self)
      (ih (fun z hz => h z (List.mem_cons_of_mem _ hz)))

/-! ## The staircase bound with the orbit's own elements -/

/-- **The never-dropper staircase.**  For an odd never-dropper `x` whose orbit is
injective on `[0, k)`, the product bound holds against the *staircase* `x + 2j`
rather than the constant `x`. -/
theorem neverDrops_staircase {x k : Nat} (hx : 0 < x) (hxodd : x % 2 = 1)
    (hnd : ∀ i : Nat, x ≤ acceleratedOrbit i x)
    (hinj : ∀ i j : Nat, i < k → j < k →
      acceleratedOrbit i x = acceleratedOrbit j x → i = j) :
    2 ^ k * stair x (oddCount x k) ≤ stairPlus x (oddCount x k) := by
  -- the elements, sorted
  have hnd' := oddElems_nodup (x := x) k hinj
  have hsorted := sortList_sorted (oddElems x k) hnd'
  have hlen : (sortList (oddElems x k)).length = oddCount x k := by
    rw [sortList_length, oddElems_length]
  have hge : ∀ y ∈ sortList (oddElems x k), x ≤ y := by
    intro y hy
    exact oddElems_ge hnd k y ((sortList_mem _ y).mp hy)
  have hodd : ∀ y ∈ sortList (oddElems x k), y % 2 = 1 := by
    intro y hy
    exact oddElems_odd x k y ((sortList_mem _ y).mp hy)
  -- the staircase comparison
  have hstair := sorted_stair_bound (sortList (oddElems x k)) x hxodd hsorted hge hodd
  rw [hlen, sortList_prod, sortList_shiftProd] at hstair
  -- the product bound
  have hprod := neverDrops_prod_le hx hnd k
  have hP : 0 < (oddElems x k).prod :=
    prod_pos _ (fun y hy => by have := oddElems_odd x k y hy; omega)
  -- combine and cancel
  have hchain : 2 ^ k * (oddElems x k).prod * stair x (oddCount x k)
      ≤ (oddElems x k).prod * stairPlus x (oddCount x k) := by
    have h1 : 2 ^ k * (oddElems x k).prod * stair x (oddCount x k)
        ≤ shiftProd (oddElems x k) * stair x (oddCount x k) :=
      Nat.mul_le_mul_right _ hprod
    exact Nat.le_trans h1 hstair
  have hre : 2 ^ k * (oddElems x k).prod * stair x (oddCount x k)
      = (oddElems x k).prod * (2 ^ k * stair x (oddCount x k)) := by
    simp [Nat.mul_comm, Nat.mul_left_comm, Nat.mul_assoc]
  rw [hre] at hchain
  exact Nat.le_of_mul_le_mul_left hchain hP

/-- **The cycle staircase.**  The same for a cycle whose period is minimal, where
the orbit is injective on one period. -/
theorem cycle_staircase {x L : Nat} (hx : 0 < x) (hxodd : x % 2 = 1)
    (hnd : ∀ i : Nat, x ≤ acceleratedOrbit i x)
    (hinj : ∀ i j : Nat, i < L → j < L →
      acceleratedOrbit i x = acceleratedOrbit j x → i = j) :
    2 ^ L * stair x (oddCount x L) ≤ stairPlus x (oddCount x L) :=
  neverDrops_staircase hx hxodd hnd hinj

end SortStair
end Collatz
