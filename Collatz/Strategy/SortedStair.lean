import Collatz.Strategy.OrbitProduct
import Collatz.Strategy.StairBound

/-!
# The staircase for a sorted list, and distinctness of the orbit's elements

Round XXVIII left one item blocking both halves' bookkeeping: the elements of
`oddElems` must be known **distinct**, and the staircase comparison needs them
**ordered**.  This file does both, and the ordered comparison turns out to be a
three-line induction once the staircase is peeled from the correct end.

## Peeling from the small end

`StairBound.stair` is defined peeling the *largest* step, `stair m (a+1) =
(m + 2a) · stair m a`.  The induction needed here peels the *smallest*:

`stair m (a+1) = m · stair (m+2) a`,  `stairPlus m (a+1) = (3m+1) · stairPlus (m+2) a`

(`stair_peel`, `stairPlus_peel`).  With the staircase in that form, the comparison
against a strictly increasing list of odd numbers is immediate: the head `y`
satisfies `m ≤ y`, every later element is `> y` and odd hence `≥ y + 2 ≥ m + 2`, so
the induction hypothesis applies at base `m + 2`, and the two heads are compared by
`StairBound.cross_step` — the statement that `3 + 1/n` decreases.

**`sorted_stair_bound`: for a strictly increasing list of odd numbers all at least
an odd `m`,**

`∏ (3 yᵢ + 1) · ∏_{j<a} (m + 2j)  ≤  ∏ yᵢ · ∏_{j<a} (3(m+2j) + 1)`.

Combined with `OrbitProduct.neverDrops_prod_le` or `cycle_prod_eq` this is the
staircase bound with the orbit's actual elements, for cycles **and** never-droppers.

## Distinctness

`oddElems_mem` records that every listed value is `T^i(x)` for some `i < k`, and
`oddElems_nodup` derives duplicate-freeness from injectivity of the orbit on
`[0, k)` — which holds for a divergent orbit outright, and for a cycle of minimal
period on one period.

## What remains

Only the *sort*: turning `oddElems x k`, known duplicate-free, into a strictly
increasing list with the same two products.  Insertion sort suffices and the
product invariance is one induction each; it is mechanical and is the single
remaining step of this bookkeeping.
-/

namespace Collatz
namespace SortedStair

open Reach StairBound OrbitProduct

/-! ## Peeling the staircase from the small end -/

theorem stair_peel (m : Nat) : ∀ a : Nat, stair m (a + 1) = m * stair (m + 2) a := by
  intro a
  induction a with
  | zero => show (m + 2 * 0) * stair m 0 = m * 1; simp [stair]
  | succ a ih =>
    show (m + 2 * (a + 1)) * stair m (a + 1) = m * ((m + 2 + 2 * a) * stair (m + 2) a)
    rw [ih]
    have he : m + 2 * (a + 1) = m + 2 + 2 * a := by omega
    rw [he]
    simp [Nat.mul_comm, Nat.mul_left_comm, Nat.mul_assoc]

theorem stairPlus_peel (m : Nat) : ∀ a : Nat,
    stairPlus m (a + 1) = (3 * m + 1) * stairPlus (m + 2) a := by
  intro a
  induction a with
  | zero => show (3 * (m + 2 * 0) + 1) * stairPlus m 0 = (3 * m + 1) * 1; simp [stairPlus]
  | succ a ih =>
    show (3 * (m + 2 * (a + 1)) + 1) * stairPlus m (a + 1)
        = (3 * m + 1) * ((3 * (m + 2 + 2 * a) + 1) * stairPlus (m + 2) a)
    rw [ih]
    have he : m + 2 * (a + 1) = m + 2 + 2 * a := by omega
    rw [he]
    simp [Nat.mul_comm, Nat.mul_left_comm, Nat.mul_assoc]

/-! ## Strictly increasing lists -/

/-- Every element is strictly below all later ones. -/
def StrictSorted : List Nat → Prop
  | [] => True
  | y :: t => (∀ z ∈ t, y < z) ∧ StrictSorted t

/-! ## The staircase bound for a sorted list -/

/-- **The staircase, against the elements themselves.**  A strictly increasing list
of odd numbers, all at least an odd `m`, satisfies the staircase product
inequality.  This is `StairBound.stair_product_bound` with the sortedness supplied
rather than assumed as an indexed sequence. -/
theorem sorted_stair_bound : ∀ (l : List Nat) (m : Nat), m % 2 = 1 →
    StrictSorted l → (∀ y ∈ l, m ≤ y) → (∀ y ∈ l, y % 2 = 1) →
    shiftProd l * stair m l.length ≤ l.prod * stairPlus m l.length := by
  intro l
  induction l with
  | nil => intro m _ _ _ _; simp [shiftProd, stair, stairPlus]
  | cons y t ih =>
    intro m hm hsort hge hodd
    have hy : m ≤ y := hge y (List.mem_cons_self)
    have hyodd : y % 2 = 1 := hodd y (List.mem_cons_self)
    have htail : ∀ z ∈ t, m + 2 ≤ z := by
      intro z hz
      have hlt := hsort.1 z hz
      have hzodd := hodd z (List.mem_cons_of_mem _ hz)
      omega
    have hrec := ih (m + 2) (by omega) hsort.2 htail
      (fun z hz => hodd z (List.mem_cons_of_mem _ hz))
    have hcross : (3 * y + 1) * m ≤ y * (3 * m + 1) := cross_step hy
    show shiftProd (y :: t) * stair m (t.length + 1)
        ≤ (y :: t).prod * stairPlus m (t.length + 1)
    rw [shiftProd_cons, stair_peel, stairPlus_peel]
    show (3 * y + 1) * shiftProd t * (m * stair (m + 2) t.length)
        ≤ y * t.prod * ((3 * m + 1) * stairPlus (m + 2) t.length)
    have hL : (3 * y + 1) * shiftProd t * (m * stair (m + 2) t.length)
        = ((3 * y + 1) * m) * (shiftProd t * stair (m + 2) t.length) := by
      simp [Nat.mul_comm, Nat.mul_left_comm, Nat.mul_assoc]
    have hR : y * t.prod * ((3 * m + 1) * stairPlus (m + 2) t.length)
        = (y * (3 * m + 1)) * (t.prod * stairPlus (m + 2) t.length) := by
      simp [Nat.mul_comm, Nat.mul_left_comm, Nat.mul_assoc]
    rw [hL, hR]
    exact Nat.mul_le_mul hcross hrec

/-! ## Distinctness of the orbit's odd elements -/

/-- Every listed value is an orbit point of index below `k`. -/
theorem oddElems_mem {x : Nat} : ∀ (k : Nat) (y : Nat), y ∈ oddElems x k →
    ∃ i : Nat, i < k ∧ acceleratedOrbit i x = y := by
  intro k
  induction k with
  | zero => intro y hy; cases hy
  | succ k ih =>
    intro y hy
    rcases Arith.mod_two_eq_zero_or_one (acceleratedOrbit k x) with he | ho
    · have hlist : oddElems x (k + 1) = oddElems x k := by
        show (if acceleratedOrbit k x % 2 = 1 then _ else oddElems x k) = _
        rw [if_neg (by omega)]
      rw [hlist] at hy
      obtain ⟨i, hi, hval⟩ := ih y hy
      exact ⟨i, by omega, hval⟩
    · have hlist : oddElems x (k + 1) = acceleratedOrbit k x :: oddElems x k := by
        show (if acceleratedOrbit k x % 2 = 1 then _ else _) = _
        rw [if_pos ho]
      rw [hlist] at hy
      rcases List.mem_cons.mp hy with h | h
      · exact ⟨k, by omega, h.symm⟩
      · obtain ⟨i, hi, hval⟩ := ih y h
        exact ⟨i, by omega, hval⟩

/-- **Duplicate-freeness.**  If the orbit is injective on `[0, k)` — true outright
for a divergent orbit, and for a cycle of minimal period on one period — then the
listed odd elements are pairwise distinct. -/
theorem oddElems_nodup {x : Nat} : ∀ k : Nat,
    (∀ i j : Nat, i < k → j < k → acceleratedOrbit i x = acceleratedOrbit j x → i = j) →
    (oddElems x k).Nodup := by
  intro k
  induction k with
  | zero => intro _; exact List.nodup_nil
  | succ k ih =>
    intro hinj
    have hrec := ih (fun i j hi hj h => hinj i j (by omega) (by omega) h)
    rcases Arith.mod_two_eq_zero_or_one (acceleratedOrbit k x) with he | ho
    · have hlist : oddElems x (k + 1) = oddElems x k := by
        show (if acceleratedOrbit k x % 2 = 1 then _ else oddElems x k) = _
        rw [if_neg (by omega)]
      rw [hlist]
      exact hrec
    · have hlist : oddElems x (k + 1) = acceleratedOrbit k x :: oddElems x k := by
        show (if acceleratedOrbit k x % 2 = 1 then _ else _) = _
        rw [if_pos ho]
      rw [hlist]
      refine List.nodup_cons.mpr ⟨?_, hrec⟩
      intro hmem
      obtain ⟨i, hi, hval⟩ := oddElems_mem k (acceleratedOrbit k x) hmem
      have := hinj i k (by omega) (by omega) hval
      omega

end SortedStair
end Collatz
