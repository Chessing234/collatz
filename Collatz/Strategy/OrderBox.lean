import Collatz.Strategy.ExtremalWord

/-!
# The accumulator on the box: balance maximises, imbalance minimises

Round VII localised the cycle problem to the ordered odd-step times
`0 ≤ t₀ < t₁ < ⋯ < t_(a−1) < L`, and `ExtremalWord` showed that on the ledge
heaviness is exactly the box `t i ≤ fexp i`.  `Cw` is monotone in every coordinate
(`Cw_le`, `Cw_strict`), so it is maximised at the box's top corner and minimised at
its bottom corner.

*Two caveats, both found by adversarial audit.*  First, the feasible set is not the
box but `box ∩ {t strictly increasing}`, and raising one `t i` alone can collide with
`t (i+1)`, so coordinatewise monotonicity does not by itself put the extremes at the
corners.  It is repairable and true — the feasible set is a **sublattice** (the
coordinatewise meet and join of two strictly increasing sequences bounded by `fexp`
are again strictly increasing and so bounded), with bottom `t i = i` and, on the
ledge, top `t i = fexp i`, and a monotone function on a lattice with top and bottom
attains its extremes there.  The theorems below are stated for the corners directly
and do not depend on that step; it is recorded because the informal argument needs it.

Second, `max C = Bcap a` is a **ledge** statement.  Below the ledge the Beatty corner
does not fit in the word and the maximum is strictly smaller — measured: `a = 7`,
`L = 9` gives `maxC = 3511` against `Bcap = 3767`; `a = 10`, `L = 13` gives `121165`
against `148813`.  It is cycle-irrelevant only because
`GapSandwich.cycle_length_determined` forces `L = fexp a + 1`, which is what the
claim must cite.  The *minimum* half is unaffected and holds at every `L`.  `ExtremalWord` supplies the top; this file supplies the bottom,
and reads both in ordering coordinates.

## The two corners

* **Top corner** `t i = fexp i` — the Beatty word.  `Cw = Bcap a` (`Cw_fexp`), and
  equality characterises it (`Cw_eq_Bcap_iff`).
* **Bottom corner** `t i = i` — the word `1^a 0^(L−a)`, every odd step taken as
  early as possible.  `Cw + 2^a = 3^a` (`Cw_id`), and it is the minimum over every
  strictly increasing time sequence (`Cw_id_le`).

So on the box

`3^a − 2^a  ≤  C  ≤  Bcap a`,

both attained, and both corners explicit.

## Why this refutes the hoped-for chain

The natural guess — and the one the Round VIII brief proposes as Chain D — is that
an accumulator-*minimal* ordering should be *balanced*, hence Sturmian, hence
rigid.  **It is exactly backwards.**  Measured at every ledge pair `L = fexp a + 1`
with `L ≤ 18`, with discrepancy `D(j) = A(j) − (a/L)·j` and width
`max D − min D`:

| `L` | argmin `C` | width | argmax `C` | width |
|---|---|---|---|---|
| 12 | `111111100000` | 2.917 | `110110110100` | 1.333 |
| 15 | `111111111000000` | 3.600 | `110110110101100` | 1.200 |
| 18 | `111111111110000000` | 4.278 | `110110110101101100` | 1.222 |

The minimiser is `1^a 0^(L−a)`, whose discrepancy width grows **linearly** in `L`;
the maximiser is the Beatty word, whose width stays near `1`.  **Balance maximises
the accumulator.**  So "accumulator-minimal ⟹ balanced" is false in the strongest
possible way, and any chain routed through it is dead.

What survives is the honest statement: `C` is a monotone function on the box, the
ordering-to-accumulator map is completely understood, and there is no hidden
ordering structure inside `C` beyond the box coordinate itself.

One caveat, inherited from `ExtremalWord`: for *proper-prefix* heaviness,
`heavy ⟺ box` holds for every `L ≤ fexp a + 1` — on the ledge **and everywhere
below it** — and fails only *above*, where the heavy set is empty while the box is
not (`a = 10`: heavy 0, box 476, at `L = 17, 18, 19`).  Verified for every
`a ≤ 8` and every `L ≤ fexp a + 1`, zero mismatches.  An earlier version of this
note, and `ExtremalWord`'s own header, said "on the ledge and only there"; the
failure is one-sided.
-/

namespace Collatz
namespace OrderBox

open ExtremalWord RealizableBound

/-! ## The bottom corner -/

/-- **The bottom corner of the box.**  Taking every odd step as early as possible,
`t i = i`, gives `Cw + 2^a = 3^a` — the word `1^a 0^(L−a)`.  Subtraction-free. -/
theorem Cw_id : ∀ a : Nat, Cw (fun i => i) a + 2 ^ a = 3 ^ a := by
  intro a
  induction a with
  | zero => rfl
  | succ a ih =>
    rw [Cw_succ, Nat.pow_succ 2 a, Nat.pow_succ 3 a]
    omega

/-- Any strictly increasing time sequence dominates the identity coordinatewise. -/
theorem le_of_strictInc {t : Nat → Nat} (h : StrictInc t) : ∀ i : Nat, i ≤ t i := by
  intro i
  induction i with
  | zero => exact Nat.zero_le _
  | succ i ih =>
    have := h i
    omega

/-- **The bottom corner is the minimum.**  Every strictly increasing time sequence
has accumulator at least that of `t i = i`. -/
theorem Cw_id_le {t : Nat → Nat} (h : StrictInc t) (a : Nat) :
    Cw (fun i => i) a ≤ Cw t a :=
  Cw_le (fun i => i) t a (fun i _ => le_of_strictInc h i)

/-- **The two-sided box bound, in ordering coordinates.**  For a strictly increasing
time sequence inside the box, `3^a ≤ C + 2^a` and `C ≤ Bcap a`. -/
theorem Cw_sandwich {t : Nat → Nat} (h : StrictInc t) {a : Nat}
    (hbox : ∀ i : Nat, i < a → t i ≤ fexp i) :
    3 ^ a ≤ Cw t a + 2 ^ a ∧ Cw t a ≤ Bcap a := by
  refine ⟨?_, ?_⟩
  · have h1 := Cw_id a
    have h2 := Cw_id_le h a
    omega
  · have := Cw_le t fexp a hbox
    rw [Cw_fexp] at this
    exact this

/-- **The minimum is attained exactly at the bottom corner**, by the same strictness
argument that pins the top. -/
theorem Cw_eq_bottom_iff {t : Nat → Nat} (h : StrictInc t) {a : Nat} :
    Cw t a = Cw (fun i => i) a ↔ ∀ i : Nat, i < a → t i = i := by
  constructor
  · intro heq i hi
    by_cases hlt : i < t i
    · have := Cw_strict (fun i => i) t a i hi (fun k _ => le_of_strictInc h k) hlt
      omega
    · have := le_of_strictInc h i
      omega
  · intro hall
    have h1 : ∀ i : Nat, i < a → t i ≤ i := fun i hi => Nat.le_of_eq (hall i hi)
    have h2 : ∀ i : Nat, i < a → i ≤ t i := fun i hi => Nat.le_of_eq (hall i hi).symm
    exact Nat.le_antisymm (Cw_le t (fun i => i) a h1) (Cw_le (fun i => i) t a h2)

end OrderBox
end Collatz
