import Collatz.Strategy.AccumulatorArith
import Collatz.Strategy.CycleAccumulator

/-!
# Round XI, Section I — the two normalisations, and the exact conversion

Two different quantities have both been called "the coupling", and Round X's reports
put them in apparent tension: one is monotone increasing, the other vanishes.  They are
different objects and the brief is right that they must not be combined without a
theorem.  Here is the theorem.

## The two objects

* **Fixed-start** `r j = C j / (3 ^ (A j) · n)` — the accumulator measured against the
  *original* starting point.  `Linearizing.coupling_monotone` shows it increases from
  `r 0 = 0`.
* **Self-normalised** `κ (i,k) = C k (x_i) / (3 ^ (A_win) · x_i)` — a window's
  accumulator measured against *that window's own* starting point.  `ScaleLadder`
  measures it falling off like `1/x_i`.

## The conversion

The whole relationship follows from one observation, which is `affine_exact` read in
coupling coordinates:

> **`1 + r j = 2^j · x_j / (3 ^ (A j) · n)`.**

Because `2^j x_j = 3^(A j) n + C j`, the numerator of `1 + r j` *is* the left-hand side
of the affine law.  Substituting into both sides and using additivity of `oddCount`
along the orbit gives, exactly:

> **`1 + r (i+k) = (1 + r i) · (1 + κ (i,k))`**

verified in exact rationals for `d = 1` (at `n = 1, 7, 27, 703, 99999`, all `i < 25`,
`k < 12`) and for `d = 5, −1, 59`.  `coupling_multiplicative` below is this identity
cleared of division, so it is a `Nat` statement.

Two consequences, and they are the point.

## 1.  `(1 + r)` is multiplicative over concatenated blocks

`1 + r_total = ∏_blocks (1 + κ_block)`.  This is the exact composition law the brief
asks for in section IX, and it settles the aggregation question of section XV: the
right law is the **product**, not the sum, so `Σ κ` converges exactly when the product
is bounded.

## 2.  Around a cycle the total is pinned, and the budget is under one bit

On a cycle `x_L = n` and `A_L = a`, so the closed form collapses to

> **`∏_blocks (1 + κ_block) = 2^L / 3^a`, exactly.**

Verified: `1.3333333333` for the trivial `d = 1` cycle, `1.0393182483` for the `3x+5`
cycle at `n = 187`, `1.4046639232` for the `3x+59` cycle at `n = 229` — each matching
`2^L/3^a` to every digit printed.

Taking logarithms, `Σ_blocks log₂(1 + κ_block) = L − a·log₂ 3 = E`, and on the ledge
`E < 1`.  So:

> **The entire coupling budget around a cycle is `E` bits, distributed among the
> blocks however the word likes but summing to exactly `E`.**

Measured, and the identity is exact to every digit: `0.415037` for the trivial `d = 1`
cycle `(L,a) = (2,1)`; `0.055637` for both `3x+5` cycles at `n = 187` and `347`
`(27,17)`; `0.490225` for `3x+59` at `229` `(10,6)`; `0.225562` for `3x+13` at `131`
`(24,15)`.

*The bound `E < 1` needs asset (c).*  On the ledge `L = ⌊a·log₂3⌋ + 1`, so
`E ∈ (0,1)` — but only when `2^L > 3^a`.  The `3x−1` cycle at `n = 17` has
`(L,a) = (11,7)` with `3^7 = 2187 > 2048 = 2^11`, and there `E = −0.094738`: the budget
is **negative**.  So "under one bit" is a statement about positive `d`, and the
identity itself is the `d`-free part.

**This kills the "vanishing but accumulative" hope on the cycle half.**  Section XV
warns against concluding `ε_i → 0 ⇒ irrelevant`, and rightly — but here the
aggregation is pinned rather than merely convergent.  No amount of block subdivision
changes the total, because the total is a function of `(L, a)` alone.

It says nothing about the divergence half, where no closure pins the product.  That
remains open and is where the accumulation question is still live.

## Honest weight of this section

The conversion is *elementary* — once `1 + r j = 2^j x_j / (3^(A j) n)` is written down,
multiplicativity is forced by `oddCount` additivity and commutativity.  Its value is
not depth but hygiene: it makes the two normalisations comparable, explains the
apparent tension between "monotone" and "vanishing" (the factor is `1 + r_i`, which is
bounded), and converts an open aggregation question into a closed one on half the
problem.
-/

namespace Collatz
namespace CouplingNormal

open AccumulatorArith CycleAccumulator AffineExact

/-! ## The closed form for `1 + r` -/

/-- **`1 + r j` in closed form.**  The numerator `3^(A j)·n + C j` is exactly
`2^j · x_j` by the affine law, so the fixed-start coupling is
`r j = 2^j x_j / (3^(A j) n) − 1` with no accumulator left in it. -/
theorem one_add_coupling (n j : Nat) :
    3 ^ oddCount n j * n + affineC j n = 2 ^ j * acceleratedOrbit j n :=
  (affine_exact n j).symm

/-! ## The conversion, cleared of division

`1 + r (i+k) = (1 + r i)(1 + κ (i,k))` becomes, after multiplying through by the three
denominators `3^(A (i+k))·n`, `3^(A i)·n` and `3^(A_win)·x_i`, an identity between
products of the closed forms above.  The content is `oddCount` additivity; the rest is
commutativity. -/

/-- **The composition law.**  Multiplicativity of `1 + r` over a split of the window at
index `i`, as a `Nat` identity.  Reading the three bracketed factors as numerators of
`1 + r (i+k)`, `1 + r i` and `1 + κ (i,k)` against their denominators recovers
`1 + r (i+k) = (1 + r i)·(1 + κ (i,k))`. -/
theorem coupling_multiplicative (n i k : Nat) :
    (2 ^ (i + k) * acceleratedOrbit (i + k) n) *
        ((3 ^ oddCount n i * n) * (3 ^ oddCount (acceleratedOrbit i n) k *
          acceleratedOrbit i n))
      = ((2 ^ i * acceleratedOrbit i n) * (2 ^ k * acceleratedOrbit (i + k) n)) *
        (3 ^ oddCount n (i + k) * n) := by
  rw [oddCount_add n i k, Nat.pow_add, Nat.pow_add]
  simp [Nat.mul_comm, Nat.mul_left_comm, Nat.mul_assoc]

/-- The window endpoint is the whole-orbit endpoint: `T^k (T^i n) = T^(i+k) n`.  Stated
so the composition law can be read with the window's own coordinates. -/
theorem window_endpoint (n i k : Nat) :
    acceleratedOrbit k (acceleratedOrbit i n) = acceleratedOrbit (i + k) n := by
  rw [acceleratedOrbit_add]
  rw [Nat.add_comm]

/-! ## The cycle case

On a cycle the closed form collapses, because `x_L = n`.  The `Nat` statement is
`CycleAccumulator.cycle_affine` — cited, **not** re-proved here; an earlier round was
caught renaming existing theorems and this file does not repeat that.  What is new is
only the reading:

`1 + r L = 2^L·n / (3^a·n) = 2^L / 3^a`, hence `∏_blocks (1 + κ_block) = 2^L / 3^a`,
hence `Σ_blocks log₂(1 + κ_block) = E = L − a·log₂ 3 < 1` on the ledge. -/

/-- The total coupling around a cycle, in the closed form above.  This is
`CycleAccumulator.cycle_affine` under the coupling reading; the proof is that
theorem. -/
theorem cycle_total_coupling {n L : Nat} (h : AccCycle.AccIsCycleOf n L) :
    3 ^ oddCount n L * n + affineC L n = 2 ^ L * n :=
  (cycle_affine h).symm

/-! ## Axiom audit -/

#print axioms one_add_coupling
#print axioms coupling_multiplicative
#print axioms cycle_total_coupling

end CouplingNormal
end Collatz
