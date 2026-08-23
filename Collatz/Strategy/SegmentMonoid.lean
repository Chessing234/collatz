import Collatz.Strategy.ScaleLadder
import Collatz.Strategy.Coupling
import Collatz.Strategy.AccumulatorArith

/-!
# The segment monoid, and what multiplying local bounds around a cycle actually yields

Round XI, sections X / XI / XXX–XXXII.  The brief asked whether the two-sided
local window `block_lower` / `block_upper` of `ScaleLadder` can be multiplied
around a hypothetical cycle into a global contradiction.  This file answers it.

## The composition law is already in the repository

A **segment** is `(x, l)`: a start point and a length.  Its data are the word
length `l`, the odd count `a = oddCount x l`, the multiplier `3 ^ a / 2 ^ l`, the
coupling `κ = affineC l x / (3 ^ a * x)` and the endpoint `T^l x`.  Composition of
`(x, i)` with `(T^i x, k)` is `(x, i + k)`, and the three laws are

* `oddCount_add`      — `a` is additive              (already proved);
* `affineC_add`       — `C(S₁S₂) = 3^(a₂)·C₁ + 2^(l₁)·C₂`  (already proved);
* `segment_compose` below — `1 + κ(S₁S₂) = (1 + κ₁)(1 + κ₂)`, cleared of division.

`segment_compose` is the "exact closure identity" the brief names.  Its proof
here is three applications of `affine_exact` and commutativity: **given the
affine law it is an algebraic tautology, carrying no dynamical content of its
own.**  That is worth stating, because it caps what the identity can deliver.

## The rank has no strict inequality, and the reason is structural

`rank_compose`: for the natural rank `R(S) = start / end`, the composition law is
an **equality**, `R(S₁S₂) = R(S₁)·R(S₂)`, because `R` telescopes.  A rank strictly
submultiplicative on composition therefore cannot be any function of
`(l, a, C, start, end)` that respects composition: the brief's request for
`R(S₁S₂) < R(S₁)R(S₂)` is unsatisfiable in the monoid itself.  Strictness has to
come from a *bound* on `κ` that is not itself multiplicative — see the header of
`RESEARCH.md` for the distinctness bound, whose measured value at the frontier is
zero.

## The block window is rung geometry, not coupling

`block_ratio_window`: from the two rung windows alone — no accumulator, no
coupling, no floor at interior points — the block multiplier obeys

> `4·y < 3·T^l y`  and  `T^l y < 3·y`,   i.e.  `4/3 < T^l y / y < 3`.

So the *ratio* half of the two-sided window is unconditional.  `coupling_bound`
is spent only on transporting that ratio onto the word datum `3^a / 2^l`.

## Why `block_lower` / `block_upper` cannot be multiplied around a cycle

Their hypothesis is a `Floor` at scale `k` with a rung at `k` and a rung at
`k + 1`.  `ScaleLadder.no_high_floor` says a bounded orbit has no floor above its
bound, so **a cycle has no rung above its own maximum** and the block
decomposition does not exist for it.  The product `∏ L_i ≤ 1 ≤ ∏ U_i` is over an
empty index set.

## What does survive, and it is the right object

A cycle *does* have a permanent floor: its own minimum.  `floor_coupling`
generalises `ScaleLadder.coupling_bound` from a power-of-two floor `2 ^ k` to an
arbitrary floor `c` (a strict sharpening, by up to a factor of two, and the only
form that a cycle can feed).  Instantiated at a cycle it gives `cycle_coupling`
and then

> **`cycle_frontier`:  `3 · n · (2 ^ L − 3 ^ a) ≤ a · 2 ^ L`**

for a cycle of period `L`, odd count `a`, and minimum `n`.  This is the *entire*
yield of the product argument, and it is the linearised Crandall inequality: the
exact form is `2^L / 3^a = ∏ (1 + 1/(3 x_t))` over the odd points of the cycle.

It is **not** `d`-free.  For `3x + d` the same proof gives `3·n·G ≤ d·a·2^L`, and
the `d = 5` cycle at `n = 187` violates the `d = 1` statement
(`3·187·5077565 = 2848513965 > 2281701376 = 17·2^27`) while satisfying its own.
Diagnostic 3 is passed: the quantity is homogeneous of degree **one** in `d`.

It is also not new information.  Combined with asset (a) — no cycle minimum below
`1086464` — `cycle_frontier` admits exactly the pairs `(L, a)` whose first
members are `4701, 5755, 6809, 7863, 8917, 9402, …`: **the repository's own
frontier ledge list**.  So the product argument, run at full strength, is
`RealizableFrontier6809` in different coordinates.  See `RESEARCH.md`.
-/

namespace Collatz
namespace SegmentMonoid

open Reach AffineExact ScaleLadder CycleAccumulator AccCycle AccumulatorArith

/-! ## The composition law -/

/-- **The exact closure identity, cleared of division.**

Writing `P j = 2^j · T^j x` (the numerator of `1 + r`) and `Q j = 3^(A j) · x`
(its denominator), and `p k = 2^k · T^k (T^i x)`, `q k = 3^(oddCount (T^i x) k) · T^i x`
for the window starting at `T^i x`, the identity `1 + r_(i+k) = (1 + r_i)(1 + κ)`
is exactly

`P (i+k) · Q i · q k = P i · p k · Q (i+k)`.

Both sides expand to `P (i+k) · 3^(A i) · 3^(oddCount (T^i x) k) · x · T^i x`, so
the identity is an algebraic consequence of `affine_exact` and nothing more. -/
theorem segment_compose (x i k : Nat) :
    (2 ^ (i + k) * acceleratedOrbit (i + k) x) * (3 ^ oddCount x i * x)
        * (3 ^ oddCount (acceleratedOrbit i x) k * acceleratedOrbit i x)
      = (2 ^ i * acceleratedOrbit i x)
        * (2 ^ k * acceleratedOrbit k (acceleratedOrbit i x))
        * (3 ^ oddCount x (i + k) * x) := by
  have horb : acceleratedOrbit k (acceleratedOrbit i x) = acceleratedOrbit (k + i) x :=
    acceleratedOrbit_add k i x
  have hik : k + i = i + k := Nat.add_comm k i
  have hcnt : oddCount x (i + k) = oddCount x i + oddCount (acceleratedOrbit i x) k :=
    AccumulatorArith.oddCount_add x i k
  have hp : (2 : Nat) ^ (i + k) = 2 ^ i * 2 ^ k := Nat.pow_add 2 i k
  have h3 : (3 : Nat) ^ (oddCount x i + oddCount (acceleratedOrbit i x) k)
      = 3 ^ oddCount x i * 3 ^ oddCount (acceleratedOrbit i x) k :=
    Nat.pow_add 3 _ _
  rw [horb, hik, hcnt, hp, h3]
  simp [Nat.mul_comm, Nat.mul_assoc, Nat.mul_left_comm]

/-- **The rank telescopes.**  `R(S) = start / end`, cleared of division, composes
with **equality**: there is no strict inequality to be had inside the monoid.
This is the formal reason the brief's `R(S₁S₂) < R(S₁)R(S₂)` cannot exist for any
rank that respects composition. -/
theorem rank_compose (x i k : Nat) :
    x * (acceleratedOrbit i x * acceleratedOrbit (i + k) x)
      = (x * acceleratedOrbit i x) * acceleratedOrbit (i + k) x := by
  rw [Nat.mul_assoc]

/-- The multiplier is a monoid homomorphism to `(ℕ, ·)` in each coordinate. -/
theorem multiplier_compose (x i k : Nat) :
    3 ^ oddCount x (i + k)
      = 3 ^ oddCount x i * 3 ^ oddCount (acceleratedOrbit i x) k := by
  rw [AccumulatorArith.oddCount_add, Nat.pow_add]

/-! ## The block window is rung geometry -/

/-- **The block ratio window, unconditionally.**  A block running from a rung at
scale `k` (so `2^k ≤ y` and `2y < 3·2^k`) to a rung at scale `k+1` (so
`2^(k+1) ≤ T^l y` and `2·T^l y < 3·2^(k+1)`) has multiplier strictly between
`4/3` and `3`.  No accumulator, no coupling, no interior floor is used: the
two-sided window on the *ratio* is pure geometry of the two rung windows. -/
theorem block_ratio_window {y k l : Nat} (_hy : 2 ^ k ≤ y) (hw : 2 * y < 3 * 2 ^ k)
    (hw2 : 2 ^ (k + 1) ≤ acceleratedOrbit l y)
    (hw' : 2 * acceleratedOrbit l y < 3 * 2 ^ (k + 1)) :
    4 * y < 3 * acceleratedOrbit l y ∧ acceleratedOrbit l y < 3 * y := by
  have hk : 2 ^ (k + 1) = 2 * 2 ^ k := by rw [Nat.pow_succ]; omega
  rw [hk] at hw2 hw'
  constructor
  · omega
  · omega

/-! ## The floor coupling bound, with an arbitrary floor -/

/-- **`coupling_bound` with a general floor.**  `ScaleLadder.coupling_bound`
requires the floor to be a power of two, which costs a factor of up to two and —
more importantly — is not the shape a cycle supplies.  With an arbitrary floor
`c` the same induction gives

`3 · c · C_j ≤ a_j · (2^j · T^j x)`,

i.e. `C_j / (2^j · T^j x) ≤ a_j / (3c)`.  The proof is `coupling_bound`'s with
`2 ^ k` replaced by `c`; nothing about the floor being a power of two was used. -/
theorem floor_coupling {x c : Nat} : ∀ j : Nat,
    (∀ t : Nat, t ≤ j → c ≤ acceleratedOrbit t x) →
      3 * c * affineC j x ≤ oddCount x j * (2 ^ j * acceleratedOrbit j x) := by
  intro j
  induction j with
  | zero => intro _; simp [affineC]
  | succ j ih =>
    intro hf
    have ihx := ih (fun t ht => hf t (by omega))
    have hy : c ≤ acceleratedOrbit j x := hf j (by omega)
    have hlast := Density.oddCount_succ_last x j
    have hstep : acceleratedOrbit (j + 1) x = acceleratedStep (acceleratedOrbit j x) :=
      acceleratedOrbit_succ_step j x
    have hp : 2 ^ (j + 1) = 2 * 2 ^ j := by rw [Nat.pow_succ]; omega
    rcases Arith.mod_two_eq_zero_or_one (acceleratedOrbit j x) with hev | hod
    · have hC : affineC (j + 1) x = affineC j x := affineC_even hev
      have hval : acceleratedOrbit (j + 1) x = acceleratedOrbit j x / 2 := by
        rw [hstep, acceleratedStep, if_pos hev]
      have hcnt : oddCount x (j + 1) = oddCount x j := by omega
      have hkey : 2 ^ (j + 1) * acceleratedOrbit (j + 1) x = 2 ^ j * acceleratedOrbit j x := by
        have h2 : 2 * (acceleratedOrbit j x / 2) = acceleratedOrbit j x := by omega
        rw [hval, hp, Nat.mul_assoc, Nat.mul_left_comm, h2]
      rw [hC, hcnt, hkey]
      exact ihx
    · have hC : affineC (j + 1) x = 3 * affineC j x + 2 ^ j := affineC_odd hod
      have hval : acceleratedOrbit (j + 1) x = (3 * acceleratedOrbit j x + 1) / 2 := by
        rw [hstep, acceleratedStep, if_neg (by omega)]
      have hcnt : oddCount x (j + 1) = oddCount x j + 1 := by omega
      have hkey : 2 ^ (j + 1) * acceleratedOrbit (j + 1) x
          = 2 ^ j * (3 * acceleratedOrbit j x + 1) := by
        have h2 : 2 * ((3 * acceleratedOrbit j x + 1) / 2) = 3 * acceleratedOrbit j x + 1 := by
          omega
        rw [hval, hp, Nat.mul_assoc, Nat.mul_left_comm, h2]
      rw [hC, hcnt, hkey]
      have hmul : 2 ^ j * c ≤ 2 ^ j * acceleratedOrbit j x := Nat.mul_le_mul_left _ hy
      have hexp : 3 * (3 * c * affineC j x)
          ≤ 3 * (oddCount x j * (2 ^ j * acceleratedOrbit j x)) :=
        Nat.mul_le_mul_left 3 ihx
      have hslack : 3 * (c * 2 ^ j) ≤ 3 * (2 ^ j * acceleratedOrbit j x) := by
        have hcomm : c * 2 ^ j = 2 ^ j * c := Nat.mul_comm _ _
        rw [hcomm]
        exact Nat.mul_le_mul_left 3 hmul
      have hlhs : 3 * c * (3 * affineC j x + 2 ^ j)
          = 3 * (3 * c * affineC j x) + 3 * (c * 2 ^ j) := by
        rw [Nat.mul_add]
        have h1 : 3 * c * (3 * affineC j x) = 3 * (3 * c * affineC j x) := by
          rw [Nat.mul_left_comm, Nat.mul_assoc]
        have h2 : 3 * c * 2 ^ j = 3 * (c * 2 ^ j) := by rw [Nat.mul_assoc]
        rw [h1, h2]
      have hrhs : (oddCount x j + 1) * (2 ^ j * (3 * acceleratedOrbit j x + 1))
          = 3 * (oddCount x j * (2 ^ j * acceleratedOrbit j x))
            + (oddCount x j * 2 ^ j + (3 * (2 ^ j * acceleratedOrbit j x) + 2 ^ j)) := by
        have e1 : 2 ^ j * (3 * acceleratedOrbit j x + 1)
            = 3 * (2 ^ j * acceleratedOrbit j x) + 2 ^ j := by
          rw [Nat.mul_add, Nat.mul_one, Nat.mul_left_comm]
        rw [e1, Nat.add_mul, Nat.one_mul, Nat.mul_add]
        have e2 : oddCount x j * (3 * (2 ^ j * acceleratedOrbit j x))
            = 3 * (oddCount x j * (2 ^ j * acceleratedOrbit j x)) := by
          rw [Nat.mul_left_comm]
        rw [e2]
        omega
      rw [hlhs, hrhs]
      omega

/-! ## The cycle instantiation: the whole yield of the product argument -/

/-- **The coupling bound at a cycle.**  A cycle is bounded below by its own
minimum at *every* index, which is exactly the hypothesis `floor_coupling` needs
and exactly the hypothesis `block_lower` cannot have.  Substituting
`cycle_gap_mul` (`G · n = C_L`) and `T^L n = n`. -/
theorem cycle_coupling {n L : Nat} (hn : 0 < n) (h : AccIsCycleOf n L)
    (hmin : ∀ j : Nat, n ≤ acceleratedOrbit j n) :
    3 * n * ((2 ^ L - 3 ^ oddCount n L) * n) ≤ oddCount n L * (2 ^ L * n) := by
  have hb := floor_coupling (x := n) (c := n) L (fun t _ => hmin t)
  rw [cycle_gap_mul hn h]
  rw [h.2] at hb
  exact hb

/-- **The frontier inequality.**  Cancelling the minimum from `cycle_coupling`:

> `3 · n · (2 ^ L − 3 ^ a) ≤ a · 2 ^ L`.

Equivalently `1 − 3^a/2^L ≤ a / (3n)`: a cycle of odd count `a` and minimum `n`
must have `2^L/3^a` within `a/(3n)` of `1`.  Together with heaviness
(`3 ^ a < 2 ^ L`, `accCycle_bounds`) this is the complete two-sided window that
multiplying local bounds around a cycle produces — and no more. -/
theorem cycle_frontier {n L : Nat} (hn : 0 < n) (h : AccIsCycleOf n L)
    (hmin : ∀ j : Nat, n ≤ acceleratedOrbit j n) :
    3 * n * (2 ^ L - 3 ^ oddCount n L) ≤ oddCount n L * 2 ^ L := by
  have hc := cycle_coupling hn h hmin
  have hl : 3 * n * ((2 ^ L - 3 ^ oddCount n L) * n)
      = (3 * n * (2 ^ L - 3 ^ oddCount n L)) * n :=
    (Nat.mul_assoc (3 * n) (2 ^ L - 3 ^ oddCount n L) n).symm
  have hr : oddCount n L * (2 ^ L * n) = (oddCount n L * 2 ^ L) * n :=
    (Nat.mul_assoc (oddCount n L) (2 ^ L) n).symm
  rw [hl, hr] at hc
  exact Nat.le_of_mul_le_mul_right hc hn

/-- The same statement with the gap written multiplicatively, so that it
typechecks without truncated subtraction: `3n·2^L ≤ 3n·3^a + a·2^L`. -/
theorem cycle_frontier_add {n L : Nat} (hn : 0 < n) (h : AccIsCycleOf n L)
    (hmin : ∀ j : Nat, n ≤ acceleratedOrbit j n) :
    3 * n * 2 ^ L ≤ 3 * n * 3 ^ oddCount n L + oddCount n L * 2 ^ L := by
  have hf := cycle_frontier hn h hmin
  have hlt : 3 ^ oddCount n L ≤ 2 ^ L := Nat.le_of_lt (accCycle_bounds hn h).2.2
  have hg : 3 ^ oddCount n L + (2 ^ L - 3 ^ oddCount n L) = 2 ^ L := Nat.add_sub_cancel' hlt
  calc 3 * n * 2 ^ L
      = 3 * n * (3 ^ oddCount n L + (2 ^ L - 3 ^ oddCount n L)) := by rw [hg]
    _ = 3 * n * 3 ^ oddCount n L + 3 * n * (2 ^ L - 3 ^ oddCount n L) := Nat.mul_add _ _ _
    _ ≤ 3 * n * 3 ^ oddCount n L + oddCount n L * 2 ^ L := Nat.add_le_add_left hf _

/-! ## Axiom audit -/

#print axioms segment_compose
#print axioms rank_compose
#print axioms block_ratio_window
#print axioms floor_coupling
#print axioms cycle_frontier

end SegmentMonoid
end Collatz
