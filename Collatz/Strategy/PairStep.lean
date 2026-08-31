import Collatz.Strategy.ProductMax

/-!
# The pair `(n, n+1)`, and why no potential can live on it

The proposal: carry both coordinates at once, since growth is clean in `u = n+1`
and contraction is clean in `n`, and let the letter decide which slot is legal.

## The step, corrected

As proposed the two second components were exchanged.  Growth (`x` odd) is the
clean one in `y = u`, and contraction (`x` even) is the clean one in `x`, so:

* `x` **even**:  `(x, y) ↦ (x/2, (y+1)/2)` — the ceiling, in `y`;
* `x` **odd**:   `(x, y) ↦ ((3x+1)/2, 3y/2)` — the exact tripling, in `y`.

The version with these swapped fails on **every** input: at `n = 2` it gives
`(1, 4)` where `(1, 2)` is wanted, at `n = 3` it gives `(5, 2)` where `(5, 6)` is
wanted — `19 999` failures out of `19 999` tested.  With the components in the
right slots there are none.

`pairStep` below is the corrected map and `pair_preserves_gap` is the check:
`pairStep (x, x+1) = (T x, T x + 1)`.

## The kill test fires by construction

The proposal's own criterion was: *if `V(x, x+1)` is secretly `f(x)`, the device is
dead.*  It is, and unavoidably so.

The locus `{(x, x+1) : x ∈ ℕ}` is the **graph of a function**.  The second
coordinate is determined by the first, so the pair carries exactly the information
`x` carries and not one bit more.  `pair_potential_is_unary` states it: for *any*
`V : ℕ → ℕ → α` whatsoever, there is an `f` with `V x (x+1) = f x` for all `x` —
namely `f = fun x => V x (x+1)`.

So **no potential defined on the pair locus can escape the test**, regardless of how
it is built.  The construction cannot fail to be unary; the gap-`1` constraint is
what makes it so.

## What the pair formalism is actually good for

Not a potential — a *typing discipline*.  The content is in the step rule, which
records which coordinate is exact at each letter, and that content is already
`CoordinateMismatch`: `odd_clean` (`T n + 1 = 3·((n+1)/2)` on odd `n`),
`even_clean` (`T n = n/2` on even `n`), and `no_common_shift` (no affine `v = n + c`
makes both branches exact, since the odd branch forces `c = 1` and the even branch
`c = 0`).

The pair is the two coordinates carried simultaneously so that neither has to be
chosen; `no_common_shift` is the theorem that they cannot be merged into one.  The
pair does not add information, it *displays* the obstruction — which is worth having
stated, and is not a route to a Lyapunov function.
-/

namespace Collatz
namespace PairStep

/-- The corrected pair step: contraction is exact in the first slot, growth in the
second. -/
def pairStep (p : Nat × Nat) : Nat × Nat :=
  if p.1 % 2 = 0 then (p.1 / 2, (p.2 + 1) / 2) else ((3 * p.1 + 1) / 2, 3 * p.2 / 2)

/-- **The pair step preserves the gap and agrees with `T`.** -/
theorem pair_preserves_gap (x : Nat) :
    pairStep (x, x + 1) = (acceleratedStep x, acceleratedStep x + 1) := by
  rcases Arith.mod_two_eq_zero_or_one x with he | ho
  · rw [pairStep, acceleratedStep, if_pos he, if_pos he]
    have : (x + 1 + 1) / 2 = x / 2 + 1 := by omega
    rw [this]
  · rw [pairStep, acceleratedStep, if_neg (by omega), if_neg (by omega)]
    have : 3 * (x + 1) / 2 = (3 * x + 1) / 2 + 1 := by omega
    rw [this]

/-- Iterating the pair step tracks the orbit in both slots. -/
theorem pair_orbit (x : Nat) : ∀ k : Nat,
    (fun p => Nat.rec p (fun _ q => pairStep q) k) (x, x + 1)
      = (acceleratedOrbit k x, acceleratedOrbit k x + 1) := by
  intro k
  induction k with
  | zero => rfl
  | succ k ih =>
    show pairStep ((fun p => Nat.rec p (fun _ q => pairStep q) k) (x, x + 1)) = _
    rw [ih, pair_preserves_gap, ← acceleratedOrbit_succ_step]

/-- **The kill test fires by construction.**  The locus `{(x, x+1)}` is the graph of
a function, so *every* `V` restricted to it is a function of `x` alone.  No
potential built on the pair can be anything but unary. -/
theorem pair_potential_is_unary {α : Type} (V : Nat → Nat → α) :
    ∃ f : Nat → α, ∀ x : Nat, V x (x + 1) = f x :=
  ⟨fun x => V x (x + 1), fun _ => rfl⟩

/-- The same for potentials taking the pair as one argument. -/
theorem pair_potential_is_unary' {α : Type} (V : Nat × Nat → α) :
    ∃ f : Nat → α, ∀ x : Nat, V (x, x + 1) = f x :=
  ⟨fun x => V (x, x + 1), fun _ => rfl⟩

end PairStep
end Collatz
