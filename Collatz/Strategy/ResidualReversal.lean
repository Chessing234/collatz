import Collatz.Strategy.ResidualComposition

/-!
# Reversal is not a symmetry of the residual

`G(w) = 2 ^ |w| − 3 ^ a(w)` depends only on the length and the odd count, so it
is **manifestly reversal-invariant**.  That makes the following tempting: if
`gcd(C, G)` were reversal-invariant too, then `δ` would carry a nontrivial
involution on words, the `δ = 1` words would come in pairs, and a fixed-point or
parity argument would become available on the residual.

It is not.  `reversal_breaks_gcd` below: at length 12 there is a word `w` that is
heavy at every proper prefix, with `gcd(C(w), G) = 1` and `δ(w) = 1909`, whose
reversal has `gcd = 23` and `δ = 83` — against the *same* `G = 1909`.  So the
residual is not a function of the reversal class, and there is no involution to
exploit.

Measured scope of the failure, so the claim is neither over- nor under-stated:

* over every word of length `≤ 14` with `G > 0`: `gcd` is preserved in 5875 cases
  and **broken in 548**;
* restricting to words heavy at every proper prefix does not rescue it: 7 of the
  142 such words are broken.  The witness below is the smallest heavy one.

## The one place reversal *does* act, and why it is empty

Over the same range, every `δ = 1` word reverses to a `δ = 1` word — 24 of 24.
That looks like the sought structure and is not, because the `δ = 1` words are
already completely characterised: `PhantomMediant` records that up to length 22
they are exactly the all-even word and the two rotations of `(10) ^ (L/2)`.  The
census here agrees exactly — 14 all-even, 14 of the form `(10)^k` or `(01)^k`,
nothing else — and that set is reversal-closed for the trivial reason that
reversing `(10)^k` gives `(01)^k`.

So the reversal-closure of `δ = 1` is the rigidity result restated.  By
`CLOSURE.md`'s Class 3 test it carries no information: a symmetry of a set whose
elements are already listed tells you nothing you did not have.

## Membership audit

The candidate passed all four tests before being formalized — it rests on no
orbit lower bound (it mentions no orbit), does not reduce to the factors of
`∏(1 + 1/(3x_t))`, consumes no prefix, and is not `d`-free, since `δ` is the
`d`-separating residual.  It is refuted by computation, not by class membership.
-/

namespace Collatz
namespace ResidualReversal

open DeltaSpectrum

/-! ### The witness -/

/-- Heavy at every proper prefix, `δ = 1909`. -/
def wf : List Bool :=
  [true, true, true, true, false, false, true, true, false, true, false, false]

/-- Its reversal: same length, same odd count, same gap — and a different
residual. -/
def wr : List Bool :=
  [false, false, true, false, true, true, false, false, true, true, true, true]

theorem wr_eq_reverse : wf.reverse = wr := rfl

theorem wf_heavy : heavy wf = true := rfl

theorem shapes_agree :
    wf.length = wr.length ∧ oddCount wf = oddCount wr ∧ gap wf = gap wr :=
  ⟨rfl, rfl, rfl⟩

theorem gap_value : gap wf = 1909 := rfl

theorem wf_data : C wf = 3227 ∧ Nat.gcd (C wf) (gap wf) = 1 ∧ delta wf = 1909 :=
  ⟨rfl, rfl, rfl⟩

theorem wr_data : C wr = 26036 ∧ Nat.gcd (C wr) (gap wr) = 23 ∧ delta wr = 83 :=
  ⟨rfl, rfl, rfl⟩

/-! ### The refutation -/

/-- **Reversal does not preserve the residual.**  The gap is reversal-invariant,
so both sides are measured against the same `G = 1909`; the gcd is not. -/
theorem reversal_breaks_gcd :
    gap wf = gap wf.reverse ∧
      Nat.gcd (C wf) (gap wf) ≠ Nat.gcd (C wf.reverse) (gap wf.reverse) := by
  constructor
  · rfl
  · decide

/-- The same statement read on `δ`, which is the form the candidate needed. -/
theorem reversal_breaks_delta : delta wf ≠ delta wf.reverse := by decide

/-- The witness is heavy at every proper prefix, so restricting the candidate to
heavy words does not rescue it. -/
theorem reversal_breaks_gcd_heavy :
    heavy wf = true ∧ delta wf ≠ delta wf.reverse := ⟨rfl, by decide⟩

/-- Reversal is an involution on words, so the failure above is a failure of a
genuine involution to descend to the residual — not an artefact of the map. -/
theorem reverse_involutive (w : List Bool) : w.reverse.reverse = w :=
  List.reverse_reverse w

end ResidualReversal
end Collatz
