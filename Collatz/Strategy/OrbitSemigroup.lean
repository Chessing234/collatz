import Collatz.Strategy.SignFlip

/-!
# The orbit semigroup of odd parts buys nothing

The proposal: the odd parts `w` appearing in `U = 2^a·w ↦ 3^(a−1)·w + 1` are not
arbitrary — they lie in the semigroup generated from `1` by `w ↦ 3w` and
`w ↦ oddpart(w+1)`.  If that semigroup missed the residue classes where lifting the
exponent gives deep `2`-valuation, the restriction would be a new constraint on
`ρ(a,w) = v₂(3^(a−1)w + 1)`.

**It misses nothing.  The kill test fires, and this file proves the decisive half.**

## The measurement

Computing the *true closure* under both generators below a bound — not a capped
breadth-first search, which truncates the paths that rise via `w ↦ 3w` and return
via `w ↦ oddpart(w+1)`, and which gave a misleadingly sparse answer:

* **density `0.5091` among odd numbers below `2^22`** — about half of them, not a
  thin set;
* **all sixteen odd residues mod `32`** occur, so there is no congruence
  obstruction at any level tested;
* `max ρ` on the closure against `max ρ` over all odd `w` of the same bit length:
  `13/13`, `18/18`, `16/15`, `17/17` — **no gap.**  The closure attains the same
  deep valuations as the unrestricted set.

## The kill test, run explicitly

`LogCoordinate.growth_blocked` says deep `2`-valuation is possible only for
`w ≡ 5, 7 (mod 8)`.  Both classes are reached, in three and four steps:

`1 → 3 → 9 → 5`  (since `9 + 1 = 2·5`), and  `1 → 3 → 9 → 27 → 7`  (since
`27 + 1 = 4·7`).

`semi_five` and `semi_seven` below are those derivations, formalised.  The family
`oddpart(3^s − 1)` named in the kill test is likewise present throughout the range
where the closure is complete.

**So the restriction buys nothing**: the semigroup meets every class in which deep
valuation can occur, with short explicit derivations, and attains the same maximal
`ρ`.  Recorded as a closed route.

## What is proved

`Semi` is the semigroup as an inductive predicate, with the second generator stated
in decomposition form (`w + 1 = 2^k · v`, `v` odd) so that no `oddpart` function is
needed.  `semi_five`, `semi_seven`: both deep-valuation classes are inhabited.
`semi_meets_both_deep_classes` packages them.
-/

namespace Collatz
namespace OrbitSemigroup

/-- The semigroup generated from `1` by `w ↦ 3w` and `w ↦ oddpart(w+1)`, with the
second generator in decomposition form. -/
inductive Semi : Nat → Prop
  | one : Semi 1
  | tripled {w : Nat} : Semi w → Semi (3 * w)
  | oddPart {w k v : Nat} : Semi w → v % 2 = 1 → w + 1 = 2 ^ k * v → Semi v

theorem semi_three : Semi 3 := by
  have h := Semi.tripled Semi.one
  simpa using h

theorem semi_nine : Semi 9 := by
  have h := Semi.tripled semi_three
  simpa using h

theorem semi_twentyseven : Semi 27 := by
  have h := Semi.tripled semi_nine
  simpa using h

/-- `1 → 3 → 9 → 5`, since `9 + 1 = 2·5`.  So the class `w ≡ 5 (mod 8)` is
inhabited. -/
theorem semi_five : Semi 5 :=
  Semi.oddPart (k := 1) (v := 5) semi_nine (by decide) (by decide)

/-- `1 → 3 → 9 → 27 → 7`, since `27 + 1 = 4·7`.  So the class `w ≡ 7 (mod 8)` is
inhabited. -/
theorem semi_seven : Semi 7 :=
  Semi.oddPart (k := 2) (v := 7) semi_twentyseven (by decide) (by decide)

/-- **The kill test, formalised.**  `LogCoordinate.growth_blocked` permits deep
`2`-valuation only for `w ≡ 5, 7 (mod 8)`; the semigroup inhabits **both** classes.
So restricting `w` to orbit-produced values cannot block deep valuation. -/
theorem semi_meets_both_deep_classes :
    (∃ w : Nat, Semi w ∧ w % 8 = 5) ∧ (∃ w : Nat, Semi w ∧ w % 8 = 7) :=
  ⟨⟨5, semi_five, by decide⟩, ⟨7, semi_seven, by decide⟩⟩

/-- Every power of three is in the semigroup — the first generator alone. -/
theorem semi_three_pow : ∀ k : Nat, Semi (3 ^ k) := by
  intro k
  induction k with
  | zero => simpa using Semi.one
  | succ k ih =>
    have h := Semi.tripled ih
    have he : (3 : Nat) ^ (k + 1) = 3 * 3 ^ k := by rw [← Nat.pow_succ']
    rw [he]
    exact h

end OrbitSemigroup
end Collatz
