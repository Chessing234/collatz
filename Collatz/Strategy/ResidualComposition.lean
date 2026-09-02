import Collatz.Strategy.PhantomMediant

/-!
# The residual is not a cocycle: `δ` has no composition law

`CLOSURE.md` lists `gcd(C, G)` — equivalently `δ(w) = G / gcd(C, G)` — as the
one quantity in no closed class.  The obvious way to attack it is by induction
over a block decomposition of the word: cut `w = u ++ v`, control `δ(u)` and
`δ(v)`, and compose.  The invitation to do so is strong, because the pair
`(C, G)` *does* compose exactly.  `PhantomMediant.C_append` and
`PhantomMediant.gap_append` say the concatenation acts by the single
two-dimensional cocycle `(3 ^ a(v), 2 ^ |u|)`:

    C(uv) = 3 ^ a(v) · C(u) + 2 ^ |u| · C(v),
    G(uv) = 3 ^ a(v) · G(u) + 2 ^ |u| · G(v)      (subtraction-free form).

This file records that **the cocycle does not descend to the residual**.  `δ` is
not a function of the pieces' `δ` together with their shape `(length, odd
count)` — the data that the cocycle itself is built from.  The witness is a
single pair of words of length four:

| word | `L` | `a` | `C` | `G` | `gcd` | `δ` |
|---|---|---|---|---|---|---|
| `u  = [0,1]`      | 2 | 1 | 2  | 1  | 1  | 1  |
| `v  = [0,0,0,1]`  | 4 | 1 | 8  | 13 | 1  | 13 |
| `v' = [0,0,1,0]`  | 4 | 1 | 4  | 13 | 1  | 13 |
| `uv  = [0,1,0,0,0,1]` | 6 | 2 | 38 | 55 | 1  | **55** |
| `uv' = [0,1,0,0,1,0]` | 6 | 2 | 22 | 55 | 11 | **5**  |

Same left factor, and right factors agreeing in every one of `(δ, L, a, G)`;
the concatenations agree in `(L, a, G)` and differ in `δ` by a factor of eleven.
Neither concatenation is trivial (`δ ≠ 1` on both), so this is not an artefact
of the rigid `δ = 1` family described in `PhantomMediant`.

**What is thereby closed.**  Any argument of the form "`δ` is bounded below on
blocks, and the bound composes" — for *any* composition rule whatsoever, since
the theorem quantifies over all `F` — cannot force `δ(w) ≥ 2`.  The residual is
created and destroyed by concatenation: `delta_created` exhibits
`δ(u) = δ(v) = 1` with `δ(uv) = 7`, and `delta_destroyed` exhibits
`δ(u) = δ(v) = 5` with `δ(uv) = 1`.

**What is not closed, stated precisely.**  `delta_destroyed`'s concatenation is
`(01) ^ 4`, a member of the rigid `δ = 1` family that `PhantomMediant` already
identified as the only `δ = 1` words up to length 22.  So the destruction
direction is exhibited only on that family, and a composition law restricted to
words with no trivial factor is *not* refuted here.  `delta_no_composition_law`
does not have that weakness: both of its concatenations are nontrivial.

Membership audit, against `CLOSURE.md`'s four tests, recorded because it is the
reason this file exists rather than a `Lean` development of the induction:

* it rests on no lower bound for orbit values — it mentions no orbit at all;
* it does not reduce to a bound on the factors of `∏(1 + 1/(3 x_t))`;
* it consumes no prefix of an infinite path — the words are finite and closed;
* it is **not** `d`-free: `δ` is exactly the quantity that separates `3x+1` from
  `3x+d`, which is why it is the residual.

So the candidate was admissible.  It is refuted by its own arithmetic, not by a
class membership — which is the strongest form the refutation can take.
-/

namespace Collatz
namespace ResidualComposition

open DeltaSpectrum

/-! ### The witnesses -/

/-- The common left factor, `δ = 1`. -/
def u : List Bool := [false, true]

/-- Right factor, `δ = 13`. -/
def v : List Bool := [false, false, false, true]

/-- Second right factor: same length, same odd count, same gap, same `δ`. -/
def v' : List Bool := [false, false, true, false]

theorem u_gap : gap u = 1 := rfl
theorem v_gap : gap v = 13 := rfl
theorem v'_gap : gap v' = 13 := rfl

theorem u_delta : delta u = 1 := rfl
theorem v_delta : delta v = 13 := rfl
theorem v'_delta : delta v' = 13 := rfl

/-- The two right factors are indistinguishable by the cocycle's own data. -/
theorem shapes_agree :
    v.length = v'.length ∧ oddCount v = oddCount v' ∧ gap v = gap v' ∧
      delta v = delta v' := ⟨rfl, rfl, rfl, rfl⟩

/-- They are distinguished only by `C`. -/
theorem C_differs : C v = 8 ∧ C v' = 4 := ⟨rfl, rfl⟩

/-- The concatenations agree in shape and gap … -/
theorem concat_shapes_agree :
    (u ++ v).length = (u ++ v').length ∧
      oddCount (u ++ v) = oddCount (u ++ v') ∧ gap (u ++ v) = gap (u ++ v') :=
  ⟨rfl, rfl, rfl⟩

/-- … and differ in the residual by a factor of eleven. -/
theorem concat_delta : delta (u ++ v) = 55 := rfl
theorem concat_delta' : delta (u ++ v') = 5 := rfl

/-- Both concatenations are nontrivial, so the collision is not an instance of
the rigid `δ = 1` family. -/
theorem concats_nontrivial : delta (u ++ v) ≠ 1 ∧ delta (u ++ v') ≠ 1 := by
  constructor <;> decide

/-! ### The refutation -/

/-- **`δ` has no composition law.**  There is no function of the two factors'
residuals and shapes that computes the residual of the concatenation — not
merely no *multiplicative* one.  The quantification is over every
`F : Nat → Nat → Nat → Nat → Nat → Nat → Nat`, so this closes the block
induction for all composition rules at once. -/
theorem delta_no_composition_law :
    ¬ ∃ F : Nat → Nat → Nat → Nat → Nat → Nat → Nat,
        ∀ p q : List Bool, 0 < gap p → 0 < gap q → 0 < gap (p ++ q) →
          delta (p ++ q) =
            F (delta p) (delta q) p.length (oddCount p) q.length (oddCount q) := by
  rintro ⟨F, hF⟩
  have h1 := hF u v (by decide) (by decide) (by decide)
  have h2 := hF u v' (by decide) (by decide) (by decide)
  simp only [show delta (u ++ v) = 55 from rfl, show delta (u ++ v') = 5 from rfl,
    show delta u = 1 from rfl, show delta v = 13 from rfl, show delta v' = 13 from rfl,
    show u.length = 2 from rfl, show oddCount u = 1 from rfl,
    show v.length = 4 from rfl, show v'.length = 4 from rfl,
    show oddCount v = 1 from rfl, show oddCount v' = 1 from rfl] at h1 h2
  exact absurd (h1.trans h2.symm) (by decide)

/-! ### The residual is created and destroyed by concatenation -/

/-- Two factors with trivial residual whose concatenation has `δ = 7`: the
residual is **created** where neither factor carries it. -/
theorem delta_created :
    delta [false, true] = 1 ∧ delta [true, false] = 1 ∧
      delta ([false, true] ++ [true, false]) = 7 := ⟨rfl, rfl, rfl⟩

/-- Two factors with `δ = 5` whose concatenation has `δ = 1`: the residual is
**destroyed**.  The concatenation is `(01) ^ 4`, so this witness lies in the
rigid family; see the module docstring for the exact scope of the claim. -/
theorem delta_destroyed :
    delta [false, true, false] = 5 ∧ delta [true, false, true, false, true] = 5 ∧
      delta ([false, true, false] ++ [true, false, true, false, true]) = 1 :=
  ⟨rfl, rfl, rfl⟩

/-- The destroyed witness is the rigid word, spelled out. -/
theorem destroyed_is_rigid :
    ([false, true, false] ++ [true, false, true, false, true] : List Bool) =
      [false, true, false, true, false, true, false, true] := rfl

/-! ### The contrast the file exists to record

`PhantomMediant.C_append` and `PhantomMediant.gap_append` compose exactly on the
same words: the cocycle is intact where the residual is not.  Both halves are
checked here on the witness, so the failure above cannot be blamed on the
append laws. -/

theorem cocycle_intact :
    C (u ++ v) = 3 ^ oddCount v * C u + 2 ^ u.length * C v ∧
      C (u ++ v') = 3 ^ oddCount v' * C u + 2 ^ u.length * C v' :=
  ⟨PhantomMediant.C_append u v, PhantomMediant.C_append u v'⟩

/-- The gap composes by the same cocycle on the witness, in the
subtraction-free form of `PhantomMediant.gap_append`. -/
theorem gap_cocycle_intact :
    3 ^ oddCount v * gap u + 2 ^ u.length * gap v + 3 ^ (oddCount u + oddCount v)
      = 2 ^ (u.length + v.length) :=
  PhantomMediant.gap_append (by decide) (by decide)

end ResidualComposition
end Collatz
