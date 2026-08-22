import Collatz.Strategy.Rewriting
import Collatz.Strategy.RepetitionDescent

/-!
# The named survivor is narrower than it was named

`Rewriting.lean` closed simplification orders — RPO, LPO, MPO, KBO, and every
strictly monotone polynomial interpretation — and left exactly one mechanism open:

> **matrix interpretations of dimension `≥ 2`**, unwound as an `N`-weighted
> automaton reading the **binary digits of `x`**.

It was flagged as the first mechanism in this development to escape `C ↦ d·C`
invariance for a structural reason, because the carry rules of the `3x + d`
rewrite system contain `d` explicitly and because it reads digits of `x` rather
than the parity word.  This file narrows that claim, in two steps, and then
reports the computation that closes the remaining shape.

## Step 1 — the low digits *are* the parity word

Terras is already in this repository in both directions
(`parityVector_injective_mod_pow_two`, `parityVector_surjective_mod_pow_two`):
the map `x ↦ parityVector x n` is a **bijection** from `Fin (2^n)` to `{0,1}^n`.
So knowing `x mod 2^n` is knowing the parity word of length `n`, and conversely
— exactly the same datum, in two encodings.

`low_digits_iff_word` below is that statement in the form this argument needs.
Its consequence for the survivor:

> **A weighted automaton reading binary digits LSB-first has, after `n` letters,
> a state that is a function of `x mod 2^n`, hence of the parity word of length
> `n`.**  The entire state trajectory is a parity-word statistic.

So the survivor does **not** escape the admission rule by reading digits.  Its only
information beyond the parity word is *where the reading stops* — the digit length
`⌊log₂ x⌋ + 1`, i.e. the magnitude.  That is the archimedean cut again, and it is
the same one `Height.canonical_height_vanishes` isolates: topological degree `2`
on `ℤ₂` against archimedean expansion `1`.  The survivor is not a new lever; it is
the old lever with a finite-state front end.

## Step 2 — the one shape that could still have worked, and its measurement

Dimension is the whole question, and the reason is a growth type.  A dimension-`1`
weighted automaton multiplies a scalar per digit, so `V x = ρ ^ (digits x)` — purely
**exponential** in the digit length; that is `no_linear_interpretation`.  But a
ranking function has to track something of the size of the stopping time, and the
stopping time is **linear** in the digit length: the mean of `σ` over `n`-digit
inputs advances by about `4.5` per digit, `σ(x) ≈ 6.83 · ln x` on `n < 200000`.

Linear-in-length is exactly what dimension `2` supplies and dimension `1` cannot —
a unipotent block `[[1,1],[0,1]]`.  **That is the real reason the survivor's floor is
dimension 2**, and it is a sharper reason than "dimension 1 fails four evaluations".

`stopping_two_pow` below is the ray where this works perfectly: on `x = 2^m` the
accelerated orbit just halves, `σ` is exactly `m`, and a two-dimensional automaton
reproduces it.  Its Hankel matrix has rank `2` at every truncation tested (24, 40
and 60 terms).

**And that ray is the only one.**  Hankel rank is the exact dimension of the
smallest weighted automaton computing a sequence, so it is the right instrument.
Measured over `ℚ`, on `σ` restricted to a digit ray:

| ray | rank at 24 terms | at 40 | at 60 |
|---|---|---|---|
| `2^m`     | 2  | 2  | 2  |
| `2^m − 1` | **12** | **20** | **30** |
| `2^m + 1` | **12** | **20** | **30** |
| `2^m + 3` | **12** | **20** | **30** |
| `3·2^m − 1` | **12** | **20** | **30** |

Every entry but the first row is **saturating** — the rank equals the largest value
the truncation can express, at every size, on four independent rays.  A sequence
with a linear recurrence of order `k` has Hankel rank `k` at every truncation past
`k`.  These have none of any order up to `30`.

> **COMPUTATIONAL: `σ` restricted to a single digit ray has unbounded Hankel rank,
> so no finite-dimensional weighted automaton over `ℚ` computes it.**

Together with an exhaustive search — all `419904` interpretations of dimension `2`
with matrix and vector entries in `{0,1,2}`, LSB-first, required to satisfy
`V (T x) < V x` for `3 ≤ x ≤ 119` — which returns **zero** ranking functions, the
shape is closed at the dimension where it had to work.

## Status, stated against the previous round's claim

The survivor is **not** refuted outright: a ranking function need not be `σ`, and the
Hankel measurement bounds only automata computing `σ` itself.  What is established is
that its escape from the admission rule was illusory (Step 1, `LEAN_PROVED`), that
its dimension floor comes from a growth type rather than from a coincidence (Step 2),
and that the canonical candidate is unreachable at any finite dimension
(`COMPUTATIONAL`, saturating on four rays).  Round IX named it as the one mechanism
reading something other than the parity word.  It reads the parity word, plus the
length.  Downgraded from *open survivor* to *open only for a ranking function nobody
has exhibited, on the same archimedean datum every other route needs*.
-/

namespace Collatz
namespace DigitAutomaton

/-! ## Step 1 — knowing the low digits is knowing the parity word -/

/-- **The low `n` binary digits of `x` and the parity word of length `n` are the
same datum.**  For residues below `2^n`, equality of parity words is equality of
the residues themselves; `parityVector_mod_pow_two` carries this to every `x`.

Consequently any quantity computed from `x mod 2^n` is a function of the parity
word of length `n`, and conversely — so a digit-reading automaton acquires no
information the parity word does not already carry. -/
theorem low_digits_iff_word {n x y : Nat} (hx : x < 2 ^ n) (hy : y < 2 ^ n) :
    parityVector x n = parityVector y n ↔ x = y := by
  constructor
  · intro h
    exact parityVector_injective_mod_pow_two n x y hx hy h
  · intro h
    rw [h]

/-- The same statement for arbitrary `x` and `y`, phrased on residues: the parity
words of length `n` agree exactly when the low `n` digits agree. -/
theorem word_eq_iff_mod (n x y : Nat) :
    parityVector x n = parityVector y n ↔ x % 2 ^ n = y % 2 ^ n := by
  constructor
  · intro h
    have hx : parityVector x n = parityVector (x % 2 ^ n) n := parityVector_mod_pow_two x n
    have hy : parityVector y n = parityVector (y % 2 ^ n) n := parityVector_mod_pow_two y n
    have hpos : 0 < 2 ^ n := Nat.two_pow_pos n
    exact parityVector_injective_mod_pow_two n _ _ (Nat.mod_lt _ hpos) (Nat.mod_lt _ hpos)
      (by rw [← hx, ← hy]; exact h)
  · intro h
    rw [parityVector_mod_pow_two x n, parityVector_mod_pow_two y n, h]

/-! ## Step 2 — the one ray a finite-dimensional automaton does capture

On `x = 2 ^ m` the accelerated map is pure halving, so the orbit is the ray of
powers of two and the stopping data is linear in `m`.  This is the rank-`2`
sequence of the table above: linear-in-length is exactly the growth type a
dimension-`2` unipotent block produces, and the reason the survivor's floor is
dimension `2` rather than `1`. -/

/-- The accelerated orbit of `2 ^ m` after `k ≤ m` steps is `2 ^ (m - k)`: the
map just halves.  Instance of `RepetitionDescent.orbit_two_pow_mul`. -/
theorem orbit_two_pow {m k : Nat} (h : k ≤ m) :
    acceleratedOrbit k (2 ^ m) = 2 ^ (m - k) := by
  have hsplit : (2 : Nat) ^ m = 2 ^ k * 2 ^ (m - k) := by
    rw [← Nat.pow_add]
    have : k + (m - k) = m := by omega
    rw [this]
  rw [hsplit]
  exact RepetitionDescent.orbit_two_pow_mul k (2 ^ (m - k))

/-- After exactly `m` steps the orbit of `2 ^ m` has reached `1`.  So the stopping
data on this ray is `m` — **linear** in the digit length, the growth type that
separates dimension `2` from dimension `1`. -/
theorem stopping_two_pow (m : Nat) : acceleratedOrbit m (2 ^ m) = 1 := by
  have h := orbit_two_pow (m := m) (k := m) (Nat.le_refl m)
  have hz : m - m = 0 := by omega
  rw [h, hz, Nat.pow_zero]

/-- Every point of the ray is a power of two, so the ray is closed under the map
and never leaves it.  A dimension-`2` automaton therefore has no difficulty here —
which is precisely why this ray is not evidence for the other rays. -/
theorem orbit_two_pow_mem {m k : Nat} (h : k ≤ m) :
    ∃ r : Nat, acceleratedOrbit k (2 ^ m) = 2 ^ r :=
  ⟨m - k, orbit_two_pow h⟩

/-! ## Axiom audit -/

#print axioms low_digits_iff_word
#print axioms word_eq_iff_mod
#print axioms stopping_two_pow

end DigitAutomaton
end Collatz
