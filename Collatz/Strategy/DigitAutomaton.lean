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

**This inference is weaker than an earlier draft claimed, and the gap matters.**  The
admission rule (`CLOSURE.md` Class 4, now diagnostic 3) kills invariance under
`C ↦ d·C`, *not* being a function of the word.  `C_L(w, d)` is a function of the word
for each fixed `d` and is plainly not `d`-blind.  The survivor was flagged precisely
because the carry rules of the `3x+d` rewrite system put `d` in the **weights**, and
Step 1 constrains only the **state space**.  So Step 1 shows the state is small; it
does **not** show the survivor is `d`-blind, and on its own it narrows nothing.

With that correction, the honest reading is:  Its only
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
a unipotent block `[[1,1],[0,1]]`.

**But this is a statement about the mean only, and an earlier draft of this header
stated it pointwise, which is false.**  `σ(31) = 66` at 5 bits while `σ(127) = 30` at
7 bits: `σ` is nowhere near monotone in digit length.  Only the *average* over a
bit-block advances near-linearly (by 4.4–4.9 per bit).  So "linear in the digit
length" is a claim about `E[σ | n bits]`, and the argument built on it is heuristic,
not a reason.  Worse, the honest obstruction to dimension `1` is not a growth type at
all: `V x = ρ^(digits x)` fails because digit length is not monotone under `T`
(`3 → 5` takes 2 bits to 3), and that kills the proposed dimension-`2` affine
`α·digits x + β` for exactly the same reason.  **The claimed "sharper reason than
dimension 1 fails four evaluations" is withdrawn; `no_linear_interpretation` remains
the actual argument.**

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

**Correction: these are two independent rays, not four.**  `3·2^m − 1 = T(2^(m+1) − 1)`
is one Collatz step, so `σ(3·2^m − 1) = σ(2^(m+1) − 1) − 1` identically (checked
`m = 1..39`); and `σ(2^m + 3) = σ(2^(m−1) + 1) + 1` identically (`m = 4..39`).  Hankel
rank is invariant under index shift and moves by at most 2 under an additive constant,
so rows 2/5 and 3/4 agree by force, not by corroboration.  The evidence base is
`2^m − 1` and `2^m + 1`.  (Saturation does persist further than stated — rank
`40, 50, 60` at `80, 100, 120` terms — so the phenomenon is real; only its
multiplicity was overcounted.)

Every entry but the first row is **saturating** — the rank equals the largest value
the truncation can express, at every size, on four independent rays.  A sequence
with a linear recurrence of order `k` has Hankel rank `k` at every truncation past
`k`.  These have none of any order up to `30`.

> **COMPUTATIONAL: `σ` restricted to a single digit ray has unbounded Hankel rank,
> so no finite-dimensional weighted automaton over `ℚ` computes it.**

Together with an exhaustive search — `419904 = 81² · 8²` interpretations of dimension
`2`: two `2×2` matrices with entries in `{0,1,2}` (`3⁴ = 81` each) and two vectors
drawn from the `8` nonzero elements of `{0,1,2}²`, LSB-first, required to satisfy
`V (T x) < V x` for `3 ≤ x ≤ 119` — which returns **zero** ranking functions, the
search finds nothing at the dimension where the growth-type heuristic predicted it
should work.  That is evidence, not closure; and since the growth-type argument is
withdrawn above, the prediction it counts against is itself weakened.

*Reproducibility caveat:* both this search and the Hankel computation were run in the
session transcript and have no script under `scripts/`, so neither can be re-run from
the repository as it stands.  Treat both as reported measurements pending a committed
script.

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
