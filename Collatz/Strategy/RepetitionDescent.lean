import Collatz.Strategy.NewModels

/-!
# Descent by repetition — what a repeated configuration actually buys

Round III closed descent by *integer magnitude*, every single-step word edit, and
every ranking function it could pose.  The remaining opening named for this file
was a descent driven by a **repeated arithmetic configuration** rather than by
size: an infinite non-descending trajectory must revisit some finite state, the
segment between two visits is an affine map fixing that state, and one hoped the
contracting and expanding cases could be excluded separately.

This file settles that, and the verdict is mixed in a precise way.

## The admission test, answered as theorems

**A repeated *state* is not a repeated *integer*.**  `state_repeat_not_value`
exhibits, for every modulus `M > 0` and every window `k > 0`, a point
`2 ^ k * M` whose orbit returns to the same class mod `M` after `k` steps at the
value `M ≠ 2 ^ k * M`.  So a loop in the state graph carries no fixed point.

**And the loop's dichotomy is the affine inequality already in the framework.**
`loop_dichotomy` : for every `x` and every window `k`,

  `T^k(x) < x  ↔  3 ^ (oddCount x k) * x + affineC k x < 2 ^ k * x`.

That is an inequality in `(2 ^ k, 3 ^ a, x, C)` and nothing else, so the
repetition sees no information the density / affine-magnitude framework cannot
see.  **The two cases cannot be excluded separately either**, because the
expanding case is realised at every odd point of every orbit
(`odd_step_expands`).  Architecture C, as posed, is dead at this line.

## What survives: the substitution mechanism, and exactly why it stops

One descent that is *not* by integer magnitude does exist, and it is formalised
here in full.  Work with the word-level accumulator

  `wC [] = 0`,  `wC (b :: t) = (if b = 1 then 3 ^ ones t else 0) + 2 * wC t`

which is proved equal to `affineC` along the parity vector of any integer
(`wC_parityVector`).  It satisfies a concatenation law (`wC_append`), and hence:

> **`subst_dvd`** — let `w = x ++ p ++ y` be a cycle word with gap `G ∣ wC w`.
> Let `q` be *any* word with `q.length = p.length`, `ones q = ones p` and
> `wC q + s = wC p`.  If `G ∣ 2 ^ x.length * 3 ^ ones y * s` then
> `G ∣ wC (x ++ q ++ y)`, and if `s > 0` the new accumulator is **strictly
> smaller**.

The measure that descends is `wC`, i.e. the accumulator `C` — not the magnitude
of any orbit point, not `v₂`, not `v₃`, not the length, not the odd-step count,
all of which the substitution leaves fixed.  It is a genuinely non-archimedean
descent, and `subst_yields_cycle` turns each step of it into a genuine cycle
point of the same period.

**The mechanism is live under the corrected soundness filter.**  It compares
`C(w)` to `G(w)` *multiplicatively* — the hypothesis is `G ∣ C`, i.e. `δ(w) = 1`
— and `δ(w) = G / gcd(C, G)` is not invariant under `C ↦ d·C`.  (For the two
`3x + 5` cycles of length 27, `δ` computed from the word alone is `5`, not `1`.)
So this is *not* one of the `d`-free word properties Round III killed.  It fails
for a different and more instructive reason.

**It does not terminate in a contradiction, and the reason is measured, not
guessed.**  The descent stops at the minimum of the set
`S(L, a, G) = {w : |w| = L, ones w = a, G ∣ wC w}`, and by
`NewModels.word_is_cycle_word` that set is exactly a union of rotation classes of
genuine cycles.  Enumerated exactly:

* `(L, a) = (11, 7)`, `|G| = 139` — `S` has **exactly 11 words**, the 11 rotations
  of the single `3x − 1` cycle through 17.  Minimum `wC = 2363 = 139 · 17`.
* `(L, a) = (27, 17)`, `G / 5 = 1 015 513` — `S` has **exactly 54 words**, the two
  rotation classes of the two genuine `3x + 5` cycles, minima `wC = 189 900 931`
  (`n = 187`) and `wC = 352 383 011` (`n = 347`).  Poisson expectation for a
  random set of that size is 8.31; the excess is entirely rotation-closure.

So the descent bottoms out precisely *at* the counterexample it was meant to
destroy.  **The exact failure line is termination, not soundness**: to get a
contradiction one needs `S(L, a, G) = ∅`, and that is the original problem
verbatim.  Run at modulus `M = |G|` in the `d = −1` world at `(11, 7)` the
mechanism descends inside the 17-cycle's rotation class and halts at `wC = 2363`;
`neg_gap_witness` records that this really is a cycle,
`3 ^ 7 * 17 = 2 ^ 11 * 17 + 2363`, with the accumulator computed by `wC` from the
very word the argument manipulates.  **Any strengthening claiming the descent
cannot halt, or that a second smaller element of `S` must exist, is refuted
there** — `S(11, 7, 139)` has exactly eleven elements and they are one rotation
class.  At `(27, 17)` the analogous set has two rotation classes, so a
minimal-`C` argument does not even get uniqueness: two genuine cycles sit at one
`(L, a)` with one gap (`two_cycles_one_gap`).

## Bridge left open

`subst_yields_cycle` takes the realiser of the substituted word as a hypothesis
(`parityVector r' L = x ++ q ++ y`).  The missing theorem is Terras
surjectivity — every `0/1` word of length `L` is the parity vector of some
integer.  It is true (injectivity is `NewModels.word_of_count_and_accum`, and the
2-adic construction is standard) but is not proved in this development, and it is
not assumed anywhere: it appears only as an explicit hypothesis.
-/

namespace Collatz
namespace RepetitionDescent

open Reach Congruence AffineExact CycleCriterion

/-! ## Part 1 — the admission test, as theorems

A repeated state is not a repeated value, and the loop's contract/expand
dichotomy is exactly the affine-magnitude inequality. -/

/-- Halving `k` times undoes multiplication by `2 ^ k`. -/
theorem orbit_two_pow_mul : ∀ (k m : Nat), acceleratedOrbit k (2 ^ k * m) = m := by
  intro k
  induction k with
  | zero => intro m; simp
  | succ k ih =>
    intro m
    have hval : (2:Nat) ^ (k + 1) * m = 2 * (2 ^ k * m) := by
      rw [Arith.two_pow_succ, Nat.mul_assoc]
    have hstep : acceleratedStep (2 ^ (k + 1) * m) = 2 ^ k * m := by
      rw [acceleratedStep, if_pos (by omega)]
      omega
    rw [acceleratedOrbit_succ, hstep, ih]

/-- **A repeated state is not a repeated integer.**  For every modulus `M > 0`
and every window `k > 0` the orbit of `2 ^ k * M` returns after `k` steps to the
same class mod `M` — at a strictly different value.  So a loop in any
residue-state graph produces no fixed point, and nothing may be read off it that
a fixed point would give. -/
theorem state_repeat_not_value {M k : Nat} (hM : 0 < M) (hk : 0 < k) :
    acceleratedOrbit k (2 ^ k * M) % M = (2 ^ k * M) % M ∧
      acceleratedOrbit k (2 ^ k * M) ≠ 2 ^ k * M := by
  have hor := orbit_two_pow_mul k M
  have h2 : 2 ≤ 2 ^ k := by
    have : (2:Nat) ^ 1 ≤ 2 ^ k := Nat.pow_le_pow_right (by omega) hk
    simpa using this
  have hmul : 2 * M ≤ 2 ^ k * M := Nat.mul_le_mul_right M h2
  refine ⟨?_, ?_⟩
  · rw [hor]
    simp
  · rw [hor]
    omega

/-- **The loop dichotomy is the affine inequality.**  Whether the segment of an
orbit over any window contracts or expands is decided by an inequality in
`2 ^ k`, `3 ^ a`, `x` and the accumulator — the very coordinates the density /
affine-magnitude framework already works in.  Repetition adds nothing. -/
theorem loop_dichotomy (x k : Nat) :
    acceleratedOrbit k x < x ↔ 3 ^ oddCount x k * x + affineC k x < 2 ^ k * x := by
  have hex := affine_exact x k
  have key : ∀ u v : Nat, u < v → 2 ^ k * u < 2 ^ k * v := by
    intro u v huv
    rcases Nat.lt_or_ge (2 ^ k * u) (2 ^ k * v) with h | h
    · exact h
    · have := Nat.le_of_mul_le_mul_left h (Arith.two_pow_pos k)
      omega
  constructor
  · intro h
    have := key _ _ h
    omega
  · intro h
    have h2 : 2 ^ k * acceleratedOrbit k x < 2 ^ k * x := by omega
    exact Nat.lt_of_mul_lt_mul_left h2

/-- **The expanding case is never vacuous.**  Every odd point of every orbit
grows under one step, so the two branches of the loop dichotomy cannot be
excluded separately by any segment-local argument. -/
theorem odd_step_expands {x : Nat} (hx : x % 2 = 1) : x < acceleratedStep x := by
  rw [acceleratedStep, if_neg (by omega)]
  omega

/-! ## Part 2 — the word-level accumulator -/

/-- Number of odd letters of a word. -/
def ones (w : List Nat) : Nat := w.count 1

/-- The accumulator of a parity word, by head recursion. -/
def wC : List Nat → Nat
  | [] => 0
  | b :: t => (if b = 1 then 3 ^ ones t else 0) + 2 * wC t

@[simp] theorem ones_nil : ones [] = 0 := rfl
@[simp] theorem wC_nil : wC [] = 0 := rfl

theorem ones_cons (b : Nat) (t : List Nat) :
    ones (b :: t) = (if b = 1 then 1 else 0) + ones t := by
  unfold ones
  by_cases hb : b = 1
  · subst hb
    simp [Nat.add_comm]
  · rw [List.count_cons, if_neg hb, if_neg (by simpa using hb)]
    omega

theorem wC_cons (b : Nat) (t : List Nat) :
    wC (b :: t) = (if b = 1 then 3 ^ ones t else 0) + 2 * wC t := rfl

theorem ones_append (u v : List Nat) : ones (u ++ v) = ones u + ones v := by
  simp [ones, List.count_append]

@[simp] theorem wC_singleton (b : Nat) : wC [b] = (if b = 1 then 1 else 0) := by
  by_cases hb : b = 1 <;> simp [wC, ones, hb]

@[simp] theorem ones_singleton (b : Nat) : ones [b] = (if b = 1 then 1 else 0) := by
  by_cases hb : b = 1 <;> simp [ones, hb]

/-- **The concatenation law.**  This is the free-monoid multiplication of
`RunAlgebra`/`NewModels` written on the accumulator coordinate. -/
theorem wC_append (u v : List Nat) :
    wC (u ++ v) = 3 ^ ones v * wC u + 2 ^ u.length * wC v := by
  induction u with
  | nil => simp
  | cons b t ih =>
    rw [List.cons_append, wC_cons, ih, ones_append, wC_cons, List.length_cons,
      Arith.two_pow_succ]
    by_cases hb : b = 1
    · rw [if_pos hb, if_pos hb, Nat.pow_add]
      generalize (3:Nat) ^ ones t = A
      generalize (3:Nat) ^ ones v = B
      generalize wC t = X
      generalize wC v = Y
      generalize (2:Nat) ^ t.length = P
      simp [Nat.mul_add, Nat.add_mul, Nat.mul_comm, Nat.mul_left_comm,
        Nat.mul_assoc, Nat.add_comm, Nat.add_left_comm, Nat.add_assoc]
    · rw [if_neg hb, if_neg hb]
      generalize (3:Nat) ^ ones v = B
      generalize wC t = X
      generalize wC v = Y
      generalize (2:Nat) ^ t.length = P
      simp [Nat.mul_add, Nat.add_mul, Nat.mul_comm, Nat.mul_left_comm,
        Nat.mul_assoc, Nat.add_comm, Nat.add_left_comm, Nat.add_assoc]

/-! ## Part 3 — the bridge to the orbit accumulator -/

theorem parityVector_snoc (r L : Nat) :
    parityVector r (L + 1) = parityVector r L ++ [acceleratedOrbit L r % 2] := by
  simp [parityVector, List.range_succ]

@[simp] theorem parityVector_length (r L : Nat) : (parityVector r L).length = L := by
  simp [parityVector]

/-- `ones` on a parity vector is `oddCount`. -/
@[simp] theorem ones_parityVector (r L : Nat) : ones (parityVector r L) = oddCount r L := rfl

/-- **`wC` computes `affineC`.**  The word-level accumulator is the orbit
accumulator, so everything proved about `wC` transfers to the cycle criterion. -/
theorem wC_parityVector (r : Nat) : ∀ L : Nat, wC (parityVector r L) = affineC L r := by
  intro L
  induction L with
  | zero => simp [parityVector]
  | succ L ih =>
    rw [parityVector_snoc, wC_append, ih, parityVector_length, wC_singleton,
      ones_singleton]
    rcases Arith.mod_two_eq_zero_or_one (acceleratedOrbit L r) with he | ho
    · rw [affineC_even he, he]
      simp
    · rw [affineC_odd ho, ho]
      simp

/-! ## Part 4 — the substitution mechanism -/

/-- **The substitution identity.**  Replacing a factor `p` by a factor `q` of the
same length and the same odd count changes the accumulator by exactly
`2 ^ |x| · 3 ^ ones y` times the change in the factor's own accumulator.  Stated
without subtraction so it is a `Nat` identity. -/
theorem wC_subst_identity (x p q y : List Nat)
    (hlen : q.length = p.length) (hones : ones q = ones p) :
    wC (x ++ q ++ y) + 2 ^ x.length * 3 ^ ones y * wC p
      = wC (x ++ p ++ y) + 2 ^ x.length * 3 ^ ones y * wC q := by
  rw [wC_append (x ++ q) y, wC_append (x ++ p) y, wC_append x q, wC_append x p,
    List.length_append, List.length_append, hlen, hones]
  generalize (3:Nat) ^ ones y = B
  generalize (3:Nat) ^ ones p = A
  generalize wC x = W
  generalize wC p = Pp
  generalize wC q = Qq
  generalize wC y = Y
  generalize (2:Nat) ^ x.length = E
  generalize (2:Nat) ^ (x.length + p.length) = F
  simp [Nat.mul_add, Nat.add_mul, Nat.mul_comm, Nat.mul_left_comm, Nat.mul_assoc,
    Nat.add_comm, Nat.add_left_comm, Nat.add_assoc]

/-- The same identity in the form the descent uses: with `wC q + s = wC p`, the
substituted word's accumulator is smaller by exactly `2 ^ |x| · 3 ^ ones y · s`. -/
theorem wC_subst_drop {x p q y : List Nat} {s : Nat}
    (hlen : q.length = p.length) (hones : ones q = ones p) (hs : wC q + s = wC p) :
    wC (x ++ q ++ y) + 2 ^ x.length * 3 ^ ones y * s = wC (x ++ p ++ y) := by
  have hid := wC_subst_identity x p q y hlen hones
  have hexp : 2 ^ x.length * 3 ^ ones y * wC p
      = 2 ^ x.length * 3 ^ ones y * wC q + 2 ^ x.length * 3 ^ ones y * s := by
    rw [← Nat.mul_add, hs]
  omega

/-- **The descent step.**  A congruent substitution preserves the divisibility
`G ∣ C` that is the cycle criterion, and strictly decreases the accumulator.
Nothing archimedean is used: `L`, `a`, `v₂`, `v₃` and every orbit magnitude are
untouched; the measure that falls is `C` itself. -/
theorem subst_dvd {x p q y : List Nat} {G s : Nat}
    (hlen : q.length = p.length) (hones : ones q = ones p)
    (hs : wC q + s = wC p)
    (hGs : G ∣ 2 ^ x.length * 3 ^ ones y * s)
    (hG : G ∣ wC (x ++ p ++ y)) :
    G ∣ wC (x ++ q ++ y) := by
  have hdrop := wC_subst_drop (x := x) (y := y) hlen hones hs
  obtain ⟨A, hA⟩ := hG
  obtain ⟨B, hB⟩ := hGs
  refine ⟨A - B, ?_⟩
  have hmul : G * (A - B) = G * A - G * B := Nat.mul_sub G A B
  omega

/-- The descent is strict as soon as the factor's accumulator genuinely drops. -/
theorem subst_lt {x p q y : List Nat} {s : Nat}
    (hlen : q.length = p.length) (hones : ones q = ones p)
    (hs : wC q + s = wC p) (hspos : 0 < s) :
    wC (x ++ q ++ y) < wC (x ++ p ++ y) := by
  have hdrop := wC_subst_drop (x := x) (y := y) hlen hones hs
  have hpos : 0 < 2 ^ x.length * 3 ^ ones y * s := by
    have h1 : 0 < 2 ^ x.length := Arith.two_pow_pos _
    have h2 : 0 < (3:Nat) ^ ones y := Arith.three_pow_pos _
    exact Nat.mul_pos (Nat.mul_pos h1 h2) hspos
  omega

/-- The substituted word has the same length and the same odd count, so it lives
at the same pair `(L, a)` and carries the same gap. -/
theorem subst_shape (x p q y : List Nat)
    (hlen : q.length = p.length) (hones : ones q = ones p) :
    (x ++ q ++ y).length = (x ++ p ++ y).length ∧ ones (x ++ q ++ y) = ones (x ++ p ++ y) := by
  constructor
  · simp [List.length_append, hlen]
  · simp [ones_append, hones]

/-! ## Part 4b — when is a substitution partner *forced*?

The substitution needs a second word `q` with the same length and odd count as a
factor `p` of the cycle word and `wC q ≡ wC p (mod G)`.  Pigeonhole forces one as
soon as the number of admissible `q` exceeds `G`.  The admissible `q` are
constrained two-sidedly by the orbit, and that is what `factor_profile_band`
records: reading the word from the cycle minimum `n` with maximum `M`, the affine
law gives, for every prefix length `u`,

  `2 ^ u * n ≤ 3 ^ A_u * n + C_u`   (the orbit never drops below `n`)
  `3 ^ A_u * n ≤ 2 ^ u * M`         (the orbit never rises above `M`)

so `A_u` is pinned to `u·log₃2 + O(log₃(M/n))`, and every factor of the word has
odd-step density within `log₃(M/n)` of `log₃ 2 = 0.63093`.  Counting the words in
that band against the modulus:

  `log₂ #{q} ≈ H(0.63093)·L + 0.48821·log₂(M/n) = 0.94996 L + 0.48821·log₂(M/n)`
  `log₂ G     = L − δ`,  `δ = L − log₂ G`

so a partner is **forced** exactly when

  `log₂(M/n) > (0.05004 L − δ) / 0.48821 ≈ 0.1025 L − 2.05 δ`.

At the frontier pair `(L, a) = (6809, 4296)` (`δ = 10.362`) that reads
`M/n > 2^690.5`; at `(4701, 2966)`, `M/n > 2^474.2`; at the archimedean survivor
`(24727, 15601)`, `M/n > 2^2518.6`.  The `3x − 1` cycle through 17 has
`M/n = 136/17 = 2³` against a threshold of `2^(−6.8)`, so a partner is forced
there — and indeed `S(11, 7, 139)` has eleven elements.  **The missing input is a
bound on a cycle's spread `M/n`.**  The crude bound is `M/n ≤ (3/2)^L = 2^0.585L`,
which does not decide it.  This is the sharp form of the "is a collision forced?"
question and it is recorded as open, not as closed.
-/

/-- **The factor-profile band.**  Both inequalities are the exact affine law read
against the two extremes of the cycle.  Together they pin the odd-step count of
every prefix — hence of every factor — to `log₃ 2` times its length, up to
`log₃(M / n)`. -/
theorem factor_profile_band {n u M : Nat}
    (hlow : n ≤ acceleratedOrbit u n) (hhigh : acceleratedOrbit u n ≤ M) :
    2 ^ u * n ≤ 3 ^ oddCount n u * n + affineC u n ∧
      3 ^ oddCount n u * n ≤ 2 ^ u * M := by
  have hex := affine_exact n u
  constructor
  · have : 2 ^ u * n ≤ 2 ^ u * acceleratedOrbit u n := Nat.mul_le_mul_left _ hlow
    omega
  · have : 2 ^ u * acceleratedOrbit u n ≤ 2 ^ u * M := Nat.mul_le_mul_left _ hhigh
    omega

/-! ## Part 5 — the mechanism produces a genuine cycle, and then halts

The realiser hypothesis `hr'` is the one bridge this file does not prove; see the
header.  Everything else is unconditional. -/

/-- **A descent step is a genuine smaller cycle point.**  Given a cycle word
realised by `r`, a congruent substitution realised by `r'`, and the divisibility
side condition, the substituted word is itself a cycle word of the *same* period
and its cycle point is strictly smaller. -/
theorem subst_yields_cycle {r r' L n s : Nat} {x p q y : List Nat}
    (hr : parityVector r L = x ++ p ++ y) (hr' : parityVector r' L = x ++ q ++ y)
    (hgap : 3 ^ oddCount r L < 2 ^ L)
    (hlen : q.length = p.length) (hones : ones q = ones p)
    (hs : wC q + s = wC p) (hspos : 0 < s)
    (hGs : (2 ^ L - 3 ^ oddCount r L) ∣ 2 ^ x.length * 3 ^ ones y * s)
    (hcyc : (2 ^ L - 3 ^ oddCount r L) * n = affineC L r) :
    ∃ n' : Nat, acceleratedOrbit L n' = n' ∧ n' % 2 ^ L = r' % 2 ^ L ∧ n' < n := by
  -- the two words have the same odd count, hence the same gap
  have hcount : oddCount r' L = oddCount r L := by
    have h1 : ones (parityVector r' L) = ones (parityVector r L) := by
      rw [hr, hr']
      simp [ones_append, hones]
    simpa using h1
  -- the divisibility transfers
  have hGp : (2 ^ L - 3 ^ oddCount r L) ∣ wC (x ++ p ++ y) := by
    rw [← hr, wC_parityVector]
    exact ⟨n, hcyc.symm⟩
  have hGq : (2 ^ L - 3 ^ oddCount r L) ∣ wC (x ++ q ++ y) :=
    subst_dvd hlen hones hs hGs hGp
  obtain ⟨n', hn'⟩ := hGq
  refine ⟨n', ?_, ?_, ?_⟩
  · exact (cycle_of_gap_dvd (r := r') (by rw [hcount]; exact hgap)
      (by rw [hcount, ← wC_parityVector, hr']; exact hn'.symm)).1
  · exact (cycle_of_gap_dvd (r := r') (by rw [hcount]; exact hgap)
      (by rw [hcount, ← wC_parityVector, hr']; exact hn'.symm)).2
  · -- strict drop of the accumulator, divided by the common positive gap
    have hlt : wC (x ++ q ++ y) < wC (x ++ p ++ y) := subst_lt hlen hones hs hspos
    have hp : wC (x ++ p ++ y) = (2 ^ L - 3 ^ oddCount r L) * n := by
      rw [← hr, wC_parityVector]; exact hcyc.symm
    have hGpos : 0 < 2 ^ L - 3 ^ oddCount r L := by omega
    have : (2 ^ L - 3 ^ oddCount r L) * n' < (2 ^ L - 3 ^ oddCount r L) * n := by
      omega
    exact Nat.lt_of_mul_lt_mul_left this

/-! ## Part 6 — the soundness filter, executed

The mechanism above is a function of the parity word alone, and `C(w, d) = d ·
C(w, 1)`, so it runs verbatim in every `d`-world.  In the `d = −1` world it must
halt at the genuine cycle through 17, and here is that cycle, with its
accumulator computed by the very `wC` the mechanism manipulates. -/

/-- The parity word of the `3x − 1` orbit of `17`, length 11, seven odd letters. -/
def w17 : List Nat := [1, 1, 1, 1, 0, 1, 1, 1, 0, 0, 0]

theorem w17_length : w17.length = 11 := rfl
theorem w17_ones : ones w17 = 7 := rfl

/-- Its accumulator, from the word alone. -/
theorem w17_accum : wC w17 = 2363 := rfl

/-- And `2363 = 139 · 17`, the gap `|2 ^ 11 − 3 ^ 7| = 139` times the cycle
minimum. -/
theorem w17_gap_mul : 2363 = 139 * 17 := rfl

/-- **The witness that kills every `d`-free descent.**  This is the exact affine
law `2 ^ L · T^L(x) = 3 ^ a · x + C` for `d = −1`, written in `Nat` with the
negative accumulator moved to the other side: the orbit of `17` under
`x ↦ (3x − 1)/2` returns to `17` after 11 steps with 7 odd steps and accumulator
`2363`.  The gap `2 ^ 11 − 3 ^ 7 = −139` is negative, which is why this cycle is
outside every `Nat`-typed cycle theorem in this development — and why any descent
argument that does not consume the sign of `d` is refuted right here. -/
theorem neg_gap_witness : 3 ^ 7 * 17 = 2 ^ 11 * 17 + wC w17 := by
  rw [w17_accum]

/-- The `3x + 5` pair, at the same `(L, a) = (27, 17)` and the *same* gap
`G = 2 ^ 27 − 3 ^ 17 = 5 077 565`, with two different accumulators.  Two distinct
cycles coexist at one `(L, a)`, so "the accumulator is minimal" is satisfiable by
a non-unique configuration and yields no contradiction. -/
theorem two_cycles_one_gap :
    (2 ^ 27 - 3 ^ 17) * 187 = 5 * 189900931 ∧ (2 ^ 27 - 3 ^ 17) * 347 = 5 * 352383011 ∧
      189900931 < 352383011 := by
  refine ⟨rfl, rfl, by decide⟩

/-- The halting point of the substitution descent in the `d = −1` world at
`(11, 7)`: the eleven rotations of the 17-cycle are the whole solution set, and
`2363` is the least of their accumulators.  (Completeness of the list is
exhaustive computation, recorded in the header; what is proved here is that every
listed value is divisible by the gap and that `2363` is the minimum of the list.) -/
def w17class : List Nat :=
  [2363, 3475, 4726, 5143, 5699, 7645, 8479, 9452, 11398, 12649, 18904]

theorem w17class_all_dvd : w17class.all (fun c => c % 139 == 0) = true := by decide

theorem w17class_min : w17class.all (fun c => 2363 ≤ c) = true := by decide

end RepetitionDescent
end Collatz
