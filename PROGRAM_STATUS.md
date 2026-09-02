# PROGRAM_STATUS

Ledger for the seven-program brief.  `open | refuted | partial | closed`.

Repo facts that constrain every entry, checked this session:

* **No Mathlib.**  `lakefile` pulls no dependency; core Lean 4 only.  `by_contra`,
  `interval_cases`, `norm_num`, `ring`, `push_neg`, `set`, `Nat.find` do not exist.
* **No `sorry`, no added axioms**, anywhere in `Collatz/`.  Every theorem below is
  `propext`/`Quot.sound` only.
* **Verified range is `1 086 464`**, kernel-proved (`verified_1086464`).  Not
  `2^68`.  Barina's `704·2^60` is present only as the clearly-marked hypothesis
  `BarinaVerified`; results using it are conditional and labelled so.
* The untracked stubs `Collatz/ProgramA…G.lean` import Mathlib, carry `sorry`, and
  contain placeholder definitions (`local_height = 0`, `S n = n`, a theorem proving
  `x = x` by `rfl`).  They do not compile and are not built on.

---

## A — Adelic filter on ghosts — **refuted** (height route)

**Strongest result:** the hoped inequality `h(σ) ≥ κ·disc(σ)`, `κ > 0`, is false.

**Certificate:** exhaustive at `L = 16`.  Of `6848` primitive words with negative
realizer, `652` have reduced height strictly below `log|2^E − 3^L|`.  Example: word
`0010111111111101`, denominator `465905`, reduces to `−320596/42355` — a collapse of
`0.37` nats.  The all-ones word gives `λ_σ = −1` exactly, for **every** length.

**Obstruction — ghost.**  The height of `λ_σ` is governed by `gcd(C(σ), 2^E − 3^L)`,
which is uncontrolled.  These are degree-`1` points, so Lehmer/Dobrowolski give
nothing, and the only available lower bound is saturated by `λ = −1`, a genuine
ghost.  The `{2,3,∞}`-restricted adelic norm was also computed along orbits: it
equals the part of `n` coprime to `6`, is neither conserved nor monotone.

---

## D — Sturmian / mechanical wall — **refuted**

**Strongest result:** the congruence tower is **never** empty.  `L₀(ε)` does not
exist for any `ε`, so "every mechanical word with `β ≤ α − ε` dies by length `L₀(ε)`"
is false for every `ε`.

**Certificate:** enumerating odd `n < 2^18`, every valuation word `(v₁,…,v_L)` of
small total occurs — missing `0` of `8`, `64`, `350`, `941` at `L = 1,2,3,4`.  This is
the Terras/Everett bijection: the first `L` valuations depend only on `n mod 2^E`, and
every word is realised by a residue class.

**Obstruction — Mersenne bypass, general form.**  The brief already forbids emptying
residue classes mod `2^M`; the same holds one level up, for valuation words
themselves.  Nothing dies at any length.

---

## F — Lexicographic vector height — **refuted as templated**

**Strongest lemma (new, Lean, `Strategy/DensitySaturation`):**

```
no_bounded_block_descent : 0 < B → B < j → 2^j - 1 < acceleratedOrbit B (2^j - 1)
no_uniform_block         : ∀ B, 0 < B → ∃ n, 0 < n ∧ n < acceleratedOrbit B n
```

resting on

```
orbit_pow_pred : i ≤ m → acceleratedOrbit i (3^k * 2^m - 1) = 3^(k+i) * 2^(m-i) - 1
```

so `T^B(2^j − 1) = 3^B·2^(j−B) − 1 > 2^j − 1`, since `2^B < 3^B`.

**Certificate:** the same for Syracuse.  With `n = 2^(B+3) − 1`, bit length over a
block of `B` steps moves `+3, +5, +10, +19, +38` for `B = 4, 8, 16, 32, 64`; all
valuations are `1` throughout.

**Obstruction — ghost/Mersenne.**  A height whose leading coordinate is the magnitude
of `n`, decreasing over a block of length bounded uniformly in `n`, cannot exist: the
family `2^j − 1` trades one `2` for one `3` per step and grows over any fixed number
of steps.  Since a block length that is "a function of `n mod 2^M`" takes finitely
many values, it is bounded, and the brief's template is dead as specified.

**Escape hatch, not excluded:** a block length depending on an *unbounded* statistic
of `n` — `v₂(n+1)` is the natural one, since it is exactly the run length.  That is
the next lemma below.

---

## B — Discrete stochastic localization — **open, not started**

Expected reduction to A stands: `κ` positive exactly on the ghosts.  Note the repo
already refutes the pointwise/block Lyapunov family and excursion-peak potentials
(`Φ(159487) ≈ 53930`, unbounded), so any drift inequality must be genuinely new.

---

## C — Carry cocycle / substitution automaton — **open, not started**

Warning from D: since every valuation word is realised by an integer residue class,
"no infinite path with empirical `v₂`-mean `< log₂ 3` is reachable from an integer
bitstream" is false for every *finite* prefix.  Any non-reachability statement must be
about infinite paths only, and must not follow from prefix reachability.

*The warning is now a theorem, not an observation.*
`Strategy.GapBarriers.exists_realizer`: for any `(a₀, …, a_{L−1})` with every
`a i ≥ 1` there is an odd `n₀` whose first `L` valuations are exactly those.  With
`traj_congr` (determinacy) this is `parity_vector_correspondence` — valuation
vectors of length `L` correspond exactly to residue classes mod `2^(K+1)`.  So
prefix reachability is not merely unrefuted but *universal*: **every** finite
valuation word is realised, with no exceptions to hunt for.  A proposed
non-reachability argument can therefore be rejected outright the moment it
consumes a finite prefix, and this is now checkable against a theorem rather than
against a remembered caution.

---

## E — Hybrid isolation of the residual Cantor set — **open, blocked on A/D**

A and D were to supply the minimising words.  A's minimiser is the all-ones word,
whose realiser is `−1` exactly; D has no minimiser because nothing dies.  Related
measurement already made: nested realisers `x_k ∈ [0,2^k)` of aperiodic high-density
words wander over the whole of `(0,1)` to `k = 3200` at densities `0.63…0.9`, with
leading-bit agreement never exceeding about `4` digits.  No linear barrier is visible.

---

## G — Function-field certificate extraction — **open, method conflict**

The brief asks for `WouldBeProofZ.lean` carrying a single `sorry`.  The repository
forbids `sorry` outright.  The equivalent that fits: state the failing step as an
explicit hypothesis `Prop` and carry it as an argument, which is exactly what this
repo already does with `HalbeisenHungerbuhler.HHExtremal` — and that Prop was later
*discharged* (`HHLemmaFive.hhExtremal_holds`).  That pattern is available and keeps
the kernel clean.

---

## Acceptance criteria

* **(P1) no nontrivial cycles — NOT met.**  Strongest unconditional result is
  `Frontier9971.length_ge_9971`, on the verified range `2 011 136`
  (`Search.VerifiedRung9971`); it supersedes `RealizableFrontier6809.length_ge_6809`
  by three risers of the ladder.  Round XLIV proved the paying route cannot
  reach further: the verified range needed to kill the `k`-th ladder rung is
  `≈ a_k·a_{k+1}/(6 ln 2)`, which diverges, so **no finite verified range excludes all
  cycle lengths**.  Climbing two rungs does not touch that conclusion — an
  independent check at Barina's `704·2^60` puts the reach there at only `~7·10^10`
  odd steps, still finite and still not all lengths.  Rungs to frontier `13133` are
  banked in `Strategy.PreCertified` and need only the corresponding ranges;
  `Strategy.FrontierParametric.length_ge_of_cert` makes each a one-line
  instantiation.  Three remain conditional (`11025`, `12079`, `13133`, needing
  `2 403 661`, `2 855 820`, `3 380 808`); `9971` is now unconditional, and it is
  the last banked rung the verified range reaches.

  **Round XLIV's divergence claim is now a theorem, not a measurement.**
  `Strategy.RouteCap.cert_reach_le`: any certificate reaching odd-step budget
  `A` at range `c` forces `A ≤ 6c`; hence
  `RouteCap.frontier_le_of_route` gives `F ≤ fexp (6c) + 1`, and
  `RouteCap.route_misses_a_length` exhibits, for every `c`, a cycle length the
  route cannot reach.  The proof is two collisions: `2 ^ fexp a ≤ 3 ^ a` turns
  the certificate into `Bcap a < 3 ^ a · c`, and `3 ^ i < 2 · 2 ^ fexp i` turns
  the `a` summands of `Bcap a` into `a · 3 ^ a ≤ 6 · Bcap a`.  The constant `6`
  is far from tight — at `c = 2 010 160` it allows `A < 12 060 960` against the
  actual `6291` — because it discards how closely `3 ^ a` approaches
  `2 ^ (fexp a + 1)`, which is the Diophantine content of the measured
  `a_k · a_{k+1} / (6 ln 2)` law and is *not* proved here.  Finiteness is
  proved; the rate is not.
* **(P2) no divergence — NOT met.**  F refuted as templated; A, D, E blocked.
* **Verdict: neither half is closed.  Cycles are not excluded; divergence is not
  excluded.**

---

## Next smallest lemma — ANSWERED (negative)

> **Resolved.**  The refined reading — may the tail depend on the run length? —
> is **false**, and `Strategy.RunLengthUnbounded.no_tail_at_run_length_two`
> proves it: for every `B` there is an `n ≡ 3 (mod 8)`, hence with `r(n) = 2`
> exactly, whose orbit has still not descended after `B` steps.  So no
> `s : ℕ → ℕ` satisfies `T^(r(n) + s(r(n)))(n) < n` for all odd `n > 1`.
>
> The construction: for `n = 8a + 3`, `T³(n) = 9a + 4`, so choosing `9a + 5 = 2^k`
> lands the orbit exactly on `2^k − 1`, and `ScaleLadder.climb` carries it to
> `3^k − 1`.  Solvable iff `k ≡ 5 (mod 6)`, giving `a₀ = 3`, `a_{j+1} = 64a_j + 35`
> and the family `27, 1819, 116507, 7456539, …`.
>
> **Where the obstruction is not.**  The `2^j − 1` family this question proposed
> as the first test does *not* refute the shape: `Strategy.MersenneDescent`
> checks that it descends within `12j` for `2 ≤ j ≤ 200`, with the ratio `σ/j`
> peaking at `11.2` on the small case `j = 5` and staying under `4.34` past
> `j = 30`.  The obstruction is at *small fixed* run length instead.
>
> **Where the run length does work.**  `r(n) = 1` is genuinely different:
> `σ = 2` for every `n ≡ 1 (mod 4)`, already in
> `Structure.CycleMinClass.two_step_descent`.  So `j = 1` is the sole exception.
>
> **Now proved at every run length.**  `Strategy.RunLengthAny.no_tail_at_any_run_length`
> generalizes the construction to every `j ≥ 2`: take `n = 2^j·d − 1` with
> `3^j·d = 2^(k+1) − 1`, which is solvable whenever `2·3^(j−1) ∣ k+1`.  That
> divisibility is `Strategy.LiftExponentThree.two_pow_three_pow`, the `p = 3`
> lift, which this repository previously lacked (`LiftExponent` covers `p = 2`
> only).  The construction's one inequality, `n < 2^k − 1`, reduces exactly to
> `2^(j+1) < 3^j` — true precisely for `j ≥ 2`, which is why `j = 1` is a genuine
> exception rather than an artefact.
>
> So the run length controls the descent time **only** at `j = 1`.
>
> **But it does bound it from below, everywhere.**
> `Strategy.MersenneLower.sigma_gt_run_half`: for every odd `n`, no iterate falls
> below `n` within `r + r/2` steps, i.e. `σ(n) > (3/2)·r(n)` — no parity
> assumption.  Sharpened at `12 ∣ r` to `σ(n) > (19/12)·r(n)` by
> `sigma_gt_nineteen_twelfths`, using the convergent `19/12` of `log₂ 3`.  That
> is within `0.1%` of `log₂ 3` itself, which is the ceiling no argument of this
> shape can pass: the run lifts `n` by exactly `(3/2)^r` and a Terras step halves
> at best.  The whole content is
> `8^m ≤ 9^m`, i.e. `2^(3m) ≤ 3^(2m)`: the run lifts `n` by `(3/2)^r`, and a
> Terras step can at best halve.  Measured over all odd `n < 200 000` of even run
> length the bound never fails and its worst-case slack is `6.7%`.
>
> So `r(n)` bounds the descent time from **below** but not from **above** — which
> is the precise sense in which the original question's shape was the wrong one.

---

## Next smallest lemma, statable cold

> Let `r(n) = v₂(n+1)`, which by Terras is exactly the number of consecutive odd
> accelerated steps from odd `n`.  Decide whether
>
> `∀ odd n > 1, n > T^(r(n) + s(n))(n)` for some explicit `s(n)`
>
> — i.e. whether a block whose length is the *run length itself* plus an explicit
> tail descends.  This is the one shape `no_uniform_block` does not refute, because
> `r(n)` is unbounded.  Refute it, or find the `s` that works.
>
> First test: `n = 2^j − 1` gives `r = j`, `T^j(n) = 3^j − 1`, which is **larger**
> than `n`.  So `s` must be large enough to undo `(3/2)^j` growth — at least
> `j·log₂3` further even steps.  Determine whether that many are available, as a
> function of `j`, or exhibit the family where they are not.
