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
  `RealizableFrontier6809.length_ge_6809`.  Round XLIV proved the paying route cannot
  reach further: the verified range needed to kill the `k`-th ladder rung is
  `≈ a_k·a_{k+1}/(6 ln 2)`, which diverges, so **no finite verified range excludes all
  cycle lengths**.
* **(P2) no divergence — NOT met.**  F refuted as templated; A, D, E blocked.
* **Verdict: neither half is closed.  Cycles are not excluded; divergence is not
  excluded.**

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
