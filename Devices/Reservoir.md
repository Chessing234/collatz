# The divisibility reservoir

`v₂(n)` is present supply: the factors of two sitting in `n`, spent one
at a time by even Collatz steps.  The **reservoir** `R(n)` measures future
halving capacity latent in the odd kernel — 2-divisibility that is not yet
present supply, and that is not the current extra-halving count `W`.

This note does not claim Collatz.

---

## 1. Exact definition of `R`

Write `n = 2^r κ` with `κ` odd (the odd kernel), and write

    κ + 1  =  2^α μ    with `μ` odd.

Then

    R(n)  :=  v₂(μ + 1).

On an odd start with excursion data `n + 1 = 2^v u` (`u` odd), the kernel
is `n` itself and `μ = u`, so `R(n) = v₂(u + 1)`.

**What it is not.**  `R` is not `v₂(n)` (present supply; zero on every odd
start).  It is not `W = v₂(3^v u − 1)` (current extra halvings; LTE reads
those off the *other* neighbor `μ − 1`).  It is not plus-five `v₂(n + 5)`,
not 11-fuel `v₂(11n + 19)`, and not `drop_iff` slack
`2^{v+W} u − 3^v u − 2^W`.

**Recursive meaning.**

* Even Collatz step: `R(2n) = R(n)`.  Present supply is spent; the kernel,
  and with it the reservoir, is unchanged.
* Continuing odd step (`n ≡ 3 (mod 4)`): the cofactor `μ` is replaced by
  `3μ`, and `R((3n+1)/2) = v₂(3μ + 1)`.  One multiply-by-3 taps the
  unused neighbor.
* Light landing `W = 1`: `3^v u + 1 = 2(e + 1)`, so the unused neighbor
  of the peak *is* the next odd-run fuel.

---

## 2. Nontrivial theorem (on paper, with a Python witness)

**Theorem (reservoir predicts the next odd run).**
Let `IsExcursion n v u 1 e` be a light excursion, write `R(n) = ρ = v₂(u + 1)`
and `L = v₂(3^v − 1)`, and let `e + 1 = 2^{v'} u'` with `u'` odd.  Then:

| comparison | next run |
|---|---|
| `ρ < L` | `v' = ρ − 1` |
| `L < ρ` | `v' = L − 1` |
| `ρ = L` | `v' ≥ ρ` |

*Proof.*  The peak-plus identity `3^v (u+1) − (3^v − 1) = 3^v u + 1` and
the light identity `3^v u + 1 = 2(e+1)` (the extra Collatz halving `W = 1`)
give `v₂(3^v u + 1) = v' + 1`.  The left side is the ultrametric of a
difference whose two summands have valuations `ρ` and `L`.  If they
differ, the difference takes the minimum; if they agree, it jumps.
∎

This is not `drop_iff`.  It names the *next letter* `v'`, not the
comparison `e < n`.

**Python witness** (0 failures on every light start `< 20000`; named
checks below).  Run:

```python
def v2(n):
    k = 0
    while n % 2 == 0:
        n //= 2; k += 1
    return k

def oddpart(n):
    while n % 2 == 0:
        n //= 2
    return n

def R(n):
    mu = oddpart(oddpart(n) + 1)
    return v2(mu + 1)

def excursion(n):
    v = v2(n + 1); u = (n + 1) >> v
    peak = 3**v * u - 1; W = v2(peak)
    return v, u, W, peak >> W

fails = 0
for n in range(3, 20000, 2):
    v, u, W, e = excursion(n)
    if W != 1:
        continue
    rho, L = v2(u + 1), v2(3**v - 1)
    vp = v2(e + 1)
    if rho < L:
        ok = (vp + 1 == rho)
    elif L < rho:
        ok = (vp + 1 == L)
    else:
        ok = (vp >= rho)
    fails += not ok
print("fails", fails)   # 0
```

Named witnesses, all kernel-checked in `DeviceReservoir.lean`:

| `n` | `(v, W)` | `u` | `R` | `L` | predicted `v'` | actual landing |
|---|---|---|---|---|---|---|
| 11 | `(2, 1)` | 3 | 2 | 3 | `2−1 = 1` | `13`, `v' = 1` |
| 59 | `(2, 1)` | 15 | 4 | 3 | `3−1 = 2` | `67`, `v' = 2` |
| 27 | `(2, 1)` | 7 | 3 | 3 | `≥ 3` | `31`, `v' = 5` |

---

## 3. `expStep` test, `3x+5`, `3x+7` test

**`expStep`** (`3x/2` even, `(3x+1)/2` odd).

* Even conservation of `R` is Collatz-specific: `10 → 5` keeps `R = 2`;
  `expStep(10) = 15` has `R = 1`.  (`expStep_breaks_reservoir`.)
* The light identity `3^v u + 1 = 2(e+1)` uses the extra halving `W = 1`.
  On the peak of `11` that peak is `26`; Collatz lands at `13`,
  `expStep` does `3·26/2 = 39`, and `v₂(39+1) = 3 ≠ 1`.
  (`expStep_misses_light_landing`.)

So the next-run theorem is false of `expStep` at the first light start.

**`3x+5`.**  The `3n+1` odd run of `11` has length `2` and passes through
`17` before the light landing `13`.  The `3x+5` step is
`(3·11+5)/2 = 19`, already a different odd number, so the peak
`3^v u − 1` is the wrong affine form.  (`three_x_five_breaks_run`.)

**`3x+7`.**  `59` is light `(2, 1)` for `3n+1`, with predicted next run
`v' = 2` and landing `67`.  The first `3x+7` odd step is
`(3·59+7)/2 = 92` (even): the run length `v₂(n+1) = 2` is `d = 1`
specific.  (`three_x_seven_breaks_run`.)

Even conservation of `R` holds for `3x+5` and `3x+7` as well (they share
the even branch `n/2`).  The discriminator for those maps is the next-run
theorem, which uses the `+1` shift.

---

## 4. What it knows that the parity word / `expStep` do not

**One orbit, versus the parity word.**
The first-excursion word of both `11` and `27` is `(odd, odd, even)`,
i.e. `(v, W) = (2, 1)`.  That word does not determine the next letter.
`R(11) = 2 < L` predicts `v' = 1` (landing `13`); `R(27) = 3 = L` only
predicts `v' ≥ 3` (landing `31`, actual `v' = 5`).  The reservoir reads
that letter off `v₂(u+1)`, which is cofactor magnitude, not a function of
the finite parity prefix.  (`same_word_different_reservoir`.)

**`3n+1`, versus `expStep`.**
`R` knows that a light Collatz landing satisfies `2(e+1) = 3^v u + 1`,
because the even branch extracts the extra factor of two that `expStep`
replaces by `3/2`.  That identity is the whole content of the next-run
theorem, and it is empty for `expStep`.  Separately, `R` is invariant
under Collatz even steps and not under `expStep` even steps — a 2-adic
fact about the kernel, invisible to any statistic of the `expStep`
parity word (which is all ones).

---

## 5. Smallest lemma that would imply descent

The reservoir names the next run on every light step with `ρ ≠ L`.  It
does not compare the second landing to the *original* start.

**Lemma (reservoir tap).**  Every odd `n > 1` has an excursion iterate
at which either `drop_iff` fires, or the step is light with `ρ ≠ L` and
the predicted next landing `e'` satisfies `e' < n`.

That lemma plus the next-run theorem would give Lemma X on the light
set.  It is **not proved**.  It is false as a *two-step* law: `47` is
light `(4, 1)` with `R = 2 < L = 4`, so `v' = 1`, and the next landing
is `91 > 47`.  Any proof of the tap lemma must look past two excursions.
The collision class `ρ = L` (the `27` family) is the other remainder.

This device does not claim Collatz.
