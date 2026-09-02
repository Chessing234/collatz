# Device: even-choice completion of the shift ARS

Agent 5 — rewrite-system theory.

The rules `n → n/2` and `n → 3n+1` are rewrite rules. Ordinary termination of
that system *is* Collatz, and is not the object. The accelerated map is a
function, so its one-step relation is orthogonal: even and odd redexes never
overlap, there are no critical pairs, and confluence is vacuous. Decreasing
diagrams, local confluence, and Knuth–Bendix have nothing to act on.

The device is a *related* ARS that is nondeterministic, whose critical pairs
carry a complexity that is well-founded if and only if the even branch contracts.
That contraction is true of `3n+1` and false of `expStep`.

## 1. The shift encoding

In the coordinate `u = n + 1` the two maps become:

| `n`     | `u`    | `3n+1` (accelerated) | `expStep`            |
|---------|--------|----------------------|----------------------|
| odd     | even   | `u ↦ 3u/2` (`τ`)     | same `τ`             |
| even    | odd    | `u ↦ (u+1)/2` (`η`)  | `u ↦ (3u−1)/2` (`ε`) |

The odd-`n` rule is shared. The even-`n` rule is the whole difference:
`expStep` replaces `n/2` by `3n/2`, which on the shift is `ε` rather than `η`.

`τ` and `η` together are still a function of the parity of `u`. No overlap.

## 2. The even-choice ARS (nondeterministic)

Drop the determination of which even rule to fire. On odd `u` *both* `η` and
`ε` apply:

```
          u          (u odd, u > 1)
        /   \
     η /     \ ε
      v       v
  (u+1)/2   (3u−1)/2
```

This is the critical pair of the even-choice system. The two reducts are
`T(n)+1` and `expStep(n)+1` for `n = u−1` even. They coincide if and only if
`u = 1`.

Knuth–Bendix, facing this overlap, must orient `(u+1)/2` against `(3u−1)/2`.
The unique orientation that is a simplification rule on `ℕ` (larger → smaller)
is

```
ε(u)  →  η(u)        (u+1)/2  <  (3u−1)/2  for u > 1.
```

That orientation *prefers the `3n+1` even branch*. The opposite orientation
`η → ε` is the `expStep` even branch and is not a simplification rule.

## 3. The rewrite lemma (formalized)

A labeling `μ : ℕ → ℕ` of the even-choice peak is **strictly monotone** when
`a < b` implies `μ a < μ b`. It **decreases on a reduct `r`** when
`μ(r u) < μ u` at every odd `u > 1`.

**Lemma.** For any strictly monotone `μ` and any reduct `r`,

```
μ decreases on r   ⟺   r u < u  at every odd u > 1.
```

The left-to-right direction is the contrapositive of monotonicity: if `u ≤ r u`
then `μ u ≤ μ(r u)`. The right-to-left direction is `μ =` the identity, or any
strictly monotone map, applied to a genuine contraction.

**Corollary (the IFF).** The even-choice critical pair admits a strictly
monotone decreasing-diagram label if and only if the even reduct contracts.

- `η` contracts: `(u+1)/2 < u` for odd `u > 1`. The identity labeling is a
  decreasing diagram for the `3n+1` side. Well-founded, because it is a
  subrelation of `<` on `ℕ`.
- `ε` expands: `u < (3u−1)/2` for odd `u > 1`. No strictly monotone `μ` can
  decrease on `ε`. The `expStep` side has no such complexity.

This is not a termination proof of Collatz. The odd-`n` rule `τ` *increases*
`u`, so the full shift system `{τ, η}` is not decreasing in the value, and a
monotone label that worked on every Collatz step would be the conjecture. The
lemma is only about the *critical pair of the even-choice overlap*.

Lean: `Collatz/Strategy/RewriteSystem.lean`,
`mono_label_descends_iff`, `eta_contracts`, `eps_expands`,
`collatz_even_has_mono_label`, `expStep_even_no_mono_label`.

## 4. Inverse overlap, and why doubling-quotient KB is sound only for `/2`

The inverse accelerated system is the other natural nondeterministic ARS:

```
D : y  →  2y                      (always)
P : y  →  (2y−1)/3                (when y ≡ 2 (mod 3))
```

A local peak at every branch point: `(2y, oddPred y)`. Both one-step inverse
reducts join *forward* at `y`:

```
T(2y) = y,     T(oddPred y) = y.
```

Label inverse steps `inv` and forward steps `fwd`, with `fwd < inv` (two-point
well-founded order). The diamond is a van Oostrom decreasing diagram. The
`D`-side of the join is a value decrease `2y > y`.

The same diamond is **not** a diagram of `expStep`. Doubling is not an inverse
step:

```
expStep(2y) = 3y ≠ y,     y < 2y < 3y.
```

So `y` is not a forward `expStep`-descendant of `2y` at all. Knuth–Bendix
completion of the inverse system *modulo the equation `y ≈ 2y`* (the quotient
by `D`) is sound for Collatz joinability because `T(2y) = y` puts `2y` and `y`
in the same class. It is unsound as an `expStep` quotient: `expStep` never
identifies `2y` with `y`.

After collapsing `D`, the residual inverse rules are indexed by extra-halving
depth `k ≥ 1`:

```
R_k :  y  →  (2^k y − 1)/3         when  2^k y ≡ 1 (mod 3), result odd.
```

Two residuals overlap when they share a residue of `y` modulo 3, i.e. when
`k ≡ k' (mod 2)`. The critical-pair complexity is the pair of depths `(k, k')`,
ordered by `ℕ`. That order is well-founded, and `k ≥ 1` is exactly
`v₂(3n+1) ≥ 1` after an odd `n` — the extra halving that `expStep`'s even
branch `3x/2` does not perform. Forward, `T^k(R_k(y)) = y`; already the second
`expStep` after the shared odd step is `3 · 2^{k-2} y`, not `2^{k-2} y`.

Lean: `inverse_peak_diamond`, `expStep_not_D_join`, `residual_joins`,
`residual_expStep_diverges`.

## 5. What this is not

- Not a termination proof of `{τ, η}`. Odd steps grow.
- Not confluence of the Collatz map. That map has no critical pairs.
- Not a residue sieve. The only modulus is `3`, and it is the branch guard of
  `P`, already in `ReverseTree`.
- Not a ranking on the full orbit. `Rewriting.no_simplification_order` already
  kills path orders on the deterministic encoding; this device never orients
  `τ`.

The only new object is the even-choice overlap and the residual inverse family
after quotient by doubling. Their decreasing-diagram / Knuth–Bendix complexity
is well-founded exactly on the `3n+1` even branch.
