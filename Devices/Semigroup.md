# Device: the affine Heisenberg monoid

Agent 2 — algebra / semigroup.  Not the free word on `{odd, even}`.

## Exact definition

Let `H` be the set of triples `(a, L, c) ∈ ℕ³`, standing for the affine map

    x  ↦  (3^a · x + c) / 2^L

on the module of numerators (the denominator is kept as an exponent).  The
product is composition, apply-right first:

    (a, L, c) · (a', L', c')  =  (a+a',  L+L',  3^a · c' + 2^{L'} · c).

This is a monoid with unit `(0,0,0)`.  It is the semidirect product of the
Parikh monoid `ℕ²` of exponents with the translation module `ℕ` in the `c`-slot.

Three generators:

| name | triple | map |
|---|---|---|
| `e` | `(0,1,0)` | `x ↦ x/2` |
| `o_d` | `(1,0,d)` | `x ↦ 3x+d` |
| `τ_t` | `(0,0,t)` | `x ↦ x+t` (numerator translation) |

The Collatz word submonoid is the image of `{e, o_1}^*`.  That image is free
(`wC_inj`) and every word is realised by an integer (`word_realizable`).  The
ambient monoid `H` is *not* that image: `τ_1` has length `0` and translation
`1`, and the only length-`0` Collatz word is the identity `c = 0`.  So `τ` is
an extra generator, not a renamed parity word.

The translation module acts on `H` by `addTrans((a,L,c), t) = (a, L, c+t)`.
Left multiplication by `u` scales a translation by `3^{a(u)}`; right
multiplication by `v` scales it by `2^{L(v)}`.

The **commutator defect** of a split `(u, v)` at additive constant `d` is

    K(u, v, d)  :=  3^{a(u)} · 2^{L(v)} · d.

Evaluated at a start `n`, this is the numerator defect of commuting `o_d` past
`e` between the frozen prefix `u` and the frozen suffix `v`.  It does not
depend on `n`.

## One nontrivial theorem

**Insertion of the commutator** (`DeviceSemigroup.middle_commutator`).
For all `u, v ∈ H`, all `d, n ∈ ℕ`,

    num(u · (o_d · e) · v, n)
      =  num(u · (e · o_d) · v, n)  +  3^{a(u)} · 2^{L(v)} · d

where `num((a,L,c), n) = 3^a · n + c`.  The two frozen words have identical
exponents; they differ by a constant translation.  The start `n` cancels.

Special case `u = v = 1`: `o_d · e` and `e · o_d` share exponents `(1,1)` and
differ in the `c`-slot by exactly `d` (`seed_commutator`).  On numerators this
is `3n+2d` versus `3n+d`.

Supporting laws, all `Nat` identities:

* `τ_t · e = e · τ_{2t}`  (`tau_conj_even`)
* `o_d · τ_t = τ_{3t} · o_d`  (`tau_conj_odd`), independent of `d`
* `num(u, n+t) = num(u, n) + 3^{a(u)} · t`  (`num_add`) — frozen words act
  linearly on translations.

None of these compares `2^L` to `3^a`.  The `2` and the `3` appear as
*conjugation weights* of the translation module, not as a cycle-product
inequality.

## `3x+d` test

Replace `o_1` by `o_d`.

* `tau_conj_even` is unchanged: the even map is still `x ↦ x/2`.  Even
  conjugation is `d`-blind.
* `tau_conj_odd` is unchanged: odd conjugation scales by `3`, independent of
  `d`.
* `K(u, v, d) = 3^{a(u)} · 2^{L(v)} · d` is homogeneous of degree **one** in
  `d`.  Diagnostic 3 of `CLOSURE.md` does not fire: this is not a `d`-free
  quantity.
* Genuine cycles of `3x+5`, `3x+7`, … satisfy the same identities with their
  own `d`.  The theorem does not exclude them, and is not claimed to.

The object sees `d` and does not pretend that `d = 1` is special.

## `expStep` test

`expStep` agrees with Collatz on odds and replaces the even branch by
`x ↦ 3x/2`.  In `H` that even generator is `eExp = (1,1,0)`, not `e = (0,1,0)`.

* `eExp ≠ e` (immediate).
* The even conjugation law **fails**: `τ_1 · eExp ≠ eExp · τ_2`.  Direct
  computation: left side has `c = 2`, right side has `c = 6`
  (`tau_conj_even_fails_expStep`).  In the group this is the statement that
  `eExp` conjugates translations by `3/2`, not by `1/2`, so the monoid
  relation `τ e = e τ²` has no integer analogue for `eExp`.
* The seed commutator against `o_d` still exists (both maps remain affine), so
  mere noncommutativity does not distinguish expStep.  The discriminator is
  the *weight* of even conjugation.

`middle_commutator` consumes the even generator `e`, i.e. the even branch's
contraction `x ↦ x/2`.  It is not a theorem of the affine law plus a saturated
odd count, so it does not hold of `expStep` upon substituting `eExp` for `e`.

## What the parity word misses

The parity word of `n` is one ray in `{e, o_1}^*`: at each point exactly one
letter is legal.  Three things live off that ray.

1. **The extra generator `τ`.**  No parity word equals `τ_1`.  Commuting an
   odd letter past an even letter is illegal on the dynamical diagonal
   (domains are disjoint: a number is not both even and odd).  The commutator
   exists only after extending `e` and `o_d` to frozen affine maps on all of
   `ℕ`.  `word_realizable` realises every finite word as some start's ray; it
   does not realise `τ`.

2. **The module action.**  A frozen word acts linearly on translations:
   `num(u, n+t) − num(u, n) = 3^{a(u)} · t`.  The dynamical step does not:
   `T(7) = 11` and `T(8) = 4`, and `4 ≠ 11 + 3` (`dynamical_step_not_module`).
   The parity-selected map is not a map of modules.

3. **`n`-independence of `K`.**  Along the dynamical diagonal the letters of
   `u` and `v` *depend on* `n`, so a word-level statistic computed from the
   orbit of `n` is `n`-dependent by construction.  `K` is the defect of two
   *frozen* words, and the theorem is that the defect does not see `n`.

## What expStep misses

expStep saturates `a = L` at every window and conjugates the translation
module by `3/2` on **both** letters.  The two generators become indistinguishable
as linear actions on the module: the even/odd asymmetry of conjugation
(`×1/2` versus `×3`) is exactly the even branch, and expStep has deleted it.
`tau_conj_even` is the named form of that asymmetry, and expStep fails it.

A theorem proved from the affine law, the parity word, heaviness and positivity
alone cannot mention `tau_conj_even`, because that law is false of `eExp`.

## Decisive lemma

**`tau_conj_even`:**  `τ_t · e = e · τ_{2t}` for every `t`.

This is the statement that the even Collatz generator is pure halving on the
translation module.  It is:

* true for every `3x+d` (the even map never depends on `d`);
* false for `expStep` (`eExp` has a `3` in the linear part);
* invisible to the parity word (which never applies `e` and a translation
  through each other);
* not a cycle-product comparison;
* the even-branch contraction that every surviving divergence-half mechanism
  is required to consume.

The insertion theorem `middle_commutator` is this lemma transported across an
arbitrary split, together with the odd conjugation `×3` and the seed defect
`d`.  The `d`-content and the even-branch content live in different slots of
the same monoid (`K` versus `tau_conj_even`), which is why one object hits
both filters without collapsing onto `2^L` versus `3^a`.

## What this is not

* Not `ExtensionClass`.  That file computes `Ext¹ ≅ ℤ/G` and identifies the
  class with `C mod G` — the cycle criterion.  The identities here never
  mention `G`.
* Not `SegmentMonoid.rank_compose`.  Rank still telescopes; this file does
  not multiply local bounds around a cycle.
* Not `RunAlgebra.runA_comm`.  That commutator is `runA(v)·G(u) − runA(u)·G(v)`,
  which is the gap again.  `K` is `3^{a(u)} 2^{L(v)} d`, a conjugation weight
  times `d`.
* Not a Collatz claim.  Every identity holds for every `d`, and the even
  conjugation is a statement about the even *generator*, not about orbits
  reaching `1`.
