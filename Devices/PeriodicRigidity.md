# Periodic labels: rigidity and a sharp defect bound

Date: 2026-09-14.

Follow-up: the [complete defect classification](PeriodicDefectClassification.md)
now determines the exact minimum at every modulus, classifies every
single-defect Boolean label, and proves a sharp inequality for numerical
potentials. That note contains the stronger research result and updated
literature assessment.

The new module is [PeriodicRigidity.lean](../Collatz/Strategy/PeriodicRigidity.lean).
It is imported by the main `Collatz` library. These are unconditional structural
theorems, with a conditional reduction to convergence at the end. They do not
prove the Collatz conjecture. Historical novelty has not been established.

## The quantitative result

Write `T(n)=n/2` for even `n`, and `T(n)=(3n+1)/2` for odd `n`.
Let `f` take values in any type and have positive period `m`:

    f(n+m) = f(n), for every n ≥ 0.

If `f` is nonconstant, there is an integer `r`, with `0<r<2m`, such that

    f(T(r+2mk)) ≠ f(r+2mk), for every k ≥ 0.

Thus every interval of `2m` consecutive nonnegative integers contains a defect.
In particular, there are at least `K` distinct positive defects below `2mK`.
The Lean statements are `defect_progression` and `defect_packing`. The latter
explicitly proves the bounds and injectivity of the `K` witnesses, rather than
using an analytic density library. The usual lower density bound `1/(2m)` is an
immediate mathematical consequence; no separate real-valued limit theorem is
claimed to be formalized.

This bound is sharp for every positive `m` divisible by 3. Take

    f(n) = 1 if m divides n, and 0 otherwise.

Then, exactly,

    f(T(n)) ≠ f(n)  iff  n ≡ m (mod 2m).

This is `divisibleLabel_defect`, quantified over all such moduli and all `n`.
The label is nonconstant and its least positive period is `m`, as proved by
`divisibleLabel_nonconstant` and `divisibleLabel_least_period`. Consequently
the sharpness does not come from artificially enlarging the stated period.
For example, at modulus 6 the defects are precisely `6,18,30,42,…`.

## Why the theorem holds

First suppose there are no defects. The inverse branch identities give

    f(2n)=f(n),
    f(3n+1)=f(n) for odd n.

We prove constancy by strong induction on a period `m`.

* If `m` is even, the doubling identity makes `m/2` a period.
* If `m` is odd, shifting an even input by `m` makes it odd. Periodicity
  therefore extends the second identity to every input.
* If this odd `m` is divisible by 3, the second identity makes `m/3` a period.
* Otherwise `m` is coprime to 6. Applying the two identities in opposite
  orders gives `f(6n+2)=f(6n+1)`. Every residue modulo `m` has a representative
  congruent to 1 modulo 6. Hence `f(n+1)=f(n)` for every `n`.

This is `branch_rigidity`, followed by `invariant_constant`. It requires no
assumption about the behavior of any infinite Collatz trajectory.

Next, the exact branch calculation gives

    T(n+2m) = T(n)+m       if n is even,
    T(n+2m) = T(n)+3m      if n is odd.

The defect predicate therefore has period `2m`. A nonconstant label must have
a defect by rigidity, and that defect repeats on the stated progression.

For sharpness, reduce `n` modulo `2m`. An even input in this interval has
`T(n)<m`, so the divisibility label changes only at `n=m` if `m` is even.
An odd input has `T(n)≡2 (mod 3)`, so its image is never divisible by `m`.
The label changes exactly at the odd multiple `n=m` if `m` is odd.

## A connection to the original conjecture

`eventually_invariant_constant` proves that a label which is invariant on all
positive Collatz steps and periodic beyond any finite threshold is constant
on the positive integers. To remove the finite exceptional region, multiply
both `n` and `n+m` by a sufficiently large power of 2. Invariance under
doubling preserves their labels, and the scaled arguments lie in the region
where periodicity applies.

Applying this to the proposition “n reaches 1” proves

    CollatzConjecture ↔ EventuallyPeriodic Reach.ReachesOne.

This is `collatz_iff_eventually_periodic_basin`, using the repository's actual
standard Collatz orbit definition. Periodicity here concerns membership as
the starting integer varies; it does not mean periodicity of an orbit.
The forward direction has threshold 1. The reverse direction uses the fact
that reaching 1 is an invariant and that 1 reaches itself.

The missing step is proving eventual periodicity of this membership predicate.
Nothing in this module establishes that assumption. Nor does the module rule
out arbitrary finite-valued invariants, binary automata, growing moduli, or
labels with dependence on the magnitude of the input.

The follow-up literature check located [Monks's theorem that every arithmetic
progression is sufficient](https://monks.scranton.edu/files/pubs/SufficiencyRev4.pdf).
The basin equivalence is a consequence of that stronger known theorem and
should not be described as novel.

## Literature and contribution status

[Laarhoven and de Weger (2012), *The Collatz conjecture and De Bruijn graphs*](https://www.deweger.net/papers/%5B52%5DLdW-CollBruijn%5B2012%5D.pdf)
studies modular Collatz graphs and identifies the power-of-two graphs with
binary De Bruijn graphs. Its modulus-3 example also explains why a trajectory
cannot return to multiples of 3 after leaving them.

[Karras and de Weger (2026), *Determinants of modular Collatz graphs and variants*](https://arxiv.org/abs/2601.15463)
studies general moduli. These papers establish that modular graph structure
is prior art. Our proof is direct arithmetic and does not import a graph
connectivity theorem from either paper. In particular it does not assert
strong connectivity for moduli divisible by 3.

The contribution in this repository is the elementary all-modulus Lean proof,
the quantitative defect progression with a sharp family of least-period
examples, and the eventual-periodicity reduction. These were derived and
formalized in this session. The searches performed did not establish priority
for their exact formulation; they should be described as a checked theorem
package, not as a claimed new breakthrough.

## Verification

Toolchain: `leanprover/lean4:v4.33.0-rc1`. No Mathlib dependency.

Commands run successfully:

```sh
lake build Collatz
lake env lean scripts/audit_periodic_rigidity.lean
bash scripts/check_integrity.sh
git diff --check
```

The initial integrated build completed with 387 jobs; the follow-up adds three
more modules. Existing unrelated modules emit warnings; the new modules compile
without warnings. The expanded audit covers 23 main endpoints. Their dependencies are subsets of `propext`, `Quot.sound`,
and `Classical.choice`. There are no added axioms, `sorry`, `admit`, or
`native_decide` in the module. The proofs cover unbounded inputs and moduli;
they are not finite numerical checks of the conjecture.
