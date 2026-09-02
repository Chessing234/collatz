# Mathlib devices for Collatz

This is the Mathlib-attack branch.  The root `Collatz` library stays Mathlib-free;
nothing here is imported by it.  The question is: **which Mathlib structures can
actually host a Collatz device**, meaning a type that the no-Mathlib branch cannot
name, on which the Collatz / Syracuse map lives as a native object.

Searched locally against mathlib `v4.33.0-rc1` (the `lakefile.toml` pin).  The
package builds.

## The one device that needs Mathlib

### Device 1 — 2-adic Syracuse on odd `PadicInt`

**Host.** `PadicInt 2`, notation `ℤ_[2]`.  Defined in
`Mathlib.NumberTheory.Padics.PadicIntegers` as `{x : ℚ_[2] // ‖x‖ ≤ 1}`.  This is
a complete DVR, a compact local ring, and the inverse limit of `ZMod (2^n)`.

**Odd locus.** Units `(ℤ_[2])ˣ`.  Equivalent characterisations already in mathlib:

* `PadicInt.isUnit_iff`: `IsUnit x ↔ ‖x‖ = 1`
* `PadicInt.valuation = 0`
* `PadicInt.toZMod` lands in `(ZMod 2)ˣ`

**The map.** For `x` with `3x + 1 ≠ 0` (i.e. `x ≠ -1/3` in `ℤ_[2]`),

```
S x  :=  (3x + 1) / 2^{v₂(3x+1)}
```

Mathlib already has this as `PadicInt.unitCoeff`: the unit `u` in the unique
writing `y = u * p^{v_p(y)}`.  That is the Syracuse stripping, as a function on a
type that does not exist without Mathlib.

Implemented in `MathlibAttack/SyracusePadic.lean`.  One lemma:
`S_ne_three_mul_div_two` — on every odd `x`, `S x` is a unit (`‖S x‖ = 1`) while
`3x/2` has 2-adic norm `2`, so they disagree as maps into `ℚ_[2]`.  On `ℕ` the
comparison cannot even be stated: for odd `n`, `3n/2` is not an integer.

**Why this needs Mathlib, not just `padicValNat`.**  `Basic.lean` already uses
`padicValNat` and `ZMod (2^k)` to name residue classes.  Those are *finite-level*
facts, and the no-Mathlib branch can (and does) replicate them.  What it cannot
replicate is:

* the type `ℤ_[2]` itself (uncountable, complete);
* a single function `S : {x : ℤ_[2]ˣ // 3x+1 ≠ 0} → ℤ_[2]ˣ` restricting to the
  Syracuse map on odd `ℕ`;
* continuity of `S` for the 2-adic topology;
* compactness of the domain (`PadicInt.compactSpace` in
  `Mathlib.NumberTheory.Padics.ProperSpace`);
* the inverse-limit universal property `PadicInt.lift`, which packages a
  compatible family `R → ZMod (2^n)` into one map `R → ℤ_[2]`.

That last point is the Terras bijection at infinity: the finite-level parity-word
bijections `ZMod (2^N) ≃ (Fin N → Bool)` of `Basic.lean` are the projections of
one map on `ℤ_[2]`.

**What this device is not.**  It is not a cycle-killing machine.  The root
`RESEARCH.md` already closed simultaneous `p`-adic cycle obstruction (Hasse is
vacuous: one linear equation in one unknown).  Periodic points of `S` on `ℤ_[2]`
include the integer cycles *and* a huge supply of purely 2-adic cycles that are
not in `ℕ`.  Compactness gives existence of periodic points and invariant
measures; it does not separate the integer ones.  The Bernstein–Lagarias map `Φ`
and the Periodicity Conjecture live on this type, and they are Collatz-hard.

### Device 2 — the same object as an inverse limit / adic completion

**Host.** Either of:

* `PadicInt.lift` / `PadicInt.toZModPow`
  (`Mathlib.NumberTheory.Padics.RingHoms`): `ℤ_[p]` is the inverse limit of
  `ZMod (p^n)` in rings;
* `AdicCompletion (Ideal.span {(2 : ℤ)}) ℤ`
  (`Mathlib.RingTheory.AdicCompletion.Basic`): the abstract `I`-adic inverse
  limit `{ f : ∀ n, M ⧸ I^n M // compatibility }`.

These *are* `ℤ_[2]`, under a different constructor.  The reason to name them
separately is the universal property: a Collatz-related family of compatible maps
on `ZMod (2^n)` (Terras, the affine law, residue-class criteria for `v₂(3n+1)`)
assembles uniquely into a map on the completion.  That sentence cannot be said in
the no-Mathlib library, which has no inverse-limit type.

`WittVector 2 (ZMod 2)` (`Mathlib.RingTheory.WittVector`) is a *third*
presentation of the same ring: `WittVector.equiv : 𝕎 (ZMod p) ≃+* ℤ_[p]`, built
exactly by comparing both sides as inverse limits of `ZMod (p^n)`.  It is not a
second device.  See the decorative list below.

Prefer `PadicInt` over raw `AdicCompletion` for any actual proof: the PadicInt
API has the valuation, the norm, `unitCoeff`, `toZModPow`, and compactness.
`AdicCompletion` has the universal property and not much else that Collatz can
use.

---

## Object-by-object

| Mathlib object | Verdict | Why |
|---|---|---|
| **`Padic` / `PadicInt`** | **Helps — this is the host** | The type `ℤ_[2]` is the device.  `unitCoeff` is Syracuse.  Compact DVR, inverse limit of `ZMod (2^n)`.  Nothing in the no-Mathlib branch can name it. |
| **`PadicInt.valuation` / `Valuation`** | **Helps — as the stripping exponent** | Needed to *state* `S` on `ℤ_[2]`.  The `ℕ`-valued `padicValNat` is already used in `Basic.lean` (residue-class criterion, LTE); that part does *not* need the type `ℤ_[2]`. |
| **`PadicInt.lift` / inverse limits** | **Helps — universal property of the host** | Assembles the Terras system into one map.  This is Device 2, not a different map. |
| **`AdicCompletion`** | **Helps — abstract packaging of the same host** | `AdicCompletion (span {2}) ℤ` is `ℤ_[2]` without the analytic API.  Use `PadicInt` in proofs; cite `AdicCompletion` when the point is the inverse-limit constructor. |
| **`Ideal`** | **Plumbing, not a host** | `ker toZModPow n = span {p^n}`, `maximalIdeal = span {p}`.  Needed to *talk about* the inverse system.  An ideal of `ℤ` or `ℤ_[2]` does not carry a Collatz map. |
| **`CompactSpace`** | **Theorem about the host, not a host** | `PadicInt.compactSpace : CompactSpace ℤ_[p]`.  This is why one *wants* `PadicInt` (dynamics, Haar, periodic points).  The class `CompactSpace` itself does not host the map. |
| **`WittVec`** | **Decorative (isomorphic coordinates)** | `WittVector p (ZMod p) ≃ ℤ_[p]`.  Extra structure — Frobenius, Verschiebung, ghost components, Teichmüller — does not see `3x+1`.  Witt polynomials are an internal encoding of carrying; they do not give a Collatz identity. |
| **`MvPolynomial`** | **Decorative** | Used internally to *define* Witt addition/multiplication.  No Collatz content.  A generating-function encoding of the affine law can be written without Mathlib. |
| **`FilteredRing` / `IsRingFiltration`** | **Decorative** | Abstract graded-monoid filtration.  The 2-adic filtration on `ℤ_[2]` is already the DVR filtration `span {2^n}`, available without this class. |
| **`WellFounded`** | **Decorative as a Mathlib device** | Collatz ⇔ well-foundedness of the inverse graph on `ℕ \ {1}` is a Lean-core statement.  Mathlib's well-founded API does not supply a host, a valuation, or a compactness argument.  The no-Mathlib branch already has this reduction (`NeverDrops`). |
| **`Quiver`** | **Decorative** | One can view `n ⟶ T(n)` as a quiver.  `Quiver` is the substrate of category theory; it does not know `v₂` or `3x+1`.  The inverse tree is already an inductive type in the no-Mathlib branch. |
| **`MonoidAlgebra`** | **Decorative** | Finite formal linear combinations with convolution.  A generating function for the affine law is a `ℕ`-indexed sum, not naturally an element of `R[M]` in a way that proves anything.  Group rings do not see the Collatz step. |

---

## What to build next (on this branch only)

1. Continuity of `S` on `{x : ℤ_[2]ˣ // 3x+1 ≠ 0}` (local constancy on residue
   classes `n ≡ -3⁻¹ (mod 2^k)`, which is `le_padicValNat_iff_residue` from
   `Basic.lean` lifted through `toZModPow`).
2. Compatibility: `toZModPow n ∘ S = S_n ∘ toZModPow n` for the finite-level
   Syracuse maps — i.e. `S` really is the inverse limit of Terras.
3. Do **not** chase periodic points of `S` as a Collatz proof.  They mix integer
   cycles with 2-adic-only cycles; compactness will not separate them.

Items 1–2 are genuine Mathlib work.  They still do not imply Collatz.
