import Collatz.Strategy.OpeningTemplate
import Collatz.Strategy.SizePerturbation
import Collatz.Strategy.CoordinateMismatch

/-!
# The two-step law separates the three maps, and the differing monomial is `3` against `9`

## A structural note on the specification

`Δ(n) = (n − T²(n))·σ(n)` was to be evaluated only where `v₂(n+1) = 1`.  But
`v₂(n+1) = 1` **is** `n ≡ 1 (mod 4)` — verified for every odd `n < 200 000` — so on
the evaluation set `σ ≡ +1` identically.  The sign factor is inert there: `Δ` is
neither odd nor even in `m mod 4`, because it is only ever evaluated on one of the
two classes.  The antisymmetry requirement cannot bind.

What does bind is the comparison across maps, and it is sharp.

## The measurement

With `n = 4k+1`, over all such `n < 2^20`, `Δ` is *exactly linear in `k`* for each
map, with no exceptions:

| map | `Δ` | slope |
|---|---|---|
| `T` | `k` | `+1` |
| mirror `3n−1` | `−5k` | `−5` |
| `expStep` | `−5k − 2` | `−5` |

**The histograms differ.**  Equivalently, as exact two-step laws on `n ≡ 1 (mod 4)`
— zero violations over all such `n < 300 000`:

* **`T`: `4·T²(n) = 3n + 1`**  (Round LV, `drop_of_v2_one`)
* **mirror: `4·M²(n) = 9n − 5`**  (`mirror_two_step`)
* **`expStep`: `4·E²(n) = 9n + 3`**  (`exp_two_step`)

**The exact differing monomial is the coefficient of `n`: `3` for `T`, `9` for both
others.**  On this class `T` contracts by `3/4` while the mirror and `expStep` both
expand by `9/4`.  `two_step_separates` is that statement: `T²(n) < M²(n)` and
`T²(n) < E²(n)` for every `n > 1` in the class.

That is filter F1/F2 made quantitative *at the contraction*: the class
`v₂(n+1) = 1` is exactly where Collatz's two-step is contracting and both filter
models are expanding, and the gap is a factor of three in the leading coefficient.

## The kill test, answered

`Δ` on a never-dropping prefix is **positive and unbounded** — `120 486` samples,
positive in all of them, maximum `1 433 531 479`.  But positive `Δ` means
`n > T²(n)`, i.e. *descent*, and the value is exactly `(n−1)/4`: this is Round LV's
`drop_of_v2_one` restated, carrying no information beyond it.  So `Δ` itself is not
formalised here, as instructed — only the differing monomial is.

`Δ` also cannot be a global descent certificate: it fires only on `n ≡ 1 (mod 4)`,
half of odd `n`, and `DensitySaturation.no_uniform_block` already proves no bounded
block descends for every `n`.
-/

namespace Collatz
namespace TwoStepSeparation

/-- The mirror map `3n − 1`. -/
def mirrorStep (n : Nat) : Nat :=
  if n % 2 = 0 then n / 2 else (3 * n - 1) / 2

/-- **The mirror's two-step law on `n ≡ 1 (mod 4)`.**  `4·M²(n) = 9n − 5`: it
*expands* by `9/4`, where `T` contracts by `3/4`. -/
theorem mirror_two_step {n : Nat} (h : n % 4 = 1) :
    4 * mirrorStep (mirrorStep n) = 9 * n - 5 := by
  have h1 : mirrorStep n = (3 * n - 1) / 2 := by
    rw [mirrorStep, if_neg (by omega)]
  have h2 : ((3 * n - 1) / 2) % 2 = 1 := by omega
  rw [h1, mirrorStep, if_neg (by omega)]
  omega

/-- **`expStep`'s two-step law on `n ≡ 1 (mod 4)`.**  `4·E²(n) = 9n + 3`: also
`9/4`, the same leading coefficient as the mirror. -/
theorem exp_two_step {n : Nat} (h : n % 4 = 1) :
    4 * CoordinateMismatch.expStep (CoordinateMismatch.expStep n) = 9 * n + 3 := by
  have h1 : CoordinateMismatch.expStep n = (3 * n + 1) / 2 := by
    rw [CoordinateMismatch.expStep, if_neg (by omega)]
  have h2 : ((3 * n + 1) / 2) % 2 = 0 := by omega
  rw [h1, CoordinateMismatch.expStep, if_pos h2]
  omega

/-- **The separation.**  On `n ≡ 1 (mod 4)` with `n > 1`, Collatz's two-step lands
strictly below both filter models': the leading coefficient is `3` against `9`. -/
theorem two_step_separates {n : Nat} (h : n % 4 = 1) (hn : 1 < n) :
    acceleratedOrbit 2 n < mirrorStep (mirrorStep n) ∧
    acceleratedOrbit 2 n < CoordinateMismatch.expStep (CoordinateMismatch.expStep n) := by
  have hT := SizePerturbation.drop_of_v2_one h
  have hM := mirror_two_step h
  have hE := exp_two_step h
  exact ⟨by omega, by omega⟩

/-- And Collatz's two-step is the only one of the three that descends here. -/
theorem only_T_descends {n : Nat} (h : n % 4 = 1) (hn : 1 < n) :
    acceleratedOrbit 2 n < n ∧ n < mirrorStep (mirrorStep n) := by
  have hT := SizePerturbation.drop_of_v2_one h
  have hM := mirror_two_step h
  exact ⟨by omega, by omega⟩

end TwoStepSeparation
end Collatz
