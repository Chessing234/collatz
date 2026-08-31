import Collatz.Strategy.HarvestSplit
import Collatz.Structure.Density

/-!
# The one place the 2-adic data and the size are visible together

Built to specification: a relation mentioning both `v₂(n+1)` and the archimedean
size of `n`, at a contraction, and surviving the test that killed every previous
candidate.

## The test, and the quantity that passes it

`n` and `n + 2^M` have the **same parity word for `M` steps**
(`parityVector_mod_pow_two`).  So every function of the parity word alone, and every
function of `u = n+1` modulo a high power of two, is blind to the difference between
them.  That is the mission's test, and it is what kills purely `2`-adic devices.

What is *not* blind is the orbit value itself.  `perturb_orbit`:

**`T^j(n + 2^M) = T^j(n) + 3^(a_j) · 2^(M−j)`  for `j ≤ M`,**  `a_j = oddCount n j`.

Proved by induction, with no appeal to `affineC`: for `j < M` the offset
`3^(a_j)·2^(M−j)` is even, so the two orbits have the *same parity at every step* —
which is why the words agree — and the offset transforms by `/2` on an even step and
by `·3/2` on an odd one.

Cleared of division (`perturb_scaled`):

**`2^j · T^j(n + 2^M) = 2^j · T^j(n) + 2^M · 3^(a_j)`.**

This is the relation the mission asks for.  It mentions `a_j` — the `2`-adic datum,
identical for the two starting points — and `2^M`, the archimedean size difference,
in one exact identity.  **It is not invariant under `n ↦ n + 2^M`**: the two sides
differ by exactly `2^M · 3^(a_j)`, which is never zero.  So the device sees precisely
what the parity word cannot.

The consequence worth naming: the *scaled deficit* `D_j(n) = 2^j·(n − T^j(n))`
satisfies `D_j(n + 2^M) − D_j(n) = 2^M·(2^j − 3^(a_j))`, verified exactly for
`M ≤ 12`, `n < 400`, `j ≤ M`.  The sign of the shift is the sign of `2^j − 3^(a_j)`
— the classical heavy/light dichotomy — and its *magnitude* is the archimedean
`2^M`.  Two-adic data fixes the direction; size fixes the amount.

## The target shape

`v₂(n+1) = 1` is exactly `n ≡ 1 (mod 4)`: by Terras the odd run has length one, so a
single growth step is followed immediately by a contraction.  There the two steps
compose to an exact affine law (`drop_of_v2_one`):

**`n ≡ 1 (mod 4)  →  4 · T²(n) = 3n + 1`,**

hence `T²(n) < n` for every `n > 1` (`drop_of_v2_one_lt`), and the drop is
`n − T²(n) = (n−1)/4` — **proportional to `n`, not bounded**.  That proportionality
is the archimedean content: a shallow run does not merely fail to grow, it loses a
fixed *fraction* of the size.

Verified for every odd `n < 40 000` with `v₂(n+1) = 1`: no exceptions.

## What it does not do

It does not iterate.  `drop_of_v2_one` fires only when `v₂(n+1) = 1`, which is half
of odd `n`; the other half has longer runs and can grow, and `no_uniform_block`
already proves no bounded block descends for all `n`.  The perturbation law relates
two starting points with the same word, and says nothing about a single orbit whose
word is not given.

What is new is that the two kinds of information appear in one exact identity, with
the `2`-adic part setting the sign and the archimedean part setting the magnitude —
the first relation in this development that survives the `n ↦ n + 2^M` test.
-/

namespace Collatz
namespace SizePerturbation

/-- One step, with the start shifted by an even amount: the shift halves. -/
theorem step_shift_even {X E : Nat} (hX : X % 2 = 0) :
    acceleratedStep (X + 2 * E) = acceleratedStep X + E := by
  rw [acceleratedStep, if_pos (by omega), acceleratedStep, if_pos hX]
  omega

/-- One step, with the start shifted by an even amount: the shift triples. -/
theorem step_shift_odd {X E : Nat} (hX : X % 2 = 1) :
    acceleratedStep (X + 2 * E) = acceleratedStep X + 3 * E := by
  rw [acceleratedStep, if_neg (by omega), acceleratedStep, if_neg (by omega)]
  omega

/-- **The perturbation law.**  Adding `2^M` to the start displaces the orbit by
`3^(a_j)·2^(M−j)` for the first `M` steps, and does not change a single parity bit. -/
theorem perturb_orbit (n M : Nat) : ∀ j : Nat, j ≤ M →
    acceleratedOrbit j (n + 2 ^ M)
      = acceleratedOrbit j n + 3 ^ oddCount n j * 2 ^ (M - j) := by
  intro j
  induction j with
  | zero => intro _; simp
  | succ j ih =>
    intro hj
    have hprev := ih (by omega)
    have hpow : (2 : Nat) ^ (M - j) = 2 ^ (M - (j + 1)) * 2 := by
      have hMj : M - j = (M - (j + 1)) + 1 := by omega
      rw [hMj, Nat.pow_succ]
    have hE : 3 ^ oddCount n j * 2 ^ (M - j)
        = 2 * (3 ^ oddCount n j * 2 ^ (M - (j + 1))) := by
      rw [hpow]
      simp [Nat.mul_comm, Nat.mul_left_comm, Nat.mul_assoc]
    rw [acceleratedOrbit_succ_step j (n + 2 ^ M), acceleratedOrbit_succ_step j n,
      hprev, hE, Density.oddCount_succ_last]
    rcases Arith.mod_two_eq_zero_or_one (acceleratedOrbit j n) with he | ho
    · rw [step_shift_even he, he]
      simp
    · rw [step_shift_odd ho, ho]
      have h3 : (3 : Nat) ^ (oddCount n j + 1) = 3 * 3 ^ oddCount n j := by
        rw [Nat.pow_succ]; omega
      rw [h3]
      simp [Nat.mul_comm, Nat.mul_left_comm, Nat.mul_assoc]

/-- The same, cleared of division: the archimedean shift `2^M` and the `2`-adic
datum `a_j` in one identity. -/
theorem perturb_scaled {n M j : Nat} (hj : j ≤ M) :
    2 ^ j * acceleratedOrbit j (n + 2 ^ M)
      = 2 ^ j * acceleratedOrbit j n + 2 ^ M * 3 ^ oddCount n j := by
  rw [perturb_orbit n M j hj, Nat.mul_add]
  have hsplit : (2 : Nat) ^ M = 2 ^ j * 2 ^ (M - j) := by
    rw [← Nat.pow_add]
    congr 1
    omega
  rw [hsplit]
  simp [Nat.mul_comm, Nat.mul_left_comm, Nat.mul_assoc]

/-! ## The target shape -/

/-- **`v₂(n+1) = 1` gives an exact two-step affine law.**  `n ≡ 1 (mod 4)` is
Terras' statement that the odd run has length one, so one growth step is followed
immediately by a contraction, and the pair composes to `4·T²(n) = 3n + 1`. -/
theorem drop_of_v2_one {n : Nat} (h : n % 4 = 1) :
    4 * acceleratedOrbit 2 n = 3 * n + 1 := by
  have e2 : acceleratedOrbit 2 n = acceleratedStep (acceleratedStep n) := by
    rw [acceleratedOrbit_succ_step 1 n, acceleratedOrbit_succ_step 0 n]
    rfl
  have h1 : acceleratedStep n = (3 * n + 1) / 2 := by
    rw [acceleratedStep, if_neg (by omega)]
  have h2 : ((3 * n + 1) / 2) % 2 = 0 := by omega
  rw [e2, h1, acceleratedStep, if_pos h2]
  omega

/-- **Hence a strict drop, proportional to the size.**  `n − T²(n) = (n−1)/4`. -/
theorem drop_of_v2_one_lt {n : Nat} (h : n % 4 = 1) (hn : 1 < n) :
    acceleratedOrbit 2 n < n := by
  have := drop_of_v2_one h
  omega

/-- The drop, named: four times the loss is `n − 1`. -/
theorem drop_amount {n : Nat} (h : n % 4 = 1) :
    4 * n - 4 * acceleratedOrbit 2 n = n - 1 := by
  have := drop_of_v2_one h
  omega

end SizePerturbation
end Collatz
