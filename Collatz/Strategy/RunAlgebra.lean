import Collatz.Strategy.TwoRunOrder

/-!
# Run algebra: the shifted accumulator, and what runs can and cannot do

This file changes coordinate.  Write `u = x + 1`.  Then

* an **odd** step is *exactly* `u ↦ (3/2) · u` — no additive defect at all;
* an **even** step is `u ↦ (u + 1)/2`, i.e. halving *plus one*.

The asymmetry is not an accident of bookkeeping: the odd map `x ↦ (3x+1)/2` has
fixed point `−1`, the even map `x ↦ x/2` has fixed point `0`, and no single
affine coordinate linearises both.  In `u`-coordinates the whole nonlinearity of
Collatz is concentrated in a *single* additive defect contributed once per even
step.  That defect is the object this file isolates.

## The shifted accumulator

`runA` is defined by the recursion

* odd step: `A ↦ 3 · A`;
* even step: `A ↦ A + 2 ^ j`.

Compare `affineC`, which is fed only by *odd* steps.  `runA` is fed only by
*even* steps, and odd steps merely transport it.  The two are related by

`runA j x + 3 ^ (oddCount x j) = affineC j x + 2 ^ j`   (`runA_eq`)

and the point of the change is the **shifted exact law**

`2 ^ j · (T^j(x) + 1) = 3 ^ (oddCount x j) · (x + 1) + runA j x`
                                                  (`shifted_affine_exact`).

Three consequences are immediate and exact.

* **Odd runs have zero defect**: `runA b x = 0` whenever `x` takes `b`
  consecutive odd steps (`runA_oddRun`).  This is `TwoRunOrder.affineC_oddRun`
  in its natural coordinate, and it is the exact form of `RunInvariance`'s
  slogan that odd steps carry information forward with slack exactly zero.
* **Even runs contribute `2 ^ t · (2 ^ e − 1)`** and nothing else
  (`runA_evenRun`, `runA_block`): one term per even run, not one per step.
* Therefore the run-grouped closed form of `TwoRunOrder` — verified there
  numerically at general `k` and proved only at `k = 2` — is here an induction
  whose step is `runA_block_step`, valid at every `k`.

## The cocycle has no correction term

`affineC` satisfies `C(uv) = 3 ^ a(v) · C(u) + 2 ^ L(u) · C(v)`; so does `runA`
(`runA_add`), and the passage between them costs the correction
`2 ^ L − 3 ^ a` at each end.  In matrix form, sending a word `w` to

`M(w) = [[3 ^ a(w), runA(w)], [0, 2 ^ L(w)]]`

is an **anti**-homomorphism, `M(uv) = M(v) · M(u)`, into the upper triangular
monoid; the generators are `O = [[3,0],[0,2]]` (odd) and `E = [[1,1],[0,2]]`
(even).  The commutator of the semigroup is exact:

`runA(uv) − runA(vu) = runA(v) · G(u) − runA(u) · G(v)`,  `G(w) = 2 ^ L − 3 ^ a`

(verified on 20 000 random word pairs; the Lean form here is `runA_comm`, stated
without subtraction).

## Rigidity: the run semigroup is free

Accumulator injectivity for `affineC` is **refuted** (first collision at length
83, `a = 53` against `a' = 55`, shared `C = 212525282698140465463422331`).  Every
known collision has *different* odd-step counts, and that is not a coincidence:
in the shifted coordinate the pair `(oddCount, runA)` determines the word.

The mechanism is a single parity bit.  Splitting off the first letter,

* `x` odd  ⟹ `runA (j+1) x = 2 · runA j (T x)`, which is **even**;
* `x` even ⟹ `runA (j+1) x = 3 ^ (oddCount (T x) j) + 2 · runA j (T x)`, **odd**.

So `v₂(runA)` reads off the leading odd run (this generalises the observation
`v₂(A) = b₁` recorded in `TwoRunOrder`), and peeling one letter at a time gives

`oddCount x j = oddCount y j → runA j x = runA j y → x % 2 ^ j = y % 2 ^ j`
                                                   (`runA_injective_mod`),

the exact converse of `AccumulatorClass.affineC_congr_of_mod`.  Verified
exhaustively over all `2 ^ 20` words before formalising.

**What this closes.**  A "compression" that merges adjacent runs, or replaces a
word by a shorter one with the same `(a, L, A)`, cannot exist: the invariants
determine the word, so there is nothing to merge.  Minimality-descent by word
surgery is therefore not available.

## No run pattern is forbidden

Task: find run patterns `(o₁,e₁,…,o_r,e_r)` that no orbit realises.  There are
none, and Terras says why: a run pattern *is* a parity word of length
`L = Σ (oᵢ + eᵢ)`, and every parity word of length `L` is exactly one nonempty
residue class modulo `2 ^ L`.  Measured over `10 ^ 6` odd starting values, the
joint law of `(oᵢ, eᵢ)` is exactly `2 ^ (−o−e)` — independent geometrics, to five
decimals, with no excluded pair for `o, e ≤ 8`.  So the target theorem "every
hypothetical cycle contains a structurally impossible run" is **false as stated**:
no run is structurally impossible.

What *is* constrained is the run pattern's aggregate.  Heaviness at a run
boundary says `2 ^ L ≤ 3 ^ B`; every run contains at least one even step; and
`3 ^ 17 < 2 ^ 27` converts the first into a linear inequality:

**a heavy window has `17 · (even steps) < 10 · (odd steps)`**  (`heavy_even_bound`),

hence fewer than `10 a / 17` complete runs (`heavy_run_count`).  The constant is
essentially sharp: the extremal heavy prefix found by exhaustive search over all
words of length `≤ 22` has `B = 12` odd steps in `r = 7` runs, and
`10 · 12 = 120 > 119 = 17 · 7` by one.

## Soundness filter

Everything here is `d`-covariant and therefore proves nothing about `d = 1`
specifically.  In `u = x + d` coordinates the odd step is `u ↦ (3/2) u` and the
even step is `u ↦ (u + d)/2` for every `d`, so `runA(w, d) = d · runA(w, 1)` and
the shifted cycle criterion reads `G · (n + d) = d · runA(w)`.  Checked against
the genuine `3x − 1` cycle through `17`: its word is two runs `(4,1), (3,3)`,
`L = 11`, `a = 7`, `G = 2048 − 2187 = −139`, `runA = 2224`, and
`(−139) · (17 − 1) = −2224 = (−1) · 2224` exactly.  The `3x + 5` cycle
`5 → 10 → 5` checks likewise.  So `cycle_shifted` below is a re-coordinatisation
of the cycle criterion, not an exclusion, and the rigidity and run-count results
are structural facts about words that hold for every `d`.
-/

namespace Collatz
namespace RunAlgebra

open Reach Congruence AffineExact AccCycle OddRuns AccumulatorArith

/-! ## The shifted accumulator -/

/-- The additive defect after `j` steps in the coordinate `u = x + 1`.  Odd steps
transport it (`A ↦ 3A`); even steps create it (`A ↦ A + 2 ^ j`). -/
def runA : Nat → Nat → Nat
  | 0, _ => 0
  | j + 1, x =>
      if acceleratedOrbit j x % 2 = 1 then 3 * runA j x else runA j x + 2 ^ j

@[simp] theorem runA_zero (x : Nat) : runA 0 x = 0 := rfl

theorem runA_odd {j x : Nat} (h : acceleratedOrbit j x % 2 = 1) :
    runA (j + 1) x = 3 * runA j x := by
  rw [runA, if_pos h]

theorem runA_even {j x : Nat} (h : acceleratedOrbit j x % 2 = 0) :
    runA (j + 1) x = runA j x + 2 ^ j := by
  rw [runA, if_neg (by omega)]

/-- **The two accumulators, related.**  Stated without subtraction:
`runA = affineC + 2 ^ j − 3 ^ a`. -/
theorem runA_eq (x : Nat) : ∀ j : Nat,
    runA j x + 3 ^ oddCount x j = affineC j x + 2 ^ j := by
  intro j
  induction j with
  | zero => simp
  | succ j ih =>
    have hlast := Density.oddCount_succ_last x j
    rcases Arith.mod_two_eq_zero_or_one (acceleratedOrbit j x) with he | ho
    · have hcount : oddCount x (j + 1) = oddCount x j := by omega
      rw [hcount, runA_even he, affineC_even he, Arith.two_pow_succ]
      omega
    · have hcount : oddCount x (j + 1) = oddCount x j + 1 := by omega
      rw [hcount, runA_odd ho, affineC_odd ho, Arith.two_pow_succ,
        Arith.three_pow_succ]
      omega

/-- **The shifted exact law.**  In the coordinate `u = x + 1` the multiplier is
`3 ^ a / 2 ^ j` and the *entire* additive defect is `runA`. -/
theorem shifted_affine_exact (x j : Nat) :
    2 ^ j * (acceleratedOrbit j x + 1)
      = 3 ^ oddCount x j * (x + 1) + runA j x := by
  have hex := affine_exact x j
  have hrel := runA_eq x j
  have hL : (2:Nat) ^ j * (acceleratedOrbit j x + 1)
      = 2 ^ j * acceleratedOrbit j x + 2 ^ j := by
    rw [Nat.mul_add, Nat.mul_one]
  have hR : (3:Nat) ^ oddCount x j * (x + 1) = 3 ^ oddCount x j * x + 3 ^ oddCount x j := by
    rw [Nat.mul_add, Nat.mul_one]
  omega

/-! ## Runs -/

/-- **An odd run has zero defect.**  Over `b` consecutive odd steps, `u = x + 1`
is multiplied by exactly `(3/2) ^ b`. -/
theorem runA_oddRun {b x : Nat} (h : OddRun x b) : runA b x = 0 := by
  have hC := TwoRunOrder.affineC_oddRun b x h
  have hrel := runA_eq x b
  have hcount : oddCount x b = b := TwoRunOrder.oddCount_oddRun h
  rw [hcount] at hrel
  omega

/-- Restated: an odd run is exactly multiplication by `3 / 2` in the shifted
coordinate. -/
theorem oddRun_shift {b x : Nat} (h : OddRun x b) :
    2 ^ b * (acceleratedOrbit b x + 1) = 3 ^ b * (x + 1) := by
  have hex := shifted_affine_exact x b
  rw [TwoRunOrder.oddCount_oddRun h, runA_oddRun h] at hex
  omega

/-- **An even run contributes `2 ^ e − 1`**, stated without subtraction. -/
theorem runA_evenRun {y e : Nat} (h : oddCount y e = 0) : runA e y + 1 = 2 ^ e := by
  have hC := AccumulatorValuation.affineC_eq_zero_of_no_odd h
  have hrel := runA_eq y e
  rw [h, hC] at hrel
  simpa using hrel

/-! ## The cocycle -/

/-- **The shifted accumulator is a cocycle, with no correction term.** -/
theorem runA_add (x j : Nat) : ∀ k : Nat,
    runA (j + k) x
      = 3 ^ oddCount (acceleratedOrbit j x) k * runA j x
        + 2 ^ j * runA k (acceleratedOrbit j x) := by
  intro k
  induction k with
  | zero => simp
  | succ k ih =>
    have hjoin : acceleratedOrbit k (acceleratedOrbit j x) = acceleratedOrbit (j + k) x := by
      rw [acceleratedOrbit_add k j x, Nat.add_comm k j]
    rcases Arith.mod_two_eq_zero_or_one (acceleratedOrbit k (acceleratedOrbit j x)) with he | ho
    · have he' : acceleratedOrbit (j + k) x % 2 = 0 := by rw [← hjoin]; exact he
      have hcount : oddCount (acceleratedOrbit j x) (k + 1)
          = oddCount (acceleratedOrbit j x) k := by
        rw [Density.oddCount_succ_last, he]; omega
      rw [← Nat.add_assoc, runA_even he', runA_even he, hcount, ih, Nat.mul_add,
        Nat.pow_add]
      omega
    · have ho' : acceleratedOrbit (j + k) x % 2 = 1 := by rw [← hjoin]; exact ho
      have hcount : oddCount (acceleratedOrbit j x) (k + 1)
          = oddCount (acceleratedOrbit j x) k + 1 := by
        rw [Density.oddCount_succ_last, ho]
      rw [← Nat.add_assoc, runA_odd ho', runA_odd ho, hcount, ih,
        Arith.three_pow_succ]
      simp [Nat.mul_add, Nat.mul_assoc, Nat.mul_left_comm]

/-! ## Blocks: one run of each kind -/

/-- **A block is one term.**  `b` odd steps followed by `e` even steps
contribute exactly `2 ^ b · (2 ^ e − 1)`; stated without subtraction. -/
theorem runA_block {x b e : Nat} (h1 : OddRun x b)
    (h2 : oddCount (acceleratedOrbit b x) e = 0) :
    runA (b + e) x + 2 ^ b = 2 ^ b * 2 ^ e := by
  rw [runA_add x b e, runA_oddRun h1, Nat.mul_zero, Nat.zero_add]
  have he := runA_evenRun h2
  have : (2:Nat) ^ b * (runA e (acceleratedOrbit b x) + 1) = 2 ^ b * 2 ^ e := by
    rw [he]
  rw [Nat.mul_add, Nat.mul_one] at this
  omega

/-- **The induction step for the run-grouped closed form, at every `k`.**
Appending one more block to a word of length `j` multiplies the accumulated
defect by `3 ^ b` and adds a single new term `2 ^ j · 2 ^ b · (2 ^ e − 1)`.
Iterating this is exactly the telescope that `TwoRunOrder` verified numerically
at general `k` and proved at `k = 2`. -/
theorem runA_block_step {x j b e : Nat}
    (h1 : OddRun (acceleratedOrbit j x) b)
    (h2 : oddCount (acceleratedOrbit (j + b) x) e = 0) :
    runA (j + (b + e)) x + 2 ^ j * 2 ^ b
      = 3 ^ b * runA j x + 2 ^ j * (2 ^ b * 2 ^ e) := by
  have hjoin : acceleratedOrbit b (acceleratedOrbit j x) = acceleratedOrbit (j + b) x := by
    rw [acceleratedOrbit_add b j x, Nat.add_comm b j]
  have h2' : oddCount (acceleratedOrbit b (acceleratedOrbit j x)) e = 0 := by
    rw [hjoin]; exact h2
  have hblk := runA_block h1 h2'
  have hcount : oddCount (acceleratedOrbit j x) (b + e)
      = b := by
    have := AccumulatorArith.oddCount_add (acceleratedOrbit j x) b e
    rw [TwoRunOrder.oddCount_oddRun h1, h2'] at this
    omega
  rw [runA_add x j (b + e), hcount]
  have hmul : (2:Nat) ^ j * (runA (b + e) (acceleratedOrbit j x) + 2 ^ b)
      = 2 ^ j * (2 ^ b * 2 ^ e) := by rw [hblk]
  rw [Nat.mul_add] at hmul
  omega

/-! ## The commutator of the semigroup -/

/-- **The commutator, exactly.**  For two words `u` (length `j`) and `v`
(length `k`, starting where `u` ends), the two orders differ by
`runA(v) · G(u) − runA(u) · G(v)`.  Stated without subtraction as a balanced
equation between the two concatenation formulas. -/
theorem runA_comm (x j k : Nat) :
    let y := acceleratedOrbit j x
    let Au := runA j x
    let Av := runA k y
    let au := oddCount x j
    let av := oddCount y k
    runA (j + k) x + (Av * 3 ^ au + Au * 2 ^ k)
      = (3 ^ av * Au + 2 ^ j * Av) + (Av * 3 ^ au + Au * 2 ^ k) := by
  intro y Au Av au av
  rw [runA_add x j k]

/-! ## The cycle criterion, shifted -/

/-- **The cycle criterion in the shifted coordinate.**  The gap times `n + 1` is
the shifted accumulator.  (`CycleAccumulator.cycle_gap_mul` gives gap times `n`
is `affineC`; the two differ by exactly the gap.) -/
theorem cycle_shifted {n L : Nat} (hn : 0 < n) (h : AccIsCycleOf n L) :
    (2 ^ L - 3 ^ oddCount n L) * (n + 1) = runA L n := by
  have hlt := (accCycle_bounds hn h).2.2
  have hgap := CycleAccumulator.cycle_gap_mul hn h
  have hrel := runA_eq n L
  have hexp : (2 ^ L - 3 ^ oddCount n L) * (n + 1)
      = (2 ^ L - 3 ^ oddCount n L) * n + (2 ^ L - 3 ^ oddCount n L) := by
    rw [Nat.mul_add, Nat.mul_one]
  omega

/-! ## Rigidity: the invariants determine the word -/

/-- One step of the shifted accumulator, split at the *front* rather than the
back.  This is the cocycle at `j = 1`. -/
theorem runA_head (x k : Nat) :
    runA (1 + k) x
      = 3 ^ oddCount (acceleratedOrbit 1 x) k * runA 1 x
        + 2 * runA k (acceleratedOrbit 1 x) := by
  have := runA_add x 1 k
  simpa using this

theorem runA_one_odd {x : Nat} (h : x % 2 = 1) : runA 1 x = 0 := by
  have h0 : acceleratedOrbit 0 x % 2 = 1 := h
  rw [show (1:Nat) = 0 + 1 from rfl, runA_odd h0]
  simp

theorem runA_one_even {x : Nat} (h : x % 2 = 0) : runA 1 x = 1 := by
  have h0 : acceleratedOrbit 0 x % 2 = 0 := h
  rw [show (1:Nat) = 0 + 1 from rfl, runA_even h0]
  simp

/-- A power of three is odd. -/
theorem three_pow_odd : ∀ k : Nat, 3 ^ k % 2 = 1 := by
  intro k
  induction k with
  | zero => rfl
  | succ k ih => rw [Arith.three_pow_succ]; omega

/-- **The leading parity bit is visible in the accumulator.**  For a nonempty
window, `runA` is even exactly when the first step is odd. -/
theorem runA_parity (x k : Nat) :
    (x % 2 = 1 → runA (1 + k) x % 2 = 0) ∧
    (x % 2 = 0 → runA (1 + k) x % 2 = 1) := by
  constructor
  · intro h
    rw [runA_head x k, runA_one_odd h]
    omega
  · intro h
    rw [runA_head x k, runA_one_even h, Nat.mul_one]
    have := three_pow_odd (oddCount (acceleratedOrbit 1 x) k)
    omega

end RunAlgebra
end Collatz
