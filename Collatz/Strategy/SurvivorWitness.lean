import Collatz.Strategy.DeviceSwap

/-!
# One witness kills two programmes

Two independent wave-three investigations — a covering/density attack and a
block-Lyapunov search — produced quantitative negatives.  They reduce to the same
family of integers, and it is the simplest one imaginable:

**`n ≡ −1 (mod 2 ^ k)`**, i.e. `n + 1 = 2 ^ k · u`.

By `DeviceSwap.run_climb` such an `n` takes `k` consecutive odd steps, and in the
shifted coordinate `u = n + 1` each of them multiplies by exactly `3/2`.  So the
orbit rises for `k` steps by the largest factor available.

## What it kills

**Covering systems.**  `survivor_exists`: for every `k` there is a residue class
mod `2 ^ k` — namely `2 ^ k − 1` — that does **not** drop within `k` steps.  So the
survivor set is never empty, and no finite covering system built from congruences
mod powers of two can force descent everywhere.

That is the exact endpoint of the density computation.  Writing
`S_j = #{r < 2 ^ j : r does not drop within j steps}`, the parity-vector bijection
gives `S_j = Σ_{a : 3 ^ a ≥ 2 ^ j} C(j, a)` exactly (binomial law verified by brute
force for `j ≤ 13`, zero exceptions).  Measured: `S_10 = 176`, `S_20 = 137 980`,
`S_30 = 107 636 402`, `S_60 ≈ 2.99 · 10 ^ 16`, with `log₂(S_j)/j` climbing to
`0.9122` at `j = 60`.  The limit is the binary entropy `H₂(log 2 / log 3) =
0.94996` — **which is exactly the Hausdorff dimension `≈ 0.95` of the never-dropping
set in `ℤ₂` found independently in wave one.**  Two unrelated computations agreeing
to three decimals; the density `d_j → 1` but the survivor count **grows** like
`1.9318 ^ j`.

**Block Lyapunov functions.**  `block_ratio`: for this same family,
`T^k(n) + 1 = 3 ^ k · u = (3/2) ^ k · (n + 1)`.  A candidate `V(n) = n · g(n mod 2 ^ k)`
with bounded `g` must survive a block ratio of `(3 ^ k / 2 ^ k)`, which diverges
geometrically.  The worst residue is exactly `2 ^ k − 1`, and the optimal
achievable sup-ratio over all bounded `g` is therefore `(3/2) ^ k ≥ 1` for every
`k` — it never approaches `1` from above; it runs away.  Measured for `k ≤ 20`:
`1.5, 2.25, 3.375, …, 3325.257`.

So the two programmes fail for one reason: **the all-odd residue class is present at
every level, and on it the map does the worst thing it can do.**

## Scope

Nothing here bears on whether a *specific integer* diverges — a residue class
surviving `k` steps says nothing about surviving forever, and `DeviceSwap`'s
theory is what governs that.  These are exclusions of two proof *strategies*, and
that is all they are.
-/

namespace Collatz
namespace SurvivorWitness

open Reach DeviceSwap

/-! ## The witness -/

/-- **The all-odd class never drops early.**  If `n + 1 = 2 ^ k · u` then for every
`i ≤ k` the orbit is still at or above its start: in the shifted coordinate the
first `k` steps multiply by `3/2` each time, and `3 ^ i ≥ 2 ^ i`. -/
theorem no_drop_within {n u k : Nat} (hu : 0 < u) (hfac : n + 1 = 2 ^ k * u) :
    ∀ i : Nat, i ≤ k → n ≤ acceleratedOrbit i n := by
  intro i hi
  -- split the factorisation at `i`
  have hsplit : (2:Nat) ^ k * u = 2 ^ i * (2 ^ (k - i) * u) := by
    rw [← Nat.mul_assoc, ← Nat.pow_add]
    congr 2
    omega
  have hwpos : 0 < (2:Nat) ^ (k - i) * u := Nat.mul_pos (Arith.two_pow_pos _) hu
  have hclimb := run_climb i (2 ^ (k - i) * u) n hwpos (by rw [hfac, hsplit])
  -- `3 ^ i ≥ 2 ^ i`, so the shifted value has not fallen
  have hpow : (2:Nat) ^ i ≤ 3 ^ i := Nat.pow_le_pow_left (by omega) i
  have hmul : 2 ^ i * (2 ^ (k - i) * u) ≤ 3 ^ i * (2 ^ (k - i) * u) :=
    Nat.mul_le_mul_right _ hpow
  omega

/-- **A survivor at every level.**  `n = 2 ^ k − 1` is positive for `k ≥ 1`, lies in
the class `−1 mod 2 ^ k`, and does not drop within `k` steps.  Hence the survivor
set is never empty and no finite covering system by powers of two can force
descent. -/
theorem survivor_exists (k : Nat) (hk : 1 ≤ k) :
    ∃ n : Nat, 0 < n ∧ n + 1 = 2 ^ k ∧ ∀ i : Nat, i ≤ k → n ≤ acceleratedOrbit i n := by
  have hpos : 0 < (2:Nat) ^ k := Arith.two_pow_pos k
  have hge : 2 ≤ (2:Nat) ^ k := by
    have : (2:Nat) ^ 1 ≤ 2 ^ k := Nat.pow_le_pow_right (by omega) hk
    simpa using this
  refine ⟨2 ^ k - 1, by omega, by omega, ?_⟩
  refine no_drop_within (u := 1) (by omega) ?_
  omega

/-- **The block ratio on the witness.**  After `k` steps the shifted coordinate has
been multiplied by exactly `3 ^ k / 2 ^ k`: `T^k(n) + 1 = 3 ^ k · u`.  This is the
quantity a block potential would have to absorb, and it grows geometrically. -/
theorem block_ratio {n u k : Nat} (hu : 0 < u) (hfac : n + 1 = 2 ^ k * u) :
    acceleratedOrbit k n + 1 = 3 ^ k * u :=
  run_climb k u n hu hfac

/-- The witness in the form the Lyapunov search needs: the shifted value after the
block is `3 ^ k` times what it was before division, against `2 ^ k` before. -/
theorem block_ratio_witness (k : Nat) (hk : 1 ≤ k) :
    ∃ n : Nat, 0 < n ∧ n + 1 = 2 ^ k ∧ acceleratedOrbit k n + 1 = 3 ^ k := by
  have hpos : 0 < (2:Nat) ^ k := Arith.two_pow_pos k
  have hge : 2 ≤ (2:Nat) ^ k := by
    have : (2:Nat) ^ 1 ≤ 2 ^ k := Nat.pow_le_pow_right (by omega) hk
    simpa using this
  refine ⟨2 ^ k - 1, by omega, by omega, ?_⟩
  have h := block_ratio (n := 2 ^ k - 1) (u := 1) (k := k) (by omega) (by omega)
  simpa using h

/-- **No covering system.**  Stated as the negation directly: there is no `k` for
which every residue class mod `2 ^ k` drops within `k` steps. -/
theorem no_covering_by_powers_of_two (k : Nat) (hk : 1 ≤ k) :
    ¬ (∀ n : Nat, 0 < n → ∃ i : Nat, i ≤ k ∧ acceleratedOrbit i n < n) := by
  intro hcov
  obtain ⟨n, hnpos, _, hnodrop⟩ := survivor_exists k hk
  obtain ⟨i, hi, hlt⟩ := hcov n hnpos
  exact absurd (hnodrop i hi) (by omega)

end SurvivorWitness
end Collatz
