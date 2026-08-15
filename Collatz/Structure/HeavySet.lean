import Collatz.Structure.OrbitMin
import Collatz.Structure.Obstruction

/-!
# Counterexample minima live in a sparse residue set

Two results now point at each other.

* `OrbitMin.heavy` — the orbit minimum `m` of any counterexample satisfies
  `2 ^ (k-1) ≤ 3 ^ {a(m,k)}` at every scale `k` with `2 ^ k ≤ m`.
* `Density.weightSum_eq` — the residues modulo `2 ^ k` carry total weight
  `Σ 2 ^ {a(r,k)} = 3 ^ k`.

Since `a(m,k)` depends only on `m mod 2 ^ k`, the first says `m`'s residue lies
in the set of *heavy-at-level-`k−1`* residues, and the second bounds how many
such residues there are.  Writing `H(k,t)` for the number of residues modulo
`2 ^ k` with `2 ^ t ≤ 3 ^ {a(r,k)}`:

**`2 ^ ⌈3t/5⌉ · H(k,t) ≤ 3 ^ k`.**

At `t = k − 1` this makes `H(k,k−1)` a vanishing fraction of `2 ^ k`, exactly as
in `Collatz.Structure.Density`.  So the orbit minimum of any counterexample is
confined, modulo every `2 ^ k` below it, to a set of density tending to zero —
and it must lie in *all* of those sets simultaneously.

That is the sharpest quantitative statement the project supports.  It is still
not a contradiction, because `Obstruction.sieve_never_clears` shows each of
those sets is nonempty; the residue `2 ^ k − 1` sits in every one of them.
-/

namespace Collatz
namespace HeavySet

open Reach Congruence Density _root_.Collatz.Sum

/-! ## Counting heavy-at-a-level residues -/

/-- `heavyAtCount k t` counts residues modulo `2 ^ k` whose multiplier reaches
`2 ^ t`. -/
def heavyAtCount (k t : Nat) : Nat :=
  countRange (2 ^ k) (fun r => decide (2 ^ t ≤ 3 ^ oddCount r k))

/-- **The counting bound.**  `2 ^ ⌈3t/5⌉ · H(k,t) ≤ 3 ^ k`, by comparing the
count against the total weight `3 ^ k`. -/
theorem mul_heavyAtCount_le (k t : Nat) :
    2 ^ ((3 * t + 4) / 5) * heavyAtCount k t ≤ 3 ^ k := by
  have hpt : ∀ i : Nat, i < 2 ^ k →
      (decide (2 ^ t ≤ 3 ^ oddCount i k) = true) →
      2 ^ ((3 * t + 4) / 5) ≤ 2 ^ oddCount i k := by
    intro i _ hi
    have h2 : 2 ^ t ≤ 3 ^ oddCount i k := by simpa using hi
    have h3 := three_mul_le_five_mul_of_heavy h2
    exact Arith.two_pow_le_two_pow (by omega)
  have h := mul_countRange_le (n := 2 ^ k) (w := 2 ^ ((3 * t + 4) / 5))
    (p := fun r => decide (2 ^ t ≤ 3 ^ oddCount r k))
    (f := fun r => 2 ^ oddCount r k) hpt
  have hw : sumRange (2 ^ k) (fun r => 2 ^ oddCount r k) = 3 ^ k := weightSum_eq k
  rw [heavyAtCount]
  omega

/-- At the level the orbit-minimum bound provides, `t = k − 1`. -/
theorem mul_heavyAtCount_pred_le (k : Nat) :
    2 ^ ((3 * (k - 1) + 4) / 5) * heavyAtCount k (k - 1) ≤ 3 ^ k :=
  mul_heavyAtCount_le k (k - 1)

/-! ## The orbit minimum lands in that set -/

/-- The odd-step count of a number over `k` steps depends only on its residue
modulo `2 ^ k`, so heaviness is a property of the residue. -/
theorem heavy_residue {n m : Nat} (hn : 0 < n)
    (hm : ∃ i : Nat, acceleratedOrbit i n = m)
    (hmin : ∀ j : Nat, m ≤ acceleratedOrbit j n) {k : Nat} (hk : 2 ^ k ≤ m) :
    2 ^ (k - 1) ≤ 3 ^ oddCount (m % 2 ^ k) k := by
  have hheavy := OrbitMin.heavy hn hm hmin hk
  have hres : oddCount m k = oddCount (m % 2 ^ k) k := Density.oddCount_mod m k
  rw [← hres]
  cases k with
  | zero =>
    have := Arith.three_pow_pos (oddCount m 0)
    simp
  | succ j =>
    have hsplit : (2:Nat) ^ (j + 1) = 2 * 2 ^ j := Arith.two_pow_succ j
    have hidx : j + 1 - 1 = j := by omega
    rw [hidx]
    omega

/-- **The synthesis.**  The orbit minimum of a counterexample is confined,
modulo every `2 ^ k` below it, to a residue set of size at most
`3 ^ k / 2 ^ ⌈3(k-1)/5⌉` — a vanishing fraction of `2 ^ k`. -/
theorem orbitMin_confined {n : Nat} (hn : 0 < n) (hnr : ¬ ReachesOne n) :
    ∃ m : Nat, 102400 ≤ m ∧
      ∀ k : Nat, 2 ^ k ≤ m →
        (2 ^ (k - 1) ≤ 3 ^ oddCount (m % 2 ^ k) k ∧
         2 ^ ((3 * (k - 1) + 4) / 5) * heavyAtCount k (k - 1) ≤ 3 ^ k) := by
  obtain ⟨m, hm, hmin⟩ := AccCycle.exists_accCycleMin n
  refine ⟨m, OrbitMin.ge_verified hn hnr hm, fun k hk => ?_⟩
  exact ⟨heavy_residue hn hm hmin hk, mul_heavyAtCount_pred_le k⟩

/-! ## The set is never empty

The counting bound says the admissible residue set is sparse.  It is never
empty, for the same reason the sieve never clears: the residue `2 ^ k − 1`
takes `k` consecutive odd steps and so is heavy at every level. -/

/-- **The admissible set is nonempty at every scale.**  The residue `2 ^ k − 1`
belongs to it. -/
theorem heavyAtCount_pos (k : Nat) : 0 < heavyAtCount k (k - 1) := by
  have hcount : oddCount (2 ^ k - 1) k = k := Obstruction.oddCount_two_pow_sub_one k
  have hlt : 2 ^ k - 1 < 2 ^ k := by
    have := Arith.two_pow_pos k
    omega
  have hmem : decide (2 ^ (k - 1) ≤ 3 ^ oddCount (2 ^ k - 1) k) = true := by
    rw [hcount]
    have h1 : (2:Nat) ^ (k - 1) ≤ 2 ^ k := Arith.two_pow_le_two_pow (by omega)
    have h2 : (2:Nat) ^ k ≤ 3 ^ k := Arith.two_pow_le_three_pow k
    simp
    omega
  have hle : (if decide (2 ^ (k - 1) ≤ 3 ^ oddCount (2 ^ k - 1) k) = true then 1 else 0)
      ≤ heavyAtCount k (k - 1) :=
    le_sumRange (n := 2 ^ k)
      (fun i => if decide (2 ^ (k - 1) ≤ 3 ^ oddCount i k) = true then 1 else 0) hlt
  rw [hmem] at hle
  simp only [if_pos] at hle
  omega

/-- **Sparse but never empty**, side by side.  This is the residue-level form of
the same gap that `Obstruction.sieve_never_clears` exhibits. -/
theorem sparse_but_nonempty (k : Nat) :
    0 < heavyAtCount k (k - 1) ∧
    2 ^ ((3 * (k - 1) + 4) / 5) * heavyAtCount k (k - 1) ≤ 3 ^ k :=
  ⟨heavyAtCount_pos k, mul_heavyAtCount_pred_le k⟩

/-! ## Concrete instances

At each scale the bound becomes a specific numeric constraint on the orbit
minimum's odd-step count. -/

/-- The orbit minimum of a counterexample takes at least `9` odd steps in its
first `16`. -/
theorem oddCount_sixteen {n m : Nat} (hn : 0 < n)
    (hm : ∃ i : Nat, acceleratedOrbit i n = m)
    (hmin : ∀ j : Nat, m ≤ acceleratedOrbit j n) (hk : 2 ^ 16 ≤ m) :
    9 ≤ oddCount m 16 := by
  have hbound := OrbitMin.three_mul_le_five_mul hn hm hmin hk
  omega

/-- And at least `5` in its first `10`. -/
theorem oddCount_ten {n m : Nat} (hn : 0 < n)
    (hm : ∃ i : Nat, acceleratedOrbit i n = m)
    (hmin : ∀ j : Nat, m ≤ acceleratedOrbit j n) (hk : 2 ^ 10 ≤ m) :
    5 ≤ oddCount m 10 := by
  have hbound := OrbitMin.three_mul_le_five_mul hn hm hmin hk
  omega

/-- And at least `2` in its first `5`. -/
theorem oddCount_five {n m : Nat} (hn : 0 < n)
    (hm : ∃ i : Nat, acceleratedOrbit i n = m)
    (hmin : ∀ j : Nat, m ≤ acceleratedOrbit j n) (hk : 2 ^ 5 ≤ m) :
    2 ≤ oddCount m 5 := by
  have hbound := OrbitMin.three_mul_le_five_mul hn hm hmin hk
  omega

end HeavySet
end Collatz
