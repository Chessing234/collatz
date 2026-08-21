import Collatz.Strategy.RealizableBound
import Collatz.Search.VerifiedExtended

/-!
# The realizability frontier at the extended range: no cycle shorter than 6809

`Strategy.RealizableBound` proves everything of substance: the Beatty ceiling
`Bcap`, the one-pass certificate `cert`, and the two lemmas
`affineC_le_Bcap` / `le_fexp_of_affineC_le` that turn the certificate into
`2 ^ j ≤ 3 ^ (oddCount m j)` for a never-dropper above the verified range.  All
of that is *parametric in the range `c`*: the only place `c = 768 000` enters is
the certificate `cert_2966` and the hypothesis `768000 ≤ m` supplied by
`CycleLength2593.ge_verified_768000`.

`Search.VerifiedExtended` has since raised the verified range to `1 086 464`.
This file re-runs the same two inputs at the new range and reports the frontier
that falls out.  There is no new argument here, and the file says so.

## The staircase, and why `1 086 464`

The certificate's reach is
`A(c) = max { A : G(i) < c for all i < A }`, `G(i) = Bcap i / (2 ^ (fexp i + 1) − 3 ^ i)`,
and the frontier is the largest `L` with `2 ^ (L−1) < 3 ^ (A(c))`, plus one.
`G` takes its records at the indices where the linear form `2 ^ (fexp i + 1) − 3 ^ i`
is small — the convergents of `log 3 / log 2` — so `A(c)` is a step function with
widely spaced risers:

| `c` at least | `A(c)` | frontier |
|---|---|---|
| `307 200` | `1636` | `L ≥ 2593` |
| `420 842` | `2301` | `L ≥ 3647` |
| `620 859` | `2966` | `L ≥ 4701` |
| `841 478` | `3631` | `L ≥ 5755` |
| `1 086 055` | `4296` | **`L ≥ 6809`** |
| `1 358 718` | `4961` | `L ≥ 7863` |

The old range `768 000` sat with `G(2966) = 841 477` just out of reach — a margin
of `73 477` integers.  Verifying `311` more blocks clears both
`841 477` and `1 086 054` at once, which is why the gain is two risers and not
one: the frontier moves `4701 → 6809`, a `45 %` improvement, and the odd-step
budget `A` moves `2966 → 4296`.

Note the arithmetic of the trade.  The risers are spaced by a factor tending to
`3/2 · ...` — empirically `G`'s records grow by roughly `272 664` each, and the
record *indices* are spaced by exactly `665` — while the
kernel cost is linear in `c`.  So each additional riser costs a *fixed* number of
blocks (about `267`), and each buys a *fixed* `1054` on the frontier.  In this
regime the ladder is, unusually, not getting steeper; what makes it a poor
long-term strategy is that `1054` per four minutes of kernel time never becomes
`∞`.

## Where `d = 1` is used

Twice, and in the same place as `RealizableBound`: the hypothesis `c ≤ m` is the
verified range (asset (a)), and the certificate compares `Bcap i` against `d · c`
in the direction `G(i) < c`, so the argument is not mirror-invariant.  For the
`3x − 1` mirror the least never-dropper is `m = 5` and `G(5) = 24.54 > 5`, so the
certificate collapses at `i = 5`, exactly as it must.
-/

namespace Collatz
namespace RealizableFrontier6809

open Reach Congruence AffineExact AccumulatorArith RealizableBound

/-! ## The verified range, in the shape the cycle argument consumes -/

/-- Every point on the orbit of a counterexample is at least the verified range.
The proof is `CycleLength2593.ge_verified_768000` verbatim at the new constant. -/
theorem ge_verified_1086464 {n m : Nat} (hn : 0 < n) (hnr : ¬ ReachesOne n)
    (hm : ∃ i : Nat, acceleratedOrbit i n = m) : 1086464 ≤ m := by
  obtain ⟨i, hi⟩ := hm
  by_cases hlt : m < 1086464
  · exfalso
    have hpos : 0 < m := by
      rw [← hi]; exact acceleratedOrbit_positive hn i
    have hreach : ReachesOne m := Search.reachesOne_of_lt_1086464 hpos hlt
    rw [← hi] at hreach
    exact hnr (reachesOne_of_accOrbit hn hreach)
  · omega

/-! ## The certificate at the new range

`cert 4296 1086464 0 1 1` is `4296` comparisons between integers of up to `2050`
decimal digits, carried out in a single forward pass by the kernel.  The binding
constraint on the range is `G(3631) = 1 086 054`; the margin against the verified
`1 086 464` is `410`, which is as thin as it is because `1061` blocks is the
*first* multiple of `1024` past the riser.  The next index, `4296`, breaches it at
`G = 1 358 717`. -/

set_option maxHeartbeats 4000000 in
set_option maxRecDepth 40000 in
set_option exponentiation.threshold 8000 in
theorem cert_4296 : cert 4296 1086464 0 1 1 = true := by decide

/-- The certificate in the form the lemmas of `RealizableBound` consume:
`G(i) < 1 086 464` for every `i < 4296`. -/
theorem cert_1086464 (i : Nat) (hi : i < 4296) :
    Bcap i + 3 ^ i * 1086464 < 2 * 2 ^ fexp i * 1086464 := by
  have h := cert_sound 4296 0 1086464 (by simpa using cert_4296) i hi
  simpa using h

/-! ## The frontier -/

set_option maxRecDepth 10000 in
set_option exponentiation.threshold 8000 in
/-- `2 ^ 6808 < 3 ^ 4296`: every cycle length below `6809` has fewer than `4296`
odd steps, which is exactly the range the certificate covers. -/
theorem pow_gap_4296 : (2:Nat) ^ 6808 < 3 ^ 4296 := by decide

/-- **A never-dropper above the extended verified range has no light window**, as
far as the new certificate reaches: `2 ^ j ≤ 3 ^ (oddCount m j)` outright, with no
factor of two on the right.  `RealizableBound.no_light_window` at the new `c`. -/
theorem no_light_window {m j : Nat} (hc : 1086464 ≤ m)
    (hnd : ∀ i : Nat, m ≤ acceleratedOrbit i m)
    (hlt : 3 ^ oddCount m j < 2 ^ j) (hA : oddCount m j < 4296) : False := by
  have hB : affineC j m ≤ Bcap (oddCount m j) :=
    affineC_le_Bcap (by omega) hc hnd cert_1086464 j (by omega)
  have htime : j ≤ fexp (oddCount m j) :=
    le_fexp_of_affineC_le (by omega) hc hnd (cert_1086464 _ hA) rfl hB
  have hpow : (2:Nat) ^ j ≤ 2 ^ fexp (oddCount m j) := Arith.two_pow_le_two_pow htime
  have hceil := fexp_le (oddCount m j)
  omega

set_option exponentiation.threshold 8000 in
open AccCycle in
/-- **Every nontrivial accelerated cycle has length at least `6809`.**

The same proof as `RealizableBound.length_ge_4701`, with the verified range
`768 000` replaced by `1 086 464` and the certificate's reach `2966` by `4296`.
No new mathematics: `311` blocks of kernel time move the frontier by `2108`. -/
theorem length_ge_6809 {n L : Nat} (hn : 0 < n) (h : AccIsCycleOf n L)
    (hnr : ¬ ReachesOne n) : 6809 ≤ L := by
  rcases Nat.lt_or_ge L 6809 with hL | hL
  · exfalso
    obtain ⟨m, hm, hmin⟩ := exists_accCycleMin n
    obtain ⟨i, hi⟩ := hm
    have hmpos : 0 < m := by rw [← hi]; exact acceleratedOrbit_positive hn i
    have htrans : ∀ k : Nat, acceleratedOrbit k m = acceleratedOrbit (k + i) n := by
      intro k; rw [← hi, acceleratedOrbit_add k i n]
    have hnd : ∀ k : Nat, m ≤ acceleratedOrbit k m := by
      intro k; rw [htrans k]; exact hmin _
    have hc : 1086464 ≤ m := ge_verified_1086464 hn hnr ⟨i, hi⟩
    have hcyc : acceleratedOrbit L m = m := by
      rw [htrans L, Nat.add_comm L i, ← acceleratedOrbit_add i L n, h.2, hi]
    have hlt : 3 ^ oddCount m L < 2 ^ L :=
      Cycle.two_pow_gt_three_pow_of_accCycle hmpos h.1 hcyc
    have hA : oddCount m L < 4296 := by
      rcases Nat.lt_or_ge (oddCount m L) 4296 with hok | hcon
      · exact hok
      · exfalso
        have h1 : (3:Nat) ^ 4296 ≤ 3 ^ oddCount m L :=
          Nat.pow_le_pow_right (by omega) hcon
        have h2 : (2:Nat) ^ L ≤ 2 ^ 6808 := Arith.two_pow_le_two_pow (by omega)
        have h3 := pow_gap_4296
        omega
    exact no_light_window hc hnd hlt hA
  · exact hL

set_option maxHeartbeats 4000000 in
set_option maxRecDepth 40000 in
set_option exponentiation.threshold 8000 in
/-- The frontier is real, not an artefact of where the certificate stops: at
`i = 4296` the quotient `G(i)` is `1 358 717`, above the verified range, so the
inductive step genuinely fails there.  Moving past it needs `267` more blocks. -/
theorem frontier_4296 : cert 4297 1086464 0 1 1 = false := by decide

end RealizableFrontier6809
end Collatz
