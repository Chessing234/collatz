import Collatz.Search.BarinaRange
import Collatz.Strategy.CycleLength1539
import Collatz.Strategy.AffineExact

/-!
# The verified range as a parameter, and what Barina's would buy

Three things live here, kept strictly apart:

* **kernel-proved, unconditional** — `verified_1086464`, and the whole
  `barina_sweep` family, which is a statement about `excludedFast` and mentions no
  orbit at all;
* **conditional on `BarinaVerified`** — every consequence of the external range,
  each carrying the hypothesis in its statement;
* **externally measured** — recorded in prose, never as a theorem.

## 1. The audit

Everything in this development that consumes the verified range does so through
one of three shapes.

**(a) Genuinely tied to the proved constant.**  Only
`Search.reachesOne_of_lt_1086464` and `Search.counterexample_ge_1086464`
themselves.  Both are theorems about a specific finished computation.

**(b) Generic in the bound — the large majority.**  Every theorem of the form
`hc : 1086464 ≤ m → P m` uses the constant only as a lower bound on the orbit, and
its proof never inspects the numeral.  `ValuationBeatty.orbit_time_le_fexp`,
`even_steps_per_306`, `orbit_run_box`, `orbit_gapC_le_Bcap`,
`RealizableFrontier6809.no_light_window`, `TropicalDefect`'s light-window bound and
the `BackwardRange` family are all of this kind.  `BottomUnreachable.bottom_unreachable`
is already explicitly parametric (`hB : B ≤ 1086464`).

The one caveat: several of them consume a **numeric certificate** keyed to the
constant — `RealizableFrontier6809.cert_1086464` — which is a finite table checked
by `decide` at that value.  Those are generic in the *statement* but their
certificates would have to be recomputed at another bound.

**(c) Free transfer to a larger range.**  Because `1086464 ≤ barinaBound`, any
theorem of shape (b) applies verbatim to a counterexample under `BarinaVerified`:
`ge_barina_ge_proved` below is the one-line bridge, and no theorem needs
restating.

**Conclusion of the audit: no theorem required conditionalising, and none was
conditionalised.**  The generic shape below removes the duplicated proof pattern
without touching any existing statement.

## 2. The parameter

`VerifiedBelow c` says every positive `n < c` reaches `1`.  `verified_1086464` is
that predicate at the proved constant; `BarinaVerified` is it at `barinaBound`.
The two orbit lemmas that were previously written out once per constant —
`CycleLength2593.ge_verified_768000`, `RealizableFrontier6809.ge_verified_1086464`,
`BarinaRange.ge_verified_barina` — are one lemma here, `ge_verified_of`.

## 3. The cycle-length machinery, certified

`excludedFast` (two bignum comparisons per length) replaces the `O(L²)` scan of
`excludedLength`; `decide` on `excludedLength 1086464 2593` exhausts recursion
depth, `excludedFast` does not.

**`barina_sweep` is unconditional**: every length from `1` to `40 000` is excluded
at `barinaBound`.  It mentions no orbit and assumes nothing — it is a fact about
integers.  Only when combined with "a cycle's minimum is at least `barinaBound`"
does `BarinaVerified` enter, in `cycle_length_ge_40001_of_barina`.

Against the repository's unconditional `2593` (`CycleLength2593`), that is a
factor of **15.4**.

Measured, not proved: `excludedFast barinaBound L` holds for every `L ≤ 60 000`
(exact integer arithmetic, outside Lean), and a `100 000` sweep was checked to pass
the kernel in `4 m 15 s`.  The committed sweep stops at `40 000` to keep the build
under a minute for this file.  The true crossover is near `√(c) ≈ 7 · 10 ^ 10`, far
beyond any kernel sweep — so the limit here is compute, not mathematics.

## 4. Can Barina's result be certified compactly?  No.

A certificate must be checkable in time far below the computation it replaces.
Barina's range is a **universally quantified statement over an unstructured
predicate**: `n` reaches `1`.  Verifying it requires exhibiting, for each residue
class not already killed, a descent — and the only known reason each one descends
is that it was run.  Sieving reduces the constant (this development's level-`10`
sieve keeps `64/1024`, so `≈ 5 · 10 ^ 19` survivors) but not the asymptotics.

There is no known compression, and there is a reason to expect none: a short
certificate would amount to a proof of the range, and the range is a finite
fragment of the conjecture itself.  **The smallest missing object is therefore not
a certificate but the computation**, and the honest options are (i) extend the
kernel-checked sieve — cost `4×` per doubling, payoff `√c` — or (ii) keep Barina as
the named hypothesis it is here.
-/

namespace Collatz
namespace VerifiedRange

open Reach Search CycleProduct CycleLength1539 BarinaRange

/-! ## The parameter -/

/-- Every positive integer below `c` reaches `1`. -/
def VerifiedBelow (c : Nat) : Prop := ∀ n : Nat, 0 < n → n < c → ReachesOne n

/-- **Kernel-proved.**  The development's own verified range. -/
theorem verified_1086464 : VerifiedBelow 1086464 :=
  fun _ hn hlt => reachesOne_of_lt_1086464 hn hlt

/-- Barina's range in the same language.  **Not proved** — see `BarinaVerified`. -/
theorem barina_is_verifiedBelow (h : BarinaVerified) : VerifiedBelow barinaBound := h

/-- A wider verified range subsumes a narrower one. -/
theorem verifiedBelow_mono {c c' : Nat} (hcc : c ≤ c') (h : VerifiedBelow c') :
    VerifiedBelow c := fun n hn hlt => h n hn (by omega)

/-! ## The one orbit lemma, previously written out once per constant -/

/-- **Every point on the orbit of a counterexample is at least `c`.**  One lemma in
place of `ge_verified_768000`, `ge_verified_1086464` and `ge_verified_barina`. -/
theorem ge_verified_of {c n m : Nat} (hv : VerifiedBelow c) (hn : 0 < n)
    (hnr : ¬ ReachesOne n) (hm : ∃ i : Nat, acceleratedOrbit i n = m) : c ≤ m := by
  obtain ⟨i, hi⟩ := hm
  rcases Nat.lt_or_ge m c with hlt | hge
  · exfalso
    have hpos : 0 < m := by rw [← hi]; exact acceleratedOrbit_positive hn i
    have hreach : ReachesOne m := hv m hpos hlt
    rw [← hi] at hreach
    exact hnr (reachesOne_of_accOrbit hn hreach)
  · exact hge

/-- A counterexample is at least `c`. -/
theorem counterexample_ge_of {c n : Nat} (hv : VerifiedBelow c) (hn : 0 < n)
    (hnr : ¬ ReachesOne n) : c ≤ n :=
  ge_verified_of hv hn hnr ⟨0, acceleratedOrbit_zero n⟩

/-- **The free transfer.**  Under `BarinaVerified` a counterexample clears the
proved constant too, so every theorem taking `1086464 ≤ m` applies unchanged. -/
theorem ge_barina_ge_proved (h : BarinaVerified) {n m : Nat} (hn : 0 < n)
    (hnr : ¬ ReachesOne n) (hm : ∃ i : Nat, acceleratedOrbit i n = m) : 1086464 ≤ m := by
  have hge := ge_verified_of (barina_is_verifiedBelow h) hn hnr hm
  have := barina_gt_verified
  omega

/-! ## The sweep — unconditional, and about integers only -/

set_option maxHeartbeats 4000000000 in
set_option exponentiation.threshold 60000 in
set_option maxRecDepth 80000000 in
/-- **Kernel-proved, unconditional.**  Every length from `1` to `40 000` passes the
fast exclusion test at Barina's bound.  No orbit appears in this statement; it is a
fact about `2`, `3` and `704 · 2 ^ 60`. -/
theorem barina_sweep :
    ((List.range 40000).map (fun i => i + 1)).all
      (fun L => excludedFast barinaBound L) = true := by
  decide

/-- Every such length is excluded outright. -/
theorem excludedLength_of_lt_40001 {L : Nat} (hL : L < 40001) (hpos : 0 < L) :
    excludedLength barinaBound L = true := by
  refine excludedLength_of_excludedFast ?_
  have h := barina_sweep
  rw [List.all_eq_true] at h
  exact h L (List.mem_map.mpr ⟨L - 1, List.mem_range.mpr (by omega), by omega⟩)

/-! ## The conditional cycle-length theorem -/

/-- **Conditional on `BarinaVerified`.**  A nontrivial accelerated cycle has length
at least `40 001` — against the repository's unconditional `2593`, a factor of
`15.4`.  The hypothesis enters only through the cycle minimum. -/
theorem cycle_length_ge_40001_of_barina (hb : BarinaVerified) {n L : Nat}
    (hn : 0 < n) (hnr : ¬ ReachesOne n) (hcyc : acceleratedOrbit L n = n)
    (hpos : 0 < L) (hsmall : 2 * oddCount n L ≤ 3 * barinaBound)
    (hlt : 3 ^ oddCount n L < 2 ^ L) : 40001 ≤ L := by
  rcases Nat.lt_or_ge L 40001 with hLlt | hLge
  · exfalso
    have hc : ∀ k : Nat, barinaBound ≤ acceleratedOrbit k n :=
      fun k => ge_verified_of (barina_is_verifiedBelow hb) hn hnr ⟨k, rfl⟩
    exact no_cycle_of_excludedLength hn (by decide) hc hcyc hsmall
      (AffineExact.oddCount_le_self n L) hlt (excludedLength_of_lt_40001 hLlt hpos)
  · exact hLge

/-! ## Regression tests -/

set_option maxHeartbeats 4000000000 in
set_option exponentiation.threshold 6000 in
set_option maxRecDepth 4000000 in
/-- The sweep genuinely uses Barina's bound: the same length fails at the proved
range.  `2593` is where `CycleLength2593` stops, and it is inside the new sweep. -/
theorem sweep_is_strictly_stronger :
    excludedFast barinaBound 2593 = true ∧ excludedFast 1086464 2593 = false := by
  refine ⟨by decide, by decide⟩

/-- And the constant in play really is `704 · 2 ^ 60`. -/
theorem sweep_constant : barinaBound = 704 * 2 ^ 60 ∧ 1086464 < barinaBound := by
  refine ⟨rfl, barina_gt_verified⟩

end VerifiedRange
end Collatz
