import Collatz.Strategy.DensitySaturation
import Collatz.Strategy.RunLengthAny
import Collatz.Strategy.MersenneLower
import Collatz.Strategy.Pillars
import Collatz.Strategy.Reductions
import Collatz.Strategy.Escape
import Collatz.Strategy.Frontier11025
import Collatz.Search.VerifiedRung14187
import Collatz.Strategy.ValuationDensity

/-!
# Which descent schemas survive the repository's kills

**2026-09-28 correction:** the historical claims below that constant 17 is
still viable are superseded by `Collatz.Strategy.LogBlockRecord`.
A kernel-checked published witness refutes every constant through 18.
The conditional reductions in this file remain valid, but their constant-17
tail hypothesis is false. The cited arXiv:2107.11160v2 paper is by Eliahou and
Simonetto, not Rozier. Its variable-length jumps are related to, but are not
identical to, this file's initial-logarithm bound. See
`Research/LogBlockRecordAttempt.md` for the precise correction.

`PROGRAM_STATUS` records, as prose, that "the repo already refutes the
pointwise/block Lyapunov family", so any new drift inequality "must be genuinely
new".  That is a warning without a boundary.  This file draws the boundary.

## The schema

Every descent-style hypothesis in this development has the shape: *there is a
block length `B n` within which `n` drops below itself*.

    BlockDescent B  :=  ∀ n, 1 < n → acceleratedOrbit (B n) n < n

The **existential** over `B` is a restatement — `exists_blockDescent_iff` proves
`(∃ B, BlockDescent B) ↔ FiniteStoppingTime`, which `Reductions` already knows is
equivalent to the conjecture.  So no content lives in "some `B` works".  All the
content is in *constraining the shape of `B`*, and that is exactly what the
existing kills do.

## What is killed

`no_bounded_blockDescent` : **no bounded `B` works.**  The witness is the
Mersenne family: `DensitySaturation.no_bounded_block_descent` says
`2 ^ j − 1 < T^B(2 ^ j − 1)` whenever `0 < B < j`, so choosing `j` past the bound
defeats any `B` with a ceiling.  Three corollaries follow immediately and cover
everything the prose warning meant:

* `no_constant_blockDescent` — `B` constant (Round F's refutation);
* `no_modular_blockDescent` — `B n` a function of `n mod 2 ^ M`, since a function
  on finitely many residues is bounded;
* `no_runLength_blockDescent` — `B n = r(n) + s(r(n))` at any *fixed* run length,
  from `RunLengthAny.no_tail_at_any_run_length` (this one is not a boundedness
  consequence: `r` is unbounded, and the kill is a separate construction).

## What survives

A `B` that **grows with the size of `n`**.  Nothing above touches it, because
`no_bounded_blockDescent` needs a ceiling and `r(n)` is not the size.  The
canonical shape:

    LogBlockDescent C  :=  BlockDescent (fun n => C * Nat.log2 n)

`logBlock_unbounded` shows the block length is unbounded, so the boundedness kill
provably does not apply; `collatz_of_logBlockDescent` shows it would settle the
conjecture.  This is standing problem **G3** with an explicit function in place of
"controlled by a proved function of `n`".

It is not vacuous in either direction.  `not_logBlockDescent_one` refutes `C = 1`
outright, from `MersenneLower.mersenne_sigma_gt`: the family `2 ^ (2m) − 1` has
`log₂ ≈ 2m − 1` but takes more than `3m` steps to drop.  And
`Strategy.MersenneDescent` checks the same family descends within `12 j` for
`2 ≤ j ≤ 200`, so `C = 12` is not refuted there.  The open interval is
`2 ≤ C ≤ 12` as far as this development can see, and `LogBlockDescent C` for any
`C` is open.

## Honest scope

Nothing here proves a new descent fact.  What it does is convert a prose warning
into theorems, so a future round can check a proposed drift hypothesis against
`no_bounded_blockDescent` mechanically instead of against a remembered caution —
the same service `GapBarriers.exists_realizer` performs for the reachability
warning.
-/

namespace Collatz
namespace DriftSurvivors

open Reach Strategy

/-! ## The schema -/

/-- A descent schema: `n` drops below itself within `B n` accelerated steps. -/
def BlockDescent (B : Nat → Nat) : Prop :=
  ∀ n : Nat, 1 < n → acceleratedOrbit (B n) n < n

theorem finiteStoppingTime_of_blockDescent {B : Nat → Nat} (h : BlockDescent B) :
    Strategy.FiniteStoppingTime := fun n hn => ⟨B n, h n hn⟩

/-- Any block-descent schema settles the conjecture. -/
theorem collatz_of_blockDescent {B : Nat → Nat} (h : BlockDescent B) :
    CollatzConjecture :=
  Strategy.collatz_of_finiteStoppingTime (finiteStoppingTime_of_blockDescent h)

/-- **The existential is a restatement.**  Content lives only in the shape of
`B`, never in its existence. -/
theorem exists_blockDescent_iff :
    (∃ B : Nat → Nat, BlockDescent B) ↔ Strategy.FiniteStoppingTime := by
  constructor
  · rintro ⟨B, hB⟩
    exact finiteStoppingTime_of_blockDescent hB
  · intro h
    have h' : ∀ n : Nat, 1 < n → ∃ k : Nat, acceleratedOrbit k n < n := h
    refine ⟨fun n => if hn : 1 < n then Classical.choose (h' n hn) else 0, ?_⟩
    intro n hn
    show acceleratedOrbit (if hn : 1 < n then Classical.choose (h' n hn) else 0) n < n
    rw [dif_pos hn]
    exact Classical.choose_spec (h' n hn)

/-! ## The boundedness kill -/

/-- **No bounded block length works.**  The Mersenne family `2 ^ j − 1` rises at
every step below `j`, so a ceiling `c` is defeated at `j = c + 2`. -/
theorem no_bounded_blockDescent {B : Nat → Nat} {c : Nat} (hb : ∀ n : Nat, B n ≤ c) :
    ¬ BlockDescent B := by
  intro h
  have hp2 : (2:Nat) ^ 2 = 4 := by decide
  have hpow : (2:Nat) ^ 2 ≤ 2 ^ (c + 2) := Nat.pow_le_pow_right (by omega) (by omega)
  have hn1 : 1 < 2 ^ (c + 2) - 1 := by omega
  have hdrop := h (2 ^ (c + 2) - 1) hn1
  have hble : B (2 ^ (c + 2) - 1) ≤ c := hb _
  rcases Nat.eq_zero_or_pos (B (2 ^ (c + 2) - 1)) with h0 | hpos
  · rw [h0, acceleratedOrbit_zero] at hdrop
    omega
  · have hrise := DensitySaturation.no_bounded_block_descent
      (B := B (2 ^ (c + 2) - 1)) (j := c + 2) hpos (by omega)
    omega

/-- `B` constant. -/
theorem no_constant_blockDescent (c : Nat) : ¬ BlockDescent (fun _ => c) :=
  no_bounded_blockDescent (c := c) (fun _ => Nat.le_refl c)

/-- `B n` determined by `n` modulo a fixed power of two.  A function on finitely
many residues is bounded, so this is the boundedness kill again — the reason the
"emptying residue classes" family cannot supply a descent schema either. -/
theorem no_modular_blockDescent {M c : Nat} (f : Nat → Nat)
    (hf : ∀ r : Nat, r < 2 ^ M → f r ≤ c) :
    ¬ BlockDescent (fun n => f (n % 2 ^ M)) := by
  refine no_bounded_blockDescent (c := c) (fun n => hf _ ?_)
  have h1 : 1 ≤ (2:Nat) ^ M := Nat.one_le_pow M 2 (by omega)
  exact Nat.mod_lt _ (by omega)

/-! ## The run-length kill

Not a boundedness consequence: `r(n) = v₂(n+1)` is unbounded.  It is
`RunLengthAny.no_tail_at_any_run_length`, restated against the schema. -/

/-- **No tail keyed to the run length works.**  For every `s` and every run
length `i + 2` there is an `n` with that run length exactly whose orbit has not
dropped after `i + 2 + s (i + 2)` steps. -/
theorem no_runLength_blockDescent (s : Nat → Nat) (i : Nat) :
    ∃ n d : Nat, 1 < n ∧ d % 2 = 1 ∧ n + 1 = 2 ^ (i + 2) * d ∧
      ¬ acceleratedOrbit (i + 2 + s (i + 2)) n < n := by
  obtain ⟨n, d, hd, hnd, hge⟩ :=
    RunLengthAny.no_tail_at_any_run_length i (i + 2 + s (i + 2))
  have hp2 : (2:Nat) ^ 2 = 4 := by decide
  have h4 : (2:Nat) ^ 2 ≤ 2 ^ (i + 2) := Nat.pow_le_pow_right (by omega) (by omega)
  have hdpos : 1 ≤ d := by omega
  have hm1 : (2:Nat) ^ (i + 2) * 1 ≤ 2 ^ (i + 2) * d :=
    Nat.mul_le_mul (Nat.le_refl _) hdpos
  have hm2 : (2:Nat) ^ (i + 2) * 1 = 2 ^ (i + 2) := Nat.mul_one _
  exact ⟨n, d, by omega, hd, hnd, by omega⟩

/-! ## The survivor -/

/-- Block length linear in the bit length.  This is standing problem `G3` with an
explicit function. -/
def LogBlockDescent (C : Nat) : Prop := BlockDescent (fun n => C * Nat.log2 n)

/-- It would settle the conjecture. -/
theorem collatz_of_logBlockDescent {C : Nat} (h : LogBlockDescent C) : CollatzConjecture :=
  collatz_of_blockDescent h

/-- **The boundedness kill provably does not apply**: the block length is
unbounded.  Witnessed on the powers of two, where `Nat.log2 (2 ^ k) = k`. -/
theorem logBlock_unbounded {C : Nat} (hC : 0 < C) (c : Nat) :
    ∃ n : Nat, c < C * Nat.log2 n := by
  refine ⟨2 ^ (c + 1), ?_⟩
  have hlog : Nat.log2 (2 ^ (c + 1)) = c + 1 := Nat.log2_two_pow
  rw [hlog]
  have hm : 1 * (c + 1) ≤ C * (c + 1) := Nat.mul_le_mul (by omega) (Nat.le_refl _)
  omega

/-- **`C = 1` is refuted.**  `2 ^ (2m) − 1` has `Nat.log2 = 2m − 1` but needs more
than `3m` steps to drop, and `2m − 1 ≤ 3m`. -/
theorem not_logBlockDescent_one : ¬ LogBlockDescent 1 := by
  intro h
  have hdrop : acceleratedOrbit (1 * Nat.log2 3) 3 < 3 := h 3 (by omega)
  have hlog : (1:Nat) * Nat.log2 3 = 1 := by decide
  rw [hlog] at hdrop
  have hge := MersenneLower.mersenne_sigma_gt 1 1 (by omega)
  have he : (2:Nat) ^ (2 * 1) - 1 = 3 := by decide
  rw [he] at hge
  omega

/-! ## The divergence-side range, refreshed

`Escape.divergent_avoids_verified` states the same fact at `1 086 464`, the
verified range of the round that wrote it.  `Search.VerifiedRung11025` has since
reached `2 404 352`, so the exclusion zone is `2.2` times wider.  The proof is
`Escape`'s, at the current constant.

This is the strongest unconditional statement the development has about a
divergent orbit: it never takes a value below `2 404 352`, so its minimum — which
exists, by `AccCycle.exists_accCycleMin` — is at least that, and
`Frontier11025.heavy_window_6955` then applies to it.  A divergent orbit is heavy
for its first `6955` accelerated steps from its minimum, with more than `4379` of
those steps odd (`Frontier11025.odd_steps_6955`).  Those two facts are stated for
any non-reaching `n`, so they cover divergence as well as cycles; what is new here
is only the range. -/

theorem divergent_avoids_2404352 {n : Nat} (h : Divergence.Divergent n) (i : Nat)
    (hpos : 0 < orbit i n) : 2404352 ≤ orbit i n := by
  by_cases hlt : orbit i n < 2404352
  · exfalso
    exact Divergence.not_divergent_of_reachesOne
      (Search.reachesOne_of_lt_2404352 hpos hlt) (Escape.divergent_tail h i)
  · omega

/-- The window collapses on the whole refreshed range. -/
theorem divergent_window_one_2404352 {n : Nat} (h : Divergence.Divergent n) (i : Nat)
    (hpos : 0 < orbit i n) {B : Nat} (hB : B < 2404352) : B < orbit i n :=
  Nat.lt_of_lt_of_le hB (divergent_avoids_2404352 h i hpos)

/-! ## Correction: the schema should read "within", not "at exactly"

`BlockDescent` asks for the drop *at* step `B n`.  That is the wrong reading of
`G3`, and it is refutable for uninteresting reasons: an orbit that has already
dropped can come back up, so `T^(B n)(n) < n` can fail at a step where the orbit
had descended long before.  `27` shows it — it first falls below itself at step
`59`, but `T^60(27) = 35`.

The faithful schema asks for a drop *somewhere within* the block. -/

/-- `n` drops below itself within `B n` accelerated steps.  This is `G3`'s reading. -/
def BlockDescentWithin (B : Nat → Nat) : Prop :=
  ∀ n : Nat, 1 < n → ∃ k : Nat, k ≤ B n ∧ acceleratedOrbit k n < n

theorem blockDescentWithin_of_blockDescent {B : Nat → Nat} (h : BlockDescent B) :
    BlockDescentWithin B := fun n hn => ⟨B n, Nat.le_refl _, h n hn⟩

theorem collatz_of_blockDescentWithin {B : Nat → Nat} (h : BlockDescentWithin B) :
    CollatzConjecture :=
  Strategy.collatz_of_finiteStoppingTime (fun n hn => by
    obtain ⟨k, _, hk⟩ := h n hn
    exact ⟨k, hk⟩)

/-- **The boundedness kill survives the correction.**  `no_bounded_block_descent`
gives a rise at *every* step below `j`, not just one, so the Mersenne witness
defeats the "within" reading too. -/
theorem no_bounded_blockDescentWithin {B : Nat → Nat} {c : Nat} (hb : ∀ n : Nat, B n ≤ c) :
    ¬ BlockDescentWithin B := by
  intro h
  have hp2 : (2:Nat) ^ 2 = 4 := by decide
  have hpow : (2:Nat) ^ 2 ≤ 2 ^ (c + 2) := Nat.pow_le_pow_right (by omega) (by omega)
  have hn1 : 1 < 2 ^ (c + 2) - 1 := by omega
  obtain ⟨k, hk, hdrop⟩ := h (2 ^ (c + 2) - 1) hn1
  have hble : B (2 ^ (c + 2) - 1) ≤ c := hb _
  rcases Nat.eq_zero_or_pos k with h0 | hpos
  · rw [h0, acceleratedOrbit_zero] at hdrop
    omega
  · have hrise := DensitySaturation.no_bounded_block_descent
      (B := k) (j := c + 2) hpos (by omega)
    omega

/-- The survivor, in the corrected reading. -/
def LogBlockDescentWithin (C : Nat) : Prop :=
  BlockDescentWithin (fun n => C * Nat.log2 n)

theorem collatz_of_logBlockDescentWithin {C : Nat} (h : LogBlockDescentWithin C) :
    CollatzConjecture := collatz_of_blockDescentWithin h

/-- **`C ≤ 14` is refuted, by `27` alone.**  `Nat.log2 27 = 4` and `27` does not
fall below itself until step `59`, so a block of `14 · 4 = 56` steps is not
enough.  This supersedes `not_logBlockDescent_one`, which was weaker by a factor
of fourteen.

A scan of every odd `n < 3 · 10⁶` finds **no** larger value of
`σ(n) / ⌊log₂ n⌋` than `27`'s `59/4 = 14.75`; the only earlier record is `n = 3`
at `4`.  So `C ≥ 15` is open, and the records are extremely sparse — two of them
below three million. -/
theorem not_logBlockDescentWithin_fourteen : ¬ LogBlockDescentWithin 14 := by
  intro h
  obtain ⟨k, hk, hdrop⟩ := h 27 (by omega)
  have hk' : k ≤ 14 * Nat.log2 27 := hk
  have hlog : (14:Nat) * Nat.log2 27 = 56 := by decide
  rw [hlog] at hk'
  have hno : ∀ j : Nat, j ≤ 56 → 27 ≤ acceleratedOrbit j 27 := by decide
  have := hno k hk'
  omega

/-! ## Prior art: this is Rozier's falling-time conjecture

**Added Round LXXV.27, correcting an omission.**  The `LogBlockDescentWithin C`
line was developed here without a literature check, and it is not new.  It is a
renormalisation of a published open conjecture.

O. Rozier, *Is the Syracuse falling time bounded by 12?* (arXiv:2107.11160; in
*Number Theory and Applications*, Springer 2022) defines the Syracuse *jump* as
`⌊log₂ n⌋ + 1` Syracuse steps and the *falling time* `sft(n)` as the least number
of jumps landing below `n`.  That is exactly this file's schema with the block
length measured in jumps rather than accelerated steps: `LogBlockDescentWithin C`
is `sft(n) ≤ C` up to the change of unit.  Rozier reports the largest known
`sft` as `10`, conjectures `sft` uniformly bounded, and records
`ft(12 235 060 455) = 14` — the same integer this development rediscovered in
Round LXXV.11 as a ratio record and banked as
`not_logBlockDescentWithin_sixteen`.

`63 728 127` (Round LXXV.10) is likewise a known record, the longest total
stopping time below `10 ^ 8`.

So: the schema, the conjecture, and both record witnesses are prior art.  What
this file adds is **formalisation** — the kills as machine-checked theorems, the
refutations as `decide`-backed witnesses, and `collatz_of_logBlock17_above` with
its finite part discharged in the kernel.  That is worth having and is not a
mathematical contribution; the entry is corrected so no later reader mistakes one
for the other.

The repository already cites Rozier for a different result
(`Papers/rozier-terracol-2026-paradoxical.md`, used by `Strategy.Paradoxical`),
which makes the omission a search failure rather than an unavailable source. -/

/-! ## Refuting `LogBlockDescentWithin C`, parametrically

A refutation needs one number: an `n` whose stopping time exceeds `C · ⌊log₂ n⌋`.
Stated once, so a new record costs one `decide` rather than a new proof. -/

/-- **A witness refutes `LogBlockDescentWithin C`.**  `hno` says the orbit of `n`
has not fallen below `n` at any step up to `C · L`, where `L = ⌊log₂ n⌋`. -/
theorem not_logBlockDescentWithin_of_witness {C n L : Nat} (h1 : 1 < n)
    (hL : Nat.log2 n = L) (hno : ∀ j : Nat, j ≤ C * L → n ≤ acceleratedOrbit j n) :
    ¬ LogBlockDescentWithin C := by
  intro h
  obtain ⟨k, hk, hdrop⟩ := h n h1
  have hk' : k ≤ C * Nat.log2 n := hk
  rw [hL] at hk'
  have := hno k hk'
  omega

/-! ### The two records

`σ(n) / ⌊log₂ n⌋` has exactly three record values below `2 · 10⁸`, found by direct
scan: `n = 3` at `4`, `n = 27` at `59/4 = 14.75`, and `n = 63 728 127` at
`376/25 = 15.04`.  The gap between the second and third is a factor of `2.4`
million in `n` for a gain of `0.29` in the ratio — the landscape is sparse, and
enumeration to `3 · 10⁶` (this file's previous state) stopped just short.

The second record's orbit peaks at `483 308 017 730`, `39` bits, so the kernel
computation is small despite the `376` steps. -/

set_option maxRecDepth 4000 in
theorem log2_63728127 : Nat.log2 63728127 = 25 := by decide

set_option maxRecDepth 100000 in
theorem no_drop_63728127 :
    ∀ j : Nat, j ≤ 15 * 25 → 63728127 ≤ acceleratedOrbit j 63728127 := by decide

/-- **`C ≤ 15` is refuted.**  `63 728 127` has `⌊log₂⌋ = 25` and does not fall
below itself until step `376`, against a block of `15 · 25 = 375`. -/
theorem not_logBlockDescentWithin_fifteen : ¬ LogBlockDescentWithin 15 :=
  not_logBlockDescentWithin_of_witness (by omega) log2_63728127 no_drop_63728127

/-! ## The other side: a verified base range for `C = 16`

`not_logBlockDescentWithin_fifteen` says `C ≤ 15` fails.  A scan of every odd
`n < 10 ^ 10` finds no ratio above `15.04`, so `C = 16` is unrefuted there.  This
section verifies it in the kernel on an initial range.

`Search.exists_lt_of_dropsWithin` forgets the bound on `k`, which is exactly what
`BlockDescentWithin` needs, so the bounded soundness lemma comes first.  It is
the same induction with the index tracked, and it is reusable: any future descent
work over `dropsWithin` needs it. -/

theorem exists_le_of_dropsAux {n : Nat} : ∀ (fuel j : Nat),
    Search.dropsAux n fuel (acceleratedOrbit j n) = true →
    ∃ k : Nat, k ≤ j + fuel ∧ acceleratedOrbit k n < n := by
  intro fuel
  induction fuel with
  | zero => intro j h; simp [Search.dropsAux] at h
  | succ fuel ih =>
    intro j h
    rw [Search.dropsAux_succ] at h
    have hnext : acceleratedStep (acceleratedOrbit j n) = acceleratedOrbit (j + 1) n :=
      (acceleratedOrbit_succ_step j n).symm
    by_cases hlt : acceleratedStep (acceleratedOrbit j n) < n
    · exact ⟨j + 1, by omega, by rw [← hnext]; exact hlt⟩
    · rw [if_neg hlt, hnext] at h
      obtain ⟨k, hk, hlt'⟩ := ih (j + 1) h
      exact ⟨k, by omega, hlt'⟩

/-- **Bounded soundness of the drop search.**  `Search.exists_lt_of_dropsWithin`
with the witness index bounded by the fuel. -/
theorem exists_le_of_dropsWithin {fuel n : Nat} (h : Search.dropsWithin fuel n = true) :
    ∃ k : Nat, k ≤ fuel ∧ acceleratedOrbit k n < n := by
  obtain ⟨k, hk, hlt⟩ :=
    exists_le_of_dropsAux (n := n) fuel 0 (by rw [acceleratedOrbit]; exact h)
  exact ⟨k, by omega, hlt⟩

/-! ### The sweep -/

/-- Check that every `n` in `[lo, lo + len)` drops within `16 · ⌊log₂ n⌋` steps. -/
def logCheck (lo len : Nat) : Bool :=
  match len with
  | 0 => true
  | k + 1 => Search.dropsWithin (16 * Nat.log2 (lo + k)) (lo + k) && logCheck lo k

theorem logCheck_read {lo len n : Nat} (h : logCheck lo len = true)
    (hlo : lo ≤ n) (hhi : n < lo + len) :
    Search.dropsWithin (16 * Nat.log2 n) n = true := by
  induction len with
  | zero => omega
  | succ k ih =>
    rw [logCheck, Bool.and_eq_true] at h
    by_cases hnk : n < lo + k
    · exact ih h.2 hnk
    · have : n = lo + k := by omega
      subst this
      exact h.1

set_option maxHeartbeats 4000000 in
set_option maxRecDepth 100000 in
theorem logCheck_2_20000 : logCheck 2 19998 = true := by decide

/-- **`LogBlockDescentWithin 16` holds below `20 000`.**  Every `n` with
`2 ≤ n < 20 000` falls below itself within `16 · ⌊log₂ n⌋` accelerated steps.

Certificate story: `logCheck` runs `Search.dropsWithin` at the per-`n` fuel
`16 · ⌊log₂ n⌋` for each of the `19 998` values and conjoins the results; the
kernel evaluates it by `decide`, `logCheck_read` extracts one entry, and
`exists_le_of_dropsWithin` turns the Boolean into the bounded existential.  No
`native_decide`.

The unverified scan reaches `10 ^ 10` with the same conclusion; this is the part
the kernel has checked. -/
theorem logBlockDescentWithin_16_below_20000 {n : Nat} (h2 : 2 ≤ n) (hN : n < 20000) :
    ∃ k : Nat, k ≤ 16 * Nat.log2 n ∧ acceleratedOrbit k n < n :=
  exists_le_of_dropsWithin (logCheck_read logCheck_2_20000 h2 (by omega))

/-! ### The third record, and where the ratio is heading

A parallel scan past `10 ^ 10` found a fourth record almost at once:

```
n = 12 235 060 455    σ = 547    ⌊log₂ n⌋ = 33    ratio = 16.58
```

so `C ≤ 16` falls too.  The orbit peaks at `49` bits, again small.

**The ratios are climbing, and there is a predicted ceiling.**  The number of
`n < N` with `σ(n) > k` is heuristically `N · 2 ^ (−γk)` with
`γ = 1 − H(log₃ 2) = 0.05004…` — the large-deviation rate that `CLOSURE.md`
identifies as *the* constant of this repository's Class 2, where it already
appears as the heavy-language density deficit and the bounded-reverse-path
exponent.  If that heuristic is right, the largest `σ` below `N` is about
`log₂ N / γ`, so

    sup  σ(n) / ⌊log₂ n⌋  =  1/γ  ≈  19.98.

That would make **`C = 20` the critical constant** for `LogBlockDescentWithin`,
with every `C ≤ 19` refutable by a large enough scan and `C ≥ 20` the only
possibly-true range.  Nothing here proves it: `γ` is a density statement and this
is a pointwise supremum, which is exactly the "almost all, therefore all" gap the
brief warns about.  What is proved is the climb so far — `14.75`, `15.04`,
`16.58` — and the observation that the target it appears to approach is a
constant the development already has a name for.

Practical consequence: refuting a given `C ≤ 19` is a search problem with a
predicted stopping point, not an open mathematical question.  Each hit costs one
`decide`. -/

set_option maxRecDepth 4000 in
theorem log2_12235060455 : Nat.log2 12235060455 = 33 := by decide

set_option maxRecDepth 200000 in
theorem no_drop_12235060455 :
    ∀ j : Nat, j ≤ 16 * 33 → 12235060455 ≤ acceleratedOrbit j 12235060455 := by decide

/-- **`C ≤ 16` is refuted.**  `12 235 060 455` has `⌊log₂⌋ = 33` and does not fall
below itself until step `547`, against a block of `16 · 33 = 528`. -/
theorem not_logBlockDescentWithin_sixteen : ¬ LogBlockDescentWithin 16 :=
  not_logBlockDescentWithin_of_witness (by omega) log2_12235060455 no_drop_12235060455

/-! ## The scan completed, and the live constant is `C = 17`

The `[10 ^ 10, 10 ^ 12)` sweep finished: eight workers, the whole interval, and
**exactly one record** — the `16.5758` at `n = 12 235 060 455` already banked.
So over every odd `n < 10 ^ 12`,

    σ(n) / ⌊log₂ n⌋  ≤  16.5758,

`C ≤ 16` is refuted and `C = 17` is the smallest value not refuted anywhere.

Against the Class 2 prediction of `1/γ ≈ 19.98`: the observed maximum is `16.58`
at `10 ^ 12`, so if the prediction is right the convergence is slow, and three
more integer values of `C` remain to be knocked out by search.  The prediction is
neither confirmed nor contradicted by this scan; recording it as such.

This section verifies `C = 17` in the kernel on an initial range, chunked in the
repository's own `checkRange` style — one `decide` over `10 ^ 5` does not
terminate, five over `2 · 10 ^ 4` do. -/

/-- `logCheck` at an arbitrary constant. -/
def logCheckC (C lo len : Nat) : Bool :=
  match len with
  | 0 => true
  | k + 1 => Search.dropsWithin (C * Nat.log2 (lo + k)) (lo + k) && logCheckC C lo k

theorem logCheckC_read {C lo len n : Nat} (h : logCheckC C lo len = true)
    (hlo : lo ≤ n) (hhi : n < lo + len) :
    Search.dropsWithin (C * Nat.log2 n) n = true := by
  induction len with
  | zero => omega
  | succ k ih =>
    rw [logCheckC, Bool.and_eq_true] at h
    by_cases hnk : n < lo + k
    · exact ih h.2 hnk
    · have : n = lo + k := by omega
      subst this
      exact h.1

set_option maxHeartbeats 4000000 in
set_option maxRecDepth 100000 in
theorem lc17_a : logCheckC 17 2 19998 = true := by decide

set_option maxHeartbeats 4000000 in
set_option maxRecDepth 100000 in
theorem lc17_b : logCheckC 17 20000 20000 = true := by decide

set_option maxHeartbeats 4000000 in
set_option maxRecDepth 100000 in
theorem lc17_c : logCheckC 17 40000 20000 = true := by decide

set_option maxHeartbeats 4000000 in
set_option maxRecDepth 100000 in
theorem lc17_d : logCheckC 17 60000 20000 = true := by decide

set_option maxHeartbeats 4000000 in
set_option maxRecDepth 100000 in
theorem lc17_e : logCheckC 17 80000 20000 = true := by decide

/-- **`LogBlockDescentWithin 17` holds below `100 000`.**  Every `n` with
`2 ≤ n < 100 000` falls below itself within `17 · ⌊log₂ n⌋` accelerated steps.

Certificate story unchanged from the `C = 16` version, except that the sweep is
five chunks rather than one: `logCheckC` runs `Search.dropsWithin` at the per-`n`
fuel `17 · ⌊log₂ n⌋`, `decide` evaluates each chunk, `logCheckC_read` extracts one
entry, and `exists_le_of_dropsWithin` turns the Boolean into the bounded
existential.  No `native_decide`.

The unverified scan reaches `10 ^ 12` with the same conclusion; this is the part
the kernel has checked. -/
theorem logBlockDescentWithin_17_below_100000 {n : Nat} (h2 : 2 ≤ n) (hN : n < 100000) :
    ∃ k : Nat, k ≤ 17 * Nat.log2 n ∧ acceleratedOrbit k n < n := by
  refine exists_le_of_dropsWithin ?_
  rcases Nat.lt_or_ge n 40000 with h | h
  · rcases Nat.lt_or_ge n 20000 with h1 | h1
    · exact logCheckC_read lc17_a h2 (by omega)
    · exact logCheckC_read lc17_b h1 (by omega)
  · rcases Nat.lt_or_ge n 80000 with h1 | h1
    · rcases Nat.lt_or_ge n 60000 with h2' | h2'
      · exact logCheckC_read lc17_c h (by omega)
      · exact logCheckC_read lc17_d h2' (by omega)
    · exact logCheckC_read lc17_e h1 (by omega)

/-! ## Closing the gap between the kernel range and the scan

`logBlockDescentWithin_17_below_100000` checks `10 ^ 5` by brute kernel
computation, against a scan that reaches `10 ^ 12`.  Most of that gap closes for
free, because the repository has already swept `[1, 3 998 720)` at fuel `224`
for `Search.VerifiedRung14187`, and `224 ≤ 17 · ⌊log₂ n⌋` as soon as
`⌊log₂ n⌋ ≥ 14`.

Two ingredients are needed.  The survivor half is the block sweep plus
`exists_le_of_dropsWithin`.  The non-survivor half needs the sieve's drop to be
*bounded*, and it is — `Congruence.exists_descends_of_not_survives` produces an
index `i ≤ K`, and `Strategy.exists_drop_of_not_survives` simply forgets it, the
same way `Search.exists_lt_of_dropsWithin` forgot its bound.  Recovering it is
the proof below with `⟨i, hiK, _⟩` in place of `⟨i, _⟩`. -/

/-- **The sieve's drop, with its index bound kept.**
`Strategy.exists_drop_of_not_survives` with the witness bounded by `K`. -/
theorem exists_le_drop_of_not_survives {n K : Nat} (hn : 1024 < n) (hK : K ≤ 10)
    (h : ¬ Congruence.survives K (n % 2 ^ K) = true) :
    ∃ k : Nat, k ≤ K ∧ acceleratedOrbit k n < n := by
  obtain ⟨i, hiK, hd⟩ := Congruence.exists_descends_of_not_survives h
  have hmod : n % 2 ^ K % 2 ^ i = n % 2 ^ i := Minimal.mod_pow_two_mod (by omega)
  rw [hmod] at hd
  have hle : 2 ^ i ≤ n := by
    have h1 : (2:Nat) ^ i ≤ 2 ^ 10 := Arith.two_pow_le_two_pow (by omega)
    have h2 : (2:Nat) ^ 10 = 1024 := by decide
    omega
  exact ⟨i, hiK, Congruence.accOrbit_lt_of_descends_of_mod hd hle⟩

/-- **`LogBlockDescentWithin 17` on the whole verified range.**  Every `n` with
`2 ≤ n < 3 998 720` falls below itself within `17 · ⌊log₂ n⌋` accelerated steps —
a fortyfold extension of the direct check, at no kernel cost beyond the sweep
that `Search.VerifiedRung14187` already performs.

Certificate story: below `40 000` it is the five `logCheckC` chunks.  Above, `n`
either survives the level-`10` sieve — and then `Search.drops_all_3905` gives
`dropsWithin 224 n`, with `224 ≤ 17 · 15 ≤ 17 · ⌊log₂ n⌋` — or it does not, and
`exists_le_drop_of_not_survives` gives a drop within `10` steps.  No
`native_decide`, and no new kernel computation at all. -/
theorem logBlockDescentWithin_17_below_3998720 {n : Nat} (h2 : 2 ≤ n)
    (hN : n < 3998720) :
    ∃ k : Nat, k ≤ 17 * Nat.log2 n ∧ acceleratedOrbit k n < n := by
  rcases Nat.lt_or_ge n 40000 with hsmall | hbig
  · exact logBlockDescentWithin_17_below_100000 h2 (by omega)
  · have hp : (2:Nat) ^ 10 = 1024 := by decide
    have hlog : 15 ≤ Nat.log2 n := by
      refine (Nat.le_log2 (by omega)).mpr ?_
      have h15 : (2:Nat) ^ 15 = 32768 := by decide
      omega
    by_cases hs : Congruence.survives 10 (n % 2 ^ 10) = true
    · have hmem := Search.mem_survivors_of_survives hs
      have hlt : n / 2 ^ 10 < 3905 := by rw [hp]; omega
      have hdec : 2 ^ 10 * (n / 2 ^ 10) + n % 2 ^ 10 = n := Nat.div_add_mod n (2 ^ 10)
      have hcheck := Search.drops_all_3905 hlt hmem
      rw [hdec] at hcheck
      obtain ⟨k, hk, hlt'⟩ := exists_le_of_dropsWithin hcheck
      exact ⟨k, by omega, hlt'⟩
    · obtain ⟨k, hk, hlt'⟩ :=
        exists_le_drop_of_not_survives (K := 10) (by omega) (Nat.le_refl 10) hs
      exact ⟨k, by omega, hlt'⟩

/-! ## What is actually left: the reduction, stated exactly

The verified range and the `C = 17` range are now the same number, `3 998 720`.
That makes the brief's pattern (C) — *a reduction to a finite check plus a proved
bound* — statable with nothing hidden: the finite check is done, and what remains
is exactly the tail.

`collatz_of_logBlock17_above` is the honest form of standing problem `G3` for this
development.  Its hypothesis is not a weakening of the conjecture dressed up; it
is a bound on the stopping time of numbers *above a range this repository has
verified in the kernel*, with the constant pinned between the refuted `16` and
the heuristic ceiling `19.98`. -/

/-- **The reduction.**  If every `n ≥ 3 998 720` falls below itself within
`17 · ⌊log₂ n⌋` accelerated steps, the Collatz conjecture follows — because
everything below `3 998 720` is already proved
(`logBlockDescentWithin_17_below_3998720`).

This is the whole outstanding content of the `C = 17` line, with the finite part
discharged. -/
theorem collatz_of_logBlock17_above
    (h : ∀ n : Nat, 3998720 ≤ n →
      ∃ k : Nat, k ≤ 17 * Nat.log2 n ∧ acceleratedOrbit k n < n) :
    CollatzConjecture := by
  refine collatz_of_blockDescentWithin (B := fun n => 17 * Nat.log2 n) ?_
  intro n hn
  rcases Nat.lt_or_ge n 3998720 with hlt | hge
  · exact logBlockDescentWithin_17_below_3998720 (by omega) hlt
  · exact h n hge

/-- The same, with the range as a parameter: any future extension of the verified
range moves the threshold with no new proof. -/
theorem collatz_of_logBlock17_above_of {N : Nat}
    (hbase : ∀ n : Nat, 2 ≤ n → n < N →
      ∃ k : Nat, k ≤ 17 * Nat.log2 n ∧ acceleratedOrbit k n < n)
    (h : ∀ n : Nat, N ≤ n → ∃ k : Nat, k ≤ 17 * Nat.log2 n ∧ acceleratedOrbit k n < n) :
    CollatzConjecture := by
  refine collatz_of_blockDescentWithin (B := fun n => 17 * Nat.log2 n) ?_
  intro n hn
  rcases Nat.lt_or_ge n N with hlt | hge
  · exact hbase n (by omega) hlt
  · exact h n hge

/-! ## Does the heavy-window machinery bear on the reduction?  No, and why

`Frontier14187.heavy_window_8950` constrains never-droppers above `3 997 765` —
the same regime as `collatz_of_logBlock17_above`'s hypothesis — so it is the
natural thing to try.  It does not help, and the reason is already a theorem
here.

Heaviness says `2 ^ j ≤ 3 ^ (oddCount m j)`, and `RunAlgebra.heavy_even_bound`
turns that into `17 · (even steps) < 10 · (odd steps)`: a constraint on the
*shape* of the first `j` steps, forcing more than `17/27` of them odd.  It says
nothing about `j` itself, because **the heavy language is nonempty at every
length** — `ValuationDensity.Enum_pos` proves `E_ℓ ≥ 2 ^ (−ℓ) > 0` for all `ℓ`,
with the all-ones word as an explicit witness at every scale.  So a bound of the
form "heavy ⟹ `j` small" is refuted outright.

Heaviness is also **scale-free**: it is a statement about the valuation word, and
carries no information about the size of `n`.  The certificate machinery does
bring `n`'s size in, but in the direction *`n` large ⟹ heavy*, never the reverse.
So nothing in that stack bounds `σ(n)` against `log₂ n`, which is the whole
content of the reduction.

What can be said cleanly is the complementary negative: the reduction's block
length genuinely has to grow. -/

theorem two_pow_ge (m : Nat) : m + 1 ≤ 2 ^ m := by
  induction m with
  | zero => decide
  | succ m ih =>
    have h : (2:Nat) ^ (m + 1) = 2 ^ m * 2 := Nat.pow_succ 2 m
    omega

/-- **No constant block length works, above any threshold.**  For every bound `B`
and every threshold `N` there is an `n > N` whose orbit has not fallen below `n`
at any step up to `B`.

`no_bounded_blockDescentWithin` already refuted constant blocks, but only by
exhibiting *some* witness; this places a witness above every `N`, which is what
the reduction needs.  It rules out the natural weakening of `G3` — "a constant
block suffices for all `n` past some `N₀`" — and so justifies the `⌊log₂ n⌋`
factor in `collatz_of_logBlock17_above` rather than leaving it a stylistic
choice. -/
theorem no_constant_above_threshold (B N : Nat) :
    ∃ n : Nat, N < n ∧ ∀ k : Nat, k ≤ B → ¬ acceleratedOrbit k n < n := by
  refine ⟨2 ^ (N + B + 2) - 1, ?_, ?_⟩
  · have h := two_pow_ge (N + B + 2)
    omega
  · intro k hk
    rcases Nat.eq_zero_or_pos k with h0 | hpos
    · rw [h0, acceleratedOrbit_zero]; omega
    · have := DensitySaturation.no_bounded_block_descent (B := k)
        (j := N + B + 2) hpos (by omega)
      omega

end DriftSurvivors
end Collatz
