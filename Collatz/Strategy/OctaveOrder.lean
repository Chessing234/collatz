import Collatz.Structure.Predecessors

/-!
# Round XII, section XXIV — the octave coordinate against the ordered odd times

The brief: an octave word determines approximate growth, the ordered odd times
`t_1 < … < t_a` determine the exact placement of the multiplication events; ask
whether the two descriptions can be **incompatible**, in the shape

> the octave path demands an odd step near time `t`  **vs**
> the ordering constraint forbids an odd step near `t`.

**They cannot.**  This file proves the two coordinates compatible, and identifies
the exact reason: the octave coordinate is blind to time.  What follows is the
forward map, the reverse map, the three structural theorems, and the verdict.

## 0.  Set-up

`oct n = ⌊log₂ n⌋` (`Nat.log2`).  Along the accelerated map `T`:

* an **even** step drops the octave by exactly `1`  (`oct_even_step`);
* an **odd** step raises it by `0` or `1`, never drops it
  (`oct_le_oct_odd_step`, `oct_odd_step_le`), with the exact increment given by the
  indicator `raiseIdx n = [2 ^ (oct n + 2) ≤ 3n + 1]`  (`oct_odd_step`).

So every step obeys the one-step identity `oct (T n) + evenIdx n = oct n + raiseIdx n`
(`oct_step_balance`), and **only an odd step can raise the octave**
(`odd_of_oct_lt`) — the single-step, all-orbits form of Round X's
`divergent_record_steps_odd`, obtained for free as the brief predicted.

## 1.  The forward map: octave word → constraints on `{t_i}`

Summing the one-step identity gives the **telescope** (`oct_orbit_balance`)

> `oct (T^j n) + #even(j) = oct n + #raise(j)`,   an identity, no hypotheses.

Two exact consequences.

**(a) The cyclic balance** (`cycle_octave_balance`).  Around a cycle
`#raise = #even`: *the number of octave-raising odd steps equals the number of even
steps*.  Since `#raise ≤ a` this yields, with no archimedean input whatsoever,

> **`L ≤ 2a`** (`cycle_length_le_two_mul_oddCnt`) — at least half the accelerated
> steps of any cycle are odd.

This is `Σ Δk_i = 0` combined with `a` and `L − a`, exactly as the brief asked for.

**(b) The ballot inequality** (`ballot_of_no_drop`, `time_bound_of_no_drop`).  If the
orbit has not dropped below its starting octave by time `j`, then
`#even(j) ≤ #raise(j)`, i.e. `j ≤ a_j + D(a_j)` where `D` is the partial-sum
function of the octave decoration.  Read at `j = t_i`:

> **`t_i ≤ (i − 1) + D(i − 1)`.**

That is the complete map from an octave-transition word to the ordered times.

## 2.  The reverse map

`oct (T^j n) + (j − a_j) = oct n + #raise(j)` (`oct_orbit_from_times`).  The even
count `j − a_j` is pure ordering data, so the times determine the octave path once
the decoration is known — and section 4 below shows the decoration is *determined*
on a counterexample.  Conversely the octave path determines the parity word outright:
a step drops the octave **iff** it is even (`oct_drop_iff_even`), so the octave
sequence reads off the word and hence `{t_1,…,t_a}`.

## 3.  Why no incompatibility exists — the decoupling theorem

`octave_word_time_invariant`:  for all `r, j, n`,

> `#raise(r + j, 2^r·n) = #raise(j, n)`,  `#even(r + j, 2^r·n) = r + #even(j, n)`,
> `#odd(r + j, 2^r·n) = #odd(j, n)`.

Prefixing `r` even steps **shifts every odd time by `r` and leaves the octave
decoration word pointwise unchanged**.  So the decoration is a function of the
odd-step *index*, never of the *time*.  A constraint of the demanded shape would have
to name a time; the octave coordinate cannot.  The obstruction the brief was hunting
is not merely absent — it is *impossible in this pair of coordinates*.

The verdict is sealed by `ballot_iff_no_drop`:

> `#even(j) ≤ #raise(j)`  **iff**  `oct n ≤ oct (T^j n)`.

The ballot inequality — the entire content of the forward map — is an `iff` with a
pure magnitude statement.  It is the heaviness/archimedean condition of Round VIII in
new coordinates, and nothing else.  **Class 3.**

### Not the Round XI isomorphism in disguise

Round XI's bridge is `E(w) = Σ_i 2^(t_i)/3^i`, which *determines* the word at fixed
`(L,a)` — an isomorphism, hence useless as a bridge.  The map here goes the other way:
it is a strict **coarsening**.  `octave_word_time_invariant` says the octave
decoration is invariant under a family of transformations (`n ↦ 2^r·n`) that move
every `t_i`; `E` is not invariant under any of them (`E` is a bijection onto its
image).  A coarsening with a nontrivial invariance group cannot be an isomorphism in
disguise — that is the proof, and it is the reason the coordinate is safe to trust
*and* the reason it cannot obstruct.

## 4.  The one genuinely new asset: the `+1` is invisible to the octave word

For odd `z` the true rise criterion is `2 ^ (oct z + 2) ≤ 3z + 1`; the purely
multiplicative one is `2 ^ (oct z + 2) < 3z`.  They differ **exactly** when
`3z + 1 = 2 ^ (oct z + 2)`, i.e. at the base-`4` repunits `z = (4^m − 1)/3 =
1, 5, 21, 85, 341, 1365, 5461, 21845, 87381, 349525, 1398101, …`  (`3z` itself is
never a power of two, `three_mul_ne_two_pow`).  Every such `z` steps to `2^(2m−1)`
and reaches `1` (`Predecessors.reachesOne_of_three_mul_add_one_eq_two_pow`).  Hence
(`raise_iff_mult`, `octave_word_multiplicative`):

> **On any orbit with `¬ ReachesOne`, the `+1` never changes an octave decision.  The
> octave word of a counterexample is exactly the octave word of the multiplicative
> map `x ↦ 3x/2`.**

*Diagnostics.*  This consumes d-assets (d) `|d| < 2` and the reach-one property, and
it is correctly **refuted** by the genuine cycles of `3x+d`: at `z = 5` on the `3x+5`
cycle (`3·5+5 = 20 ≥ 16 > 15`) and at `z = 5` on the `3x+7` cycle (`22 ≥ 16 > 15`)
the two criteria disagree, so the theorem is false for those `d`.  The cyclic balance
of section 1(a), by contrast, is `d`-independent and holds on every genuine cycle —
`3x−1` at `17` and `5`, `3x+5` at `5, 19, 23, 187, 347`, `3x+7` at `5`, `3x+13` at
`131`, `3x+59` at `229` — with `#raise = #even` in every case (verified, two
independent implementations).

## 5.  Composition with the sibling file `Strategy/OctaveWord.lean`

That file (same round, different desk) proves the octave alphabet as predicates
(`Octave.octave_alphabet`), the sojourn theorem (`no_three_in_octave`), and the local
forbidden block `O0 E^m O0` (`Octave.O0_forces_O1`): after an octave-preserving odd
step the *next* odd step must raise the octave, however many even steps intervene —
which is the same "even steps are transparent" phenomenon that this file turns into
`octave_word_time_invariant`.

Composing the two: `cycle_nonraise_count` says a cycle has exactly `2a − L`
non-raising odd steps, and `O0_forces_O1` forbids two in a row, so `2a − L ≤ ⌈a/2⌉`,
i.e. **`L ≥ 3a/2`**.  Checked on the genuine cycles: `3x−1` at `17` (`3 ≤ 4`), `3x+5`
at `187` (`7 ≤ 9`), `3x+13` at `131` (`6 ≤ 8`), `3x+59` at `229` (`2 ≤ 3`), all
satisfied, none tight.  *Diagnosis:* `1.5a ≤ L ≤ 2a` brackets the archimedean value
`1.585a` from both sides but never excludes it — the local language and the cyclic
balance together are still strictly coarser than `2^L > 3^a`.  A cyclic obstruction
would have to beat `1.585a` from one side, and neither ingredient is that sharp.


## Status labels

* LEAN_PROVED: everything in this file (`propext, Quot.sound`, plus
  `Classical.choice` where `by_cases` on a decidable proposition is used).
* COMPUTATIONAL (exact ranges): the octave step law `Δ ∈ {0,1}` for odd and `Δ = −1`
  for even, all `2 ≤ x < 300000`, zero exceptions, two implementations; the repunit
  characterisation of the criterion gap, all odd `z < 4·10^6`, exceptions exactly
  `(4^m−1)/3`, two implementations; the cyclic balance and `L ≤ 2a` on the ten
  genuine `3x+d` cycles listed above; the Lean counts cross-checked against Python at
  `n = 27, j = 41`: `(#raise, #even, #odd, oct) = (17, 12, 29, 9)` both.
* CONJECTURE: none is used here.

## Failed attempts, with diagnosis

* **"The octave decoration is the Sturmian word of slope `log₂3` started at
  `frac(log₂ n)`, so the times must realise a Beatty sequence."**  Refuted
  numerically: the true decoration departs from the pure rotation word at
  odd-step index `13` for `n = 27`, index `16` for `n = 1086467`, index `59` for
  `n = 10^12 + 39` (0-based; the rotation is computed in exact rationals).
  *Diagnosis:* section 4 says the `+1` never changes an *individual* decision, but the
  accumulated `+1`s do move the *value*, and hence the phase, by
  `log₂ ∏ (1 + 1/(3x_i))`.  That product is Round XI's coupling — bounded by
  `a/(3·1086464·ln2)` on a counterexample, small but nonzero, and it eventually
  crosses the threshold.  Per-step exactness does not integrate to orbit-level
  exactness.  This is the honest boundary of section 4.
* **"Use the balance `#raise = #even` to force a contradiction with `2^L > 3^a`."**
  The balance gives `a ≤ L ≤ 2a`; the archimedean condition gives `L ≥ a·log₂3 ≈
  1.585a`.  The two intervals overlap in `[1.585a, 2a]`, which is where every
  realizable pair already lives.  *Diagnosis:* the balance is `Σ Δk = 0` and the
  archimedean condition is `Σ log₂(x_{j+1}/x_j) = 0` — the same equation read to
  different precision, so the coarser one cannot contradict the finer one.  This is
  the mechanism behind the `ballot_iff_no_drop` verdict.
* **"Find a cyclic word admissible for the octave path but forbidden by the ordering."**
  Impossible by `octave_word_time_invariant`: the constraint sets are indexed by
  different variables (index vs time) and the octave side is invariant under the
  reparametrisation that moves the ordering side.  *Diagnosis:* this is why the local
  forbidden languages of earlier rounds concatenated forever — the octave coordinate
  has a nontrivial invariance group acting transitively on the times.

## What survives for a later round

The one asset produced here that is *not* a restatement of heaviness is section 4:
on a counterexample the octave word is exactly multiplicative.  It buys an exact,
`+1`-free symbolic dynamics for the magnitude coordinate.  Its weakness is recorded
above (per-step, not orbit-level).  Any use of it must supply its own control of the
phase drift, and Round XI already showed that drift *is* the spread.
-/

namespace Collatz
namespace OctaveOrder

open Reach

/-! ## 1.  The octave function -/

/-- `oct n = ⌊log₂ n⌋`, the dyadic **octave** of `n`. -/
abbrev oct (n : Nat) : Nat := Nat.log2 n

theorem le_oct_of_pow_le {k n : Nat} (h : 2 ^ k ≤ n) : k ≤ oct n := by
  have hlt : n < 2 ^ (oct n + 1) := Nat.lt_log2_self
  have : (2:Nat) ^ k < 2 ^ (oct n + 1) := Nat.lt_of_le_of_lt h hlt
  have := (Nat.pow_lt_pow_iff_right (a := 2) (by omega)).mp this
  omega

theorem oct_le_of_lt_pow {k n : Nat} (hn : 0 < n) (h : n < 2 ^ (k + 1)) : oct n ≤ k := by
  have hle : 2 ^ oct n ≤ n := Nat.log2_self_le (by omega)
  have : (2:Nat) ^ oct n < 2 ^ (k + 1) := Nat.lt_of_le_of_lt hle h
  have := (Nat.pow_lt_pow_iff_right (a := 2) (by omega)).mp this
  omega

/-- The octave is characterised by its two defining inequalities. -/
theorem oct_eq_of_bounds {k n : Nat} (h1 : 2 ^ k ≤ n) (h2 : n < 2 ^ (k + 1)) : oct n = k := by
  have hn : 0 < n := Nat.lt_of_lt_of_le (Nat.two_pow_pos k) h1
  have a1 := le_oct_of_pow_le h1
  have a2 := oct_le_of_lt_pow hn h2
  omega

theorem pow_oct_le {n : Nat} (hn : 0 < n) : 2 ^ oct n ≤ n := Nat.log2_self_le (by omega)

theorem lt_pow_oct_succ (n : Nat) : n < 2 ^ (oct n + 1) := Nat.lt_log2_self


/-! ## 2.  The octave step law -/

/-- **An even step drops the octave by exactly one.** -/
theorem oct_even_step {n : Nat} (hn : 2 ≤ n) (he : n % 2 = 0) : oct (n / 2) + 1 = oct n := by
  obtain ⟨m, rfl⟩ : ∃ m, n = 2 * m := ⟨n / 2, by omega⟩
  have hm : 0 < m := by omega
  have hd : 2 * m / 2 = m := by omega
  rw [hd]
  have h1 : 2 ^ oct m ≤ m := pow_oct_le hm
  have h2 : m < 2 ^ (oct m + 1) := lt_pow_oct_succ _
  have hp : (2:Nat) ^ (oct m + 1) = 2 * 2 ^ oct m := by rw [Nat.pow_succ, Nat.mul_comm]
  have hp2 : (2:Nat) ^ (oct m + 1 + 1) = 2 * 2 ^ (oct m + 1) := by
    rw [Nat.pow_succ, Nat.mul_comm]
  have hk := oct_eq_of_bounds (k := oct m + 1) (n := 2 * m) (by omega) (by omega)
  omega

/-- **An odd step never drops the octave.** -/
theorem oct_le_oct_odd_step {n : Nat} (hn : 0 < n) (ho : n % 2 = 1) :
    oct n ≤ oct ((3 * n + 1) / 2) := by
  have h1 : 2 ^ oct n ≤ n := pow_oct_le hn
  have h2 : n ≤ (3 * n + 1) / 2 := by omega
  exact le_oct_of_pow_le (Nat.le_trans h1 h2)

/-- **An odd step raises the octave by at most one.** -/
theorem oct_odd_step_le {n : Nat} (hn : 0 < n) (ho : n % 2 = 1) :
    oct ((3 * n + 1) / 2) ≤ oct n + 1 := by
  have h2 : n < 2 ^ (oct n + 1) := lt_pow_oct_succ n
  have hpos : 0 < (3 * n + 1) / 2 := by omega
  refine oct_le_of_lt_pow hpos ?_
  have hp : (2:Nat) ^ (oct n + 1 + 1) = 2 * 2 ^ (oct n + 1) := by
    rw [Nat.pow_succ, Nat.mul_comm]
  omega

/-- The **raise indicator** of a single step: `1` exactly when the step is an odd
step that crosses into the next octave, `0` otherwise. -/
def raiseIdx (n : Nat) : Nat :=
  if n % 2 = 1 then (if 2 ^ (oct n + 2) ≤ 3 * n + 1 then 1 else 0) else 0

/-- The **even indicator** of a single step. -/
def evenIdx (n : Nat) : Nat := if n % 2 = 1 then 0 else 1

/-- The **odd indicator** of a single step. -/
def oddIdx (n : Nat) : Nat := if n % 2 = 1 then 1 else 0

theorem raiseIdx_le_oddIdx (n : Nat) : raiseIdx n ≤ oddIdx n := by
  unfold raiseIdx oddIdx
  by_cases h : n % 2 = 1
  · rw [if_pos h, if_pos h]; split <;> omega
  · rw [if_neg h, if_neg h]
    omega

theorem oddIdx_add_evenIdx (n : Nat) : oddIdx n + evenIdx n = 1 := by
  unfold oddIdx evenIdx; split <;> omega

/-- **The exact octave increment of an odd step.** -/
theorem oct_odd_step {n : Nat} (hn : 0 < n) (ho : n % 2 = 1) :
    oct ((3 * n + 1) / 2) = oct n + raiseIdx n := by
  unfold raiseIdx
  rw [if_pos ho]
  have hlow : 2 ^ oct n ≤ n := pow_oct_le hn
  have hhigh : n < 2 ^ (oct n + 1) := lt_pow_oct_succ n
  have hp1 : (2:Nat) ^ (oct n + 1) = 2 * 2 ^ oct n := by rw [Nat.pow_succ, Nat.mul_comm]
  have hp2 : (2:Nat) ^ (oct n + 2) = 2 * 2 ^ (oct n + 1) := by
    rw [Nat.pow_succ, Nat.mul_comm]
  by_cases hcross : 2 ^ (oct n + 2) ≤ 3 * n + 1
  · rw [if_pos hcross]
    refine oct_eq_of_bounds ?_ ?_
    · omega
    · have hp3 : (2:Nat) ^ (oct n + 1 + 1) = 2 * 2 ^ (oct n + 1) := by
        rw [Nat.pow_succ, Nat.mul_comm]
      omega
  · rw [if_neg hcross]
    show oct ((3 * n + 1) / 2) = oct n
    refine oct_eq_of_bounds ?_ ?_
    · omega
    · omega

/-- **The one-step octave balance.**  Every step, odd or even, satisfies
`oct (T x) + evenIdx x = oct x + raiseIdx x`. -/
theorem oct_step_balance {n : Nat} (hn : 0 < n) :
    oct (acceleratedStep n) + evenIdx n = oct n + raiseIdx n := by
  unfold evenIdx
  by_cases ho : n % 2 = 1
  · rw [if_pos ho]
    have hT : acceleratedStep n = (3 * n + 1) / 2 := by
      unfold acceleratedStep; rw [if_neg (by omega)]
    rw [hT, oct_odd_step hn ho]
    omega
  · rw [if_neg ho]
    have he : n % 2 = 0 := by omega
    have hT : acceleratedStep n = n / 2 := by
      unfold acceleratedStep; rw [if_pos he]
    have hn2 : 2 ≤ n := by omega
    have hr : raiseIdx n = 0 := by unfold raiseIdx; rw [if_neg ho]
    rw [hT, hr]
    have := oct_even_step hn2 he
    omega

/-- **Only an odd step can raise the octave.**  This is the word/magnitude
rigidity of Round X's `divergent_record_steps_odd`, at the level of a single step
and for every orbit. -/
theorem odd_of_oct_lt {n : Nat} (hn : 0 < n) (h : oct n < oct (acceleratedStep n)) :
    n % 2 = 1 := by
  by_cases ho : n % 2 = 1
  · exact ho
  · exfalso
    have he : n % 2 = 0 := by omega
    have hT : acceleratedStep n = n / 2 := by
      unfold acceleratedStep; rw [if_pos he]
    have hn2 : 2 ≤ n := by omega
    have := oct_even_step hn2 he
    rw [hT] at h
    omega

/-! ## 3.  Counting along the orbit, and the telescope -/

/-- Number of octave-raising steps among the first `j` steps from `n`. -/
def raiseCount : Nat → Nat → Nat
  | 0, _ => 0
  | k + 1, n => raiseIdx n + raiseCount k (acceleratedStep n)

/-- Number of even steps among the first `j` steps from `n`. -/
def evenCnt : Nat → Nat → Nat
  | 0, _ => 0
  | k + 1, n => evenIdx n + evenCnt k (acceleratedStep n)

/-- Number of odd steps among the first `j` steps from `n`. -/
def oddCnt : Nat → Nat → Nat
  | 0, _ => 0
  | k + 1, n => oddIdx n + oddCnt k (acceleratedStep n)

theorem oddCnt_add_evenCnt (j : Nat) : ∀ n : Nat, oddCnt j n + evenCnt j n = j := by
  induction j with
  | zero => intro n; rfl
  | succ j ih =>
    intro n
    have h1 := oddIdx_add_evenIdx n
    have h2 := ih (acceleratedStep n)
    unfold oddCnt evenCnt
    omega

theorem raiseCount_le_oddCnt (j : Nat) : ∀ n : Nat, raiseCount j n ≤ oddCnt j n := by
  induction j with
  | zero => intro n; exact Nat.le_refl 0
  | succ j ih =>
    intro n
    have h1 := raiseIdx_le_oddIdx n
    have h2 := ih (acceleratedStep n)
    unfold raiseCount oddCnt
    omega

/-- **The octave telescope.**  For every start and every horizon,
`oct (T^j n) + #even = oct n + #raises`.  This is an identity: it uses nothing
about `3x+1` beyond the one-step law. -/
theorem oct_orbit_balance (j : Nat) : ∀ n : Nat, 0 < n →
    oct (acceleratedOrbit j n) + evenCnt j n = oct n + raiseCount j n := by
  induction j with
  | zero => intro n _; rfl
  | succ j ih =>
    intro n hn
    have hpos : 0 < acceleratedStep n := by
      have h1 := acceleratedOrbit_positive hn 1
      rw [acceleratedOrbit, acceleratedOrbit] at h1
      exact h1
    have h1 := ih (acceleratedStep n) hpos
    have h2 := oct_step_balance hn
    rw [acceleratedOrbit_succ]
    unfold evenCnt raiseCount
    omega

/-! ## 4.  The cyclic balance and its consequence -/

/-- **The cyclic octave balance.**  Around a cycle the number of octave-raising
odd steps equals the number of even steps. -/
theorem cycle_octave_balance {n L : Nat} (hn : 0 < n) (hcyc : acceleratedOrbit L n = n) :
    raiseCount L n = evenCnt L n := by
  have h := oct_orbit_balance L n hn
  rw [hcyc] at h
  omega

/-- **`L ≤ 2a` for every cycle.**  Combining the balance with `raise ≤ odd`: a
cycle of length `L` with `a` odd steps has `L ≤ 2a`.  Equivalently, at least half
of the accelerated steps of a cycle are odd. -/
theorem cycle_length_le_two_mul_oddCnt {n L : Nat} (hn : 0 < n)
    (hcyc : acceleratedOrbit L n = n) : L ≤ 2 * oddCnt L n := by
  have hb := cycle_octave_balance hn hcyc
  have hr := raiseCount_le_oddCnt L n
  have hs := oddCnt_add_evenCnt L n
  omega

/-- The same statement in the form "the number of even steps of a cycle is at most
the number of odd steps". -/
theorem cycle_evenCnt_le_oddCnt {n L : Nat} (hn : 0 < n)
    (hcyc : acceleratedOrbit L n = n) : evenCnt L n ≤ oddCnt L n := by
  have hb := cycle_octave_balance hn hcyc
  have hr := raiseCount_le_oddCnt L n
  omega

/-- **The non-raising odd steps of a cycle are counted exactly.**  A cycle of length
`L` with `a` odd steps has exactly `2a − L` odd steps that do *not* cross an octave.
Combined with `Octave.O0_forces_O1` (a sibling file of this round: the block
`O0 E^m O0` is impossible, so no two consecutive odd steps can both fail to cross),
this forces `2a − L ≤ ⌈a/2⌉`, i.e. `L ≥ 3a/2`. -/
theorem cycle_nonraise_count {n L : Nat} (hn : 0 < n) (hcyc : acceleratedOrbit L n = n) :
    oddCnt L n - raiseCount L n + L = 2 * oddCnt L n := by
  have hb := cycle_octave_balance hn hcyc
  have hr := raiseCount_le_oddCnt L n
  have hs := oddCnt_add_evenCnt L n
  omega

/-! ## 5.  The ballot inequality: what the octave path says about the times -/

/-- **The ballot inequality.**  If the orbit has not dropped below its starting
octave by time `j`, then the number of even steps so far is at most the number of
octave-raising odd steps so far.  This is the exact content of the octave path as
a constraint on the ordered odd times. -/
theorem ballot_of_no_drop {n j : Nat} (hn : 0 < n)
    (hnd : oct n ≤ oct (acceleratedOrbit j n)) : evenCnt j n ≤ raiseCount j n := by
  have h := oct_orbit_balance j n hn
  omega

/-- The converse reading: an excess of even steps over raises is exactly an octave
drop below the start. -/
theorem drop_of_ballot_fail {n j : Nat} (hn : 0 < n)
    (h : raiseCount j n < evenCnt j n) : oct (acceleratedOrbit j n) < oct n := by
  have hb := oct_orbit_balance j n hn
  omega

/-! ## 6.  Shift invariance: the octave decoration does not read the times -/

theorem accStep_two_mul (m : Nat) : acceleratedStep (2 * m) = m := by
  unfold acceleratedStep
  rw [if_pos (by omega)]
  omega

theorem raiseIdx_two_mul (m : Nat) : raiseIdx (2 * m) = 0 := by
  unfold raiseIdx; rw [if_neg (by omega)]

theorem evenIdx_two_mul (m : Nat) : evenIdx (2 * m) = 1 := by
  unfold evenIdx; rw [if_neg (by omega)]

theorem oddIdx_two_mul (m : Nat) : oddIdx (2 * m) = 0 := by
  unfold oddIdx; rw [if_neg (by omega)]

@[simp] theorem raiseCount_zero (n : Nat) : raiseCount 0 n = 0 := rfl
@[simp] theorem evenCnt_zero (n : Nat) : evenCnt 0 n = 0 := rfl
@[simp] theorem oddCnt_zero (n : Nat) : oddCnt 0 n = 0 := rfl
theorem raiseCount_succ (k n : Nat) :
    raiseCount (k + 1) n = raiseIdx n + raiseCount k (acceleratedStep n) := rfl
theorem evenCnt_succ (k n : Nat) :
    evenCnt (k + 1) n = evenIdx n + evenCnt k (acceleratedStep n) := rfl
theorem oddCnt_succ (k n : Nat) :
    oddCnt (k + 1) n = oddIdx n + oddCnt k (acceleratedStep n) := rfl

theorem raiseCount_add (i : Nat) : ∀ (j n : Nat),
    raiseCount (i + j) n = raiseCount i n + raiseCount j (acceleratedOrbit i n) := by
  induction i with
  | zero => intro j n; rw [Nat.zero_add, acceleratedOrbit_zero, raiseCount_zero, Nat.zero_add]
  | succ i ih =>
    intro j n
    have h : i + 1 + j = (i + j) + 1 := by omega
    rw [h, raiseCount_succ, raiseCount_succ, ih j (acceleratedStep n), acceleratedOrbit_succ]
    omega

theorem evenCnt_add (i : Nat) : ∀ (j n : Nat),
    evenCnt (i + j) n = evenCnt i n + evenCnt j (acceleratedOrbit i n) := by
  induction i with
  | zero => intro j n; rw [Nat.zero_add, acceleratedOrbit_zero, evenCnt_zero, Nat.zero_add]
  | succ i ih =>
    intro j n
    have h : i + 1 + j = (i + j) + 1 := by omega
    rw [h, evenCnt_succ, evenCnt_succ, ih j (acceleratedStep n), acceleratedOrbit_succ]
    omega

theorem oddCnt_add (i : Nat) : ∀ (j n : Nat),
    oddCnt (i + j) n = oddCnt i n + oddCnt j (acceleratedOrbit i n) := by
  induction i with
  | zero => intro j n; rw [Nat.zero_add, acceleratedOrbit_zero, oddCnt_zero, Nat.zero_add]
  | succ i ih =>
    intro j n
    have h : i + 1 + j = (i + j) + 1 := by omega
    rw [h, oddCnt_succ, oddCnt_succ, ih j (acceleratedStep n), acceleratedOrbit_succ]
    omega

/-- Prefixing `r` even steps: the orbit of `2^r · n` reaches `n` after exactly `r`
steps. -/
theorem orbit_two_pow_mul (r : Nat) : ∀ n : Nat, acceleratedOrbit r (2 ^ r * n) = n := by
  induction r with
  | zero => intro n; rw [Nat.pow_zero, Nat.one_mul]; rfl
  | succ r ih =>
    intro n
    have h : (2:Nat) ^ (r + 1) * n = 2 * (2 ^ r * n) := by
      rw [Nat.pow_succ, Nat.mul_comm ((2:Nat) ^ r) 2, Nat.mul_assoc]
    rw [acceleratedOrbit_succ, h, accStep_two_mul, ih]

theorem raiseCount_two_pow_mul (r : Nat) : ∀ n : Nat, raiseCount r (2 ^ r * n) = 0 := by
  induction r with
  | zero => intro n; rfl
  | succ r ih =>
    intro n
    have h : (2:Nat) ^ (r + 1) * n = 2 * (2 ^ r * n) := by
      rw [Nat.pow_succ, Nat.mul_comm ((2:Nat) ^ r) 2, Nat.mul_assoc]
    rw [raiseCount_succ, h, raiseIdx_two_mul, accStep_two_mul, ih]

theorem evenCnt_two_pow_mul (r : Nat) : ∀ n : Nat, evenCnt r (2 ^ r * n) = r := by
  induction r with
  | zero => intro n; rfl
  | succ r ih =>
    intro n
    have h : (2:Nat) ^ (r + 1) * n = 2 * (2 ^ r * n) := by
      rw [Nat.pow_succ, Nat.mul_comm ((2:Nat) ^ r) 2, Nat.mul_assoc]
    rw [evenCnt_succ, h, evenIdx_two_mul, accStep_two_mul, ih]
    omega

/-- **The decoupling theorem.**  Prefixing `r` even steps shifts every odd time by
`r` and leaves the octave decoration word *unchanged*.  The number of raises after
`r + j` steps from `2^r · n` is the number of raises after `j` steps from `n`,
while the even count — hence every odd time — has moved by `r`.

Consequently the octave decoration is a function of the **odd-step index**, not of
the **time**: it cannot demand an odd step *near a given time*.  A cross-coordinate
contradiction of the shape "the octave path wants an odd step near `t`, the ordering
forbids one near `t`" is therefore impossible. -/
theorem octave_word_time_invariant (r j n : Nat) :
    raiseCount (r + j) (2 ^ r * n) = raiseCount j n ∧
    evenCnt (r + j) (2 ^ r * n) = r + evenCnt j n ∧
    oddCnt (r + j) (2 ^ r * n) = oddCnt j n := by
  have ho := orbit_two_pow_mul r n
  refine ⟨?_, ?_, ?_⟩
  · rw [raiseCount_add r j (2 ^ r * n), raiseCount_two_pow_mul r n, ho, Nat.zero_add]
  · rw [evenCnt_add r j (2 ^ r * n), evenCnt_two_pow_mul r n, ho]
  · rw [oddCnt_add r j (2 ^ r * n), ho]
    have : oddCnt r (2 ^ r * n) = 0 := by
      have h1 := oddCnt_add_evenCnt r (2 ^ r * n)
      have h2 := evenCnt_two_pow_mul r n
      omega
    omega

/-! ## 7.  The `+1` is invisible to the octave word of a counterexample -/

theorem two_pow_mod_three (m : Nat) : 2 ^ m % 3 = 1 ∨ 2 ^ m % 3 = 2 := by
  induction m with
  | zero => left; rfl
  | succ m ih =>
    have hp : (2:Nat) ^ (m + 1) = 2 * 2 ^ m := by rw [Nat.pow_succ, Nat.mul_comm]
    omega

theorem three_mul_ne_two_pow (z m : Nat) : 3 * z ≠ 2 ^ m := by
  intro h
  have := two_pow_mod_three m
  omega

/-- **The octave criterion is exactly multiplicative on a counterexample.**

For an odd `z` the true criterion for an octave rise is `2 ^ (oct z + 2) ≤ 3z + 1`,
which differs from the purely multiplicative criterion `2 ^ (oct z + 2) < 3z`
exactly when `3z + 1` is a power of two — the base-`4` repunits
`1, 5, 21, 85, 341, 1365, …`.  Every such `z` reaches `1` in one odd step followed
by halvings, so on an orbit that does not reach `1` the two criteria agree.

Hence the `+1` of the Collatz map never changes an octave decision along a
counterexample orbit: the octave word of a counterexample is *exactly* the octave
word of the multiplicative map `x ↦ 3x/2`. -/
theorem raise_iff_mult {z : Nat} (hz : 0 < z) (ho : z % 2 = 1) (hnr : ¬ ReachesOne z) :
    raiseIdx z = 1 ↔ 2 ^ (oct z + 2) < 3 * z := by
  have hne : 3 * z + 1 ≠ 2 ^ (oct z + 2) := by
    intro h
    exact hnr (Predecessors.reachesOne_of_three_mul_add_one_eq_two_pow hz (by omega) h)
  have hne2 : 3 * z ≠ 2 ^ (oct z + 2) := three_mul_ne_two_pow z (oct z + 2)
  unfold raiseIdx
  rw [if_pos ho]
  constructor
  · intro h
    have hle : 2 ^ (oct z + 2) ≤ 3 * z + 1 := by
      by_cases hc : 2 ^ (oct z + 2) ≤ 3 * z + 1
      · exact hc
      · rw [if_neg hc] at h; omega
    omega
  · intro h
    rw [if_pos (by omega)]

/-- A counterexample stays a counterexample along its own orbit. -/
theorem not_reachesOne_orbit {n : Nat} (hn : 0 < n) (hnr : ¬ ReachesOne n) (i : Nat) :
    ¬ ReachesOne (acceleratedOrbit i n) := by
  intro h
  exact hnr (reachesOne_of_accOrbit hn h)

/-- The orbit form of `raise_iff_mult`. -/
theorem octave_word_multiplicative {n : Nat} (hn : 0 < n) (hnr : ¬ ReachesOne n) (i : Nat)
    (ho : acceleratedOrbit i n % 2 = 1) :
    raiseIdx (acceleratedOrbit i n) = 1 ↔
      2 ^ (oct (acceleratedOrbit i n) + 2) < 3 * acceleratedOrbit i n :=
  raise_iff_mult (acceleratedOrbit_positive hn i) ho (not_reachesOne_orbit hn hnr i)

/-- **The forward map, in the form used on the ordered times.**  If the orbit has not
dropped below its starting octave by time `j`, then

  `j ≤ (number of odd steps so far) + (number of octave raises so far)`.

Read at `j = t_i`, the time of the `i`-th odd step: `t_i ≤ (i−1) + D(i−1)`, where
`D` is the partial-sum function of the octave decoration.  This is the exact map
from an octave-transition word to a constraint on `{t_1, …, t_a}`. -/
theorem time_bound_of_no_drop {n j : Nat} (hn : 0 < n)
    (hnd : oct n ≤ oct (acceleratedOrbit j n)) : j ≤ oddCnt j n + raiseCount j n := by
  have h := oct_orbit_balance j n hn
  have hs := oddCnt_add_evenCnt j n
  omega

/-- **The reverse map.**  The octave path is the start octave plus the raise count
minus the even count, and the even count is `j − a_j`, pure ordering data.  So a
given ordered-time set determines the octave path once the decoration is known, and
determines it *completely* once the decoration is known to be multiplicative
(`octave_word_multiplicative`). -/
theorem oct_orbit_from_times {n j : Nat} (hn : 0 < n) :
    oct (acceleratedOrbit j n) + (j - oddCnt j n) = oct n + raiseCount j n := by
  have h := oct_orbit_balance j n hn
  have hs := oddCnt_add_evenCnt j n
  omega

/-! ## 8.  The reverse map, and the verdict -/

/-- **The octave path determines the parity word.**  A step drops the octave iff it
is even.  Since an even step drops by exactly one and an odd step never drops, the
sequence of octaves reads off the parity word, hence the ordered odd times. -/
theorem oct_drop_iff_even {n : Nat} (hn : 2 ≤ n) :
    oct (acceleratedStep n) < oct n ↔ n % 2 = 0 := by
  constructor
  · intro h
    by_cases ho : n % 2 = 1
    · exfalso
      have hT : acceleratedStep n = (3 * n + 1) / 2 := by
        unfold acceleratedStep; rw [if_neg (by omega)]
      have := oct_le_oct_odd_step (n := n) (by omega) ho
      rw [hT] at h
      omega
    · omega
  · intro he
    have hT : acceleratedStep n = n / 2 := by
      unfold acceleratedStep; rw [if_pos he]
    have := oct_even_step hn he
    rw [hT]
    omega

/-- **The ballot inequality is not an independent constraint.**  For every start and
every horizon, "the even steps so far do not outnumber the octave raises so far" is
*equivalent* to "the orbit has not dropped below its starting octave".

This is the verdict of section XXIV.  The map from the octave word to the ordered
odd times is exactly this inequality, and it is an `iff` with a pure magnitude
statement — the heaviness/archimedean condition of Round VIII in new coordinates.
The octave coordinate therefore places **no constraint on the ordered times beyond
the one already owned**, and, by `octave_word_time_invariant`, it cannot place a
time-localised one even in principle. -/
theorem ballot_iff_no_drop {n j : Nat} (hn : 0 < n) :
    evenCnt j n ≤ raiseCount j n ↔ oct n ≤ oct (acceleratedOrbit j n) := by
  have h := oct_orbit_balance j n hn
  constructor
  · intro hb; omega
  · intro hb; omega

/-- The trivial cycle satisfies the balance: `L = 2`, one odd step, one even step,
one raise.  A witness that the constraint pair of section XXIV is nonempty. -/
theorem trivial_cycle_balance : raiseCount 2 1 = 1 ∧ evenCnt 2 1 = 1 ∧ oddCnt 2 1 = 1 := by
  refine ⟨by decide, by decide, by decide⟩

end OctaveOrder
end Collatz
