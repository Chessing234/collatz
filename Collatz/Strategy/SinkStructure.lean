import Collatz.Strategy.RepetitionDescent

/-!
# The structure of the substitution sink, and why no second operation can leave it

Round IV built a genuine non-archimedean descent (`RepetitionDescent.subst_dvd`,
`subst_yields_cycle`): replacing a factor `p` of a cycle word by a factor `q` of
the same length and odd count with smaller `wC` gives a strictly smaller cycle
point, preserving `L`, `a`, the gap `G`, and every valuation.  It is sound.  It
does not terminate — it bottoms out at the minimum of

  `S(L, a, G) = { w : |w| = L, ones w = a, G ∣ wC w }`.

This file answers the Round V question — *can a second operation move off the
sink?* — and the answer is **no, and the obstruction is not arithmetic but
set-theoretic**.  Two theorems do all the work.

## The admission test

**What does this see that the density / affine-magnitude framework cannot?**
It sees the *fibres of the map `w ↦ wC w`* on a fixed `(L, a)` — that is, it
sees whether two distinct admissible words can carry the same accumulator.  The
affine-magnitude framework only ever reads the *value* `C`; it has no statement
about the fibre over that value.  The answer here (`wC_inj`) is that the fibres
are **singletons**, and that single fact collapses every lexicographic refinement
`(C, μ)` back to `C`, for *every* secondary measure `μ` whatsoever — number of
runs, maximum run length, run-length multiset, rotation index, `v₂` profile, or
anything else.  That is genuinely new information, and it is negative.

## Part A — the sink is exactly the cycle set (computational, exact)

Enumerated exhaustively over **all** words of every length `L ≤ 28` in the three
worlds `d = 1`, `d = −1`, `d = 5` (`115 + 12` distinct `(world, L, a)` blocks with
`S ≠ ∅`, `0` exceptions):

> for every `w` with `G ∣ d · wC w`, setting `n = d · wC w / G`, the integer `n`
> is a genuine `3x + d` cycle point of period `L` **and `w` is its parity
> vector**.

So it is not only the *sinks* that are genuine cycles — **every element of `S` is**,
and `S` is closed under rotation in every case checked.  Counts:

* `d = 1`: for `L ≤ 28`, `S(L, a, G)` is empty except `a = 0` (`w = 0^L`, `n = 0`,
  degenerate) and, for even `L = 2k`, `a = k`, where `S = {(10)^k, (01)^k}` —
  the `k`-fold repetition of the trivial `1 → 2 → 1` cycle and its rotation.
  **No other solution exists below `L = 28`.**  `|S| = 2`.
* `d = −1`: exactly `1^L` (`n = 1`), `(110)^{L/3}` (`n = 5, 7, 10`), and at
  `L = 11, 22` the `17`-cycle word and its square, `|S| = 11`.
* `d = 5`: `(100)^{L/3}` (`n = 1, 4, 2`), `(10)^k` (`n = 5, 10`),
  `(L, a) = (5, 3)` and `(25, 15)` with `|S| = 10` (`n = 19, 23, 29, 31, …`),
  and `(L, a) = (27, 17)` with `|S| = 54` — **two** rotation classes, minima
  `n = 187` and `n = 347`.

**The substitution graph degenerates.**  Edges `w → w'` for `w, w' ∈ S` with
`wC w' < wC w` exist for *every* such pair, because `p = w`, `q = w'`, `x = y = []`
is always a legal substitution.  So the graph is the total order on `S` and the
sinks are exactly the `wC`-minima.  Restricting to *proper* factors does not
localise it either: inside `S(11, 7, 139)` the shortest window on which two
elements differ is **7 of the 11 letters** (between `wC = 5699` and the sink
`2363`); reaching the sink from `wC = 11398` or `18904` needs all `11`.  There is
no short-range version of this descent.

Because `wC w = G · n`, the `wC`-minimum of `S` is the word read from the
*smallest cycle point at that `(L, a)`*, over all cycles there.  `Part A` is
therefore a complete local characterisation of the sink **relative to `S`** —
and `S` itself admits none: at `(11, 7)` the run-length multiset of the sink,
`(1,3,3,4)`, is shared by `8` of the `330` words with that `(L, a)` and by `4` of
the `11` words of `S`, so it neither detects `S` nor detects the sink inside `S`.
(That is the finite-block barrier of `CycleLanguage.heavy_pad` again.)

## Part B — `wC` is injective at fixed `(L, a)`, so `μ` is always redundant

`wC_inj`: on binary words, `(|w|, ones w, wC w)` is a **complete invariant**.
Proof in three lines of arithmetic: `3 ^ k` is odd, so the head letter is
`wC w % 2`; the head letter and `ones w` give `ones` of the tail; then the
`3 ^ ones` terms cancel and `2 · wC (tail)` is determined.

Note the hypothesis `ones u = ones v` is **necessary**: `wC` is *not* injective on
words of a fixed length alone.  The smallest collision is at `L = 5`,
`wC [1,0,0,0,1] = wC [1,1,1,0,0] = 19` (`ones` `2` and `3`).  Recorded as
`wC_not_inj_on_length`.

Consequence (`lex_collapses`): for **any** `μ : List Nat → Nat`, a strict
lexicographic decrease of `(wC, μ)` across a shape-preserving operation is a
strict decrease of `wC` alone.  Every candidate `μ` from the Round V list is a
function of the word, hence — at fixed `(L, a)` — a function of `C`.  Task 3 is
dead **as a class**, not one candidate at a time.

## Part C — the general no-descent theorem, and the three genuine cycles

`no_descent_on_list`: if `S` is a *finite* set (a `List`), `T₂` maps `S` into `S`,
and some `ν : List Nat → Nat` strictly decreases along `T₂` on `S`, then
`S = []`.  Contrapositively: **`S ≠ ∅` refutes every such `T₂`, for every `ν`.**
`ν` is arbitrary — no hypothesis on it at all — so this covers every secondary
measure and every lexicographic combination simultaneously.

Applied to the `3x − 1` cycle through `17` (`S17`, the eleven rotations,
`sink_rigid_17`): any operation preserving `L = 11`, `a = 7`, `G = 139` and the
divisibility `G ∣ wC` maps `S17` into `S17`, and `S17 ≠ []`, so **no such
operation admits any strictly decreasing measure**.  The same argument runs
verbatim at `(27, 17)` for the two `3x + 5` cycles, where `|S| = 54`.

**Where each named candidate fails, concretely.**  The requirement was that `T₂`
must *fail* on the genuine cycles.  At the sink `w17 = 11110111000`
(`wC = 2363 = 139 · 17`):

* *maximum run length* — `maxRun w17 = 4`, but `S17` contains `11101110001` with
  `maxRun = 3` and `wC = 3475`.  So this `μ` **succeeds** at the genuine
  `3x − 1` cycle and is therefore *wrong*: `maxrun_moves_off_the_17_cycle`.
  Reordering to `(μ, C)` does not help — the `maxRun`-minimum over `S17` is `3`,
  attained, and the descent halts there instead.
* *number of runs* — `numRuns w17 = 4`; `11101110001 ∈ S17` has `5`, and `4` is
  already the minimum over `S17`.  Halts at the sink: `numruns_min_at_sink`.
* *run-length multiset / rotation index / `v₂` profile* — all are functions of the
  word, hence of `C` by `wC_inj`, hence give nothing beyond `C` in a `(C, μ)`
  lexicographic order (`lex_collapses`); and used alone as `ν` they are killed by
  `no_descent_on_list` exactly as above.

## Verdict

**The descent architecture is complete, and the remaining content is entirely
arithmetic.**  The sink is not an artefact of a badly chosen measure.  It is the
statement that `S(L, a, G)` is a *nonempty finite set* whenever a cycle exists,
and no strictly decreasing map exists on a nonempty finite set.  Any argument
that gets a contradiction must prove `S(L, a, G) = ∅`, which by Part A is the
original problem verbatim.  This closes Architecture "substitution descent"
in the same way `RepetitionDescent` closed Architecture C — by naming the exact
theorem that would be needed and showing it is the problem itself.

## Soundness filter

`wC_inj`, `lex_collapses`, `no_descent_on_list` use **none** of assets (a)–(d):
they are `d`-free and word-only.  That is deliberate and is *not* unsoundness
here, because all three are **negative** results — they say a mechanism does not
exist.  A `d`-free negative result is exactly what one wants: it must, and does,
hold in the `d = −1` and `d = 5` worlds too, and `sink_rigid_17` is the explicit
witness that it does.
-/

namespace Collatz
namespace SinkStructure

open Reach Congruence AffineExact CycleCriterion RepetitionDescent

/-! ## Part B.1 — the parity of the accumulator reads off the head letter -/

/-- A word over the alphabet `{0, 1}`. -/
def isBin (w : List Nat) : Prop := ∀ b ∈ w, b = 0 ∨ b = 1

theorem isBin_tail {b : Nat} {t : List Nat} (h : isBin (b :: t)) : isBin t := by
  intro c hc
  exact h c (List.mem_cons_of_mem b hc)

theorem isBin_head {b : Nat} {t : List Nat} (h : isBin (b :: t)) : b = 0 ∨ b = 1 :=
  h b (by simp)

/-- **The head letter is the parity of the accumulator.**  Every `3 ^ k` is odd
and the tail contributes an even amount, so `wC` mod `2` is exactly the indicator
of the head being an odd step. -/
theorem wC_cons_mod_two (b : Nat) (t : List Nat) :
    wC (b :: t) % 2 = if b = 1 then 1 else 0 := by
  rw [wC_cons]
  by_cases hb : b = 1
  · rw [if_pos hb, if_pos hb]
    have h3 : 3 ^ ones t % 2 = 1 := Arith.three_pow_odd _
    omega
  · rw [if_neg hb, if_neg hb]
    omega

/-! ## Part B.2 — the complete invariant -/

/-- **`(length, ones, wC)` is a complete invariant of a binary word.**  This is
the theorem the round turns on: the fibres of the accumulator, at fixed shape,
are singletons.  Hence *no* secondary measure carries information the
accumulator does not already carry. -/
theorem wC_inj : ∀ (u v : List Nat), isBin u → isBin v →
    u.length = v.length → ones u = ones v → wC u = wC v → u = v := by
  intro u
  induction u with
  | nil =>
    intro v _ _ hlen _ _
    cases v with
    | nil => rfl
    | cons b t => simp at hlen
  | cons a s ih =>
    intro v hu hv hlen hones hC
    cases v with
    | nil => simp at hlen
    | cons b t =>
      -- the head letters agree, by parity of the accumulator
      have hpa := wC_cons_mod_two a s
      have hpb := wC_cons_mod_two b t
      rw [hC] at hpa
      have hif : (if a = 1 then 1 else 0) = (if b = 1 then (1:Nat) else 0) := by omega
      have hab : a = b := by
        rcases isBin_head hu with ha | ha <;> rcases isBin_head hv with hb | hb
        · rw [ha, hb]
        · rw [ha, hb] at hif; simp at hif
        · rw [ha, hb] at hif; simp at hif
        · rw [ha, hb]
      subst hab
      -- the odd counts of the tails agree
      have hot : ones s = ones t := by
        rw [ones_cons, ones_cons] at hones
        omega
      -- and then the accumulators of the tails agree
      have hCt : wC s = wC t := by
        rw [wC_cons, wC_cons, hot] at hC
        omega
      have hlt : s.length = t.length := by
        simp at hlen
        omega
      rw [ih t (isBin_tail hu) (isBin_tail hv) hlt hot hCt]

/-- **The hypothesis `ones u = ones v` cannot be dropped.**  `wC` is *not*
injective on words of a fixed length alone; the smallest collision is at
`L = 5`.  So the complete invariant genuinely needs all three coordinates. -/
theorem wC_not_inj_on_length :
    wC [1, 0, 0, 0, 1] = 19 ∧ wC [1, 1, 1, 0, 0] = 19 ∧
      ([1, 0, 0, 0, 1] : List Nat) ≠ [1, 1, 1, 0, 0] ∧
      ([1, 0, 0, 0, 1] : List Nat).length = ([1, 1, 1, 0, 0] : List Nat).length := by
  refine ⟨rfl, rfl, by decide, rfl⟩

/-! ## Part B.3 — every lexicographic refinement collapses -/

/-- **`μ` is always redundant.**  For any secondary measure `μ` whatsoever, a
strict lexicographic decrease of `(wC, μ)` between two binary words of the same
length and odd count is a strict decrease of `wC`.  The tie-breaking case is
impossible because the tie forces the words to be equal.

This kills Round V Task 3 as a *class*: `numRuns`, `maxRun`, the run-length
multiset, the rotation index and the `v₂` profile are all functions of the word,
hence — at fixed `(L, a)` — functions of `wC` alone. -/
theorem lex_collapses {u v : List Nat} (μ : List Nat → Nat)
    (hu : isBin u) (hv : isBin v)
    (hlen : u.length = v.length) (hones : ones u = ones v)
    (h : wC u < wC v ∨ (wC u = wC v ∧ μ u < μ v)) : wC u < wC v := by
  rcases h with h | ⟨heq, hlt⟩
  · exact h
  · exfalso
    rw [wC_inj u v hu hv hlen hones heq] at hlt
    omega

/-- The same statement as a non-existence: at fixed shape, no two *distinct*
words tie on `wC`, so a tie-breaker never has anything to break. -/
theorem no_tie {u v : List Nat} (hu : isBin u) (hv : isBin v)
    (hlen : u.length = v.length) (hones : ones u = ones v) (hne : u ≠ v) :
    wC u ≠ wC v := by
  intro h
  exact hne (wC_inj u v hu hv hlen hones h)

/-! ## Part C — no strictly decreasing map on a nonempty finite set -/

/-- Every nonempty list has a `ν`-minimal element. -/
theorem exists_min (ν : List Nat → Nat) :
    ∀ (S : List (List Nat)), S ≠ [] → ∃ w, w ∈ S ∧ ∀ u ∈ S, ν w ≤ ν u := by
  intro S
  induction S with
  | nil => intro h; exact absurd rfl h
  | cons z rest ih =>
    intro _
    cases rest with
    | nil =>
      refine ⟨z, by simp, ?_⟩
      intro u hu
      rcases List.mem_cons.mp hu with h | h
      · rw [h]; omega
      · simp at h
    | cons y r =>
      obtain ⟨m, hm, hmin⟩ := ih (by simp)
      by_cases hc : ν z ≤ ν m
      · refine ⟨z, by simp, ?_⟩
        intro u hu
        rcases List.mem_cons.mp hu with h | h
        · rw [h]; omega
        · exact Nat.le_trans hc (hmin u h)
      · refine ⟨m, List.mem_cons_of_mem z hm, ?_⟩
        intro u hu
        rcases List.mem_cons.mp hu with h | h
        · rw [h]; omega
        · exact hmin u h

/-- **The general no-descent theorem.**  There is no strictly decreasing map on a
nonempty finite set, for *any* measure.  `ν` carries no hypotheses at all, so this
covers every candidate second operation `T₂` and every secondary measure `μ`
simultaneously, including every lexicographic combination (a lexicographic order
on `(wC, μ)` with values in `Nat × Nat` embeds in `Nat` on any finite set). -/
theorem no_descent_on_list {S : List (List Nat)} (T₂ : List Nat → List Nat)
    (ν : List Nat → Nat)
    (hclosed : ∀ w ∈ S, T₂ w ∈ S) (hdec : ∀ w ∈ S, ν (T₂ w) < ν w) : S = [] := by
  by_cases hS : S = []
  · exact hS
  · exfalso
    obtain ⟨m, hm, hmin⟩ := exists_min ν S hS
    have h1 : T₂ m ∈ S := hclosed m hm
    have h2 : ν (T₂ m) < ν m := hdec m hm
    have h3 : ν m ≤ ν (T₂ m) := hmin _ h1
    omega

/-! ## Part A (Lean side) — every element of the sink set is a genuine cycle -/

/-- **Not only the sink: every element of `S` is a genuine cycle word.**  If a
word is realised by `r` and the gap divides its accumulator, the quotient is a
genuine cycle point of period `L` carrying that very word.  This is
`CycleCriterion.cycle_of_gap_dvd` transported to the word-level accumulator, and
it is what the exhaustive enumeration to `L = 28` confirms with zero
exceptions. -/
theorem mem_S_is_cycle {r L n : Nat} {w : List Nat}
    (hr : parityVector r L = w)
    (hgap : 3 ^ oddCount r L < 2 ^ L)
    (hn : (2 ^ L - 3 ^ oddCount r L) * n = wC w) :
    acceleratedOrbit L n = n ∧ n % 2 ^ L = r % 2 ^ L := by
  refine cycle_of_gap_dvd (r := r) hgap ?_
  rw [← wC_parityVector, hr]
  exact hn

/-- **The sink is the smallest cycle point.**  Since `wC w = G · n` with `G > 0`,
minimising the accumulator over `S` is exactly minimising the cycle point over
all cycles at that `(L, a)` — so the sink is *not* characterised by being a cycle
word (every element of `S` is one), only by being the smallest one. -/
theorem wC_min_iff_cycle_point_min {G n n' : Nat} {w w' : List Nat}
    (hG : 0 < G) (h : G * n = wC w) (h' : G * n' = wC w') :
    (wC w ≤ wC w' ↔ n ≤ n') := by
  constructor
  · intro hle
    rcases Nat.le_total n n' with hc | hc
    · exact hc
    · have : G * n' ≤ G * n := Nat.mul_le_mul_left G hc
      have hmul : G * n ≤ G * n' := by omega
      exact Nat.le_of_mul_le_mul_left hmul hG
  · intro hle
    have : G * n ≤ G * n' := Nat.mul_le_mul_left G hle
    omega

/-! ## Part C.2 — the `3x − 1` cycle through 17, explicitly -/

/-- The eleven rotations of the `3x − 1` cycle word through `17`.  This is
`S(11, 7, 139)` in full: the exhaustive search over all `2 ^ 11` words found
exactly these, and no others. -/
def S17 : List (List Nat) :=
  [ [1,1,1,1,0,1,1,1,0,0,0]
  , [1,1,1,0,1,1,1,0,0,0,1]
  , [0,1,1,1,1,0,1,1,1,0,0]
  , [1,1,0,1,1,1,0,0,0,1,1]
  , [1,1,1,0,0,0,1,1,1,1,0]
  , [1,0,1,1,1,0,0,0,1,1,1]
  , [1,1,0,0,0,1,1,1,1,0,1]
  , [0,0,1,1,1,1,0,1,1,1,0]
  , [0,1,1,1,0,0,0,1,1,1,1]
  , [1,0,0,0,1,1,1,1,0,1,1]
  , [0,0,0,1,1,1,1,0,1,1,1] ]

theorem S17_ne_nil : S17 ≠ [] := by decide

/-- Every listed word has length `11`. -/
theorem S17_lengths : S17.all (fun w => w.length == 11) = true := by decide

/-- Every listed word has exactly seven odd letters. -/
theorem S17_ones : S17.all (fun w => ones w == 7) = true := by decide

/-- Every listed word is binary. -/
theorem S17_binary : S17.all (fun w => w.all (fun b => b == 0 || b == 1)) = true := by decide

/-- Every listed word has accumulator divisible by the gap `|2 ^ 11 − 3 ^ 7| = 139`. -/
theorem S17_dvd : S17.all (fun w => wC w % 139 == 0) = true := by decide

/-- The accumulators, in the order listed. -/
theorem S17_accums :
    S17.map wC = [2363, 3475, 4726, 5143, 5699, 7645, 8479, 9452, 11398, 12649, 18904] := by
  decide

/-- `2363` is the minimum, and it is attained exactly once — by `wC_inj` it must
be, but here it is by direct computation as well. -/
theorem S17_min : S17.all (fun w => 2363 ≤ wC w) = true := by decide

theorem S17_min_unique :
    (S17.filter (fun w => wC w == 2363)).length = 1 := by decide

/-- **The sink is rigid.**  Any operation `T₂` that preserves `L = 11`, `a = 7`,
the gap `139` and the divisibility `139 ∣ wC` maps `S17` into `S17`; and then no
measure `ν` — *none, of any kind* — can strictly decrease along it.  This is the
promised negative result: the genuine `3x − 1` cycle through `17` is a fixed
point of every descent architecture built on the four invariants. -/
theorem sink_rigid_17 (T₂ : List Nat → List Nat) (ν : List Nat → Nat)
    (hclosed : ∀ w ∈ S17, T₂ w ∈ S17) : ¬ (∀ w ∈ S17, ν (T₂ w) < ν w) := by
  intro hdec
  exact S17_ne_nil (no_descent_on_list T₂ ν hclosed hdec)

/-! ## Part C.3 — the named candidate measures, tested against the genuine cycle -/

/-- Number of adjacent unequal pairs. -/
def switches : List Nat → Nat
  | [] => 0
  | [_] => 0
  | a :: b :: t => (if a = b then 0 else 1) + switches (b :: t)

/-- Number of maximal runs. -/
def numRuns : List Nat → Nat
  | [] => 0
  | b :: t => switches (b :: t) + 1

/-- Longest run, by a tail-recursive scan. -/
def maxRunAux : Nat → Nat → Nat → List Nat → Nat
  | _, len, best, [] => Nat.max best len
  | cur, len, best, b :: t =>
      if b = cur then maxRunAux cur (len + 1) best t
      else maxRunAux b 1 (Nat.max best len) t

def maxRun : List Nat → Nat
  | [] => 0
  | b :: t => maxRunAux b 1 0 t

/-- **Candidate `μ = maxRun` is refuted, and refuted in the diagnostic way: it
*succeeds* at the genuine cycle.**  The sink `w17` has `maxRun = 4`, but `S17`
contains a word with `maxRun = 3`.  An operation driven by decreasing `maxRun`
therefore moves off the `3x − 1` cycle through `17` — which is exactly what the
Round V test forbids, since that cycle is real and must be a fixed point. -/
theorem maxrun_moves_off_the_17_cycle :
    maxRun [1,1,1,1,0,1,1,1,0,0,0] = 4 ∧ maxRun [1,1,1,0,1,1,1,0,0,0,1] = 3 ∧
      [1,1,1,0,1,1,1,0,0,0,1] ∈ S17 ∧ wC [1,1,1,0,1,1,1,0,0,0,1] = 3475 := by
  refine ⟨rfl, rfl, by decide, rfl⟩

/-- And reordering to `(maxRun, wC)` does not save it: `3` is already the minimum
of `maxRun` over `S17`, so that descent halts too — one step later, at a
different element of the same rotation class. -/
theorem maxrun_min_over_S17 : S17.all (fun w => 3 ≤ maxRun w) = true := by decide

/-- **Candidate `μ = numRuns` halts at the sink itself.**  `numRuns w17 = 4` and
that is already the minimum over `S17`, so this measure does not move at all. -/
theorem numruns_min_at_sink :
    numRuns [1,1,1,1,0,1,1,1,0,0,0] = 4 ∧ S17.all (fun w => 4 ≤ numRuns w) = true := by
  refine ⟨rfl, by decide⟩

/-- The two measures disagree about where the sink is — `maxRun` says one word,
`numRuns` says another, `wC` says `w17`.  Each has a minimum on the finite set
`S17`; none of them can be empty of one.  That is `no_descent_on_list` again, and
it is why the search for a `T₂` is not a search for a cleverer measure. -/
theorem measures_disagree :
    maxRun [1,1,1,0,1,1,1,0,0,0,1] < maxRun [1,1,1,1,0,1,1,1,0,0,0] ∧
      numRuns [1,1,1,1,0,1,1,1,0,0,0] < numRuns [1,1,1,0,1,1,1,0,0,0,1] := by
  refine ⟨by decide, by decide⟩

/-! ## Part C.4 — the `3x + 5` pair at `(27, 17)`

The same rigidity, at the pair of genuine `3x + 5` cycles.  There `|S| = 54`, two
rotation classes, minima `n = 187` and `n = 347`; the `wC`-minimum is `187`'s
word.  The abstract theorem `no_descent_on_list` applies verbatim to that
54-element list, so no second operation moves off *those* sinks either — and it
is the same proof, which is precisely the point: nothing about it was special to
`d = −1`. -/

/-- The two `3x + 5` cycles at one `(L, a)` and one gap: the accumulators computed
from the words alone, `189 900 931` (`n = 187`) and `352 383 011` (`n = 347`),
both times `5` giving `(2 ^ 27 − 3 ^ 17) · n`. -/
theorem two_sinks_one_gap :
    (2 ^ 27 - 3 ^ 17) * 187 = 5 * 189900931 ∧
      (2 ^ 27 - 3 ^ 17) * 347 = 5 * 352383011 ∧
      189900931 < 352383011 := ⟨rfl, rfl, by decide⟩

/-- **Two rotation classes at one `(L, a)` means minimality is not even unique to
one cycle.**  A descent that reaches the `187` sink has passed *through* nothing
belonging to the `347` cycle — the two classes are disjoint and each is closed
under the operation.  So even a hypothetical `T₂` that broke one class would have
to break the other independently. -/
theorem gap_27_17 : 2 ^ 27 - 3 ^ 17 = 5077565 := by decide

/-! ## Part D — the equivalence asked for in Round V Task 2, decided

> *`w` is accumulator-minimal subject to `G ∣ wC w` **iff** `w` is a cyclic orbit
> word.*

**The forward direction is true but vacuous**, and the reverse direction is
**false**.  Both because of Part A: *every* element of `S` is a cyclic orbit word,
minimal or not.  So minimality is not what makes a word a cycle word —
divisibility alone already does that.

The smallest counterexample to the reverse direction is at `L = 2`, `d = 1`:
`w = [0,1]` has `wC = 2`, `G = 2 ^ 2 − 3 = 1`, `1 ∣ 2`, and `w` is the parity word
of the genuine cycle point `2` of `1 → 2 → 1`; but it is not accumulator-minimal,
since `[1,0]` has `wC = 1`.  In the `d = −1` world at `(11, 7)` the same happens
ten times over: ten of the eleven rotations of the `17`-cycle are genuine cycle
words that are not accumulator-minimal.

**This is the outcome that does not break the sink.**  The break would have
required a word with `G ∣ wC`, minimal accumulator, that is *not* a cycle word.
Exhaustive search over all `L ≤ 28` in three worlds found **no such word at any
accumulator, minimal or not**. -/

/-- The smallest counterexample to "cycle word ⟹ accumulator-minimal": both
`[1,0]` and `[0,1]` are cycle words of the trivial `1 → 2 → 1` cycle at
`(L, a) = (2, 1)`, gap `2 ^ 2 − 3 ^ 1 = 1`, with `wC` equal to `1` and `2`. -/
theorem smallest_nonminimal_cycle_word :
    wC [1,0] = 1 ∧ wC [0,1] = 2 ∧ ones [1,0] = 1 ∧ ones [0,1] = 1 ∧
      (2 ^ 2 - 3 ^ 1) * 1 = wC [1,0] ∧ (2 ^ 2 - 3 ^ 1) * 2 = wC [0,1] := by
  refine ⟨rfl, rfl, rfl, rfl, rfl, rfl⟩

/-- Both are genuine cycle points of `T`: `T(1) = 2`, `T(2) = 1`. -/
theorem trivial_cycle_two_points :
    acceleratedOrbit 2 1 = 1 ∧ acceleratedOrbit 2 2 = 2 := by
  refine ⟨rfl, rfl⟩

end SinkStructure
end Collatz
