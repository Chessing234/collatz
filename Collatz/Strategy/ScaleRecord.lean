import Collatz.Strategy.FiniteInfinite
import Collatz.Strategy.Denominator
import Collatz.Structure.RunValue

/-!
# Round X, sections XI / XIV / XIX / XX — the escape record, and the first
# divergence-half soundness witness

Round IX ended by naming the missing object: **a refuting witness family for the
divergence half**.  Every filter this programme owns is a cycle witness — the
genuine cycles of `3x−1, 3x+5, 3x+7, 3x+11, 3x+13` refute `d`-free cycle
mechanisms on contact — and no divergent orbit of any `3x + d` is known, so a
divergence-half mechanism currently faces no filter at all.

This file supplies two things.

## 1.  A record function that is the divergence half *exactly*

`FiniteInfinite.MinNonDropUnbounded` ("the least non-dropper grows without
bound") is already known to be the **whole** conjecture: a non-trivial cycle's
minimum never drops, so it caps the record just as a divergent orbit's minimum
does.  Replace "never drops" by "**escapes the scale**":

`minEsc B = min { m ≥ 1 : the orbit of m rises strictly above B }`,
`ScaleRecordUnbounded  ↔  minEsc B → ∞`.

`scaleRecord_iff_no_divergence` proves

> `ScaleRecordUnbounded  ↔  no positive integer has an unbounded orbit`,

the **divergence half alone**, with no cycle content: a cycle is a bounded
orbit, and a bounded orbit caps `minEsc` at only finitely many scales
(`cycle_bounded`, `separation`).  So `minEsc` is to the divergence half what
`minNonDrop` is to the whole conjecture, and it is the first record function in
this development that a cycle does not refute.

The certificate attached to it answers the brief's asymmetry directly.  A cycle
is a single finite witness; a divergent orbit is not.  Here the witness at scale
`B` is the finite orbit segment of `m` up to the first index exceeding `B` —
finite for each `B` — and divergence supplies **one `m` that carries a
certificate at every scale**.  The filter is not "no long certificate exists"
(false: see `mersenne_nonDropping` below) but "**no bounded `m` carries
certificates at unboundedly many scales**".

Measured (accelerated map, exhaustive over all `m ≤ 3·10⁶`; `minEsc B` is the
least `m ≥ 2` whose accelerated orbit rises strictly above `B`):

```
  k    minEsc(2^k)    log2 minEsc    log2 minEsc / k
 10             27          4.755            0.476
 16            703          9.457            0.591
 20           4255         12.055            0.603
 24          20895         14.351            0.598
 28          60975         15.896            0.568
 32         159487         17.283            0.540
 36        1212415         20.209            0.561
 37        2684647         21.356            0.577
```

so `minEsc(2^k) = 2^(0.57 k ± 0.03)` over `k ∈ [14, 37]` with no visible drift —
equivalently `maxOrbit(m) ≈ m^1.75`, near but not equal to the `m²` excursion
heuristic.  That constant is **not** in Class 2 of `CLOSURE.md`: every counting
quantity there collapses onto `0.05004 = 1 − H(log₃2)`, and
`minNonDrop L = Θ(2^L / heavyCount L)` has slope `0.05004` per *step*, while
`minEsc` has slope `0.57` per *bit of scale*.  Nor is it `0.585 = log₂3 − 1`,
which is growth per odd step.  The two record functions are not the same
measurement in different coordinates.

## 2.  The first member of the divergence-half filter, and why it is the only one

`expStep x = 3x/2` on evens, `(3x+1)/2` on odds.  It **agrees with the Collatz
map on every odd input** (`expStep_odd_eq`), it obeys the same affine law
`2^j · f^j(x) = 3^j · x + b` (`expOrbit_affine`) — the accumulator algebra of the
whole development, with the odd-count saturated at `a = j` — it is heavy at every
scale (`2^j ≤ 3^j`), and **every one of its orbits provably diverges**
(`expOrbit_divergent`).

So it is a genuine soundness filter for the divergence half:

> **any divergence-half mechanism whose proof uses only the affine law, the
> parity word, heaviness, and positivity — without consuming `oddCount n j < j`,
> i.e. the *contraction* of the even branch — proves a false statement.**

That is the exact analogue of `C(w,d) = d·C(w,1)` for the cycle half, and it
locates the one bit that Round IX's Part VI said carries the whole remaining
content: the filter is passed only by mechanisms that read the archimedean size
of the even branch, not just the 2-adic branch structure.

**Why the family has one member, and not more.**  The interpolating family
`T_k(x) = x/2` if `2^k ∣ x`, `3x/2` if `x` even with `2^k ∤ x`, `(3x+1)/2` if `x`
odd has `T_1 = ` the Collatz map and `T_∞ = expStep`, and its average log-drift
is positive for every `k ≥ 2` (drift `= (1 − 2^(−k))·log₂(3/2) − 2^(−k)`, which
is `−0.2075` at `k = 1` and `+0.19` already at `k = 2`).  Yet no `T_k` with `k`
finite has a *provably* divergent orbit, and one half of the reason is a theorem
already here: the only certificate this development can write down for an
infinite orbit is a periodic parity word, and
`InfiniteWord.wordEventuallyPeriodic_iff_eventuallyCyclic` says an eventually
periodic word **is** an eventual cycle — never a divergence.  A heavy periodic
word `u` has 2-adic fixed point `C(u)/(2^L − 3^a) < 0`, so a positive integer can
follow it only finitely long.  *That a periodic word is the only available
certificate is a statement about this development, not a theorem*; but it is why
the filter below has exactly one member, and why the member must differ from the
Collatz map on a whole branch rather than in a constant.  That is also the
filter's weakness, stated plainly: `3x + d` differs from `3x + 1` in one
constant, while `expStep` differs on every even input, so this filter kills a
coarser class of mechanisms than the cycle filter does.

## 3.  The tree, and where König fails (section XIX)

`mersenne_nonDropping` proves, unconditionally, that the non-dropping tree has
branches of **every finite length**: `2^k − 1` does not drop for `k` steps.  So no
divergence filter may take the form "long certificates are impossible".  Two
towers must be kept apart:

* the **word tree** is finitely branching, so König applies — but its infinite
  branches are 2-adic integers, and `lim¹` vanishes, so branches always exist;
  the arithmetic condition selecting the integral ones is
  `FiniteInfinite.realized_iff_rep_eventually_const`, i.e. **boundedness of the
  canonical representative**, and on the all-odd branch that representative is
  exactly `2^k − 1 → ∞` (`OddRuns.mod_of_oddRun`) — the one branch where the
  elimination is provable, and it is provable for a purely archimedean reason;
* the **integer tree** (nodes = integers surviving to level `L`) has *infinite*
  levels, because nothing bounds the minimum of a hypothetical divergent orbit
  from above.  König does not apply, and the missing hypothesis is exactly an
  upper bound on that minimum.

So the localisation is sharp: **the divergence half needs archimedean
compactness — an upper bound on the minimum of a divergent orbit — and the
2-adic tower cannot supply it.**  `scaleRecord_iff_no_divergence` is that
statement in record-function form: `minEsc` is bounded iff such a minimum exists.

## Soundness filter (assets used)

`Exceeds`, `BoundedBy`, `scaleRecord_iff_no_divergence`, `cycle_bounded`,
`separation`, and the whole `expStep` section use **none** of assets (a)–(d) and
no property of `d`: they are proved from determinism, the affine law and
positivity.  `minNonDrop_implies_scaleRecord` inherits asset (b) through
`FiniteInfinite.minNonDropUnbounded_implies_both` and is the only statement here
that uses an asset.  `five_separates` uses the genuine `3x+5` cycle — that is the
point of it: it is the cycle filter, applied to show that this filter is *not* a
cycle detector.
-/

namespace Collatz
namespace ScaleRecord

open AccDivergence InfiniteWord

/-! ## Part 1: the escape record -/

/-- The orbit of `m` rises strictly above `B` at some time: a **scale-`B` escape
certificate** for `m`.  The certificate itself is the finite orbit segment
`m, T m, …, T^i m`. -/
def Exceeds (m B : Nat) : Prop := ∃ i : Nat, B < acceleratedOrbit i m

/-- The orbit of `m` never rises above `B`. -/
def BoundedBy (m B : Nat) : Prop := ∀ i : Nat, acceleratedOrbit i m ≤ B

/-- The two are complementary, with no classical step. -/
theorem not_exceeds_iff (m B : Nat) : (¬ Exceeds m B) ↔ BoundedBy m B := by
  constructor
  · intro h i
    rcases Nat.lt_or_ge B (acceleratedOrbit i m) with hlt | hge
    · exact absurd ⟨i, hlt⟩ h
    · exact hge
  · intro h hex
    obtain ⟨i, hi⟩ := hex
    have := h i
    omega

/-- **The escape record grows without bound**: for every bound `M` there is a
scale `B` that no `m ≤ M` ever reaches.  This is `minEsc B → ∞` written without
a minimisation operator, in the shape of
`FiniteInfinite.MinNonDropUnbounded`. -/
def ScaleRecordUnbounded : Prop :=
  ∀ M : Nat, ∃ B : Nat, ∀ m : Nat, 0 < m → m ≤ M → BoundedBy m B

/-- A single bound covering every `m ≤ M`, when no orbit is unbounded. -/
theorem uniform_bound (h : ∀ n : Nat, 0 < n → ¬ AccDivergent n) :
    ∀ M : Nat, ∃ B : Nat, ∀ m : Nat, 0 < m → m ≤ M → BoundedBy m B := by
  intro M
  induction M with
  | zero => exact ⟨0, fun m hm hmM => by omega⟩
  | succ M ih =>
    obtain ⟨B, hB⟩ := ih
    obtain ⟨B', hB'⟩ := accBounded_of_not_accDivergent (h (M + 1) (by omega))
    refine ⟨max B B', fun m hm hmM i => ?_⟩
    rcases Nat.lt_or_ge m (M + 1) with hlt | hge
    · have := hB m hm (by omega) i
      have : B ≤ max B B' := Nat.le_max_left _ _
      omega
    · have hme : m = M + 1 := by omega
      subst hme
      have := hB' i
      have : B' ≤ max B B' := Nat.le_max_right _ _
      omega

/-- **The equivalence.**  The escape record grows without bound **iff** no
positive integer has an unbounded orbit.  Unlike
`FiniteInfinite.minNonDrop_unbounded_iff_reachesOne`, which is the whole
conjecture, this is the divergence half and nothing else. -/
theorem scaleRecord_iff_no_divergence :
    ScaleRecordUnbounded ↔ (∀ n : Nat, 0 < n → ¬ AccDivergent n) := by
  constructor
  · intro h n hn hdiv
    obtain ⟨B, hB⟩ := h n
    obtain ⟨i, hi⟩ := hdiv B
    have := hB n hn (Nat.le_refl _) i
    omega
  · exact uniform_bound

/-! ### Divergence-specificity: a cycle does not refute this filter

`FiniteInfinite.not_minNonDropUnbounded_of_never_drops` says a single
never-dropping integer kills `MinNonDropUnbounded` outright, and a non-trivial
cycle's minimum is such an integer.  The escape record is immune: a cycle is a
bounded orbit, and a bounded orbit caps only finitely many scales. -/

/-- A cyclic point has a bounded orbit, so it supplies escape certificates at
only finitely many scales. -/
theorem cycle_bounded {m p : Nat} (hp : 0 < p) (hcyc : acceleratedOrbit p m = m) :
    ∃ B : Nat, BoundedBy m B := by
  have hec : EventuallyCyclic m := ⟨0, p, hp, by
    have h0 : (0 : Nat) + p = p := by omega
    rw [h0, hcyc]
    rfl⟩
  obtain ⟨B, hB⟩ := accBounded_of_eventuallyCyclic hec
  exact ⟨B, hB⟩

/-- **The separation.**  A non-trivial cycle refutes the non-dropping record
filter and leaves the escape record filter standing.  So the escape record is
not a cycle detector in disguise: the object that kills every cycle-half
mechanism does not touch it. -/
theorem separation {m p : Nat} (hm : 2 ≤ m) (hp : 0 < p)
    (hcyc : acceleratedOrbit p m = m) (hnd : ∀ j : Nat, m ≤ acceleratedOrbit j m) :
    (¬ FiniteInfinite.MinNonDropUnbounded) ∧ (∃ B : Nat, BoundedBy m B) :=
  ⟨FiniteInfinite.not_minNonDropUnbounded_of_never_drops hm hnd, cycle_bounded hp hcyc⟩

/-- The escape record is implied by the non-dropping record, hence strictly
weaker as a hypothesis: it is the divergence half of what that one asserts. -/
theorem minNonDrop_implies_scaleRecord (h : FiniteInfinite.MinNonDropUnbounded) :
    ScaleRecordUnbounded :=
  scaleRecord_iff_no_divergence.mpr (FiniteInfinite.minNonDropUnbounded_implies_both h).1

/-- The separation made concrete in the one family where a genuine cycle exists.
Under `3x + 5` the number `5` never drops — refuting the `d = 5` analogue of the
non-dropping record — while its orbit stays inside `{5, 10}`, so it supplies no
escape certificate above scale `10`. -/
theorem five_separates :
    Denominator.GenNeverDrops 5 5 ∧ (∀ j : Nat, Denominator.genOrbit 5 j 5 ≤ 10) := by
  refine ⟨Denominator.five_genNeverDrops, fun j => ?_⟩
  rcases Denominator.orbit_five j with h | h <;> rw [h] <;> omega

/-! ## Part 2: arbitrarily long finite branches (why no filter may forbid them)

`2 ^ k − 1` climbs for `k` steps, so the non-dropping tree has branches of every
finite length.  The value at step `i` is `3^i·2^(k−i) − 1`. -/

/-- A prefix of an odd run is an odd run. -/
theorem oddRun_le {x j i : Nat} (h : OddRuns.OddRun x j) (hij : i ≤ j) :
    OddRuns.OddRun x i := fun t ht => h t (by omega)

/-- **Arbitrarily long finite branches.**  `2 ^ k − 1` does not drop within `k`
accelerated steps.  Hence no divergence filter can say "certificates longer than
`L₀` do not exist"; the filter must be about a *family* of certificates carried
by one bounded witness, which is what `ScaleRecordUnbounded` negates. -/
theorem mersenne_nonDropping (k : Nat) :
    FiniteInfinite.NonDropping (2 ^ k - 1) k := by
  intro i hi
  have hpos : 0 < 2 ^ k := Arith.two_pow_pos k
  have hrun : OddRuns.OddRun (2 ^ k - 1) i :=
    oddRun_le (OddRuns.oddRun_two_pow_sub_one k) hi
  have hsplit : (2 : Nat) ^ k = 2 ^ i * 2 ^ (k - i) := by
    rw [← Nat.pow_add]
    have : i + (k - i) = k := by omega
    rw [this]
  have hq : (2 ^ k - 1) + 1 = 2 ^ i * 2 ^ (k - i) := by omega
  have hval := RunValue.oddRun_value_quot hrun hq
  have hle : (2 : Nat) ^ i * 2 ^ (k - i) ≤ 3 ^ i * 2 ^ (k - i) :=
    Nat.mul_le_mul_right _ (Arith.two_pow_le_three_pow i)
  omega

/-! ## Part 3: the divergence-half soundness witness

`expStep` is the Collatz map with the even branch `x/2` replaced by `3x/2`.  It
agrees with the Collatz map on odd inputs, satisfies the same affine law with
`a = j`, and diverges from every positive start. -/

/-- The witness map: `3x/2` on evens, `(3x+1)/2` on odds. -/
def expStep (x : Nat) : Nat := if x % 2 = 0 then 3 * x / 2 else (3 * x + 1) / 2

/-- Its orbit. -/
def expOrbit : Nat → Nat → Nat
  | 0, x => x
  | k + 1, x => expOrbit k (expStep x)

@[simp] theorem expOrbit_zero (x : Nat) : expOrbit 0 x = x := rfl

@[simp] theorem expOrbit_succ (k x : Nat) : expOrbit (k + 1) x = expOrbit k (expStep x) := rfl

/-- Peeling the last step. -/
theorem expOrbit_succ_step (k x : Nat) : expOrbit (k + 1) x = expStep (expOrbit k x) := by
  induction k generalizing x with
  | zero => rfl
  | succ k ih => rw [expOrbit_succ, ih (expStep x)]; rfl

/-- **It is the Collatz map on odd inputs.**  The two maps differ only in the
even branch, which is exactly the datum a divergence mechanism must consume. -/
theorem expStep_odd_eq {x : Nat} (h : x % 2 = 1) : expStep x = acceleratedStep x := by
  unfold expStep acceleratedStep
  rw [if_neg (by omega), if_neg (by omega)]

/-- Every step strictly increases a positive value. -/
theorem expStep_gt {x : Nat} (h : 0 < x) : x < expStep x := by
  unfold expStep
  by_cases he : x % 2 = 0
  · rw [if_pos he]; omega
  · rw [if_neg he]; omega

/-- Positivity is preserved. -/
theorem expStep_pos {x : Nat} (h : 0 < x) : 0 < expStep x := by
  have := expStep_gt h; omega

/-- The orbit grows at least linearly. -/
theorem expOrbit_ge : ∀ (k x : Nat), 0 < x → x + k ≤ expOrbit k x := by
  intro k
  induction k with
  | zero => intro x _; simp
  | succ k ih =>
    intro x hx
    have h1 : x + 1 ≤ expStep x := expStep_gt hx
    have h2 := ih (expStep x) (expStep_pos hx)
    rw [expOrbit_succ]
    omega

/-- **Every orbit of the witness map diverges**, provably and from every positive
start.  This is the object Round IX said the divergence half lacked. -/
theorem expOrbit_divergent {x : Nat} (h : 0 < x) : ∀ B : Nat, ∃ i : Nat, B < expOrbit i x := by
  intro B
  refine ⟨B + 1, ?_⟩
  have := expOrbit_ge (B + 1) x h
  omega

/-- **The witness map obeys the development's affine law**, with the odd count
saturated at `a = j`: `2^j · f^j(x) = 3^j · x + b`.  Every accumulator identity
of this development therefore applies to it verbatim. -/
theorem expOrbit_affine : ∀ (j x : Nat), ∃ b : Nat, 2 ^ j * expOrbit j x = 3 ^ j * x + b := by
  intro j
  induction j with
  | zero => intro x; exact ⟨0, by simp⟩
  | succ j ih =>
    intro x
    obtain ⟨b, hb⟩ := ih x
    have hstep : expOrbit (j + 1) x = expStep (expOrbit j x) := expOrbit_succ_step j x
    have h2 : (2 : Nat) ^ (j + 1) = 2 * 2 ^ j := Arith.two_pow_succ j
    have h3 : (3 : Nat) ^ (j + 1) = 3 * 3 ^ j := Arith.three_pow_succ j
    by_cases he : (expOrbit j x) % 2 = 0
    · refine ⟨3 * b, ?_⟩
      have hval : expStep (expOrbit j x) = 3 * expOrbit j x / 2 := by
        unfold expStep; rw [if_pos he]
      have hdouble : 2 * (3 * expOrbit j x / 2) = 3 * expOrbit j x := by omega
      have hcomm : 2 * (2 ^ j * (3 * expOrbit j x / 2))
          = 2 ^ j * (2 * (3 * expOrbit j x / 2)) := by rw [Nat.mul_left_comm]
      rw [hstep, hval, h2, h3, Nat.mul_assoc, hcomm, hdouble]
      calc 2 ^ j * (3 * expOrbit j x) = 3 * (2 ^ j * expOrbit j x) := by
            rw [Nat.mul_left_comm]
        _ = 3 * (3 ^ j * x + b) := by rw [hb]
        _ = 3 * 3 ^ j * x + 3 * b := by rw [Nat.mul_add, Nat.mul_assoc]
    · refine ⟨3 * b + 2 ^ j, ?_⟩
      have hval : expStep (expOrbit j x) = (3 * expOrbit j x + 1) / 2 := by
        unfold expStep; rw [if_neg he]
      have hdouble : 2 * ((3 * expOrbit j x + 1) / 2) = 3 * expOrbit j x + 1 := by omega
      have hcomm : 2 * (2 ^ j * ((3 * expOrbit j x + 1) / 2))
          = 2 ^ j * (2 * ((3 * expOrbit j x + 1) / 2)) := by rw [Nat.mul_left_comm]
      rw [hstep, hval, h2, h3, Nat.mul_assoc, hcomm, hdouble]
      calc 2 ^ j * (3 * expOrbit j x + 1) = 3 * (2 ^ j * expOrbit j x) + 2 ^ j := by
            rw [Nat.mul_add, Nat.mul_one, Nat.mul_left_comm]
        _ = 3 * (3 ^ j * x + b) + 2 ^ j := by rw [hb]
        _ = 3 * 3 ^ j * x + (3 * b + 2 ^ j) := by rw [Nat.mul_add, Nat.mul_assoc]; omega

/-- **The divergence-half soundness filter, in one statement.**  There is a map
which

* agrees with the accelerated Collatz map on every odd input,
* satisfies the affine law `2^j · f^j x = 3^j · x + b`,
* is heavy at every scale (`2^j ≤ 3^j`), and
* diverges from every positive integer.

Hence any divergence-half mechanism using only those three inputs proves a false
statement.  A sound mechanism must consume the even branch's contraction —
`oddCount n j < j` — which is the archimedean datum, not the 2-adic one. -/
theorem divergence_filter :
    (∀ x : Nat, x % 2 = 1 → expStep x = acceleratedStep x)
      ∧ (∀ j x : Nat, ∃ b : Nat, 2 ^ j * expOrbit j x = 3 ^ j * x + b)
      ∧ (∀ j : Nat, 2 ^ j ≤ 3 ^ j)
      ∧ (∀ x : Nat, 0 < x → ∀ B : Nat, ∃ i : Nat, B < expOrbit i x) :=
  ⟨fun _ h => expStep_odd_eq h, fun j x => expOrbit_affine j x,
   Arith.two_pow_le_three_pow, fun _ h => expOrbit_divergent h⟩

end ScaleRecord
end Collatz
