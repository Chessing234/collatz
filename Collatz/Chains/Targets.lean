import Collatz.Chains.Descent
import Collatz.Structure.Predecessor
import Collatz.Search.Descent

/-!
# Chains 7–12: reaching a target

Instead of asking an orbit to get *smaller*, ask it to reach a specific set.
Different targets give genuinely different-looking hypotheses, even when the
underlying difficulty is the same, and one of them — the backward tree — turns
the problem from a statement about iteration into a statement about generation.

| chain | hypothesis                                        | status |
|-------|---------------------------------------------------|--------|
| 7     | every orbit hits a power of two                    | open   |
| 8     | every orbit enters the verified range `[1, 10000]` | open   |
| 9     | every odd `n > 1` reaches a smaller odd number     | open   |
| 10    | every positive number lies in the backward tree of `1` | open |
| 11    | every odd `n > 1` drops under the Syracuse map      | open   |
| 12    | no minimal counterexample exists                   | open   |
-/

namespace Collatz
namespace Chains

open Reach Strategy Predecessor

/-! ## Chain 7 — hitting a power of two -/

/-- Hypothesis: every orbit meets the powers of two. -/
def H7_hitsPowerOfTwo : Prop := ∀ n : Nat, 0 < n → ∃ k j : Nat, orbit k n = 2 ^ j

/-- **Chain 7.**  Hitting a power of two implies Collatz, because powers of two
already reach `1`. -/
theorem chain07 (h : H7_hitsPowerOfTwo) : CollatzConjecture := by
  intro n hn
  obtain ⟨k, j, hkj⟩ := h n hn
  exact (reachesOne_iff_orbit k n).mpr (by rw [hkj]; exact reachesOne_two_pow j)

/-- The converse holds too — `1 = 2 ^ 0` — so Chain 7 is a restatement. -/
theorem chain07_of_collatz (hC : CollatzConjecture) : H7_hitsPowerOfTwo := by
  intro n hn
  obtain ⟨k, hk⟩ := hC n hn
  exact ⟨k, 0, by rw [hk]⟩

/-! ## Chain 8 — entering the verified range -/

/-- Hypothesis: every orbit eventually enters the range already verified by
kernel computation. -/
def H8_entersVerified : Prop := ∀ n : Nat, 0 < n → ∃ k : Nat, orbit k n ≤ 10000

/-- **Chain 8.**  Entering the verified range implies Collatz.  This chain is
the one that actually improves when the verified range is extended. -/
theorem chain08 (h : H8_entersVerified) : CollatzConjecture := by
  intro n hn
  obtain ⟨k, hk⟩ := h n hn
  have hpos : 0 < orbit k n := orbit_positive hn k
  exact (reachesOne_iff_orbit k n).mpr (Search.reachesOne_of_le_10000 hpos hk)

/-! ## Chain 9 — a smaller odd number -/

/-- Hypothesis: every odd `n > 1` reaches a strictly smaller odd number. -/
def H9_smallerOdd : Prop :=
  ∀ n : Nat, 1 < n → n % 2 = 1 → ∃ k : Nat, acceleratedOrbit k n < n

/-- **Chain 9.**  Descent on the odd numbers implies Collatz, since even numbers
descend on their own. -/
theorem chain09 (h : H9_smallerOdd) : CollatzConjecture :=
  collatz_of_finiteStoppingTime (finiteStoppingTime_of_odd h)

/-! ## Chain 10 — the backward tree

Rather than iterating forwards, generate.  Start from `1`, and close under the
two backward moves: doubling, and the odd predecessor `(m-1)/3` available
exactly when `m ≡ 4 (mod 6)`.  The conjecture says the closure is everything. -/

/-- `InTree n` says `n` can be generated from `1` by backward Collatz moves. -/
inductive InTree : Nat → Prop
  | one : InTree 1
  | double {m : Nat} : InTree m → InTree (2 * m)
  | oddPred {m : Nat} : InTree m → m % 6 = 4 → InTree ((m - 1) / 3)

/-- **Soundness of the tree.**  Everything generated from `1` reaches `1`. -/
theorem reachesOne_of_inTree {n : Nat} (h : InTree n) : ReachesOne n := by
  induction h with
  | one => exact reachesOne_one
  | double _ ih => exact reachesOne_two_mul ih
  | oddPred _ hm ih => exact (reachesOne_odd_pred_iff hm).mpr ih

/-- Hypothesis: the backward tree of `1` exhausts the positive integers. -/
def H10_treeIsEverything : Prop := ∀ n : Nat, 0 < n → InTree n

/-- **Chain 10.**  If the backward tree is everything, Collatz holds. -/
theorem chain10 (h : H10_treeIsEverything) : CollatzConjecture :=
  fun n hn => reachesOne_of_inTree (h n hn)

/-- The converse also holds, so the tree really is the set of numbers reaching
`1` — but proving membership for a given `n` is exactly the original problem. -/
theorem inTree_two : InTree 2 := by
  have := InTree.double InTree.one
  simpa using this

theorem inTree_four : InTree 4 := by
  have := InTree.double inTree_two
  simpa using this

theorem inTree_eight : InTree 8 := by
  have := InTree.double inTree_four
  simpa using this

theorem inTree_sixteen : InTree 16 := by
  have := InTree.double inTree_eight
  simpa using this

/-- `5` enters the tree through the odd predecessor of `16`. -/
theorem inTree_five : InTree 5 := by
  have h := InTree.oddPred inTree_sixteen (by decide)
  simpa using h

theorem inTree_ten : InTree 10 := by
  have := InTree.double inTree_five
  simpa using this

/-- `3` enters through the odd predecessor of `10`. -/
theorem inTree_three : InTree 3 := by
  have h := InTree.oddPred inTree_ten (by decide)
  simpa using h

theorem inTree_six : InTree 6 := by
  have := InTree.double inTree_three
  simpa using this

theorem inTree_twenty : InTree 20 := by
  have := InTree.double inTree_ten
  simpa using this

/-- `13` enters through the odd predecessor of `40`. -/
theorem inTree_thirteen : InTree 13 := by
  have h40 : InTree 40 := by
    have := InTree.double inTree_twenty
    simpa using this
  have h := InTree.oddPred h40 (by decide)
  simpa using h

/-! ## Chain 11 — the Syracuse map

The Syracuse map sends an odd `n` to the odd part of `3n + 1`, compressing every
run of halvings into a single move.  It is the natural object when one wants to
think of the dynamics as acting on odd numbers alone. -/

/-- Strip factors of two, using `fuel` to stay structurally recursive. -/
def oddPartAux : Nat → Nat → Nat
  | 0, n => n
  | fuel + 1, n => if n % 2 = 0 then oddPartAux fuel (n / 2) else n

/-- The odd part of a positive number. -/
def oddPart (n : Nat) : Nat := oddPartAux n n

/-- The Syracuse map on odd numbers. -/
def syracuse (n : Nat) : Nat := oddPart (3 * n + 1)

/-- **Specification of the odd part.**  Enough fuel recovers a factorisation
`n = 2 ^ v · odd`. -/
theorem oddPartAux_spec : ∀ (fuel n : Nat), 0 < n → n ≤ fuel →
    ∃ v : Nat, n = 2 ^ v * oddPartAux fuel n ∧ oddPartAux fuel n % 2 = 1 := by
  intro fuel
  induction fuel with
  | zero => intro n hn hle; omega
  | succ fuel ih =>
    intro n hn hle
    rw [oddPartAux]
    by_cases he : n % 2 = 0
    · rw [if_pos he]
      have hn2 : 0 < n / 2 := by omega
      have hle2 : n / 2 ≤ fuel := by omega
      obtain ⟨v, hv, hodd⟩ := ih (n / 2) hn2 hle2
      refine ⟨v + 1, ?_, hodd⟩
      rw [Arith.two_pow_succ, Nat.mul_assoc, ← hv]
      omega
    · rw [if_neg he]
      exact ⟨0, by simp, by omega⟩

/-- The odd part is a power-of-two divisor away from the number itself. -/
theorem oddPart_spec {n : Nat} (hn : 0 < n) :
    ∃ v : Nat, n = 2 ^ v * oddPart n ∧ oddPart n % 2 = 1 :=
  oddPartAux_spec n n hn (Nat.le_refl n)

/-- Stripping factors of two does not change whether a number reaches `1`. -/
theorem reachesOne_oddPart_iff {n : Nat} (hn : 0 < n) :
    ReachesOne n ↔ ReachesOne (oddPart n) := by
  obtain ⟨v, hv, _⟩ := oddPart_spec hn
  constructor
  · intro h
    rw [hv] at h
    exact (reachesOne_two_pow_mul_iff v (oddPart n)).mp h
  · intro h
    rw [hv]
    exact (reachesOne_two_pow_mul_iff v (oddPart n)).mpr h

/-- **The Syracuse step preserves reaching `1`.** -/
theorem reachesOne_syracuse_iff {n : Nat} (hn : 0 < n) (hodd : n % 2 = 1) :
    ReachesOne n ↔ ReachesOne (syracuse n) := by
  rw [syracuse, ← reachesOne_oddPart_iff (by omega), ← reachesOne_odd_iff hn hodd]

/-- Hypothesis: the Syracuse map descends. -/
def H11_syracuseDescends : Prop :=
  ∀ n : Nat, 1 < n → n % 2 = 1 → ∃ k : Nat, acceleratedOrbit k n < n

/-- **Chain 11.**  Syracuse descent implies Collatz. -/
theorem chain11 (h : H11_syracuseDescends) : CollatzConjecture :=
  collatz_of_finiteStoppingTime (finiteStoppingTime_of_odd h)

/-- Concrete Syracuse values, confirming the map is what it should be. -/
theorem syracuse_one : syracuse 1 = 1 := by decide
theorem syracuse_three : syracuse 3 = 5 := by decide
theorem syracuse_five : syracuse 5 = 1 := by decide
theorem syracuse_seven : syracuse 7 = 11 := by decide
theorem syracuse_eleven : syracuse 11 = 17 := by decide

/-! ## Chain 12 — no minimal counterexample -/

/-- Hypothesis: no least counterexample exists. -/
def H12_noMinimal : Prop := ¬ ∃ n : Nat, Minimal.MinimalCounterexample n

/-- **Chain 12.**  Excluding a minimal counterexample implies Collatz. -/
theorem chain12 (h : H12_noMinimal) : CollatzConjecture :=
  Minimal.collatz_iff_no_minimalCounterexample.mpr h

/-- And conversely, so this chain is an exact restatement. -/
theorem chain12_equiv : CollatzConjecture ↔ H12_noMinimal :=
  Minimal.collatz_iff_no_minimalCounterexample

end Chains
end Collatz
