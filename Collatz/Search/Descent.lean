import Collatz.Core.Reach
import Collatz.Core.Minimum

/-!
# Verification by descent

`Collatz.Search.Verify` clears an initial segment by following each orbit all
the way to `1`.  That is wasteful: the orbit of `27` runs for `111` steps, most
of them below `27`, and every one of those steps re-verifies numbers already
checked.

The efficient device is *descent*.  To clear `[1, N]` it is enough to show that
every `n` in that range with `n > 1` has **some** accelerated iterate below `n`;
strong induction then supplies the rest.  Stopping times are tiny — the largest
below `10 000` is `81`, against a total stopping time of over `250` — so the
same computation budget reaches far higher.

The engine is `dropsWithin` (a fuelled Boolean search for a drop) and
`allDropUpTo` (its sweep).  `reachesOne_of_allDrop` is the soundness theorem
that turns a Boolean sweep into a proof about `ReachesOne`, and the exported
bound is `reachesOne_of_le_10000`.
-/

namespace Collatz
namespace Search

open Reach

/-! ## Searching for a drop -/

/-- `dropsAux n fuel cur` looks for an iterate below `n`, starting the search
from `cur` and spending at most `fuel` accelerated steps. -/
def dropsAux (n : Nat) : Nat → Nat → Bool
  | 0, _ => false
  | fuel + 1, cur =>
      let next := acceleratedStep cur
      if next < n then true else dropsAux n fuel next

/-- `dropsWithin fuel n` is `true` when `n` has an accelerated iterate below
itself within `fuel` steps. -/
def dropsWithin (fuel n : Nat) : Bool := dropsAux n fuel n

/-- Unfolding the search at a successor fuel. -/
theorem dropsAux_succ (n fuel cur : Nat) :
    dropsAux n (fuel + 1) cur =
      (if acceleratedStep cur < n then true
       else dropsAux n fuel (acceleratedStep cur)) := rfl

/-- The search has no power at zero fuel. -/
@[simp] theorem dropsAux_zero (n cur : Nat) : dropsAux n 0 cur = false := rfl

/-- Soundness of the search, in the general form needed for the induction: if
the search started at an iterate of `n` succeeds, some iterate of `n` lies
below `n`. -/
theorem exists_lt_of_dropsAux {n : Nat} : ∀ (fuel j : Nat),
    dropsAux n fuel (acceleratedOrbit j n) = true → ∃ k : Nat, acceleratedOrbit k n < n := by
  intro fuel
  induction fuel with
  | zero => intro j h; simp at h
  | succ fuel ih =>
    intro j h
    rw [dropsAux_succ] at h
    have hnext : acceleratedStep (acceleratedOrbit j n) = acceleratedOrbit (j + 1) n :=
      (acceleratedOrbit_succ_step j n).symm
    by_cases hlt : acceleratedStep (acceleratedOrbit j n) < n
    · exact ⟨j + 1, by rw [← hnext]; exact hlt⟩
    · rw [if_neg hlt] at h
      rw [hnext] at h
      exact ih (j + 1) h

/-- Soundness of the drop search. -/
theorem exists_lt_of_dropsWithin {fuel n : Nat} (h : dropsWithin fuel n = true) :
    ∃ k : Nat, acceleratedOrbit k n < n := by
  refine exists_lt_of_dropsAux fuel 0 ?_
  rw [acceleratedOrbit]
  exact h

/-! ## Sweeping an interval -/

/-- `allDropUpTo N fuel` is `true` when every `n` with `1 < n ≤ N` drops below
itself within `fuel` accelerated steps. -/
def allDropUpTo : Nat → Nat → Bool
  | 0, _ => true
  | m + 1, fuel =>
      (if m + 1 == 1 then true else dropsWithin fuel (m + 1)) && allDropUpTo m fuel

/-- Unfolding the sweep. -/
theorem allDropUpTo_succ (m fuel : Nat) :
    allDropUpTo (m + 1) fuel =
      ((if m + 1 == 1 then true else dropsWithin fuel (m + 1)) && allDropUpTo m fuel) := rfl

/-- A successful sweep yields a drop for each member of the range above `1`. -/
theorem dropsWithin_of_allDrop {N fuel n : Nat} (h : allDropUpTo N fuel = true)
    (hn : 1 < n) (hle : n ≤ N) : dropsWithin fuel n = true := by
  induction N with
  | zero => omega
  | succ m ih =>
    rw [allDropUpTo_succ, Bool.and_eq_true] at h
    by_cases hnm : n = m + 1
    · subst hnm
      have hne : ¬ ((m + 1) == 1) = true := by simp; omega
      rw [if_neg hne] at h
      exact h.1
    · exact ih h.2 (by omega)

/-- **Soundness of descent verification.**  A successful sweep of `[1, N]`
proves that every positive `n ≤ N` reaches `1`. -/
theorem reachesOne_of_allDrop {N fuel : Nat} (h : allDropUpTo N fuel = true) :
    ∀ n : Nat, 0 < n → n ≤ N → ReachesOne n := by
  intro n
  induction n using Nat.strongRecOn with
  | _ n ih =>
    intro hpos hle
    by_cases hn1 : n = 1
    · subst hn1; exact reachesOne_one
    · have hn : 1 < n := by omega
      obtain ⟨k, hk⟩ := exists_lt_of_dropsWithin (dropsWithin_of_allDrop h hn hle)
      have hkpos : 0 < acceleratedOrbit k n := acceleratedOrbit_positive hpos k
      have hkreach : ReachesOne (acceleratedOrbit k n) :=
        ih (acceleratedOrbit k n) hk hkpos (by omega)
      exact reachesOne_of_accOrbit hpos hkreach

/-! ## Verified bounds

Each is a single kernel computation.  Because the search stops at the first
drop, these are far cheaper than following orbits to `1`. -/

set_option maxRecDepth 8000 in
/-- Every `n` with `1 < n ≤ 1000` drops below itself within `100` accelerated
steps. -/
theorem check_drop_1000 : allDropUpTo 1000 100 = true := by decide

set_option maxRecDepth 40000 in
/-- Every `n` with `1 < n ≤ 10000` drops below itself within `100` accelerated
steps. -/
theorem check_drop_10000 : allDropUpTo 10000 100 = true := by decide

/-- Every positive `n ≤ 1000` reaches `1`. -/
theorem reachesOne_of_le_1000 {n : Nat} (hn : 0 < n) (hle : n ≤ 1000) : ReachesOne n :=
  reachesOne_of_allDrop check_drop_1000 n hn hle

/-- Every positive `n ≤ 10000` reaches `1`. -/
theorem reachesOne_of_le_10000 {n : Nat} (hn : 0 < n) (hle : n ≤ 10000) : ReachesOne n :=
  reachesOne_of_allDrop check_drop_10000 n hn hle

/-- A counterexample to Collatz exceeds `10000`. -/
theorem counterexample_gt_10000 {n : Nat} (hn : 0 < n) (h : ¬ ReachesOne n) : 10000 < n := by
  by_cases hle : n ≤ 10000
  · exact absurd (reachesOne_of_le_10000 hn hle) h
  · omega

/-- A counterexample exceeds `2 ^ 13 = 8192`, the largest power of two covered
by the verified range. -/
theorem counterexample_gt_two_pow_13 {n : Nat} (hn : 0 < n) (h : ¬ ReachesOne n) :
    2 ^ 13 < n := by
  have h1 : (2:Nat) ^ 13 = 8192 := by decide
  have := counterexample_gt_10000 hn h
  omega

end Search
end Collatz
