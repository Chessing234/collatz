import Collatz.Strategy.ExcursionClock
import Collatz.Strategy.ExcursionEleven
import Collatz.Strategy.ExcursionCofactor
import Collatz.Strategy.ExcursionLandOne

/-!
# Lyapunov search on the excursion map — negative theorems

A ranking `Φ` that strictly decreases on every `IsExcursion` of every odd
start `n > 1` would close Lemma X: the unique odd orbit would have to
reach `1` by well-founded descent on `Φ`, and `1 < n`.  That implication
is proved below.  None of the obvious candidates satisfy the hypothesis.

The two clocks that *do* spend fuel on a single light class are not
jointly a ranking:

* plus-five `v₂(n + 5)` drops by 3 on every `(2, 1)` step, and grows
  (or stays) on leftover `(3, 1)` and on the mixed step `121 → 91`;
* eleven-fuel `v₂(11n + 19)` drops by 4 on every `(3, 1)` step, and
  grows on `(2, 1)` remainder-2 (witness `27`) and on `121 → 91`.

On that mixed step **both** fuels increase (`1 → 5` and `1 → 2`).  Every
nonnegative integer combination `α v₂(n+5) + β v₂(11n+19)` therefore
increases there, including the sum and the weighted sum
`10 v₂(n+5) + v₂(11n+19)`.  The same mixed pair keeps `91 > 71`, so the
two-step composite is not a drop below the start either.

There is no integer translate `an + b` whose 2-adic valuation is a clock
for both light classes at once: the `(2, 1)` clock forces `b = 5a` and
the `(3, 1)` clock forces `19a = 11b`, hence `a = b = 0`.  Concrete
translates `n+1` and `3n+1` fail on the requested witnesses.

Cofactors are already a 2-cycle `1 ⇄ 7` (`ExcursionCofactor`); the same
pair kills `u + 1`, and `|u − u'|` grows at `27 → 31 → 121`.

`expStep` has no `W`, so none of these drop proofs could transfer to it.
Lemma X is not closed.  This file does not claim Collatz.
-/

namespace Collatz
namespace ExcursionLyapunov

open Collatz.Arith Collatz.LiftExponent Collatz.ExcursionMap
open Collatz.ExcursionClock Collatz.ExcursionEleven
open Collatz.ExcursionCofactor Collatz.ExcursionLandOne
open Collatz.ExcursionExit Collatz.ExcursionOddLight


/-! ## 1.  A strict ranking would close Lemma X -/

/-- A ranking on odd starts: the value at the landing is strictly smaller. -/
def StrictRanking (Φ : Nat → Nat) : Prop :=
  ∀ n v u W e : Nat, 1 < n → IsExcursion n v u W e → Φ e < Φ n

/-- **Reduction.**  A strict ranking on every excursion of every odd
`n > 1` forces the odd orbit down to `1`, which is a Lemma X witness. -/
theorem lemmaX_of_strict_ranking {Φ : Nat → Nat} (hΦ : StrictRanking Φ) :
    LemmaX := by
  intro n hodd hn
  have hone : ∀ k m : Nat, Φ m = k → m % 2 = 1 → 1 < m →
      ∃ e : Nat, ExChain m e ∧ e = 1 := by
    intro k
    induction k using Nat.strongRecOn with
    | _ k ih =>
      intro m hk hmod hm
      obtain ⟨v, u, W, e, hex⟩ := exists_excursion hmod
      have hΦe : Φ e < Φ m := hΦ m v u W e hm hex
      have hke : Φ e < k := hk ▸ hΦe
      have heodd : e % 2 = 1 := hex.2.2.1
      rcases Nat.lt_or_ge e 2 with hlt | hge
      · refine ⟨e, ExChain.one ⟨v, u, W, hex⟩, ?_⟩
        omega
      · obtain ⟨e', hchain, heq⟩ := ih (Φ e) hke e rfl heodd hge
        exact ⟨e', ExChain.cons ⟨v, u, W, hex⟩ hchain, heq⟩
  obtain ⟨e, hchain, heq⟩ := hone (Φ n) n rfl hodd hn
  refine ⟨e, hchain, ?_⟩
  omega

/-!
Restricting the ranking to *growing* landings does not give Lemma X
by the same argument: `121 → 91` drops below `121` while staying above
the original start `71`.  The next sections kill the candidates even
as growth-only rankings, on that mixed step or on a light step.
-/

/-! ## 2.  The mixed witness `71 → 121 → 91` -/

/-- Unpacked mixed pair.  First step is leftover `(3, 1)`; second is
`v = 1`, `W = 1`.  The second landing is still above the start. -/
theorem seventy_one_mixed :
    IsExcursion 71 3 9 1 121 ∧
    IsExcursion 121 1 61 1 91 ∧
    71 < 91 :=
  ⟨seventy_one_fuel_grows.1, seventy_one_land_one_light.2.2.1, by omega⟩

/-- **Both fuels increase on the mixed step.**  Plus-five `1 → 5`,
eleven-fuel `1 → 2`. -/
theorem mixed_both_fuels_increase :
    IsExcursion 121 1 61 1 91 ∧
    Val2 (121 + 5) 1 ∧ Val2 (91 + 5) 5 ∧
    Val2 (11 * 121 + 19) 1 ∧ Val2 (11 * 91 + 19) 2 :=
  ⟨seventy_one_land_one_light.2.2.1,
    ⟨63, rfl, rfl⟩, ⟨3, rfl, rfl⟩,
    ⟨675, rfl, rfl⟩, ⟨255, rfl, rfl⟩⟩


/-! ## 3.  Nonnegative combinations of the two fuels -/

/-- `α v₂(n+5) + β v₂(11n+19)` strictly decreases along every excursion. -/
def JointFuelDecrease (α β : Nat) : Prop :=
  ∀ n v u W e r s r' s' : Nat,
    1 < n →
    IsExcursion n v u W e →
    Val2 (n + 5) r → Val2 (11 * n + 19) s →
    Val2 (e + 5) r' → Val2 (11 * e + 19) s' →
    α * r' + β * s' < α * r + β * s

/-- **No nonnegative combination is a ranking.**  On `121 → 91` the
inequality is `5α + 2β < α + β`, i.e. `4α + β < 0`. -/
theorem not_joint_fuel (α β : Nat) : ¬ JointFuelDecrease α β := by
  intro hf
  have h121 := mixed_both_fuels_increase
  have hlt :=
    hf 121 1 61 1 91 1 1 5 2 (by omega) h121.1
      h121.2.1 h121.2.2.2.1 h121.2.2.1 h121.2.2.2.2
  omega

/-- In particular the unweighted sum `v₂(n+5) + v₂(11n+19)` is not a ranking. -/
theorem not_fuel_sum : ¬ JointFuelDecrease 1 1 :=
  not_joint_fuel 1 1

/-- The weighted sum `10 v₂(n+5) + v₂(11n+19)` is not a ranking. -/
theorem not_fuel_weighted : ¬ JointFuelDecrease 10 1 :=
  not_joint_fuel 10 1

/-- Two-step composite on the `71` family: the joint fuel returns to its
start value, and the landing is still larger.  Fuel `7 → 2 → 7`. -/
theorem seventy_one_two_step_fuel_flat :
    IsExcursion 71 3 9 1 121 ∧
    IsExcursion 121 1 61 1 91 ∧
    Val2 (71 + 5) 2 ∧ Val2 (11 * 71 + 19) 5 ∧
    Val2 (121 + 5) 1 ∧ Val2 (11 * 121 + 19) 1 ∧
    Val2 (91 + 5) 5 ∧ Val2 (11 * 91 + 19) 2 ∧
    2 + 5 = 5 + 2 ∧ 71 < 91 :=
  ⟨seventy_one_fuel_grows.1,
    seventy_one_land_one_light.2.2.1,
    ⟨19, rfl, rfl⟩, ⟨25, rfl, rfl⟩,
    ⟨63, rfl, rfl⟩, ⟨675, rfl, rfl⟩,
    ⟨3, rfl, rfl⟩, ⟨255, rfl, rfl⟩,
    rfl, by omega⟩


/-! ## 4.  Each fuel separately, on the other light class -/

/-- Plus-five is a ranking. -/
def PlusFiveDecrease : Prop :=
  ∀ n v u W e r r' : Nat,
    1 < n → IsExcursion n v u W e →
    Val2 (n + 5) r → Val2 (e + 5) r' → r' < r

/-- Eleven-fuel is a ranking. -/
def ElevenDecrease : Prop :=
  ∀ n v u W e s s' : Nat,
    1 < n → IsExcursion n v u W e →
    Val2 (11 * n + 19) s → Val2 (11 * e + 19) s' → s' < s

/-- **Plus-five grows on the mixed step.**  `v₂(121 + 5) = 1`,
`v₂(91 + 5) = 5`. -/
theorem not_plus_five_mixed : ¬ PlusFiveDecrease := by
  intro hf
  have h121 := mixed_both_fuels_increase
  have := hf 121 1 61 1 91 1 5 (by omega) h121.1 h121.2.1 h121.2.2.1
  omega

/-- **Plus-five does not drop on leftover `(3, 1)`.**  Witness `103`:
valuation `2` at both ends.  Same stagnation at `231`. -/
theorem not_plus_five_leftover :
    IsExcursion 103 3 13 1 175 ∧
    Val2 (103 + 5) 2 ∧ Val2 (175 + 5) 2 ∧
    IsExcursion 231 3 29 1 391 ∧
    Val2 (231 + 5) 2 ∧ Val2 (391 + 5) 2 :=
  ⟨one_oh_three_fuel.1, ⟨27, rfl, rfl⟩, ⟨45, rfl, rfl⟩,
    two_thirty_one_two_light.1, ⟨59, rfl, rfl⟩, ⟨99, rfl, rfl⟩⟩

theorem not_plus_five_of_one_oh_three : ¬ PlusFiveDecrease := by
  intro hf
  have h := not_plus_five_leftover
  have := hf 103 3 13 1 175 2 2 (by omega) h.1 h.2.1 h.2.2.1
  omega

/-- Plus-five *increases* on a leftover step: `39 → 67`, valuation `2 → 3`.
This is why overweighting plus-five fails even on `(3, 1)`. -/
theorem plus_five_increases_at_thirty_nine :
    IsExcursion 39 3 5 1 67 ∧ Val2 (39 + 5) 2 ∧ Val2 (67 + 5) 3 :=
  ⟨thirty_nine_fuel.1, ⟨11, rfl, rfl⟩, ⟨9, rfl, rfl⟩⟩

/-- Weighted fuel grows at `39` even though the unweighted sum drops there
(`8 → 5` versus `26 → 32`). -/
theorem weighted_grows_at_thirty_nine :
    IsExcursion 39 3 5 1 67 ∧
    Val2 (39 + 5) 2 ∧ Val2 (11 * 39 + 19) 6 ∧
    Val2 (67 + 5) 3 ∧ Val2 (11 * 67 + 19) 2 ∧
    ¬ (10 * 3 + 2 < 10 * 2 + 6) :=
  ⟨thirty_nine_fuel.1, ⟨11, rfl, rfl⟩, ⟨7, rfl, rfl⟩,
    ⟨9, rfl, rfl⟩, ⟨189, rfl, rfl⟩, by decide⟩

/-- **Eleven-fuel grows on `(2, 1)`.**  Witness `27`: valuation `2 → 3`. -/
theorem not_eleven_light :
    IsExcursion 27 2 7 1 31 ∧
    Val2 (11 * 27 + 19) 2 ∧ Val2 (11 * 31 + 19) 3 :=
  ⟨twenty_seven_fuel.1, ⟨79, rfl, rfl⟩, ⟨45, rfl, rfl⟩⟩

theorem not_eleven_of_twenty_seven : ¬ ElevenDecrease := by
  intro hf
  have h := not_eleven_light
  have := hf 27 2 7 1 31 2 3 (by omega) h.1 h.2.1 h.2.2
  omega

/-- Eleven-fuel also grows on the mixed step `121 → 91` (`1 → 2`). -/
theorem not_eleven_mixed : ¬ ElevenDecrease := by
  intro hf
  have h121 := mixed_both_fuels_increase
  have :=
    hf 121 1 61 1 91 1 2 (by omega) h121.1 h121.2.2.2.1 h121.2.2.2.2
  omega

/-- Joint sum fails on a `(2, 1)` step of the `71` family: `91 → 103`
sends `7 → 9` (plus-five drops `5 → 2`, eleven-fuel jumps `2 → 7`). -/
theorem joint_grows_at_ninety_one :
    IsExcursion 91 2 23 1 103 ∧
    Val2 (91 + 5) 5 ∧ Val2 (11 * 91 + 19) 2 ∧
    Val2 (103 + 5) 2 ∧ Val2 (11 * 103 + 19) 7 ∧
    ¬ (2 + 7 < 5 + 2) :=
  ⟨⟨rfl, rfl, rfl, by omega, by omega, rfl, rfl⟩,
    ⟨3, rfl, rfl⟩, ⟨255, rfl, rfl⟩,
    ⟨27, rfl, rfl⟩, ⟨9, rfl, rfl⟩, by decide⟩


/-! ## 5.  `v₂(n+1)` and `v₂(3n+1)` -/

def SuccDecrease : Prop :=
  ∀ n v u W e r r' : Nat,
    1 < n → IsExcursion n v u W e →
    Val2 (n + 1) r → Val2 (e + 1) r' → r' < r

def ThreeNOneDecrease : Prop :=
  ∀ n v u W e r r' : Nat,
    1 < n → IsExcursion n v u W e →
    Val2 (3 * n + 1) r → Val2 (3 * e + 1) r' → r' < r

/-- **`v₂(n+1)` grows on `(2, 1)`.**  Witness `27`: `2 → 5`.  This is
the odd-run length, which the remainder-2 exit of the light clock
lengthens. -/
theorem succ_grows_at_twenty_seven :
    IsExcursion 27 2 7 1 31 ∧ Val2 (27 + 1) 2 ∧ Val2 (31 + 1) 5 :=
  ⟨twenty_seven_fuel.1, ⟨7, rfl, rfl⟩, ⟨1, rfl, rfl⟩⟩

theorem not_succ_of_twenty_seven : ¬ SuccDecrease := by
  intro hf
  have h := succ_grows_at_twenty_seven
  have := hf 27 2 7 1 31 2 5 (by omega) h.1 h.2.1 h.2.2
  omega

/-- `v₂(n+1)` also grows on leftover `103` (`3 → 4`) and is flat on
`231` (`3 → 3`). -/
theorem succ_not_drop_leftover :
    IsExcursion 103 3 13 1 175 ∧ Val2 (103 + 1) 3 ∧ Val2 (175 + 1) 4 ∧
    IsExcursion 231 3 29 1 391 ∧ Val2 (231 + 1) 3 ∧ Val2 (391 + 1) 3 :=
  ⟨one_oh_three_fuel.1, ⟨13, rfl, rfl⟩, ⟨11, rfl, rfl⟩,
    two_thirty_one_two_light.1, ⟨29, rfl, rfl⟩, ⟨49, rfl, rfl⟩⟩

/-- **`v₂(3n+1)` grows on the first step of `71`.**  `1 → 2`. -/
theorem three_n_one_grows_at_seventy_one :
    IsExcursion 71 3 9 1 121 ∧
    Val2 (3 * 71 + 1) 1 ∧ Val2 (3 * 121 + 1) 2 :=
  ⟨seventy_one_fuel_grows.1, ⟨107, rfl, rfl⟩, ⟨91, rfl, rfl⟩⟩

theorem not_three_n_one_of_seventy_one : ¬ ThreeNOneDecrease := by
  intro hf
  have h := three_n_one_grows_at_seventy_one
  have := hf 71 3 9 1 121 1 2 (by omega) h.1 h.2.1 h.2.2
  omega

/-- `v₂(3n+1)` is already `1` at the light witnesses `27`, `103`, `231`,
and stays `1` at the landing. -/
theorem three_n_one_flat_lights :
    IsExcursion 27 2 7 1 31 ∧
    Val2 (3 * 27 + 1) 1 ∧ Val2 (3 * 31 + 1) 1 ∧
    IsExcursion 103 3 13 1 175 ∧
    Val2 (3 * 103 + 1) 1 ∧ Val2 (3 * 175 + 1) 1 ∧
    IsExcursion 231 3 29 1 391 ∧
    Val2 (3 * 231 + 1) 1 ∧ Val2 (3 * 391 + 1) 1 :=
  ⟨twenty_seven_fuel.1, ⟨41, rfl, rfl⟩, ⟨47, rfl, rfl⟩,
    one_oh_three_fuel.1, ⟨155, rfl, rfl⟩, ⟨263, rfl, rfl⟩,
    two_thirty_one_two_light.1, ⟨347, rfl, rfl⟩, ⟨587, rfl, rfl⟩⟩


/-! ## 6.  No common integer clock `an + b` -/

/-- If `8(ae + b) = 9(an + b)` on a `(2, 1)` excursion, the translate is
a scale of plus-five: `b = 5a`. -/
theorem affine_clock_two_one {n u e a b : Nat}
    (h : IsExcursion n 2 u 1 e)
    (heq : 8 * (a * e + b) = 9 * (a * n + b)) : b = 5 * a := by
  have h8 : 8 * e = 9 * n + 5 := by
    have := eight_clock h
    omega
  have lhs : 8 * (a * e + b) = a * (8 * e) + 8 * b := by
    rw [Nat.mul_add, ← Nat.mul_assoc, Nat.mul_comm 8 a, Nat.mul_assoc]
  have lhs' : 8 * (a * e + b) = 9 * (a * n) + 5 * a + 8 * b := by
    rw [lhs, h8, Nat.mul_add, ← Nat.mul_assoc, Nat.mul_comm a 9, Nat.mul_assoc,
        Nat.mul_comm a 5]
  have rhs : 9 * (a * n + b) = 9 * (a * n) + 9 * b := Nat.mul_add _ _ _
  have heq' : 9 * (a * n) + (5 * a + 8 * b) = 9 * (a * n) + 9 * b := by
    rw [← Nat.add_assoc, ← lhs', heq, rhs]
  have : 5 * a + 8 * b = 9 * b := Nat.add_left_cancel heq'
  omega

/-- If `16(ae + b) = 27(an + b)` on a `(3, 1)` excursion, the translate
is a scale of eleven-fuel: `19a = 11b`. -/
theorem affine_clock_three_one {n u e a b : Nat}
    (h : IsExcursion n 3 u 1 e)
    (heq : 16 * (a * e + b) = 27 * (a * n + b)) : 19 * a = 11 * b := by
  have h16 : 16 * e = 27 * n + 19 := by
    have ⟨hnu, hpeak⟩ := eqs_of_v_three_W_one h
    omega
  have lhs : 16 * (a * e + b) = a * (16 * e) + 16 * b := by
    rw [Nat.mul_add, ← Nat.mul_assoc, Nat.mul_comm 16 a, Nat.mul_assoc]
  have lhs' : 16 * (a * e + b) = 27 * (a * n) + 19 * a + 16 * b := by
    rw [lhs, h16, Nat.mul_add, ← Nat.mul_assoc, Nat.mul_comm a 27, Nat.mul_assoc,
        Nat.mul_comm a 19]
  have rhs : 27 * (a * n + b) = 27 * (a * n) + 27 * b := Nat.mul_add _ _ _
  have heq' : 27 * (a * n) + (19 * a + 16 * b) = 27 * (a * n) + 27 * b := by
    rw [← Nat.add_assoc, ← lhs', heq, rhs]
  have : 19 * a + 16 * b = 27 * b := Nat.add_left_cancel heq'
  omega

/-- **No common integer clock.**  A translate cannot be a 2-adic clock
for both light classes unless it is the zero translate. -/
theorem no_common_integer_clock {a b : Nat}
    (h21 : ∀ n u e : Nat, IsExcursion n 2 u 1 e →
      8 * (a * e + b) = 9 * (a * n + b))
    (h31 : ∀ n u e : Nat, IsExcursion n 3 u 1 e →
      16 * (a * e + b) = 27 * (a * n + b)) :
    a = 0 ∧ b = 0 := by
  have hb : b = 5 * a :=
    affine_clock_two_one eleven_fuel.1 (h21 11 3 13 eleven_fuel.1)
  have h19 : 19 * a = 11 * b :=
    affine_clock_three_one seven_is_v_three_W_one
      (h31 7 1 13 seven_is_v_three_W_one)
  omega

/-- The same obstruction at the two seed excursions, as a closed
equality: `b = 5a` and `19a = 11b`. -/
theorem no_common_clock_of_seeds {a b : Nat}
    (h21 : 8 * (a * 13 + b) = 9 * (a * 11 + b))
    (h31 : 16 * (a * 13 + b) = 27 * (a * 7 + b)) :
    a = 0 ∧ b = 0 := by omega


/-! ## 7.  Cofactor candidates `u`, `u + 1`, `|u − u'|` -/

/-- Absolute difference on `Nat`, without truncated subtraction traps. -/
def absDiff (a b : Nat) : Nat := if a ≤ b then b - a else a - b

/-- `u` grows at `71` (`9 → 61`) and at `231` (`29 → 49`). -/
theorem u_grows_at_seventy_one :
    IsExcursion 71 3 9 1 121 ∧ 121 + 1 = 2 ^ 1 * 61 ∧ 9 < 61 :=
  ⟨seventy_one_fuel_grows.1, rfl, by omega⟩

theorem u_grows_at_two_thirty_one :
    IsExcursion 231 3 29 1 391 ∧ 391 + 1 = 2 ^ 3 * 49 ∧ 29 < 49 :=
  ⟨two_thirty_one_two_light.1, rfl, by omega⟩

/-- `u` itself is not a ranking: the pair `7 ↦ 13` (`1 → 7`) and
`27 ↦ 31` (`7 → 1`) is a 2-cycle.  Reuses `ExcursionCofactor.no_u_energy`. -/
theorem not_u_ranking : ¬ DecreasesAlong (fun _ u => u) :=
  ExcursionCofactor.not_u_ranking

/-- `u + 1` is the same 2-cycle shifted, so it is not a ranking either. -/
theorem not_u_succ_ranking : ¬ DecreasesAlong (fun _ u => u + 1) :=
  no_u_energy (fun u => u + 1)

/-- Gap ranking: `|u − u'|` of one excursion versus the next. -/
def GapDecrease : Prop :=
  ∀ n v u W e v' u' W' e' v'' u'' W'' e'' : Nat,
    1 < n →
    IsExcursion n v u W e →
    IsExcursion e v' u' W' e' →
    IsExcursion e' v'' u'' W'' e'' →
    absDiff u' u'' < absDiff u u'

/-- **`|u − u'|` grows at `27`.**  The cofactor crashes `7 → 1`, then
the Mersenne landing `31` opens `1 → 61`.  Gaps `6 → 60`. -/
theorem gap_grows_at_twenty_seven :
    IsExcursion 27 2 7 1 31 ∧
    IsExcursion 31 5 1 1 121 ∧
    IsExcursion 121 1 61 1 91 ∧
    absDiff 7 1 = 6 ∧ absDiff 1 61 = 60 :=
  ⟨twenty_seven_is_excursion, thirty_one_is_excursion,
    seventy_one_land_one_light.2.2.1, rfl, rfl⟩

theorem not_gap_ranking : ¬ GapDecrease := by
  intro hf
  have h := gap_grows_at_twenty_seven
  have hlt :=
    hf 27 2 7 1 31 5 1 1 121 1 61 1 91 (by omega) h.1 h.2.1 h.2.2.1
  have hne : ¬ absDiff 1 61 < absDiff 7 1 := by
    simp [absDiff]
  exact hne hlt

/-- At `103` the first gap is tiny (`13 → 11`) and the next is not:
`175` has cofactor `11` and lands on `445` with cofactor `223`. -/
theorem gap_grows_at_one_oh_three :
    IsExcursion 103 3 13 1 175 ∧
    IsExcursion 175 4 11 1 445 ∧
    absDiff 13 11 = 2 ∧ absDiff 11 223 = 212 :=
  ⟨one_oh_three_fuel.1,
    ⟨rfl, rfl, rfl, by omega, by omega, rfl, rfl⟩, rfl, rfl⟩


/-! ## 8.  What this does not close -/

/-- The search does not produce a `StrictRanking`, so
`lemmaX_of_strict_ranking` has nothing to apply to.  Lemma X remains
the remaining input of `collatz_of_lemmaX`.  This is not a proof of
Collatz, and not a proof that no ranking exists — only that the
clocks, their nonnegative combinations, the two standard translates
`n+1` and `3n+1`, and the cofactor energies all fail, with explicit
excursions `71`, `27`, `103`, `231`. -/
theorem lemmaX_still_open :
    (∀ α β : Nat, ¬ JointFuelDecrease α β) ∧
    ¬ PlusFiveDecrease ∧ ¬ ElevenDecrease ∧
    ¬ SuccDecrease ∧ ¬ ThreeNOneDecrease ∧
    ¬ DecreasesAlong (fun _ u => u) ∧
    ¬ DecreasesAlong (fun _ u => u + 1) ∧
    ¬ GapDecrease :=
  ⟨not_joint_fuel, not_plus_five_mixed, not_eleven_of_twenty_seven,
    not_succ_of_twenty_seven, not_three_n_one_of_seventy_one,
    not_u_ranking, not_u_succ_ranking, not_gap_ranking⟩

end ExcursionLyapunov
end Collatz

section AxiomAudit
open Collatz.ExcursionLyapunov
#print axioms lemmaX_of_strict_ranking
#print axioms not_joint_fuel
#print axioms not_plus_five_mixed
#print axioms not_plus_five_of_one_oh_three
#print axioms not_eleven_of_twenty_seven
#print axioms not_succ_of_twenty_seven
#print axioms not_three_n_one_of_seventy_one
#print axioms no_common_integer_clock
#print axioms not_u_succ_ranking
#print axioms not_gap_ranking
#print axioms lemmaX_still_open
end AxiomAudit
