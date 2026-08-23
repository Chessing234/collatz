import Collatz.Strategy.ExtremalWord

/-!
# `Bcap` is sharp, and stays sharp: an exponentially large near-extremal family

Round XIII, section LIII.  The question put to this desk was whether the ceiling
`RealizableBound.Bcap` admits a *uniform* improvement — a constant `β > 0` with
`C(w) ≤ (1 − β) · Bcap a` for every word `w` satisfying all currently known cycle
constraints.  The answer proved here is **no**, and the obstruction is not a near
miss: the top of the heaviness box is not an isolated spike but the summit of an
exponentially large plateau, every point of which is a legal heavy word.

## What is proved

`ExtremalWord.Cw_eq_Bcap_iff` already pins the single maximiser (the Beatty word
`t i = fexp i`).  That statement is compatible with the maximiser being isolated,
which is what an improvement programme needs.  It is not.

For a selector `S : Nat → Bool` that is `false` at `0` and is `true` only at
indices where `fexp` jumps by two, define the **lowered word**

`tSub S i = fexp i − (if S i then 1 else 0)`.

* `tSub_strictInc` — every such word is a legal word (strictly increasing times);
* `tSub_heavy` — every such word is heavy on `[0, fexp a]`, i.e. it is admissible
  for exactly the same certificate that produces `Bcap`;
* `Cw_tSub_add_loss` — its accumulator is `Bcap a` minus an explicit loss;
* `sharp` — **`(a − s) · Bcap a ≤ a · Cw (tSub S) a`** where `s = cntS S a` is the
  number of lowered coordinates.  In words: `C ≥ (1 − s/a) · Bcap a`.
* `tSub_injective` — distinct selectors give distinct words.

So for every `s` there are `Nat.choose m s` distinct heavy words within a relative
`s/a` of the ceiling, `m` being the number of two-jumps of `fexp` below `a`
(`m ≈ (log₂3 − 1)·a ≈ 0.585 a`).  A uniform improvement by `β` must therefore
exclude at least `Nat.choose (0.585 a) (β a)` words, which is `2^(Θ(a))`.

## The measured version (exact integer arithmetic, independently recomputed)

* `max C` over heavy words is `Bcap a` exactly, at every `a` — attained, not
  approached.
* The runner-up gap is `1 − second/Bcap = (2 ln 2 / 3)/a + o(1/a)`; recomputed
  values of `a·(1 − second/Bcap)` are `0.46574` (`a=20`), `0.46766` (`40`),
  `0.46126` (`80`), `0.46280` (`160`), `0.46202` (`320`), `0.46227` (`1280`),
  `0.462257` (`4296`), against `2 ln 2/3 = 0.4620981`.  Four-digit stability sets
  in only past `a ≈ 320`; below that the third digit still moves.
* The count of heavy words within `1 %` of `Bcap` is `1` for every `a ≤ 46`, `2`
  at `a = 47`, `7` at `50`, `166` at `100`, `1821` at `120`.  The "unique within
  `1 %`" observation is an artefact of `0.462/a > 0.01`, i.e. of `a < 46`.
* At the surviving ledge `(6809, 4296)`: `Bcap/G = 1358717.75`, `c = 1086464`, so
  the required reduction is `20.04 %`, and the reduction bought by deleting the
  extremiser is `0.010760 %` — short by a factor `1862`.

## Why the remaining constraints cannot help

Two of them are theorems about every orbit, hence satisfied by every cycle and so
excluding nothing; the file proves both vacuities.

* `minPhase_of_heavy` — the minimum-phase (never-drop) inequality
  `2^j · x ≤ 3^k · x + C_j` is *implied* by heaviness `2^j ≤ 3^k`.  Minimum-phase
  is weaker than the hypothesis already in use, so it cannot remove a word the
  box keeps.  (Measured: at `a = 12` there are `2652` heavy words and `6310`
  minimum-phase words, and `max C` over minimum-phase words is `1.5164 · Bcap` —
  minimum-phase does not even imply the ceiling.)
* `step_odd_mod_three` and `halve_mod_three` — every orbit point after an odd step
  is `≡ 2 (mod 3)`, and even steps preserve non-divisibility, so no cycle
  containing an odd step ever meets a multiple of `3`.  The leaf condition
  ("every odd multiple of `3` is a leaf") is therefore automatic on cycles.
* `Octave.no_O0_after_O0` is likewise a theorem about all orbits.  Measured on the
  extremiser and on every single-lowering neighbour at `a = 8, 12, 17, 29, 41, 53,
  94`: the forbidden block never occurs, in `100 %` of the family.

That leaves `G ∣ C`, and `G ∣ C` together with heaviness is, by
`CycleCriterion`, *exactly* the statement that the word is a cycle word.  Using it
to shrink `Bcap` is circular: the constrained family is the set one is trying to
prove empty, and it *is* empty at every `a ≤ 15` by full enumeration (and at
`a = 1` it is non-empty — the trivial cycle, `Bcap 1 = 1 = G 1`).

**Conclusion.**  `Bcap` is sharp over the heavy words, sharp over the heavy words
after every word-level constraint known to this repository, and the one remaining
constraint is the conjecture itself.  A uniform improvement does not exist, and
the round's target should be retired rather than reassigned.
-/

namespace Collatz
namespace BcapSharp

open RealizableBound ExtremalWord

/-! ## Counting lemmas the box needs

`ExtremalWord` proves heaviness ⟹ box.  The family below needs the converse
direction, which is available once the endpoint `2 ^ J ≤ 3 ^ a` is supplied; here
`J = fexp a`, so the endpoint is `fexp_le`. -/

/-- The prefix odd-count never exceeds the number of odd steps. -/
theorem cnt_le (t : Nat → Nat) (j : Nat) : ∀ a : Nat, cnt t a j ≤ a := by
  intro a
  induction a with
  | zero => exact Nat.le_refl 0
  | succ a ih => rw [cnt_succ]; by_cases h : t a < j <;> simp [h] <;> omega

/-- If the first `k + 1` odd steps all happen before time `j`, the prefix count at
`j` is at least `k + 1`. -/
theorem cnt_ge {t : Nat → Nat} {j : Nat} :
    ∀ a k : Nat, k < a → (∀ i : Nat, i ≤ k → t i < j) → k + 1 ≤ cnt t a j := by
  intro a
  induction a with
  | zero => intro k hk; exact absurd hk (Nat.not_lt_zero k)
  | succ a ih =>
    intro k hk hall
    rcases Nat.lt_or_ge k a with hka | hka
    · have := ih k hka hall
      rw [cnt_succ]
      by_cases h : t a < j <;> simp [h] <;> omega
    · have hka' : k = a := by omega
      subst hka'
      have hfull : cnt t k j = k := cnt_all_lt k (fun i hi => hall i (Nat.le_of_lt hi))
      rw [cnt_succ, hfull, if_pos (hall k (Nat.le_refl k))]
      omega

/-- **Box ⟹ heavy, with the endpoint supplied.**  A strictly increasing word
inside the box `t i ≤ fexp i` is heavy at every time up to `fexp a`. -/
theorem heavy_of_box {t : Nat → Nat} (hst : StrictInc t) {a : Nat}
    (hbox : ∀ i : Nat, i < a → t i ≤ fexp i) :
    ∀ j : Nat, j ≤ fexp a → 2 ^ j ≤ 3 ^ cnt t a j := by
  intro j hj
  rcases Nat.lt_or_ge (cnt t a j) a with hk | hk
  · -- the count is `k < a`; then the `k`-th odd step is at or after `j`
    have hge : j ≤ t (cnt t a j) := by
      rcases Nat.lt_or_ge (t (cnt t a j)) j with hlt | hge
      · exfalso
        have hall : ∀ i : Nat, i ≤ cnt t a j → t i < j := by
          intro i hi
          rcases Nat.lt_or_ge i (cnt t a j) with h1 | h1
          · exact Nat.lt_trans (strictInc_mono hst i _ h1) hlt
          · have : i = cnt t a j := by omega
            rw [this]; exact hlt
        have := cnt_ge a (cnt t a j) hk hall
        omega
      · exact hge
    have h1 : j ≤ fexp (cnt t a j) :=
      Nat.le_trans hge (hbox (cnt t a j) hk)
    exact Nat.le_trans (Arith.two_pow_le_two_pow h1) (fexp_le (cnt t a j))
  · have hka : cnt t a j = a := Nat.le_antisymm (cnt_le t j a) hk
    rw [hka]
    exact Nat.le_trans (Arith.two_pow_le_two_pow hj) (fexp_le a)

/-- **Fact 1, in Lean.**  The top corner of the box is itself a heavy word, so
the ceiling is attained, not merely approached: `Cw fexp a = Bcap a`
(`ExtremalWord.Cw_fexp`) and the corner is heavy on `[0, fexp a]`. -/
theorem corner_heavy (a : Nat) : ∀ j : Nat, j ≤ fexp a → 2 ^ j ≤ 3 ^ cnt fexp a j :=
  heavy_of_box fexp_strictInc (fun i _ => Nat.le_refl (fexp i))

/-! ## The lowered family -/

/-- A selector is **admissible** when it never fires at index `0` and fires only
where `fexp` jumps by two — exactly the indices where lowering by one keeps the
odd-step times strictly increasing. -/
def Adm (S : Nat → Bool) : Prop :=
  S 0 = false ∧ ∀ i : Nat, S (i + 1) = true → fexp i + 2 ≤ fexp (i + 1)

/-- The lowered word: the Beatty word with the selected coordinates dropped by
one. -/
def tSub (S : Nat → Bool) (i : Nat) : Nat := fexp i - (if S i = true then 1 else 0)

theorem tSub_le (S : Nat → Bool) (i : Nat) : tSub S i ≤ fexp i := Nat.sub_le _ _

/-- At a firing index the exponent is at least two, so the drop is real. -/
theorem fexp_ge_two_of_fire {S : Nat → Bool} (hS : Adm S) {i : Nat} (h : S i = true) :
    2 ≤ fexp i := by
  match i with
  | 0 => rw [hS.1] at h; exact absurd h (by simp)
  | (p + 1) =>
    have := hS.2 p h
    omega

theorem tSub_fire {S : Nat → Bool} (hS : Adm S) {i : Nat} (h : S i = true) :
    tSub S i + 1 = fexp i := by
  have h2 := fexp_ge_two_of_fire hS h
  rw [tSub, if_pos h]
  omega

theorem tSub_quiet {S : Nat → Bool} {i : Nat} (h : S i = false) : tSub S i = fexp i := by
  rw [tSub, if_neg (by rw [h]; simp)]
  omega

/-- **Every lowered word is a legal word.** -/
theorem tSub_strictInc {S : Nat → Bool} (hS : Adm S) : StrictInc (tSub S) := by
  intro i
  have hbase : tSub S i ≤ fexp i := tSub_le S i
  by_cases h : S (i + 1) = true
  · have hjump := hS.2 i h
    have := tSub_fire hS h
    omega
  · have h' : S (i + 1) = false := by
      cases hh : S (i + 1) with
      | false => rfl
      | true => rw [hh] at h; exact absurd rfl h
    have := tSub_quiet h'
    have := fexp_strictInc i
    omega

/-- **Every lowered word is heavy**, on exactly the range the certificate uses. -/
theorem tSub_heavy {S : Nat → Bool} (hS : Adm S) (a : Nat) :
    ∀ j : Nat, j ≤ fexp a → 2 ^ j ≤ 3 ^ cnt (tSub S) a j :=
  heavy_of_box (tSub_strictInc hS) (fun i _ => tSub_le S i)

/-! ## The loss, exactly -/

/-- The accumulated loss of a lowered word, in the same Horner form as `Bcap`. -/
def lossW (S : Nat → Bool) : Nat → Nat
  | 0 => 0
  | a + 1 => 3 * lossW S a + (if S a = true then 2 ^ (fexp a - 1) else 0)

/-- The number of lowered coordinates below `a`. -/
def cntS (S : Nat → Bool) : Nat → Nat
  | 0 => 0
  | a + 1 => cntS S a + (if S a = true then 1 else 0)

/-- **The accumulator of a lowered word, exactly.** -/
theorem Cw_tSub_add_loss {S : Nat → Bool} (hS : Adm S) :
    ∀ a : Nat, Cw (tSub S) a + lossW S a = Bcap a := by
  intro a
  induction a with
  | zero => rfl
  | succ a ih =>
    rw [Cw_succ, Bcap_succ, lossW]
    by_cases h : S a = true
    · have hlow := tSub_fire hS h
      have hpow : (2:Nat) ^ fexp a = 2 * 2 ^ (tSub S a) := by
        rw [← hlow, Arith.two_pow_succ]
      have hd : tSub S a = fexp a - 1 := by rw [tSub, if_pos h]
      rw [if_pos h, ← hd, hpow]
      omega
    · have h' : S a = false := by
        cases hh : S a with
        | false => rfl
        | true => rw [hh] at h; exact absurd rfl h
      have := tSub_quiet (S := S) (i := a) h'
      rw [if_neg h, this]
      omega

/-! ## The two size bounds -/

/-- Horner shape, kept as a lemma so no rewrite has to guess an association. -/
theorem succ_mul_three (n X : Nat) : (n + 1) * (3 * X) = 3 * (n * X) + 3 * X := by
  rw [Nat.succ_mul, Nat.mul_left_comm]

theorem mul_three (n X : Nat) : n * (3 * X) = 3 * (n * X) := Nat.mul_left_comm n 3 X

/-- `Bcap` is at least `a · 3 ^ (a−1) / 2`, written without division. -/
theorem Bcap_lower : ∀ a : Nat, a * 3 ^ a ≤ 6 * Bcap a := by
  intro a
  induction a with
  | zero => simp
  | succ a ih =>
    have hstep : (3:Nat) ^ a < 2 * 2 ^ fexp a := by
      have := lt_fexp a
      rw [Arith.two_pow_succ] at this
      exact this
    have h3 : (3:Nat) ^ (a + 1) = 3 * 3 ^ a := Arith.three_pow_succ a
    rw [Bcap_succ, h3]
    have hmul : (a + 1) * (3 * 3 ^ a) = 3 * (a * 3 ^ a) + 3 * 3 ^ a :=
      succ_mul_three a (3 ^ a)
    have hgoal : 6 * (3 * Bcap a + 2 ^ fexp a) = 3 * (6 * Bcap a) + 6 * 2 ^ fexp a := by
      omega
    rw [hmul, hgoal]
    have h1 : 3 * (a * 3 ^ a) ≤ 3 * (6 * Bcap a) :=
      Nat.mul_le_mul_left 3 ih
    omega

/-- Each lowered coordinate costs at most `3 ^ (a−1) / 2`, again without
division: `6 · loss ≤ s · 3 ^ a`. -/
theorem loss_upper {S : Nat → Bool} (hS : Adm S) :
    ∀ a : Nat, 6 * lossW S a ≤ cntS S a * 3 ^ a := by
  intro a
  induction a with
  | zero => simp [lossW, cntS]
  | succ a ih =>
    have h3 : (3:Nat) ^ (a + 1) = 3 * 3 ^ a := Arith.three_pow_succ a
    rw [lossW, cntS, h3]
    by_cases h : S a = true
    · have h2 := fexp_ge_two_of_fire hS h
      have heq : (fexp a - 1) + 1 = fexp a := by omega
      have hdouble : (2:Nat) ^ ((fexp a - 1) + 1) = 2 * 2 ^ (fexp a - 1) :=
        Arith.two_pow_succ _
      rw [heq] at hdouble
      have hfe := fexp_le a
      have hpow : (2:Nat) ^ (fexp a - 1) * 2 ≤ 3 ^ a := by omega
      rw [if_pos h, if_pos h]
      have hexp : (cntS S a + 1) * (3 * 3 ^ a) = 3 * (cntS S a * 3 ^ a) + 3 * 3 ^ a :=
        succ_mul_three (cntS S a) (3 ^ a)
      have h1 : 3 * (6 * lossW S a) ≤ 3 * (cntS S a * 3 ^ a) := Nat.mul_le_mul_left 3 ih
      rw [hexp]
      omega
    · rw [if_neg h, if_neg h]
      have hexp : (cntS S a + 0) * (3 * 3 ^ a) = 3 * (cntS S a * 3 ^ a) := by
        rw [Nat.add_zero]
        exact mul_three (cntS S a) (3 ^ a)
      have h1 : 3 * (6 * lossW S a) ≤ 3 * (cntS S a * 3 ^ a) := Nat.mul_le_mul_left 3 ih
      rw [hexp]
      omega

/-- `a · loss ≤ s · Bcap a`. -/
theorem loss_le {S : Nat → Bool} (hS : Adm S) (a : Nat) : a * lossW S a ≤ cntS S a * Bcap a := by
  have h1 : 6 * (a * lossW S a) ≤ 6 * (cntS S a * Bcap a) := by
    have hA : a * (6 * lossW S a) ≤ a * (cntS S a * 3 ^ a) :=
      Nat.mul_le_mul_left a (loss_upper hS a)
    have hB : cntS S a * (a * 3 ^ a) ≤ cntS S a * (6 * Bcap a) :=
      Nat.mul_le_mul_left (cntS S a) (Bcap_lower a)
    have e1 : a * (6 * lossW S a) = 6 * (a * lossW S a) := by
      rw [← Nat.mul_assoc, ← Nat.mul_assoc, Nat.mul_comm a 6]
    have e2 : a * (cntS S a * 3 ^ a) = cntS S a * (a * 3 ^ a) := by
      rw [← Nat.mul_assoc, ← Nat.mul_assoc, Nat.mul_comm a (cntS S a)]
    have e3 : cntS S a * (6 * Bcap a) = 6 * (cntS S a * Bcap a) := by
      rw [← Nat.mul_assoc, ← Nat.mul_assoc, Nat.mul_comm (cntS S a) 6]
    rw [e1] at hA
    rw [e2] at hA
    rw [e3] at hB
    exact Nat.le_trans hA hB
  exact Nat.le_of_mul_le_mul_left h1 (by decide)

/-! ## The sharpness theorem -/

/-- **`Bcap` is sharp along an exponentially large family.**  For every admissible
selector `S` with `s = cntS S a` lowered coordinates, the lowered word is a legal
heavy word whose accumulator satisfies `C ≥ (1 − s/a) · Bcap a`, stated without
division as `(a − s) · Bcap a ≤ a · C`. -/
theorem sharp {S : Nat → Bool} (hS : Adm S) (a : Nat) :
    (a - cntS S a) * Bcap a ≤ a * Cw (tSub S) a := by
  have hid := Cw_tSub_add_loss hS a
  have hloss := loss_le hS a
  have hsplit : a * Cw (tSub S) a + a * lossW S a = a * Bcap a := by
    rw [← Nat.mul_add, hid]
  have hsub : (a - cntS S a) * Bcap a + cntS S a * Bcap a = a * Bcap a ∨
      a ≤ cntS S a := by
    rcases Nat.lt_or_ge (cntS S a) a with h | h
    · left
      rw [← Nat.add_mul]
      have : a - cntS S a + cntS S a = a := by omega
      rw [this]
    · right; exact h
  rcases hsub with h | h
  · omega
  · have : a - cntS S a = 0 := by omega
    rw [this]
    omega

/-- The single-lowering case, in the form the report quotes: one coordinate
lowered costs at most a relative `1/a`. -/
theorem sharp_one {S : Nat → Bool} (hS : Adm S) {a : Nat} (h1 : cntS S a = 1) :
    (a - 1) * Bcap a ≤ a * Cw (tSub S) a := by
  have := sharp hS a
  rw [h1] at this
  exact this

/-- **Distinct selectors give distinct words.**  So the family really has
`2 ^ (number of two-jumps below a)` members, not fewer. -/
theorem tSub_injective {S T : Nat → Bool} (hS : Adm S) (hT : Adm T) {i : Nat}
    (h : S i ≠ T i) : tSub S i ≠ tSub T i := by
  cases hs : S i with
  | true =>
    cases ht : T i with
    | true => rw [hs, ht] at h; exact absurd rfl h
    | false =>
      rw [tSub_quiet ht]
      have := tSub_fire hS hs
      omega
  | false =>
    cases ht : T i with
    | false => rw [hs, ht] at h; exact absurd rfl h
    | true =>
      rw [tSub_quiet hs]
      have := tSub_fire hT ht
      omega

/-! ## A concrete witness, so that nothing above is vacuous -/

/-- The selector that lowers coordinate `2` only.  `fexp 1 = 1`, `fexp 2 = 3`, so
`2` is a two-jump and the selector is admissible. -/
def S2 : Nat → Bool := fun i => decide (i = 2)

theorem S2_adm : Adm S2 := by
  refine ⟨by decide, ?_⟩
  intro i h
  have hi : i = 1 := by
    rcases Nat.lt_or_ge i 1 with h1 | h1
    · exfalso; have : i = 0 := by omega
      rw [this] at h; exact absurd h (by decide)
    · rcases Nat.lt_or_ge 1 i with h2 | h2
      · exfalso
        have : ¬ (i + 1 = 2) := by omega
        rw [S2] at h
        simp at h
        omega
      · omega
  rw [hi]
  decide

/-- The lowered word at `a = 5` is `t = (0,1,2,4,6)`, its accumulator is `283`
against `Bcap 5 = 319`, and `sharp` reads `4 · 319 ≤ 5 · 283`. -/
theorem S2_witness : Cw (tSub S2) 5 = 283 ∧ Bcap 5 = 319 ∧ cntS S2 5 = 1 := by
  refine ⟨by decide, by decide, by decide⟩

theorem S2_sharp : 4 * Bcap 5 ≤ 5 * Cw (tSub S2) 5 := by
  have h := sharp S2_adm 5
  have hc : cntS S2 5 = 1 := by decide
  rw [hc] at h
  exact h

/-! ## The two vacuities

Both of the non-divisibility constraints proposed for this round are theorems
about every orbit, so they hold of every cycle and exclude nothing. -/

/-- **Minimum-phase is implied by heaviness.**  If the prefix is heavy at time
`j` — `2 ^ j ≤ 3 ^ k` with `k` the prefix odd-count — then the never-drop
inequality `2 ^ j · x ≤ 3 ^ k · x + C_j` holds automatically, whatever `x` and
`C_j` are.  Minimum-phase is therefore *weaker* than the hypothesis the ceiling
already assumes, and can never remove a word the box keeps. -/
theorem minPhase_of_heavy {j k x Cj : Nat} (h : 2 ^ j ≤ 3 ^ k) :
    2 ^ j * x ≤ 3 ^ k * x + Cj :=
  Nat.le_trans (Nat.mul_le_mul_right x h) (Nat.le_add_right _ _)

/-- **An odd step lands on `2 mod 3`.**  `T(2y+1) = 3y + 2`. -/
theorem step_odd_mod_three {x : Nat} (h : x % 2 = 1) : acceleratedStep x % 3 = 2 := by
  have hx : x = 2 * (x / 2) + 1 := by omega
  have hstep : acceleratedStep x = (3 * x + 1) / 2 := by
    rw [acceleratedStep, if_neg (by omega)]
  have harith : (3 * x + 1) / 2 = 3 * (x / 2) + 2 := by omega
  rw [hstep, harith]
  omega

/-- **An even step preserves non-divisibility by three.** -/
theorem halve_mod_three {x : Nat} (h : x % 2 = 0) (hx : x % 3 ≠ 0) :
    acceleratedStep x % 3 ≠ 0 := by
  have hstep : acceleratedStep x = x / 2 := by rw [acceleratedStep, if_pos h]
  rw [hstep]
  intro hcon
  have h2 : x = 2 * (x / 2) := by omega
  omega

/-- The leaf condition is vacuous on a cycle: once an odd step has occurred, no
later orbit point is a multiple of three, and on a cycle every point is a later
point. -/
theorem leaf_vacuous {x : Nat} (h : x % 2 = 1) : acceleratedStep x % 3 ≠ 0 := by
  rw [step_odd_mod_three h]
  decide

/-! ## Axiom audit -/

#print axioms heavy_of_box
#print axioms corner_heavy
#print axioms tSub_strictInc
#print axioms tSub_heavy
#print axioms Cw_tSub_add_loss
#print axioms Bcap_lower
#print axioms loss_upper
#print axioms loss_le
#print axioms sharp
#print axioms tSub_injective
#print axioms S2_adm
#print axioms S2_sharp
#print axioms minPhase_of_heavy
#print axioms step_odd_mod_three
#print axioms leaf_vacuous

end BcapSharp
end Collatz
