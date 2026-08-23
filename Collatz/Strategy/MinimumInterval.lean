import Collatz.Strategy.RealizableBound

/-!
# The minimum interval `I(w)`, and why it costs the certificate nothing

For a cycle word the start is **forced**: `x₀ = C(w) / G(w)`.  So the
minimum-phase requirement "`x₀` is the least element of the cycle" turns into a
statement with no magnitude in it at all — a pure inequality between the word's
own partial accumulators.  Sections XLIV–XLVIII asked what that buys.  The
answer proved here is: **exactly nothing, and provably nothing.**

## The interval

Write the odd-step times as `t₀ < t₁ < … < t_{a−1}` (`tᵢ` = number of even steps
before the `(i+1)`-st odd step) and

`C⁽ⁱ⁾ = Σ_{k<i} 3 ^ (i−1−k) · 2 ^ (t_k)`,  `C = C⁽ᵃ⁾`,  `G = 2 ^ E − 3 ^ a`,  `E = L − a`.

A start value `x` makes the start the minimum iff `xⱼ ≥ x` at every one of the
`L` prefixes.  Since `Cⱼ` is constant along an even run while `2 ^ (eⱼ)` grows,
only the **last** prefix of each run can bind, and those are exactly the prefixes
sitting just before an odd step.  Hence

`I(w) = { x : 2 ^ (tᵢ) · x ≤ 3 ^ i · x + C⁽ⁱ⁾ for i = 1 … a−1, and 2 ^ E · x ≤ 3 ^ a · x + C }`

— an **interval** `[1, M(w)]`, `M(w) = min over light prefixes of C⁽ⁱ⁾/(2^(tᵢ) − 3^i)`,
whose right endpoint is realised by the last constraint alone at `x = C/G`.

## The theorem

`minPhase_of_heavy` below: a word that is heavy (`2 ^ (tᵢ) ≤ 3 ^ i`, the
`RealizableBound` hypothesis) satisfies **every** minimum-phase inequality, and
satisfies the proper ones **strictly**.  The reason is not delicate — under
heaviness the left side of `2 ^ (tᵢ) · C ≤ 3 ^ i · C + G · C⁽ⁱ⁾` is already
`≤ 3 ^ i · C` before the `G · C⁽ⁱ⁾` term is spent.

So minimum-phase is *implied by* the constraint the certificate already imposes.
It cannot cut down the feasible set, so it cannot lower `Bcap`.  Together with
`corner_acc` (the top corner `tᵢ = fexp i` is a legal heavy word attaining
`Bcap a`) and `acc_le_Bcap`, this closes the section:

**`Bcap` is sharp over heavy words, and remains sharp after minimum-phase and
strict minimum-phase are added.**
-/

namespace Collatz
namespace MinimumInterval

open RealizableBound

/-! ## Words and their accumulators -/

/-- Horner pass: `go s (t :: ts) = go (3 * s + 2 ^ t) ts`.  Started at `0` over
`[t₀, …, t_{a−1}]` this is `Σ_{i<a} 3 ^ (a−1−i) · 2 ^ (tᵢ)`. -/
def go : Nat → List Nat → Nat
  | s, [] => s
  | s, t :: ts => go (3 * s + 2 ^ t) ts

/-- The accumulator `C(w)` of a word given by its ordered odd-step times. -/
def acc (l : List Nat) : Nat := go 0 l

theorem go_append : ∀ (l₁ l₂ : List Nat) (s : Nat), go s (l₁ ++ l₂) = go (go s l₁) l₂ := by
  intro l₁
  induction l₁ with
  | nil => intro l₂ s; rfl
  | cons t ts ih => intro l₂ s; simp [go, ih]

/-- `go` is monotone in the running state. -/
theorem go_mono_state : ∀ (l : List Nat) (s s' : Nat), s ≤ s' → go s l ≤ go s' l := by
  intro l
  induction l with
  | nil => intro s s' h; exact h
  | cons t ts ih =>
    intro s s' h
    exact ih _ _ (by omega)

/-! ## Heaviness -/

/-- `Heavy i l` : the times `l = [tᵢ, t_{i+1}, …]` starting at index `i` all obey
`2 ^ (t_k) ≤ 3 ^ k`.  This is exactly the `RealizableBound` hypothesis. -/
def Heavy : Nat → List Nat → Prop
  | _, [] => True
  | i, t :: ts => 2 ^ t ≤ 3 ^ i ∧ Heavy (i + 1) ts

/-- The Beatty corner `[fexp i, fexp (i+1), …, fexp (i+n−1)]`, built by snoc so
that it matches the `Bcap` recursion. -/
def corner : Nat → List Nat
  | 0 => []
  | a + 1 => corner a ++ [fexp a]

theorem corner_length : ∀ a : Nat, (corner a).length = a := by
  intro a
  induction a with
  | zero => rfl
  | succ a ih => simp [corner, ih]

/-- **The corner attains `Bcap` exactly.** -/
theorem corner_acc : ∀ a : Nat, acc (corner a) = Bcap a := by
  intro a
  induction a with
  | zero => rfl
  | succ a ih =>
    show go 0 (corner a ++ [fexp a]) = Bcap (a + 1)
    rw [go_append]
    show go (acc (corner a)) [fexp a] = Bcap (a + 1)
    rw [ih, Bcap_succ]
    rfl

/-- The corner's letters are heavy at their own indices, stated directly. -/
theorem corner_letters_heavy (i : Nat) : 2 ^ fexp i ≤ 3 ^ i := fexp_le i

/-- The corner is strictly increasing: `fexp` gains one or two at every step, so
the times are a legal (strictly increasing) odd-step schedule. -/
theorem corner_strict_mono (i : Nat) : fexp i < fexp (i + 1) := by
  have h1 := fexp_le i
  have h2 := lt_fexp (i + 1)
  have h3 := fexp_le (i + 1)
  have hlt : (3:Nat) ^ i < 3 ^ (i + 1) := by
    have hstep : (3:Nat) ^ (i + 1) = 3 * 3 ^ i := Arith.three_pow_succ i
    have hp : (0:Nat) < 3 ^ i := Arith.three_pow_pos i
    omega
  rcases Nat.lt_or_ge (fexp i) (fexp (i + 1)) with h | h
  · exact h
  · exfalso
    have := Arith.two_pow_le_two_pow h
    omega

/-! ## The upper bound: no heavy word beats the corner -/

/-- Every heavy word of length `a` starting at index `i` has accumulator at most
the corner's, run from the same state.  Induction on the word. -/
theorem go_le_corner : ∀ (l : List Nat) (i s s' : Nat), Heavy i l → s ≤ s' →
    go s l ≤ go s' (List.map fexp (List.range' i l.length)) := by
  intro l
  induction l with
  | nil => intro i s s' _ hs; exact hs
  | cons t ts ih =>
    intro i s s' hH hs
    obtain ⟨ht, hts⟩ := hH
    have hle : 2 ^ t ≤ 2 ^ fexp i := by
      have hmax : t ≤ fexp i := le_fexp_of_pow_le ht
      exact Arith.two_pow_le_two_pow hmax
    have : (List.range' i (t :: ts).length) = i :: List.range' (i + 1) ts.length := by
      simp [List.range'_succ]
    rw [this]
    show go (3 * s + 2 ^ t) ts ≤ go (3 * s' + 2 ^ fexp i) (List.map fexp (List.range' (i + 1) ts.length))
    exact ih (i + 1) _ _ hts (by omega)


/-- The snoc-built corner is the Beatty prefix `map fexp [0, …, a−1]`. -/
theorem corner_eq_map : ∀ a : Nat, corner a = List.map fexp (List.range' 0 a) := by
  intro a
  induction a with
  | zero => rfl
  | succ a ih =>
    show corner a ++ [fexp a] = List.map fexp (List.range' 0 (a + 1))
    rw [List.range'_concat, List.map_append, ih]
    have h0 : 0 + 1 * a = a := by omega
    rw [h0, List.map_cons, List.map_nil]

/-- **No heavy word beats the corner.**  `acc l ≤ Bcap a` for every heavy word
of length `a` — the upper half of sharpness. -/
theorem acc_le_Bcap {l : List Nat} (h : Heavy 0 l) : acc l ≤ Bcap l.length := by
  have := go_le_corner l 0 0 0 h (Nat.le_refl 0)
  rw [← corner_eq_map] at this
  have hc : go 0 (corner l.length) = Bcap l.length := corner_acc l.length
  exact hc ▸ this

/-- **Two-sided sharpness.**  `Bcap a` is exactly the maximum of `C` over heavy
words of length `a`: attained by `corner a`, and never exceeded. -/
theorem Bcap_is_max (a : Nat) :
    acc (corner a) = Bcap a ∧ ∀ l : List Nat, Heavy 0 l → l.length = a → acc l ≤ Bcap a :=
  ⟨corner_acc a, fun _ h hlen => hlen ▸ acc_le_Bcap h⟩

/-! ## Minimum phase

`x_j ≥ x₀` at the prefix just before the `(i+1)`-st odd step, with the cycle's
forced start `x₀ = C / G`, is

`(2 ^ (tᵢ) − 3 ^ i) · C ≤ G · C⁽ⁱ⁾`,

written here in `Nat` without truncated subtraction. -/

/-- The minimum-phase inequality at one prefix, in `Nat`-safe form. -/
@[reducible] def MinPhaseAt (t i C G Ci : Nat) : Prop := 2 ^ t * C ≤ 3 ^ i * C + G * Ci

/-- **Minimum phase is free on heavy words.**  If the prefix is heavy then the
inequality holds with the whole `G · C⁽ⁱ⁾` term to spare. -/
theorem minPhase_of_heavy {t i C G Ci : Nat} (h : 2 ^ t ≤ 3 ^ i) :
    MinPhaseAt t i C G Ci := by
  have : 2 ^ t * C ≤ 3 ^ i * C := Nat.mul_le_mul_right C h
  exact Nat.le_trans this (Nat.le_add_right _ _)

/-- **And it holds strictly at every proper prefix.**  Section XXXII asked
whether strictness buys anything past the non-strict form; it does not, because
heaviness already gives the strict inequality whenever `G · C⁽ⁱ⁾ > 0`, which is
every proper prefix of a cycle word (`i ≥ 1` makes `C⁽ⁱ⁾ > 0`, and `G > 0`). -/
theorem minPhase_strict_of_heavy {t i C G Ci : Nat} (h : 2 ^ t ≤ 3 ^ i)
    (hG : 0 < G) (hCi : 0 < Ci) : 2 ^ t * C < 3 ^ i * C + G * Ci := by
  have h1 : 2 ^ t * C ≤ 3 ^ i * C := Nat.mul_le_mul_right C h
  have h2 : 0 < G * Ci := Nat.mul_pos hG hCi
  omega

/-- The partial accumulator `C⁽ⁱ⁾` is positive as soon as one odd step has
happened, so the strict form applies at every proper prefix. -/
theorem go_pos : ∀ (l : List Nat) (t s : Nat), 0 < go s (t :: l) := by
  intro l
  induction l with
  | nil =>
    intro t s
    show 0 < 3 * s + 2 ^ t
    have := Arith.two_pow_pos t
    omega
  | cons u us ih =>
    intro t s
    exact ih u (3 * s + 2 ^ t)


/-! ## Minimum phase alone is strictly weaker, so it cannot replace heaviness

The converse of `minPhase_of_heavy` is false, and quantitatively so: at `a = 6`,
`L = 10` the word `t = (0,1,3,5,6,8)` satisfies every minimum-phase inequality
against its own forced start `x₀ = C/G` (`G = 2 ^ 10 − 3 ^ 6 = 295`) yet is
**not** heavy — `2 ^ 8 = 256 > 243 = 3 ^ 5` — and its accumulator `1357`
overshoots `Bcap 6 = 1085` by 25 %.  So the minimum interval is a *weaker*
constraint than the one `RealizableBound` already uses; substituting it would
lose ground, and adjoining it gains none. -/

/-- The witness word, as its ordered odd-step times. -/
def witness : List Nat := [0, 1, 3, 5, 6, 8]

theorem witness_acc : acc witness = 1357 := by decide

theorem witness_beats_Bcap : Bcap 6 < acc witness := by decide

theorem witness_not_heavy : ¬ (2 ^ (8:Nat) ≤ 3 ^ (5:Nat)) := by decide

/-- Every minimum-phase inequality holds for the witness at `G = 295`,
`C = 1357`, with the partial accumulators `C⁽ⁱ⁾ = 1, 5, 23, 101, 397`. -/
theorem witness_minPhase :
    MinPhaseAt 1 1 1357 295 1 ∧ MinPhaseAt 3 2 1357 295 5 ∧
    MinPhaseAt 5 3 1357 295 23 ∧ MinPhaseAt 6 4 1357 295 101 ∧
    MinPhaseAt 8 5 1357 295 397 := by
  refine ⟨?_, ?_, ?_, ?_, ?_⟩ <;> decide

/-! ## The conclusion of the section -/

/-- **`Bcap` is sharp, and minimum phase does not move it.**

The corner word is heavy, so by `minPhase_of_heavy` it satisfies every
minimum-phase inequality (strictly, by `minPhase_strict_of_heavy`), and by
`corner_acc` its accumulator is `Bcap a` on the nose.  Therefore the maximum of
`C` over heavy words *and* over heavy minimum-phase words is the same number,
`Bcap a`: adding the minimum interval to the certificate reduces the bound by
exactly zero. -/
theorem sharp_under_minPhase (a : Nat) :
    acc (corner a) = Bcap a ∧
      (∀ i : Nat, 2 ^ (fexp i) ≤ 3 ^ i) ∧
      (∀ i C G Ci : Nat, MinPhaseAt (fexp i) i C G Ci) := by
  refine ⟨corner_acc a, fexp_le, ?_⟩
  intro i C G Ci
  exact minPhase_of_heavy (fexp_le i)

end MinimumInterval
end Collatz

/-! ## Axiom audit -/
section Audit
open Collatz.MinimumInterval
-- #print axioms Bcap_is_max
-- #print axioms minPhase_of_heavy
-- #print axioms minPhase_strict_of_heavy
end Audit
