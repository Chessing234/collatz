import Collatz.Strategy.BcapSharp

/-!
# The cyclic gap vector, the slack coordinate, and the depth of the cut

A cycle word of length `L` with `a` odd steps is a **cyclic composition**: the
gaps `g 0, …, g (a−1)`, where `g i` is the number of even steps between odd step
`i` and odd step `i+1`, with `Σ g i = L − a`.  The odd-step times are
`t 0 = 0`, `t (i+1) = t i + 1 + g i` (`gapT`), and the accumulator is
`C = Σ_{i<a} 3 ^ (a−1−i) · 2 ^ (t i)` (`gapC`, written by its recursion).

## 1.  The extremal gap profile (`gapT_beatty`, `gapC_eq_Bcap`)

Write `s i = i · log₂ 3 − t i` for the **slack**.  Then

    C = 3 ^ (a−1) · Σ_{i<a} 2 ^ (−s i),      s (i+1) − s i = log₂ 3 − 1 − g i,

so maximising `C` is *pointwise* minimising the slacks; and since `s i ≡ i log₂ 3`
mod `1` while heaviness forces `s i ≥ 0`, the pointwise minimum is
`s i = {i log₂ 3}`, i.e. `t i = ⌊i log₂ 3⌋ = fexp i`.  The optimisation is
**separable**: there is no majorisation or Schur-convexity content, because the
constraint set is a product of shifted lattices `s i ∈ {i log₂ 3} + ℕ` and not a
simplex.  The extremiser is therefore optimal for *every* increasing separable
objective simultaneously, and it is unique.

In gap coordinates the profile is `g i = fexp (i+1) − fexp i − 1 ∈ {0,1}`
(`beattyGap`, `beattyGap_le_one`) — the Sturmian/Beatty word of slope
`log₂ 3 − 1`.  This file proves that profile attains `Bcap` (`gapC_eq_Bcap`) and
that nothing else exceeds it (`gapC_le_Bcap`).

## 2.  The `O0 E^m O0` ban is *not* a gap inequality

`Octave.highPos_halve` says an even step preserves `HighPos` exactly, and
`Octave.highPos_odd_escapes` says `HighPos` forbids an octave-preserving odd
step.  So the letter (`O0` / `O1`) carried by odd step `i` is a function of the
normalised position `r`, which even steps leave *unchanged*.  The decoration is
therefore a function of the odd-step **index** alone; it does not see the gaps.
Ban and gap vector are variation-independent, coupled only through the single
scalar identity `#O1 = Σ g i = L − a` (octave balance around a cycle).

All the ban can say is therefore a statement about the letter sequence, and
`ban_zeros_le` extracts the whole of it: no two `O0` adjacent gives
`2 · #O0 ≤ a + 1`, and with `#O0 = 2a − L` that is `3a ≤ 2L + 1`
(`ban_length`) — the `a/L ≤ 2/3` already on record, weaker than the criterion's
`0.63093`.  **The constrained maximum equals the unconstrained one.**

## 3.  What is left: the ladder is infinite

`Bcap` is attained (`gapC_beatty`) and, by the parallel desk's `BcapSharp.sharp`,
attained along a plateau of `2 ^ Θ(a)` heavy words.  So an improvement must
*forbid* words, and `Bcap_pinned` prices the ceiling exactly:
`Bcap a ∈ (a·3^(a−1)/2, a·3^(a−1)]`.

The reason no constant factor suffices is arithmetic, not combinatorial.  With
`ε = 1 − 3 ^ a / 2 ^ L` at a ledge, `Bcap / (2^L − 3^a) = 0.24045 · a · (1−ε)/ε`,
and `ε` returns to `0` along the convergents of `log₂ 3` (`a` steps by `665`,
`L` by `1054`).  Exactly `14704` ledges with `a ≤ 300000` have
`Bcap/G > 1086464`, and the factor by which the ceiling must be beaten to clear
them tends to `0`.  Any bound of the shape `C ≤ K · a · 3 ^ (a−1)` therefore
clears only finitely many ledges, whatever `K`.  The ceiling route is a ladder by
construction.

**Audit note (Round XIII adversary).**  `CD S` is defined as an accumulator, but the
lowered word is never shown strictly increasing or heavy in this file; if `S` fires at a
one-jump index of `fexp` the word is illegal and `cut_depth`'s prose reading fails.  The
legality proofs are `BcapSharp.Adm` / `tSub_strictInc` / `tSub_heavy`.  The conclusion
is unaffected: `cut_depth` is `BcapSharp.sharp` reached independently.
-/

namespace Collatz
namespace GapVector

open RealizableBound

/-! ## The `fexp` jump is one or two -/

/-- `⌊(i+1) log₂ 3⌋ − ⌊i log₂ 3⌋ ∈ {1, 2}`. -/
theorem fexp_step (i : Nat) : fexp i + 1 ≤ fexp (i + 1) ∧ fexp (i + 1) ≤ fexp i + 2 := by
  have h : fexp (i + 1) = fexp i + (if 2 ^ (fexp i + 2) ≤ 3 ^ (i + 1) then 2 else 1) := rfl
  by_cases hc : 2 ^ (fexp i + 2) ≤ 3 ^ (i + 1)
  · rw [h, if_pos hc]; omega
  · rw [h, if_neg hc]; omega

/-! ## The gap vector -/

/-- Odd-step times from the gap vector: `t 0 = 0`, `t (i+1) = t i + 1 + g i`. -/
def gapT (g : Nat → Nat) : Nat → Nat
  | 0 => 0
  | i + 1 => gapT g i + 1 + g i

/-- The accumulator of a gap vector: `C = Σ_{i<a} 3 ^ (a−1−i) · 2 ^ (t i)`. -/
def gapC (g : Nat → Nat) : Nat → Nat
  | 0 => 0
  | a + 1 => 3 * gapC g a + 2 ^ gapT g a

theorem gapT_succ (g : Nat → Nat) (i : Nat) : gapT g (i + 1) = gapT g i + 1 + g i := rfl

theorem gapC_succ (g : Nat → Nat) (a : Nat) : gapC g (a + 1) = 3 * gapC g a + 2 ^ gapT g a := rfl

/-- **The box bound in gap coordinates.**  Any gap vector whose odd-step times
stay under the Beatty line has accumulator at most `Bcap`. -/
theorem gapC_le_Bcap (g : Nat → Nat) :
    ∀ a : Nat, (∀ i, i < a → gapT g i ≤ fexp i) → gapC g a ≤ Bcap a := by
  intro a
  induction a with
  | zero => intro _; exact Nat.le_refl 0
  | succ a ih =>
    intro h
    have h1 : gapC g a ≤ Bcap a := ih (fun i hi => h i (Nat.lt_succ_of_lt hi))
    have h2 : (2:Nat) ^ gapT g a ≤ 2 ^ fexp a :=
      Arith.two_pow_le_two_pow (h a (Nat.lt_succ_self a))
    rw [gapC_succ, Bcap_succ]
    omega

/-- Equality when the times *are* the Beatty line. -/
theorem gapC_eq_Bcap (g : Nat → Nat) :
    ∀ a : Nat, (∀ i, i < a → gapT g i = fexp i) → gapC g a = Bcap a := by
  intro a
  induction a with
  | zero => intro _; rfl
  | succ a ih =>
    intro h
    have h1 : gapC g a = Bcap a := ih (fun i hi => h i (Nat.lt_succ_of_lt hi))
    have h2 : gapT g a = fexp a := h a (Nat.lt_succ_self a)
    rw [gapC_succ, Bcap_succ, h1, h2]

/-! ## The extremal profile is the Beatty/Sturmian gap word -/

/-- The extremal gap profile: `g i = ⌊(i+1) log₂ 3⌋ − ⌊i log₂ 3⌋ − 1`. -/
def beattyGap (i : Nat) : Nat := fexp (i + 1) - fexp i - 1

/-- **Every gap of the extremiser is `0` or `1`** — a Sturmian word of slope
`log₂ 3 − 1`. -/
theorem beattyGap_le_one (i : Nat) : beattyGap i ≤ 1 := by
  have h := fexp_step i
  rw [beattyGap]
  omega

/-- The extremal profile realises the Beatty times. -/
theorem gapT_beatty : ∀ i : Nat, gapT beattyGap i = fexp i := by
  intro i
  induction i with
  | zero => rfl
  | succ i ih =>
    have h := fexp_step i
    rw [gapT_succ, ih, beattyGap]
    omega

/-- **The extremiser attains the ceiling.** -/
theorem gapC_beatty (a : Nat) : gapC beattyGap a = Bcap a :=
  gapC_eq_Bcap beattyGap a (fun i _ => gapT_beatty i)

/-! ## Two-sided size of `Bcap` -/

/-- `Bcap a ≤ a · 3 ^ (a−1)`, in the form `3 · Bcap a ≤ a · 3 ^ a`. -/
theorem three_Bcap_le : ∀ a : Nat, 3 * Bcap a ≤ a * 3 ^ a := by
  intro a
  induction a with
  | zero => decide
  | succ a ih =>
    have hP : (3:Nat) ^ (a + 1) = 3 * 3 ^ a := Arith.three_pow_succ a
    have h1 : 3 * (3 * Bcap a) ≤ 3 * (a * 3 ^ a) := Nat.mul_le_mul_left 3 ih
    have h2 : 3 * 2 ^ fexp a ≤ 3 * 3 ^ a := Nat.mul_le_mul_left 3 (fexp_le a)
    have hexp : 3 * Bcap (a + 1) = 3 * (3 * Bcap a) + 3 * 2 ^ fexp a := by
      rw [Bcap_succ, Nat.mul_add]
    have key : (a + 1) * 3 ^ (a + 1) = 3 * (a * 3 ^ a) + 3 * 3 ^ a := by
      rw [hP, Nat.add_mul, Nat.one_mul, Nat.mul_left_comm]
    omega

/-- **Two-sided pinning of the ceiling.**  With `BcapSharp.Bcap_lower`
(`a · 3 ^ a ≤ 6 · Bcap a`) this brackets `Bcap a / (a · 3 ^ (a−1))` in `(1/2, 1]`.
Its true limit is `∫₀¹ 2^(−θ) dθ = 1 / (2 ln 2) = 0.7213475…`, since
`Bcap a = 3 ^ (a−1) · Σ_{i<a} 2 ^ (−{i log₂ 3})` exactly and `{i log₂ 3}`
equidistributes. -/
theorem Bcap_pinned (a : Nat) : a * 3 ^ a ≤ 6 * Bcap a ∧ 6 * Bcap a ≤ 2 * (a * 3 ^ a) := by
  refine ⟨BcapSharp.Bcap_lower a, ?_⟩
  have h := three_Bcap_le a
  omega

/-! ## The `O0 E^m O0` ban, as the only inequality it is -/

/-- `#{i < a : o i = false}` — the number of `O0` letters among the first `a`
odd steps, `o i = true` meaning `O1`. -/
def zeros (o : Nat → Bool) : Nat → Nat
  | 0 => 0
  | a + 1 => zeros o a + (if o a then 0 else 1)

/-- The ban, carried as an induction with a look-back. -/
theorem ban_aux (o : Nat → Bool) (hban : ∀ i, o i = false → o (i + 1) = true) :
    ∀ a : Nat, 2 * zeros o (a + 1) ≤ a + 2 ∧ (o a = true → 2 * zeros o (a + 1) ≤ a + 1) := by
  intro a
  induction a with
  | zero =>
    have h0 : zeros o (0 + 1) = (if o 0 then 0 else 1) := by
      show zeros o 0 + (if o 0 then 0 else 1) = _
      have hz : zeros o 0 = 0 := rfl
      omega
    by_cases h : o 0 = true
    · rw [if_pos h] at h0
      exact ⟨by omega, fun _ => by omega⟩
    · rw [if_neg h] at h0
      exact ⟨by omega, fun hc => absurd hc h⟩
  | succ a ih =>
    obtain ⟨ih1, ih2⟩ := ih
    by_cases h : o (a + 1) = true
    · have hz : zeros o (a + 1 + 1) = zeros o (a + 1) := by
        show zeros o (a + 1) + (if o (a + 1) then 0 else 1) = _
        rw [if_pos h]; omega
      exact ⟨by omega, fun _ => by omega⟩
    · have hfalse : o (a + 1) = false := by
        cases hb : o (a + 1) with
        | false => rfl
        | true => exact absurd hb h
      have hz : zeros o (a + 1 + 1) = zeros o (a + 1) + 1 := by
        show zeros o (a + 1) + (if o (a + 1) then 0 else 1) = _
        rw [if_neg h]
      have hprev : o a = true := by
        cases hb : o a with
        | true => rfl
        | false =>
          have hc := hban a hb
          rw [hc] at hfalse
          exact absurd hfalse (by decide)
      have hh := ih2 hprev
      exact ⟨by omega, fun hc => absurd hc h⟩

/-- **The whole content of the ban:** no two `O0` adjacent forces
`2 · #O0 ≤ a + 1`. -/
theorem ban_zeros_le (o : Nat → Bool) (hban : ∀ i, o i = false → o (i + 1) = true)
    (a : Nat) : 2 * zeros o a ≤ a + 1 := by
  cases a with
  | zero =>
    have hz : zeros o 0 = 0 := rfl
    omega
  | succ a => exact (ban_aux o hban a).1

/-- With the cyclic octave balance `#O1 = L − a`, i.e. `#O0 = 2a − L`, the ban is
exactly `3a ≤ 2L + 1` — the recorded `a / L ≤ 2/3`, weaker than the criterion's
`0.63093`.  Nothing in it mentions the gap vector. -/
theorem ban_length {o : Nat → Bool} (hban : ∀ i, o i = false → o (i + 1) = true)
    {a L : Nat} (h : 2 * a = L + zeros o a) : 3 * a ≤ 2 * L + 1 := by
  have := ban_zeros_le o hban a
  omega

/-! ## Axiom audit -/

#print axioms fexp_step
#print axioms gapC_le_Bcap
#print axioms gapC_beatty
#print axioms beattyGap_le_one
#print axioms three_Bcap_le
#print axioms Bcap_pinned
#print axioms ban_zeros_le
#print axioms ban_length

end GapVector
end Collatz
