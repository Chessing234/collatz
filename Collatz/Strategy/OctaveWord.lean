import Collatz.Accelerated

/-!
# The octave word: dyadic position retained across even steps

All statements here are about the **accelerated map** `T(x) = x/2` for even `x`,
`T(x) = (3x+1)/2` for odd `x` (`Collatz.acceleratedStep`).

Write `x = 2^k * r` with `1 <= r < 2`; `k` is the *octave* (dyadic scale) of `x`
and `r` its *normalized position* inside the octave.  Two predicates encode this
with integers only:

* `InOctave k x` : `2^k <= x < 2^(k+1)`, i.e. `x` has octave `k`;
* `HighPos k x`  : `3 * 2^k <= 2 * x`, i.e. `r >= 3/2` (top quarter of the octave).

The three results that matter.

1. **Octave alphabet.**  One step changes the octave by exactly `-1` (even step),
   `0` (odd step, `octave_step_zero`) or `+1` (odd step, `octave_step_one`).
   Nothing else occurs: `octave_alphabet`.
2. **Octave theorem.**  No orbit occupies one octave for three consecutive steps
   (`no_three_in_octave`), and a two-step sojourn forces `r < 4/3` at entry
   (`sojourn_low`) and `r >= 3/2` at exit (`sojourn_high`).
3. **Even steps are transparent to `r`.**  `HighPos` is preserved exactly by an
   even step (`highPos_halve`), and `HighPos` forbids an octave-preserving odd
   step (`highPos_odd_escapes`).  Chaining these gives `O0_forces_O1`: after an
   octave-preserving odd step, the *next odd step of the orbit* must raise the
   octave, no matter how many even steps intervene.  In the three-letter word
   this says the block `O0 E^m O0` is impossible for every `m`.
-/

namespace Collatz
namespace Octave

/-- `x` lies in the dyadic octave `[2^k, 2^(k+1))`. -/
def InOctave (k x : Nat) : Prop := 2 ^ k ≤ x ∧ x < 2 ^ (k + 1)

/-- `x` lies in the top quarter of its octave: `x / 2^k >= 3/2`. -/
def HighPos (k x : Nat) : Prop := 3 * 2 ^ k ≤ 2 * x

/-! ## Power bookkeeping (the common power is always kept as a variable) -/

theorem pow_succ_eq (k : Nat) : 2 ^ (k + 1) = 2 * 2 ^ k := by
  rw [Nat.pow_succ]; omega

theorem pow_two_eq (k : Nat) : 2 ^ (k + 2) = 4 * 2 ^ k := by
  rw [Nat.pow_succ, Nat.pow_succ]; omega

/-- `2^(p+1) * u = 2 * (2^p * u)`: keeps the product a single atom for `omega`. -/
theorem pow_mul_succ (p u : Nat) : 2 ^ (p + 1) * u = 2 * (2 ^ p * u) := by
  rw [pow_succ_eq, Nat.mul_assoc]

/-! ## Step normal forms -/

/-- An even step halves. -/
theorem step_even {x : Nat} (h : x % 2 = 0) : 2 * acceleratedStep x = x := by
  rw [acceleratedStep, if_pos h]; omega

/-- An odd step: `2 * T(x) = 3x + 1`. -/
theorem step_odd {x : Nat} (h : x % 2 = 1) : 2 * acceleratedStep x = 3 * x + 1 := by
  rw [acceleratedStep, if_neg (by omega)]; omega

/-! ## The octave alphabet -/

/-- **Even step: the octave drops by exactly one.** -/
theorem octave_even {k x : Nat} (hx : InOctave (k + 1) x) (h : x % 2 = 0) :
    InOctave k (acceleratedStep x) := by
  obtain ⟨h1, h2⟩ := hx
  have hs := step_even h
  have hp := pow_succ_eq k
  have hq := pow_succ_eq (k + 1)
  rw [show k + 1 + 1 = k + 2 by omega, pow_two_eq] at hq
  constructor <;> omega

/-- **Odd step: the octave rises by `0` or `1`, never more, never less.** -/
theorem octave_odd {k x : Nat} (hx : InOctave k x) (h : x % 2 = 1) :
    2 ^ k ≤ acceleratedStep x ∧ acceleratedStep x < 2 ^ (k + 2) := by
  obtain ⟨h1, h2⟩ := hx
  have hs := step_odd h
  have hp := pow_succ_eq k
  have hq := pow_two_eq k
  constructor <;> omega

/-- An odd step stays in the octave exactly when `3x + 1 < 2^(k+2)`, i.e. `r < 4/3`. -/
theorem octave_step_zero_iff {k x : Nat} (hx : InOctave k x) (h : x % 2 = 1) :
    (InOctave k (acceleratedStep x) ↔ 3 * x + 1 < 2 ^ (k + 2)) := by
  obtain ⟨h1, h2⟩ := hx
  have hs := step_odd h
  have hp := pow_succ_eq k
  have hq := pow_two_eq k
  constructor
  · intro hh; obtain ⟨_, hb⟩ := hh; omega
  · intro hh; exact ⟨by omega, by omega⟩

/-- The three letters are the only ones: for any `x` in octave `k`, the image lies
in octave `k-1`, `k` or `k+1`, and which one is pinned by the parity. -/
theorem octave_alphabet {k x : Nat} (hx : InOctave (k + 1) x) :
    (x % 2 = 0 ∧ InOctave k (acceleratedStep x)) ∨
    (x % 2 = 1 ∧ (InOctave (k + 1) (acceleratedStep x) ∨
       InOctave (k + 2) (acceleratedStep x))) := by
  rcases Nat.mod_two_eq_zero_or_one x with he | ho
  · exact Or.inl ⟨he, octave_even hx he⟩
  · refine Or.inr ⟨ho, ?_⟩
    obtain ⟨hlo, hhi⟩ := octave_odd hx ho
    rcases Nat.lt_or_ge (acceleratedStep x) (2 ^ (k + 2)) with hc | hc
    · exact Or.inl ⟨hlo, hc⟩
    · exact Or.inr ⟨hc, by rw [show k + 1 + 2 = k + 2 + 1 by omega] at hhi; exact hhi⟩

/-! ## The octave theorem and the two-step catalogue -/

/-- A two-step sojourn starts with an **odd** step. -/
theorem sojourn_odd {k x : Nat} (h0 : InOctave k x) (h1 : InOctave k (acceleratedStep x)) :
    x % 2 = 1 := by
  rcases Nat.mod_two_eq_zero_or_one x with he | ho
  · exfalso
    obtain ⟨ha, hb⟩ := h0
    obtain ⟨hc, _⟩ := h1
    have hs := step_even he
    have hp := pow_succ_eq k
    omega
  · exact ho

/-- **Entry constraint.**  A two-step sojourn forces `3x + 1 < 2^(k+2)`, i.e. the
entry point lies in the bottom third of the octave, `r < 4/3`. -/
theorem sojourn_low {k x : Nat} (h0 : InOctave k x) (h1 : InOctave k (acceleratedStep x)) :
    3 * x + 1 < 2 ^ (k + 2) :=
  (octave_step_zero_iff h0 (sojourn_odd h0 h1)).mp h1

/-- **Exit constraint.**  The second point of a two-step sojourn lies in the top
quarter of the octave, `r >= 3/2`. -/
theorem sojourn_high {k x : Nat} (h0 : InOctave k x) (h1 : InOctave k (acceleratedStep x)) :
    HighPos k (acceleratedStep x) := by
  have ho := sojourn_odd h0 h1
  have hs := step_odd ho
  obtain ⟨ha, _⟩ := h0
  unfold HighPos
  omega

/-- **A point in the top quarter cannot take an octave-preserving odd step.**
If `r >= 3/2` and `x` is odd then the octave strictly rises. -/
theorem highPos_odd_escapes {k x : Nat} (hh : HighPos k x) (h : x % 2 = 1) :
    2 ^ (k + 1) ≤ acceleratedStep x := by
  have hs := step_odd h
  have hp := pow_succ_eq k
  unfold HighPos at hh
  omega

/-- **The octave theorem.**  No three consecutive orbit points share an octave. -/
theorem no_three_in_octave {k x : Nat}
    (h0 : InOctave k x) (h1 : InOctave k (acceleratedStep x))
    (h2 : InOctave k (acceleratedStep (acceleratedStep x))) : False := by
  have hh := sojourn_high h0 h1
  have ho := sojourn_odd h1 h2
  have hesc := highPos_odd_escapes hh ho
  obtain ⟨_, hb⟩ := h2
  have hp := pow_succ_eq k
  omega

/-! ## Even steps are transparent to the normalized position -/

/-- **`HighPos` survives an even step exactly.**  This is the statement that the
normalized coordinate `r` is *unchanged* by halving. -/
theorem highPos_halve {k x : Nat} (hh : HighPos (k + 1) x) (h : x % 2 = 0) :
    HighPos k (acceleratedStep x) := by
  have hs := step_even h
  have hp := pow_succ_eq k
  unfold HighPos at hh ⊢
  omega

/-- Iterating `m` even steps out of `2^m * u`. -/
theorem orbit_pow_mul (m u : Nat) : acceleratedOrbit m (2 ^ m * u) = u := by
  induction m with
  | zero => simp
  | succ p ih =>
    have hstep : acceleratedStep (2 ^ (p + 1) * u) = 2 ^ p * u := by
      rw [pow_mul_succ]
      have hev : (2 * (2 ^ p * u)) % 2 = 0 := by omega
      have hs := step_even hev
      omega
    rw [acceleratedOrbit_succ, hstep, ih]

/-- `HighPos` propagates down a whole run of `m` even steps. -/
theorem highPos_run {m : Nat} : ∀ {j u : Nat},
    HighPos (j + m) (2 ^ m * u) → HighPos j u := by
  induction m with
  | zero => intro j u h; simpa using h
  | succ p ih =>
    intro j u h
    refine @ih j u ?_
    rw [pow_mul_succ] at h
    unfold HighPos at h ⊢
    have hq : 2 ^ (j + (p + 1)) = 2 * 2 ^ (j + p) := by
      rw [show j + (p + 1) = (j + p) + 1 by omega, pow_succ_eq]
    omega

/-- Likewise `InOctave` survives the run: the octave drops by exactly `m`. -/
theorem inOctave_run {m : Nat} : ∀ {j u : Nat},
    InOctave (j + m) (2 ^ m * u) → InOctave j u := by
  induction m with
  | zero => intro j u h; simpa using h
  | succ p ih =>
    intro j u h
    refine @ih j u ?_
    rw [pow_mul_succ] at h
    obtain ⟨ha, hb⟩ := h
    have hq : 2 ^ (j + (p + 1)) = 2 * 2 ^ (j + p) := by
      rw [show j + (p + 1) = (j + p) + 1 by omega, pow_succ_eq]
    have hr : 2 ^ (j + (p + 1) + 1) = 2 * 2 ^ (j + p + 1) := by
      rw [show j + (p + 1) + 1 = (j + p + 1) + 1 by omega, pow_succ_eq]
    exact ⟨by omega, by omega⟩

/-! ## The forbidden cyclic-word block `O0 E^m O0` -/

/-- **After an octave-preserving odd step, the next odd step of the orbit must
raise the octave** -- however many even steps sit in between.

`x` takes an odd step that stays inside octave `k` (the letter `O0`).  Its image
is written `2^m * u` with `u` odd, so the orbit next performs exactly `m` even
steps (letters `E`) and arrives at `u`, whose octave is `k - m = j`.  The
conclusion is that the odd step out of `u` leaves octave `j` upward: that letter
is `O1`.  Hence the block `O0 E^m O0` never occurs, for any `m`. -/
theorem O0_forces_O1 {j m x u : Nat}
    (h0 : InOctave (j + m) x) (h1 : InOctave (j + m) (acceleratedStep x))
    (hrep : acceleratedStep x = 2 ^ m * u) (hu : u % 2 = 1) :
    acceleratedOrbit m (acceleratedStep x) = u ∧ InOctave j u ∧
      2 ^ (j + 1) ≤ acceleratedStep u := by
  have hh : HighPos (j + m) (2 ^ m * u) := by
    have := sojourn_high h0 h1; rw [hrep] at this; exact this
  have hin : InOctave (j + m) (2 ^ m * u) := by rw [hrep] at h1; exact h1
  refine ⟨by rw [hrep]; exact orbit_pow_mul m u, inOctave_run hin, ?_⟩
  exact highPos_odd_escapes (highPos_run hh) hu

/-- Contrapositive form: the block `O0 E^m O0` is impossible. -/
theorem no_O0_after_O0 {j m x u : Nat}
    (h0 : InOctave (j + m) x) (h1 : InOctave (j + m) (acceleratedStep x))
    (hrep : acceleratedStep x = 2 ^ m * u) (hu : u % 2 = 1)
    (hbad : InOctave j (acceleratedStep u)) : False := by
  obtain ⟨-, -, hesc⟩ := O0_forces_O1 h0 h1 hrep hu
  obtain ⟨-, hb⟩ := hbad
  omega

/-! ## Sharpness: both two-step sojourns occur -/

/-- `17 -> 26` is a two-step sojourn in octave `4 = [16,32)` whose second step is
**even**, so the orbit leaves downward (`26 -> 13`, octave `3`). -/
theorem sharp_even_exit :
    InOctave 4 17 ∧ InOctave 4 (acceleratedStep 17) ∧
      InOctave 3 (acceleratedStep (acceleratedStep 17)) := by
  refine ⟨⟨by decide, by decide⟩, ⟨by decide, by decide⟩, ⟨by decide, by decide⟩⟩

/-- `19 -> 29` is a two-step sojourn in octave `4` whose second step is **odd**,
so the orbit leaves upward (`29 -> 44`, octave `5`). -/
theorem sharp_odd_exit :
    InOctave 4 19 ∧ InOctave 4 (acceleratedStep 19) ∧
      InOctave 5 (acceleratedStep (acceleratedStep 19)) := by
  refine ⟨⟨by decide, by decide⟩, ⟨by decide, by decide⟩, ⟨by decide, by decide⟩⟩

/-- The entry bound `r < 4/3` is attained tightly: `19` has `3*19+1 = 58 < 64`. -/
theorem sharp_entry_bound : 3 * 19 + 1 < 2 ^ (4 + 2) := by decide

/-! ## Axiom audit -/

#print axioms octave_even
#print axioms octave_odd
#print axioms octave_alphabet
#print axioms sojourn_low
#print axioms sojourn_high
#print axioms no_three_in_octave
#print axioms highPos_halve
#print axioms highPos_run
#print axioms inOctave_run
#print axioms O0_forces_O1
#print axioms no_O0_after_O0
#print axioms sharp_even_exit
#print axioms sharp_odd_exit

end Octave
end Collatz
