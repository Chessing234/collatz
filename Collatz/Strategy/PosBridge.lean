import Collatz.Strategy.HalbeisenHungerbuhler
import Collatz.Strategy.RealizableBound
import Collatz.Strategy.PriceIdentity
import Collatz.Strategy.HHMinTime

namespace Collatz
namespace PosBridge

open HalbeisenHungerbuhler PriceIdentity ExtremalTime

/-! ## Scanning for the `i`-th one-bit of the Beatty word `(l,n)`, window `l` -/

/-- Scan forward from `start` for `fuel` more steps, returning the first
position in `[start, start+fuel)` with `beattyBit l n = 1` (falling back to
`start` if none is found within the fuel). -/
def nextOne (l n : Nat) : Nat → Nat → Nat
  | start, 0 => start
  | start, fuel + 1 => if beattyBit l n start = 1 then start else nextOne l n (start + 1) fuel

theorem nextOne_spec (l n : Nat) : ∀ start fuel : Nat,
    beattyCount l n (start + fuel) > beattyCount l n start →
    start ≤ nextOne l n start fuel ∧ nextOne l n start fuel < start + fuel ∧
      beattyBit l n (nextOne l n start fuel) = 1 ∧
      beattyCount l n (nextOne l n start fuel) = beattyCount l n start := by
  intro start fuel
  induction fuel generalizing start with
  | zero =>
    intro h
    simp only [Nat.add_zero] at h
    omega
  | succ fuel ih =>
    intro h
    show (start ≤ (if beattyBit l n start = 1 then start else nextOne l n (start + 1) fuel) ∧
          (if beattyBit l n start = 1 then start else nextOne l n (start + 1) fuel) < start + (fuel + 1) ∧
          beattyBit l n (if beattyBit l n start = 1 then start else nextOne l n (start + 1) fuel) = 1 ∧
          beattyCount l n (if beattyBit l n start = 1 then start else nextOne l n (start + 1) fuel)
            = beattyCount l n start)
    by_cases hb : beattyBit l n start = 1
    · rw [if_pos hb]
      exact ⟨Nat.le_refl start, by omega, hb, rfl⟩
    · rw [if_neg hb]
      have hble := beattyBit_le_one l n start
      have hstep : beattyCount l n (start + 1) = beattyCount l n start := by
        show beattyBit l n start + beattyCount l n start = beattyCount l n start
        omega
      have hidx : start + 1 + fuel = start + (fuel + 1) := by omega
      have h' : beattyCount l n (start + 1 + fuel) > beattyCount l n (start + 1) := by
        rw [hidx, hstep]; exact h
      obtain ⟨h1, h2, h3, h4⟩ := ih (start + 1) h'
      refine ⟨by omega, by omega, h3, ?_⟩
      rw [h4, hstep]

/-- **`pos l n i`, the position of the `i`-th one-bit (0-indexed) of the Beatty
word `(l, n)`.**  Each stage restarts the scan just past the previous one-bit,
with fuel trimmed down to the fixed horizon `l`. -/
def pos (l n : Nat) : Nat → Nat
  | 0 => nextOne l n 0 l
  | j + 1 => nextOne l n (pos l n j + 1) (l - (pos l n j + 1))

/-- For `i < beattyCount l n l`, `pos l n i` lies inside `[0, l)`, its bit is
`1`, and the running weight up to it is exactly `i`. -/
theorem pos_spec (l n : Nat) : ∀ i, i < beattyCount l n l →
    pos l n i < l ∧ beattyBit l n (pos l n i) = 1 ∧ beattyCount l n (pos l n i) = i := by
  intro i
  induction i with
  | zero =>
    intro h
    have h0 : beattyCount l n 0 = 0 := rfl
    have hwin : beattyCount l n (0 + l) > beattyCount l n 0 := by
      rw [h0]; simpa using h
    have hunfold : pos l n 0 = nextOne l n 0 l := rfl
    rw [hunfold]
    obtain ⟨_, h2, h3, h4⟩ := nextOne_spec l n 0 l hwin
    refine ⟨by simpa using h2, h3, ?_⟩
    rw [h4, h0]
  | succ j ih =>
    intro h
    have hjlt : j < beattyCount l n l := by omega
    obtain ⟨hlt, hone, hcnt⟩ := ih hjlt
    have hsle : pos l n j + 1 ≤ l := by omega
    have hstep : beattyCount l n (pos l n j + 1)
        = beattyBit l n (pos l n j) + beattyCount l n (pos l n j) := rfl
    have hwin : beattyCount l n (pos l n j + 1 + (l - (pos l n j + 1)))
        > beattyCount l n (pos l n j + 1) := by
      have hLs : pos l n j + 1 + (l - (pos l n j + 1)) = l := by omega
      rw [hLs, hstep, hone, hcnt]
      omega
    show pos l n (j + 1) < l ∧ beattyBit l n (pos l n (j + 1)) = 1
        ∧ beattyCount l n (pos l n (j + 1)) = j + 1
    have hunfold : pos l n (j + 1) = nextOne l n (pos l n j + 1) (l - (pos l n j + 1)) := rfl
    rw [hunfold]
    obtain ⟨h1, h2, h3, h4⟩ := nextOne_spec l n (pos l n j + 1) (l - (pos l n j + 1)) hwin
    refine ⟨by omega, h3, ?_⟩
    rw [h4, hstep, hone, hcnt]
    omega

/-- **Injectivity of `beattyCount` restricted to one-positions.**  Two
one-positions carrying the same running weight are the same position: if
`j < j'` were both bit-`1`, monotonicity would force
`beattyCount l n j' ≥ beattyCount l n (j+1) = 1 + beattyCount l n j`, contradicting
equality. -/
theorem beattyBit_pos_inj {l n j j' : Nat}
    (hj : beattyBit l n j = 1) (hj' : beattyBit l n j' = 1)
    (heq : beattyCount l n j = beattyCount l n j') : j = j' := by
  have hstepj : beattyCount l n (j + 1) = beattyBit l n j + beattyCount l n j := rfl
  have hstepj' : beattyCount l n (j' + 1) = beattyBit l n j' + beattyCount l n j' := rfl
  rcases Nat.lt_trichotomy j j' with hlt | heqjj | hgt
  · exfalso
    have hmono := ExtremalTime.beattyCount_mono l n (j + 1) j' (by omega)
    omega
  · exact heqjj
  · exfalso
    have hmono := ExtremalTime.beattyCount_mono l n (j' + 1) j (by omega)
    omega

/-- **The reindexing identity, prefix form.**  The `hhMin` fold over positions
`< j` equals `Bsum` of the `pos`-exponents consumed so far (`beattyCount l n j`
many of them), corrected by the `3`-power owed to the ones not yet reached.
Compare `ExtremalTime.hhMin_eq_hhMinTime_prefix`, whose induction this copies —
the only change is that the `2`-power at a one-position is `2 ^ (pos l n i)`
with `pos l n i = j` supplied by `beattyBit_pos_inj` in place of the closed-form
`tildeTime_of_bit`. -/
theorem hhMin_eq_Bsum_pos_prefix {l n : Nat} (hl : 0 < l) (hnl : n ≤ l) :
    ∀ j, j ≤ l →
      hhMin l n j = 3 ^ (n - beattyCount l n j) * PriceIdentity.Bsum (pos l n) (beattyCount l n j) := by
  intro j
  induction j with
  | zero =>
    intro _
    show (0 : Nat) = 3 ^ (n - 0) * PriceIdentity.Bsum (pos l n) 0
    simp [PriceIdentity.Bsum]
  | succ j ih =>
    intro hjl
    have hjl' : j ≤ l := by omega
    have ihj := ih hjl'
    rcases Nat.eq_zero_or_pos (beattyBit l n j) with hb0 | hb1
    · have hcnt_eq : beattyCount l n (j + 1) = beattyCount l n j := by
        show beattyBit l n j + beattyCount l n j = beattyCount l n j
        omega
      show beattyBit l n j * 2 ^ j * 3 ^ (n - beattyCount l n (j + 1)) + hhMin l n j
          = 3 ^ (n - beattyCount l n (j + 1)) * PriceIdentity.Bsum (pos l n) (beattyCount l n (j + 1))
      rw [hcnt_eq, hb0]
      simpa using ihj
    · have hbb := beattyBit_le_one l n j
      have hb1' : beattyBit l n j = 1 := by omega
      have hcnt_eq : beattyCount l n (j + 1) = beattyCount l n j + 1 := by
        show beattyBit l n j + beattyCount l n j = beattyCount l n j + 1
        omega
      have hcnt_lt : beattyCount l n j < n := by
        have hmono := ExtremalTime.beattyCount_le_n hl hnl (j + 1) hjl
        omega
      have hnval : beattyCount l n l = n := beatty_count_eq hl hnl
      have hi_lt : beattyCount l n j < beattyCount l n l := by rw [hnval]; exact hcnt_lt
      obtain ⟨_, hposbit, hposcnt⟩ := pos_spec l n (beattyCount l n j) hi_lt
      have hposeq : pos l n (beattyCount l n j) = j :=
        beattyBit_pos_inj hposbit hb1' hposcnt
      have hnew : PriceIdentity.Bsum (pos l n) (beattyCount l n j + 1)
          = 3 * PriceIdentity.Bsum (pos l n) (beattyCount l n j) + 2 ^ j := by
        show 3 * PriceIdentity.Bsum (pos l n) (beattyCount l n j)
              + 2 ^ (pos l n (beattyCount l n j)) = _
        rw [hposeq]
      show beattyBit l n j * 2 ^ j * 3 ^ (n - beattyCount l n (j + 1)) + hhMin l n j
          = 3 ^ (n - beattyCount l n (j + 1)) * PriceIdentity.Bsum (pos l n) (beattyCount l n (j + 1))
      rw [hb1', hcnt_eq, hnew, Nat.one_mul, ihj]
      have e1 : (3 : Nat) ^ (n - beattyCount l n j)
          = 3 ^ (n - (beattyCount l n j + 1)) * 3 := by
        have hexp : n - beattyCount l n j = (n - (beattyCount l n j + 1)) + 1 := by omega
        rw [hexp, Nat.pow_succ]
      rw [e1]
      generalize (3 : Nat) ^ (n - (beattyCount l n j + 1)) = P
      generalize PriceIdentity.Bsum (pos l n) (beattyCount l n j) = T
      generalize (2 : Nat) ^ j = Q
      calc Q * P + P * 3 * T
          = P * Q + P * 3 * T := by rw [Nat.mul_comm Q P]
        _ = P * 3 * T + P * Q := by rw [Nat.add_comm]
        _ = P * (3 * T) + P * Q := by rw [Nat.mul_assoc]
        _ = P * (3 * T + Q) := by rw [← Nat.mul_add]

/-- **The bridge.**  `hhMin l n l` — Halbeisen–Hungerbühler's `M_{l,n}` — equals
`Bsum` of the Beatty word's own one-positions.  The reindexing that
`PriceIdentity` needed as an unproved hypothesis. -/
theorem hhMin_eq_Bsum_pos {l n : Nat} (hl : 0 < l) (hnl : n ≤ l) :
    hhMin l n l = PriceIdentity.Bsum (pos l n) n := by
  have h := hhMin_eq_Bsum_pos_prefix hl hnl l (Nat.le_refl l)
  have hc := beatty_count_eq hl hnl
  rw [hc] at h
  simpa using h

/-! ## Specialising to `l = fexp a + 1`, `n = a` -/

theorem two_pow_le_three_pow : ∀ a : Nat, 2 ^ a ≤ 3 ^ a := by
  intro a
  induction a with
  | zero => simp
  | succ a ih =>
    have h2 : (2:Nat) ^ (a + 1) = 2 * 2 ^ a := by rw [Nat.pow_succ, Nat.mul_comm]
    have h3 : (3:Nat) ^ (a + 1) = 3 * 3 ^ a := by rw [Nat.pow_succ, Nat.mul_comm]
    rw [h2, h3]
    have hstep : 2 * 2 ^ a ≤ 2 * 3 ^ a := Nat.mul_le_mul_left 2 ih
    have h33 : 2 * 3 ^ a ≤ 3 * 3 ^ a := Nat.mul_le_mul_right (3 ^ a) (by omega)
    omega

theorem a_le_fexp (a : Nat) : a ≤ RealizableBound.fexp a :=
  RealizableBound.le_fexp_of_pow_le (two_pow_le_three_pow a)

/-- **The missing bridge, specialised.**  With `L = fexp a + 1`,
`hhMin L a L = Bsum pos a` where `pos` is the position function of the
ceiling-Beatty word of shape `(L, a)`. -/
theorem hhMin_eq_Bsum_pos_fexp (a : Nat) :
    hhMin (RealizableBound.fexp a + 1) a (RealizableBound.fexp a + 1)
      = PriceIdentity.Bsum (pos (RealizableBound.fexp a + 1) a) a := by
  have hl : 0 < RealizableBound.fexp a + 1 := by omega
  have hnl : a ≤ RealizableBound.fexp a + 1 := by have := a_le_fexp a; omega
  exact hhMin_eq_Bsum_pos hl hnl

/-! ## The capstone: the two certificates are one integer

`PriceIdentity.numerators_agree` supplies the other half, `Bsum pos a = Bcap a`, under
the hypothesis that the two exponent sequences agree below `a`.  Chaining gives the
identity that three rounds of this development met as an unexplained numerical
coincidence — the Halbeisen–Hungerbühler minimum over admissible words and the
`Bcap` realizable-frontier bound are **the same integer**.
-/

/-- **`hhMin = Bcap`.**  Both certificates are `Σ_{i<a} 3^(a−1−i)·2^(e i)`; they
coincide exactly when their exponent sequences do.  This is now a theorem, not a
measurement: the numerical agreement to `2053` digits at `a = 306, 971, 1636, 2301,
2966, 3631, 4296` is the hypothesis `hpos` holding there, and the failures at
`a = 2, 12, 53, 665` are `hpos` failing.  **The whole coincidence has been reduced
to the single arithmetic condition `pos i = fexp i`** — the `i`-th one-position of
the ceiling-Beatty word equalling the `i`-th frontier exponent. -/
theorem hhMin_eq_Bcap (a : Nat)
    (hpos : ∀ i : Nat, i < a → pos (RealizableBound.fexp a + 1) a i = RealizableBound.fexp i) :
    hhMin (RealizableBound.fexp a + 1) a (RealizableBound.fexp a + 1)
      = RealizableBound.Bcap a := by
  rw [hhMin_eq_Bsum_pos_fexp a]
  exact PriceIdentity.numerators_agree a hpos

end PosBridge
end Collatz
