import Collatz.Strategy.HighPart
import Collatz.Strategy.ScaleRecord

/-!
# The dyadic corona — real size selects a 2-adic window

The hybrid state is

    S(n) = ( |n| , n mod 2^{κ(n)} )     κ(n) := ⌊log₂ n⌋

The scale is **not a frozen modulus**.  It is the unique 2-adic precision at
which the archimedean annulus `[2^κ, 2^{κ+1})` forces the high part to be the
unit `1`.  The residue `n mod 2^{κ(n)}` is then the entire remaining 2-adic
datum: the dyadic mantissa.

This is not a residue-class list (different `n` carry different moduli) and it
is not a translate clock `v₂(an+b)`.

The two arrows the brief asked for, in this coordinate:

1. **Real expansion localises.**  Non-drop through the corona window rewrites
   as `3^a + T^κ(mantissa) ≥ 2^κ + mantissa`.  The left odd-count `a` is a
   function of the mantissa alone, so a real lower bound forces a 2-adic
   lower bound on the odd-density of that window.
2. **Strong localisation contracts.**  If the window is *strongly light*
   (`2 · 3^a ≤ 2^κ`), the same identity forces `T^κ(n) < n`
   (`light_corona_drops`).  The factor `2` is exact: it is `affineC_lt`
   matching the corona lower bound `n ≥ 2^κ`.

`expStep` fails the drop: at the same dynamic window its orbit is strictly
larger (`expStep_fails_corona_drop`).  It also never meets the strong-light
hypothesis, because it saturates `a = j` (`saturated_not_strongly_light`).

The theorem does not claim Collatz.  Heavy coronas (Mersenne-like mantissas)
expand, and the second arrow for those windows is the open decisive lemma
recorded in `Devices/HybridGeometry.md`.
-/

namespace Collatz
namespace DeviceHybrid

open AffineExact HighPart ScaleRecord

/-- **Dynamic scale.**  The 2-adic precision selected by the real magnitude. -/
def coronaScale (n : Nat) : Nat := Nat.log2 n

/-- The 2-adic coordinate of the hybrid state: low bits at the corona scale. -/
def mantissa (n : Nat) : Nat := n % 2 ^ coronaScale n

/-- Midscale pinch window: half the corona, still a function of `|n|`. -/
def pinchScale (n : Nat) : Nat := Nat.log2 n / 2

/-- Strong lightness at a dynamic window: twice the 3-power still fits in the
2-adic scale.  This is the localisation that the pinch converts into a drop. -/
def StronglyLight (n k : Nat) : Prop :=
  2 * 3 ^ oddCount n k ≤ 2 ^ k

/-! ## 1.  The corona identity: high part is the unit -/

/-- `⌊log₂ n⌋ ≥ 1` as soon as `n ≥ 2`. -/
theorem one_le_coronaScale {n : Nat} (hn : 2 ≤ n) : 1 ≤ coronaScale n := by
  have hlt : n < 2 ^ (coronaScale n + 1) := Nat.lt_log2_self
  have h2 : (2 : Nat) ^ 1 ≤ n := by omega
  have : (2 : Nat) ^ 1 < 2 ^ (coronaScale n + 1) := Nat.lt_of_le_of_lt h2 hlt
  have := (Nat.pow_lt_pow_iff_right (a := 2) (by omega)).mp this
  omega

/-- `2^{⌊log₂ n⌋} ≤ n` for positive `n`. -/
theorem pow_coronaScale_le {n : Nat} (hn : 0 < n) : 2 ^ coronaScale n ≤ n :=
  Nat.log2_self_le (Nat.ne_of_gt hn)

/-- **The high part at the corona is identically 1.**  This is the geometric
content of choosing `k` from `|n|`: the integer sits in the dyadic annulus
`[2^k, 2^{k+1})`, so stripping `k` bits leaves the leading bit. -/
theorem corona_highPart {n : Nat} (hn : 0 < n) :
    highPart (coronaScale n) n = 1 := by
  have hle : 2 ^ coronaScale n ≤ n := pow_coronaScale_le hn
  have h1 : 1 * 2 ^ coronaScale n ≤ n := by simpa using hle
  have hlt : n < 2 ^ (coronaScale n + 1) := Nat.lt_log2_self
  have hpow : 2 ^ (coronaScale n + 1) = 2 * 2 ^ coronaScale n := Arith.two_pow_succ _
  have h2 : n < 2 * 2 ^ coronaScale n := by omega
  exact Nat.div_eq_of_lt_le h1 h2

/-- The splitting at the corona: `n = 2^{κ(n)} + mantissa`. -/
theorem corona_split {n : Nat} (hn : 0 < n) :
    2 ^ coronaScale n + mantissa n = n := by
  have h := split (coronaScale n) n
  rw [corona_highPart hn, Nat.mul_one] at h
  simpa [mantissa, lowPart, coronaScale] using h

/-- **The corona orbit law.**  After `κ(n)` accelerated steps the image is the
3-power of the mantissa's odd-count, plus the orbit of a strictly smaller
representative.  Real size has been spent as the window length; what remains
is a 2-adic computation on the mantissa. -/
theorem corona_orbit {n : Nat} (hn : 0 < n) :
    acceleratedOrbit (coronaScale n) n
      = 3 ^ oddCount n (coronaScale n)
        + acceleratedOrbit (coronaScale n) (mantissa n) := by
  have h := orbit_high (coronaScale n) n
  have hh := corona_highPart hn
  have hl : lowPart (coronaScale n) n = mantissa n := rfl
  rw [hh, hl, Nat.mul_one] at h
  exact h

/-! ## 2.  Real expansion forces 2-adic localisation -/

/-- **Expansion localises.**  If the orbit has not dropped through the corona
window, the mantissa's odd-count `a` obeys

    `2^κ + mantissa ≤ 3^a + T^κ(mantissa)`.

The left side is the real size (via `corona_split`).  The right side is a
function of the 2-adic window alone.  A real lower bound is therefore a
2-adic lower bound on odd-density. -/
theorem expansion_localizes {n : Nat} (hn : 0 < n)
    (hexp : n ≤ acceleratedOrbit (coronaScale n) n) :
    2 ^ coronaScale n + mantissa n
      ≤ 3 ^ oddCount n (coronaScale n)
        + acceleratedOrbit (coronaScale n) (mantissa n) := by
  have hs := corona_split hn
  have ho := corona_orbit hn
  omega

/-- Strong lightness implies the window is light. -/
theorem stronglyLight_three_le {n k : Nat} (h : StronglyLight n k) :
    3 ^ oddCount n k ≤ 2 ^ k := by
  unfold StronglyLight at h
  have : 3 ^ oddCount n k ≤ 2 * 3 ^ oddCount n k := by
    have := Arith.three_pow_pos (oddCount n k)
    omega
  exact Nat.le_trans this h

/-- Strong lightness gives a positive gap at least as large as the 3-power. -/
theorem stronglyLight_gap {n k : Nat} (h : StronglyLight n k) :
    3 ^ oddCount n k ≤ 2 ^ k - 3 ^ oddCount n k := by
  have hle := stronglyLight_three_le h
  unfold StronglyLight at h
  exact (Nat.le_sub_iff_add_le hle).mpr (by omega)

/-- The crude accumulator bound matches the corona gap exactly on a strongly
light window. -/
theorem stronglyLight_accum_le_gap {n k : Nat} (h : StronglyLight n k) :
    2 ^ k * 3 ^ oddCount n k ≤ 2 ^ k * (2 ^ k - 3 ^ oddCount n k) :=
  Nat.mul_le_mul_left _ (stronglyLight_gap h)

/-! ## 3.  Localisation forces real contraction (the pinch) -/

/-- **Light window drops.**  A strongly light window of length `k` with
`n ≥ 2^k` forces `T^k(n) < n`.  The comparison `n ≥ 2^k` is the real-size
input; `k` itself may still be a function of `n`. -/
theorem light_window_drops {n k : Nat} (hle : 2 ^ k ≤ n)
    (hlight : StronglyLight n k) :
    acceleratedOrbit k n < n := by
  have hG := stronglyLight_three_le hlight
  have hC := affineC_lt n k
  have hgap := stronglyLight_accum_le_gap (n := n) (k := k) hlight
  have hngap : 2 ^ k * (2 ^ k - 3 ^ oddCount n k)
      ≤ n * (2 ^ k - 3 ^ oddCount n k) :=
    Nat.mul_le_mul_right _ hle
  have hexact := affine_exact n k
  have hsum :
      3 ^ oddCount n k * n + n * (2 ^ k - 3 ^ oddCount n k) = n * 2 ^ k := by
    have : 3 ^ oddCount n k * n = n * 3 ^ oddCount n k := Nat.mul_comm _ _
    rw [this, ← Nat.mul_add, Nat.add_comm, Nat.sub_add_cancel hG]
  have hlt : 3 ^ oddCount n k * n + affineC k n < n * 2 ^ k := by
    have hClt : affineC k n < n * (2 ^ k - 3 ^ oddCount n k) :=
      Nat.lt_of_lt_of_le hC (Nat.le_trans hgap hngap)
    omega
  have hmul : 2 ^ k * acceleratedOrbit k n < 2 ^ k * n := by
    rw [hexact]
    have : n * 2 ^ k = 2 ^ k * n := Nat.mul_comm _ _
    omega
  exact Nat.lt_of_mul_lt_mul_left hmul

/-- **Light corona drops.**  A strongly light window at the *dynamic* scale
`κ(n) = ⌊log₂ n⌋` forces `T^{κ(n)}(n) < n`.

The proof consumes the even branch `x ↦ x/2` through `affine_exact` /
`affineC_lt`.  It is not a statement about a frozen modulus: the window
length is a function of real size, and the comparison `n ≥ 2^{κ(n)}` is the
definition of that function. -/
theorem light_corona_drops {n : Nat} (hn : 0 < n)
    (hlight : StronglyLight n (coronaScale n)) :
    acceleratedOrbit (coronaScale n) n < n :=
  light_window_drops (pow_coronaScale_le hn) hlight

/-- Lightness is a property of the mantissa, but the window length is not:
`κ(n)` is read from `|n|`.  That is the single-orbit datum a free parity word
of unspecified length does not carry. -/
theorem stronglyLight_of_mantissa (n : Nat) :
    StronglyLight n (coronaScale n) ↔ StronglyLight (mantissa n) (coronaScale n) := by
  have h : oddCount (mantissa n) (coronaScale n) = oddCount n (coronaScale n) := by
    simpa [mantissa, lowPart, coronaScale] using oddCount_lowPart (coronaScale n) n
  simp [StronglyLight, h]

/-- The pinch scale is still selected by real size, and `n` dominates `2^{2π}`. -/
theorem pinch_pow_le {n : Nat} (hn : 0 < n) :
    2 ^ (2 * pinchScale n) ≤ n := by
  have hhalf : 2 * pinchScale n ≤ Nat.log2 n := Nat.mul_div_le (Nat.log2 n) 2
  have hpow : 2 ^ (2 * pinchScale n) ≤ 2 ^ Nat.log2 n :=
    Nat.pow_le_pow_right (by decide) hhalf
  exact Nat.le_trans hpow (pow_coronaScale_le hn)

/-- `2^{π(n)} ≤ n` because `π(n) ≤ 2 π(n)`. -/
theorem pow_pinchScale_le {n : Nat} (hn : 0 < n) : 2 ^ pinchScale n ≤ n := by
  have h2 : 2 ^ (2 * pinchScale n) ≤ n := pinch_pow_le hn
  have hk : pinchScale n ≤ 2 * pinchScale n := by omega
  exact Nat.le_trans (Nat.pow_le_pow_right (by decide) hk) h2

/-- **Midscale pinch.**  The same drop at the half-octave window
`π(n) = ⌊log₂ n / 2⌋`, where the high part is at least `2^{π(n)}` rather than
`1`.  Stronger real-size input, same 2-adic lightness. -/
theorem light_pinch_drops {n : Nat} (hn : 0 < n)
    (hlight : StronglyLight n (pinchScale n)) :
    acceleratedOrbit (pinchScale n) n < n :=
  light_window_drops (pow_pinchScale_le hn) hlight

/-! ## 4.  The expStep filter: the drop is false, and lightness is unreachable -/

/-- Saturation `a = k` — the defining property of `expStep`'s affine law —
is incompatible with strong lightness at a positive scale. -/
theorem saturated_not_strongly_light {n k : Nat} (_hk : 0 < k)
    (hsat : oddCount n k = k) :
    ¬ StronglyLight n k := by
  intro h
  have h3 : (3 : Nat) ^ k ≤ 2 ^ k - 3 ^ k := by
    simpa [StronglyLight, hsat] using stronglyLight_gap (n := n) (k := k) h
  have hle : (3 : Nat) ^ k ≤ 2 ^ k := by
    simpa [hsat] using stronglyLight_three_le (n := n) (k := k) h
  have h2 : (2 : Nat) ^ k ≤ 3 ^ k := Arith.two_pow_le_three_pow k
  have heq : (2 : Nat) ^ k = 3 ^ k := Nat.le_antisymm h2 hle
  have hpos : 0 < (3 : Nat) ^ k := Arith.three_pow_pos k
  omega

/-- **`expStep` fails the corona drop.**  At the same dynamically chosen window
`κ(n)`, every `expStep` orbit with `n ≥ 2` is strictly above `n`.  The Collatz
pinch `light_corona_drops` is therefore not a theorem of the affine law plus
heaviness: it uses the contracting even branch that `expStep` replaces by
`3x/2`. -/
theorem expStep_fails_corona_drop {n : Nat} (hn : 2 ≤ n) :
    n < expOrbit (coronaScale n) n := by
  have hpos : 0 < n := by omega
  have hk : 1 ≤ coronaScale n := one_le_coronaScale hn
  have hge := expOrbit_ge (coronaScale n) n hpos
  omega

/-! ## Axiom audit -/

#print axioms corona_highPart
#print axioms corona_orbit
#print axioms expansion_localizes
#print axioms stronglyLight_of_mantissa
#print axioms light_window_drops
#print axioms light_corona_drops
#print axioms light_pinch_drops
#print axioms expStep_fails_corona_drop

end DeviceHybrid
end Collatz
