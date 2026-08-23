import Collatz.Strategy.NewModels
import Collatz.Strategy.Linearizing

/-!
# The `(word, magnitude)` fibre is exactly rank one

Round XI's question: *is there any genuinely two-variable information left in the
`(word, magnitude)` fibre?*  This file answers it in the direction the brief allows
as an equally valuable outcome — **the decoupling is real, and it is an identity, not
a limit.**

## The exact expansion, and why it is not an expansion

Fix a window length `j`.  The affine law is `2 ^ j · x_j = 3 ^ (A j) · n + C j`, so the
coupling of `Coupling.lean`/`Linearizing.lean` is

    r_j(n) = C j / (3 ^ (A j) · n).

`C j` and `A j` are functions of `n % 2 ^ j` only (`NewModels.class_iff_count_accum`).
Therefore, **on the fibre over a fixed word**,

> `r_j(n) = E(w) / n`  with  `E(w) = C j / 3 ^ (A j)`,  *exactly, with zero remainder.*

There is no `kappa_inf(w)`: the limit is `0`.  There is no `O(n^-2)` term: it is
identically zero.  The strongest rigorous finite statement is an **identity**, and the
identity says the fibre map is affine in the magnitude with word-determined
coefficients — `fibre_affine` below is that statement cleared of division:

    y · (2 ^ j · x_j(x))  =  x · (2 ^ j · x_j(y))  +  (y − x) · C j      (x ≤ y, same word).

The deviation between two magnitudes carrying the same word is `(y − x) · C`, a *pure
word quantity times a pure magnitude quantity*.  That is rank one.  Nothing in the
fibre is a genuine function of two variables.

## The residual, named

The natural rescaling is `n · r_j`, and it is attained at **every** `n`, not in a limit:

> **the residual is `E(w) = C j / 3 ^ (A j)`.**

`residual_class_constant` is the invariance, `residual_injective` the sharpness:
at fixed `(L, a)` the residual **determines the word**.  So `E` is maximally
ordering-sensitive — it is `Σ 2 ^ (t_i) / 3 ^ i` over the ordered odd times
`t_1 < ⋯ < t_a` of Round VIII — and it is exactly as informative as `C`, hence
Class 3 by `CLOSURE.md` diagnostic 2.  *Ordering-sensitivity is real and worthless:
the residual is a relabelling of the accumulator.*

## The one genuinely two-variable predicate, and its explicit threshold

What is *not* a function of the word alone is a **discrete** datum: the order type of
the profile `x_0, …, x_L`.  For `i < j`,

    2 ^ (i+j) · (x_i − x_j)  =  n · D  +  (2 ^ j · C_i − 2 ^ i · C_j),
    D := 2 ^ j · 3 ^ (A i) − 2 ^ i · 3 ^ (A j).

`D` is the pure word term; the second summand is the **finite-scale correction**, and
it is *negative* for `d > 0` (because `C` is increasing along the window).  So for
`3x + 1` the correction can only flip a pair the word calls "down" into "up", never the
reverse — the sign of the correction is `sign d`, and nothing else about the word
enters it.  `order_word_determined` gives the exact threshold, `drop_of_scale` its
`i = 0` specialisation

> `2 ^ (L − a) · 3 ^ a  ≤  n · (2 ^ L − 3 ^ a)`  ⟹  `x_L ≤ n`,

so the scale above which the word decides is `N(w) = 2 ^ (L − a) · 3 ^ a / G`.  It is
large exactly when `G` is small — **at the ledges, and nowhere else.**  All remaining
two-variable content is concentrated on the frontier, which is a mapped Class 1/3
asset.

## Status labels

Everything stated in Lean below is LEAN_PROVED.  The `d`-dependence discussed in the
header is MATHEMATICALLY_PROVED from `C(w,d) = d · C(w,1)` plus COMPUTATIONAL
measurement, and is recorded in `RESEARCH.md`, not here: `Nat` cannot express `d < 0`.
-/

namespace Collatz
namespace ScaleFibre

open AffineExact NewModels

/-- `0 < k ^ m` for `k ≥ 1`, in the two shapes this file needs. -/
theorem pow_pos_two : ∀ m : Nat, 0 < 2 ^ m
  | 0 => by decide
  | m + 1 => by rw [Nat.pow_succ]; have := pow_pos_two m; omega

theorem pow_pos_three : ∀ m : Nat, 0 < 3 ^ m
  | 0 => by decide
  | m + 1 => by rw [Nat.pow_succ]; have := pow_pos_three m; omega

/-! ## 1.  The fibre is exactly affine — rank one, with no remainder -/

/-- Two magnitudes carrying the same parity word to level `j` have the same word data.
This is `NewModels.class_iff_count_accum` in the direction the fibre argument uses. -/
theorem word_data_eq {x y j : Nat} (h : x % 2 ^ j = y % 2 ^ j) :
    oddCount x j = oddCount y j ∧ affineC j x = affineC j y :=
  (class_iff_count_accum).1 h

/-- **The fibre is exactly affine.**  Over a fixed parity word, the map
`n ↦ 2 ^ j · x_j(n)` is `n ↦ 3 ^ a · n + C` with `(a, C)` word-determined.  Cleared of
subtraction, the deviation between two magnitudes on the fibre is exactly
`(y − x) · C` — a pure word factor times a pure magnitude factor.

This is the round's central answer: **the `(word, magnitude)` fibre carries no
two-variable information at all.  It is rank one, as an identity, not as a limit.** -/
theorem fibre_affine {x y j : Nat} (h : x % 2 ^ j = y % 2 ^ j) (hxy : x ≤ y) :
    y * (2 ^ j * acceleratedOrbit j x)
      = x * (2 ^ j * acceleratedOrbit j y) + (y - x) * affineC j x := by
  obtain ⟨hA, hC⟩ := word_data_eq h
  rw [affine_exact x j, affine_exact y j, ← hA, ← hC]
  have hsub : (y - x) * affineC j x + x * affineC j x = y * affineC j x := by
    rw [← Nat.add_mul, Nat.sub_add_cancel hxy]
  have hxy3 : y * (3 ^ oddCount x j * x) = x * (3 ^ oddCount x j * y) := by
    simp [Nat.mul_comm, Nat.mul_left_comm]
  rw [Nat.mul_add, Nat.mul_add, hxy3]
  omega

/-- The `n = 0` boundary of `fibre_affine`: the word datum `C` is literally the value
of `2 ^ j · x_j` extrapolated to magnitude zero.  Recorded because it is the reason
there is no second-order term: an affine function has no second difference. -/
theorem fibre_second_difference {x y z j : Nat}
    (hxy : x % 2 ^ j = y % 2 ^ j) (hxz : x % 2 ^ j = z % 2 ^ j) :
    (2 ^ j * acceleratedOrbit j y) + (2 ^ j * acceleratedOrbit j z)
      + 3 ^ oddCount x j * x
      = (2 ^ j * acceleratedOrbit j x) + 3 ^ oddCount x j * y
        + 3 ^ oddCount x j * z + affineC j x := by
  obtain ⟨hAy, hCy⟩ := word_data_eq hxy
  obtain ⟨hAz, hCz⟩ := word_data_eq hxz
  rw [affine_exact x j, affine_exact y j, affine_exact z j, ← hAy, ← hAz, ← hCy, ← hCz]
  omega

/-! ## 2.  The residual `E(w) = C / 3 ^ a`, and its exact information content -/

/-- **The residual is constant on the fibre.**  `n · r_j(n) = C j / 3 ^ (A j)` takes the
same value at every magnitude carrying the word.  Cleared of division. -/
theorem residual_class_constant {x y j : Nat} (h : x % 2 ^ j = y % 2 ^ j) :
    affineC j x * 3 ^ oddCount y j = affineC j y * 3 ^ oddCount x j := by
  obtain ⟨hA, hC⟩ := word_data_eq h
  rw [hA, hC]

/-- **The residual is a complete invariant of the word at fixed odd-count.**  So it is
maximally ordering-sensitive — and, being a bijective relabelling of `affineC`, it is
Class 3 and carries no new information.  Both halves of that sentence are this one
theorem. -/
theorem residual_injective {x y L : Nat} (hcount : oddCount x L = oddCount y L)
    (hE : affineC L x * 3 ^ oddCount y L = affineC L y * 3 ^ oddCount x L) :
    x % 2 ^ L = y % 2 ^ L := by
  have hpos : 0 < 3 ^ oddCount y L := pow_pos_three (oddCount y L)
  rw [hcount] at hE
  exact word_of_count_and_accum hcount (Nat.eq_of_mul_eq_mul_right hpos hE)

/-! ## 3.  The finite-scale correction, with its explicit threshold -/

/-- **The exact two-scale comparison.**  `2 ^ (i+j) · x_i` against `2 ^ (i+j) · x_j`,
with the word term `2 ^ j · 3 ^ (A i) · n` versus `2 ^ i · 3 ^ (A j) · n` and the
finite-scale correction `2 ^ j · C_i` versus `2 ^ i · C_j`, all cleared of subtraction. -/
theorem compare_expand (n i j : Nat) :
    2 ^ i * (2 ^ j * acceleratedOrbit j n)
      = 2 ^ i * (3 ^ oddCount n j * n) + 2 ^ i * affineC j n := by
  rw [affine_exact n j, Nat.mul_add]

/-- **The word decides above an explicit scale.**  If the word term separates the two
levels (`hD`) and the magnitude `n` exceeds the finite-scale correction against that
separation (`hN`), then the order of `x_i` and `x_j` is the word's order.

The hypothesis `hN` is the threshold: `n ≥ 2 ^ i · C_j / D`.  Nothing else about the
word enters, and the correction enters only through `C_j`. -/
theorem order_word_determined {n i j : Nat}
    (hD : 2 ^ i * 3 ^ oddCount n j ≤ 2 ^ j * 3 ^ oddCount n i)
    (hN : 2 ^ i * affineC j n
        ≤ n * (2 ^ j * 3 ^ oddCount n i - 2 ^ i * 3 ^ oddCount n j)) :
    2 ^ i * (2 ^ j * acceleratedOrbit j n) ≤ 2 ^ j * (2 ^ i * acceleratedOrbit i n) := by
  have hj := compare_expand n i j
  have hi : 2 ^ j * (2 ^ i * acceleratedOrbit i n)
      = 2 ^ j * (3 ^ oddCount n i * n) + 2 ^ j * affineC i n := by
    rw [affine_exact n i, Nat.mul_add]
  have hmul : n * (2 ^ j * 3 ^ oddCount n i - 2 ^ i * 3 ^ oddCount n j)
      + n * (2 ^ i * 3 ^ oddCount n j) = n * (2 ^ j * 3 ^ oddCount n i) := by
    rw [← Nat.mul_add, Nat.sub_add_cancel hD]
  have hcomm1 : 2 ^ i * (3 ^ oddCount n j * n) = n * (2 ^ i * 3 ^ oddCount n j) := by
    simp [Nat.mul_comm, Nat.mul_left_comm]
  have hcomm2 : 2 ^ j * (3 ^ oddCount n i * n) = n * (2 ^ j * 3 ^ oddCount n i) := by
    simp [Nat.mul_comm, Nat.mul_left_comm]
  omega

/-- Cancelling the common power: the conclusion of `order_word_determined` as a
statement about the orbit values themselves. -/
theorem orbit_le_of_scaled {i j u v : Nat} (h : 2 ^ i * (2 ^ j * u) ≤ 2 ^ j * (2 ^ i * v)) :
    u ≤ v := by
  have hpos : 0 < 2 ^ i * 2 ^ j := Nat.mul_pos (pow_pos_two i) (pow_pos_two j)
  have h1 : 2 ^ i * 2 ^ j * u ≤ 2 ^ i * 2 ^ j * v := by
    have e1 : 2 ^ i * (2 ^ j * u) = 2 ^ i * 2 ^ j * u := (Nat.mul_assoc _ _ _).symm
    have e2 : 2 ^ j * (2 ^ i * v) = 2 ^ i * 2 ^ j * v := by
      rw [← Nat.mul_assoc, Nat.mul_comm (2 ^ j) (2 ^ i)]
    rw [← e1, ← e2]; exact h
  exact Nat.le_of_mul_le_mul_left h1 hpos

/-- **The threshold in purely word-side terms.**  `affineC_le` bounds the correction by
`2 ^ (j − a) · 3 ^ a`, so the scale above which the word decides is
`N(w; i, j) = 2 ^ (i + j − A j) · 3 ^ (A j) / D` — no reference to the actual
accumulator, only to the word's shape. -/
theorem order_word_determined_shape {n i j : Nat}
    (hD : 2 ^ i * 3 ^ oddCount n j ≤ 2 ^ j * 3 ^ oddCount n i)
    (hN : 2 ^ i * (2 ^ (j - oddCount n j) * 3 ^ oddCount n j)
        ≤ n * (2 ^ j * 3 ^ oddCount n i - 2 ^ i * 3 ^ oddCount n j)) :
    acceleratedOrbit j n ≤ acceleratedOrbit i n := by
  have hbound := affineC_le n j
  have hstep : 2 ^ i * affineC j n
      ≤ 2 ^ i * (2 ^ (j - oddCount n j) * 3 ^ oddCount n j) := by
    exact Nat.mul_le_mul_left _ (Nat.le_trans (Nat.le_add_right _ _) hbound)
  exact orbit_le_of_scaled
    (order_word_determined hD (Nat.le_trans hstep hN))

/-- **The `i = 0` specialisation: the explicit drop threshold.**  A light word drops the
orbit as soon as the magnitude clears `N(w) = 2 ^ (L − a) · 3 ^ a / G`.  `N(w)` is large
exactly when the gap `G` is small — i.e. **only at the ledges**.  Everywhere else the
word decides at every admissible magnitude, and the fibre is decoupled outright. -/
theorem drop_of_scale {n L : Nat}
    (hlight : 3 ^ oddCount n L ≤ 2 ^ L)
    (hN : 2 ^ (L - oddCount n L) * 3 ^ oddCount n L
        ≤ n * (2 ^ L - 3 ^ oddCount n L)) :
    acceleratedOrbit L n ≤ n := by
  have h0 : acceleratedOrbit 0 n = n := rfl
  have hD : 2 ^ 0 * 3 ^ oddCount n L ≤ 2 ^ L * 3 ^ oddCount n 0 := by
    have hz : oddCount n 0 = 0 := rfl
    rw [hz]
    simpa using hlight
  have hN' : 2 ^ 0 * (2 ^ (L - oddCount n L) * 3 ^ oddCount n L)
      ≤ n * (2 ^ L * 3 ^ oddCount n 0 - 2 ^ 0 * 3 ^ oddCount n L) := by
    have hz : oddCount n 0 = 0 := rfl
    rw [hz]
    simpa using hN
  have := order_word_determined_shape (n := n) (i := 0) (j := L) hD hN'
  rw [h0] at this
  exact this

/-! ## 4.  What the threshold costs at a ledge

`drop_of_scale` needs `n · G ≥ 2 ^ (L−a) · 3 ^ a`.  Since `2 ^ (L−a) · 3 ^ a ≥ 2 ^ L`
whenever the word has at least one odd step, the threshold always exceeds `2 ^ L / G`.
So the fibre's residual freedom is *bounded below* by the reciprocal gap — which is the
frontier, restated as a statement about magnitudes rather than about words. -/

/-- `2 ^ L ≤ 2 ^ (L − a) · 3 ^ a` for `a ≤ L`: the threshold never falls below
`2 ^ L / G`. -/
theorem two_pow_le_shape {L a : Nat} (h : a ≤ L) : 2 ^ L ≤ 2 ^ (L - a) * 3 ^ a := by
  have hsplit : (2:Nat) ^ L = 2 ^ (L - a) * 2 ^ a := by
    rw [← Nat.pow_add, Nat.sub_add_cancel h]
  rw [hsplit]
  exact Nat.mul_le_mul_left _ (Nat.pow_le_pow_left (by decide) a)

/-! ## Axiom audit -/

#print axioms fibre_affine
#print axioms residual_injective
#print axioms order_word_determined
#print axioms drop_of_scale

end ScaleFibre
end Collatz
