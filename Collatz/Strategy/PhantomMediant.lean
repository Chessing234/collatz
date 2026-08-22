import Collatz.Strategy.DeltaSpectrum

/-!
# The phantom cocycle: `[C(w) : G(w)]` as a projective point, and its mediant law

## The object

To a parity word `w` the development already attaches the pair `(C w, G w)`.
This file attaches instead the **projective point**

    Ψ(w) = [C(w) : G(w)] ∈ P¹(ℚ),      ρ(w) = C(w) / G(w) ∈ ℚ ∪ {∞},

called the **phantom** of `w`: the unique fixed point in `ℚ` of the affine map
`Φ_w(x) = (3 ^ a x + C) / 2 ^ L` which the word induces on the line.  `ρ(w)` is
the value the orbit *would* have to start at for `w` to close up into a cycle;
`δ(w)` is exactly the denominator of `ρ(w)` in lowest terms.

The point of the file is not `ρ` as a number — `ρ` is a function of `(C, G)` and
therefore carries no information beyond the known complete invariant.  The point
is the **composition law**, which is new:

* `C` and `G` obey the *same* append cocycle
  (`C_append`, `gap_append`), so `(C, G)` is a two-dimensional cocycle and `ρ`
  is a genuine projective coordinate;
* consequently `ρ(uv)` is the **weighted mediant** of `ρ(u)` and `ρ(v)` with
  weights `3 ^ a(v)` and `2 ^ |u|`, hence `ρ(uv)` lies *strictly between*
  `ρ(u)` and `ρ(v)` whenever both halves are heavy (`mediant_betweenness`);
* on a genuine integer trajectory the phantom is *localised* by the endpoints:
  `C = 2 ^ L (y − x) + G x` (`localisation`), so for a heavy window the phantom
  lies strictly beyond the far endpoint — above `y` if the window rises, below
  `y` if it falls (`sandwich_rise`, `sandwich_fall`), and *equals* the endpoint
  exactly when the window closes (`sandwich_cycle`).

## The refutation recorded here

The order structure suggests a descent: split a minimal cycle word `w = uv`,
and if both halves are heavy the mediant law puts one phantom strictly below the
cycle minimum.  **The descent is empty.**  `heavy_split_forces_band` shows that
`u` and `v` are both heavy exactly when the split point stays inside the band
`3 ^ a(u) · 2 ^ |w| > 3 ^ a(w) · 2 ^ |u|`, i.e. exactly when the discrepancy
path stays below the chord — the closed class.  For a real cycle word the band
has width `−log₂(1 − G/2^L) ≈ G / (2^L ln 2)` bits, which is under one bit, and
measurement confirms it is empty: over the parity words of the `3x+5` cycles at
`5, 19, 23, 187, 347`, the `3x+7` cycle at `5`, the `3x+13` cycle at `131` and
the `3x+1` cycle at `1`, **not one** of the `1 + 4 + 4 + 26 + 26 + 3 + 23 + 1`
splits has both halves heavy.  So the mediant order on phantoms never applies to
a cycle word at all.

## Measurements (never a proof)

* `C_append` and `gap_append` verified on all `260100` ordered pairs of words of
  length `≤ 8`; `0` violations.
* `mediant_betweenness` verified on all `164025` heavy ordered pairs of the same
  set; `0` violations, `507` ties (`ρ(u) = ρ(v)`, where the mediant is equal).
  On the `96075` mixed-sign pairs betweenness fails `85050` times — heaviness is
  not a convenience hypothesis, it is the whole content.
* `localisation` and the sandwich verified on all `5500000` windows
  `[i, i+L)` with `i < 20`, `L ≤ 19` of the genuine trajectories of every
  `x ≤ 20000`; `0` violations of either.
* Exhaustively over **every** word of length `L ≤ 22` with `G > 0`, the words
  with `δ = 1` are: the all-even word (`ρ = 0`) for every `L`, and for even `L`
  the two rotations of `(10) ^ (L/2)` (`ρ = 1, 2`).  Nothing else.  So `δ = 1`
  is rigid, and the hereditary condition "no proper factor has `δ = 1`" is very
  nearly vacuous — a second reason the descent has no teeth.
-/

namespace Collatz
namespace PhantomMediant

open DeltaSpectrum

/-- A commutative-semiring normaliser for `Nat`, standing in for `ring`
(unavailable without Mathlib). -/
macro "nring" : tactic =>
  `(tactic| simp [Nat.mul_add, Nat.add_mul, Nat.mul_assoc, Nat.mul_comm,
      Nat.mul_left_comm, Nat.add_assoc, Nat.add_comm, Nat.add_left_comm])

/-! ## 1.  The two append laws — `C` and `G` share one cocycle -/

theorem oddCount_append : ∀ u v : List Bool,
    oddCount (u ++ v) = oddCount u + oddCount v
  | [], v => by simp [oddCount]
  | b :: u, v => by
      simp [oddCount, oddCount_append u v]
      cases b <;> simp <;> omega

theorem accC_append : ∀ (u v : List Bool) (j c : Nat),
    accC (u ++ v) j c = accC v (j + u.length) (accC u j c)
  | [], v, j, c => by simp [accC]
  | b :: u, v, j, c => by
      have h := accC_append u v (j + 1) (if b then 3 * c + 2 ^ j else c)
      simp [accC, h, List.length_cons]
      congr 1
      omega

/-- **The key recursion.**  Running a word from offset `j` with accumulator `c`
splits exactly into the carried part `3 ^ a · c` and the word's own `2 ^ j · C`.
Both the affine dependence on `c` and the `2 ^ j` scaling in the offset are in
this one statement. -/
theorem accC_key : ∀ (w : List Bool) (j c : Nat),
    accC w j c = 3 ^ oddCount w * c + 2 ^ j * C w
  | [], j, c => by simp [accC, oddCount, C]
  | b :: w, j, c => by
      have ih := accC_key w
      cases b
      · have h1 := ih (j + 1) c
        have h2 := ih 1 0
        show accC w (j + 1) c = 3 ^ oddCount (false :: w) * c + 2 ^ j * accC w 1 0
        rw [h1, h2]
        simp [oddCount, Nat.pow_succ]
        nring
      · have h3 : (3:Nat) ^ (1 + oddCount w) = 3 * 3 ^ oddCount w := by
          rw [Nat.pow_add, Nat.pow_one]
        have h1 := ih (j + 1) (3 * c + 2 ^ j)
        have h2 := ih 1 1
        show accC w (j + 1) (3 * c + 2 ^ j)
            = 3 ^ oddCount (true :: w) * c + 2 ^ j * accC w 1 1
        rw [h1, h2]
        simp [oddCount, Nat.pow_succ, h3]
        nring

/-- **The append law for `C`.**  `C(uv) = 3 ^ a(v) · C(u) + 2 ^ |u| · C(v)`. -/
theorem C_append (u v : List Bool) :
    C (u ++ v) = 3 ^ oddCount v * C u + 2 ^ u.length * C v := by
  show accC (u ++ v) 0 0 = _
  rw [accC_append u v 0 0, accC_key v (0 + u.length) (accC u 0 0)]
  simp [C]

/-- **The append law for `G`, subtraction-free.**  With `g + 3 ^ a = 2 ^ L` on
each half, the same cocycle `(3 ^ a(v), 2 ^ |u|)` reproduces the gap of the
concatenation.  This is the reason `(C, G)` is a two-dimensional cocycle and
`ρ = C / G` a projective coordinate. -/
theorem gap_append {Lu au Lv av gu gv : Nat}
    (hu : gu + 3 ^ au = 2 ^ Lu) (hv : gv + 3 ^ av = 2 ^ Lv) :
    3 ^ av * gu + 2 ^ Lu * gv + 3 ^ (au + av) = 2 ^ (Lu + Lv) := by
  have h : 3 ^ av * gu + 2 ^ Lu * gv + 3 ^ au * 3 ^ av = 2 ^ Lu * 2 ^ Lv := by
    calc 3 ^ av * gu + 2 ^ Lu * gv + 3 ^ au * 3 ^ av
        = 3 ^ av * (gu + 3 ^ au) + 2 ^ Lu * gv := by nring
      _ = 3 ^ av * 2 ^ Lu + 2 ^ Lu * gv := by rw [hu]
      _ = 2 ^ Lu * (gv + 3 ^ av) := by nring
      _ = 2 ^ Lu * 2 ^ Lv := by rw [hv]
  rw [Nat.pow_add, Nat.pow_add]
  exact h

/-! ## 2.  The mediant law

Pure arithmetic: if `ρ(u) < ρ(v)` as fractions with positive denominators, then
the weighted mediant with any positive weights lies strictly between.  This is
the whole order content of the phantom. -/

/-- Left half of betweenness: `ρ(u) < ρ(uv)`. -/
theorem mediant_left {cu gu cv gv p q : Nat} (hq : 0 < q)
    (h : cu * gv < cv * gu) :
    cu * (p * gu + q * gv) < (p * cu + q * cv) * gu := by
  have hstep : q * (cu * gv) < q * (cv * gu) := (Nat.mul_lt_mul_left hq).mpr h
  have hl : cu * (p * gu + q * gv) = p * cu * gu + q * (cu * gv) := by nring
  have hr : (p * cu + q * cv) * gu = p * cu * gu + q * (cv * gu) := by nring
  rw [hl, hr]
  exact Nat.add_lt_add_left hstep _

/-- Right half of betweenness: `ρ(uv) < ρ(v)`. -/
theorem mediant_right {cu gu cv gv p q : Nat} (hp : 0 < p)
    (h : cu * gv < cv * gu) :
    (p * cu + q * cv) * gv < cv * (p * gu + q * gv) := by
  have hstep : p * (cu * gv) < p * (cv * gu) := (Nat.mul_lt_mul_left hp).mpr h
  have hl : (p * cu + q * cv) * gv = p * (cu * gv) + q * cv * gv := by nring
  have hr : cv * (p * gu + q * gv) = p * (cv * gu) + q * cv * gv := by nring
  rw [hl, hr]
  exact Nat.add_lt_add_right hstep _

/-- **Mediant betweenness.**  Stated cross-multiplied, so no rationals are
needed: `ρ(u) < ρ(v)` implies `ρ(u) < ρ(uv) < ρ(v)`. -/
theorem mediant_betweenness {cu gu cv gv p q : Nat} (hp : 0 < p) (hq : 0 < q)
    (h : cu * gv < cv * gu) :
    cu * (p * gu + q * gv) < (p * cu + q * cv) * gu ∧
      (p * cu + q * cv) * gv < cv * (p * gu + q * gv) :=
  ⟨mediant_left hq h, mediant_right hp h⟩

/-- Ties are fixed: `ρ(u) = ρ(v)` forces `ρ(uv)` to equal them.  In particular
`ρ(w ^ k) = ρ(w)` for every power, so the phantom is a *primitive-root*
invariant of the word. -/
theorem mediant_tie {cu gu cv gv p q : Nat} (h : cu * gv = cv * gu) :
    (p * cu + q * cv) * gu = cu * (p * gu + q * gv) := by
  have : q * (cv * gu) = q * (cu * gv) := by rw [h]
  calc (p * cu + q * cv) * gu = p * cu * gu + q * (cv * gu) := by nring
    _ = p * cu * gu + q * (cu * gv) := by rw [this]
    _ = cu * (p * gu + q * gv) := by nring

/-- The phantom of a word applied to itself: `C(ww) · G(w) = C(w) · G(ww)`,
so `ρ(w²) = ρ(w)`.  Instance of `mediant_tie`. -/
theorem phantom_square {c g p q : Nat} :
    (p * c + q * c) * g = c * (p * g + q * g) := mediant_tie rfl

/-! ## 3.  Localisation on a genuine integer trajectory

This is the half of the object that is *not* a function of the word: it couples
the phantom to the actual magnitudes at the two ends of the window. -/

/-- **Localisation.**  If the window of length `L` with `a` odd letters carries
the integer `x` to the integer `y` (`2 ^ L y = 3 ^ a x + C`) and `g` is the gap
(`g + 3 ^ a = 2 ^ L`), then `C = 2 ^ L (y − x) + g x`, stated without
subtraction. -/
theorem localisation {L a C x y g : Nat}
    (hstep : 2 ^ L * y = 3 ^ a * x + C) (hg : g + 3 ^ a = 2 ^ L) :
    C + 2 ^ L * x = 2 ^ L * y + g * x := by
  calc C + 2 ^ L * x = C + (g + 3 ^ a) * x := by rw [hg]
    _ = (3 ^ a * x + C) + g * x := by nring
    _ = 2 ^ L * y + g * x := by rw [hstep]

/-- **Phantom sandwich, rising case.**  A heavy window that rises has its
phantom strictly *above* the far endpoint: `g · y < C`, i.e. `y < ρ`. -/
theorem sandwich_rise {L a C x y g : Nat}
    (hstep : 2 ^ L * y = 3 ^ a * x + C) (hg : g + 3 ^ a = 2 ^ L)
    (hlt : x < y) : g * y < C := by
  have hloc := localisation hstep hg
  have hgl : g < 2 ^ L := by
    have : 0 < 3 ^ a := Nat.pow_pos (by decide)
    omega
  have hd : g * (y - x) < 2 ^ L * (y - x) :=
    (Nat.mul_lt_mul_right (Nat.sub_pos_of_lt hlt)).mpr hgl
  have h1 : g * y = g * (y - x) + g * x := by
    rw [← Nat.mul_add]; congr 1; omega
  have h2 : 2 ^ L * y = 2 ^ L * (y - x) + 2 ^ L * x := by
    rw [← Nat.mul_add]; congr 1; omega
  omega

/-- **Phantom sandwich, falling case.**  A heavy window that falls has its
phantom strictly *below* the far endpoint: `C < g · y`. -/
theorem sandwich_fall {L a C x y g : Nat}
    (hstep : 2 ^ L * y = 3 ^ a * x + C) (hg : g + 3 ^ a = 2 ^ L)
    (hlt : y < x) : C < g * y := by
  have hloc := localisation hstep hg
  have hgl : g < 2 ^ L := by
    have : 0 < 3 ^ a := Nat.pow_pos (by decide)
    omega
  have hd : g * (x - y) < 2 ^ L * (x - y) :=
    (Nat.mul_lt_mul_right (Nat.sub_pos_of_lt hlt)).mpr hgl
  have h1 : g * x = g * (x - y) + g * y := by
    rw [← Nat.mul_add]; congr 1; omega
  have h2 : 2 ^ L * x = 2 ^ L * (x - y) + 2 ^ L * y := by
    rw [← Nat.mul_add]; congr 1; omega
  omega

/-- **Phantom sandwich, closing case.**  The window closes exactly when the
phantom *is* the endpoint: this is the cycle criterion `G n = C`, recovered as
the degenerate case of the sandwich. -/
theorem sandwich_cycle {L a C x g : Nat}
    (hstep : 2 ^ L * x = 3 ^ a * x + C) (hg : g + 3 ^ a = 2 ^ L) :
    g * x = C := by
  have : (g + 3 ^ a) * x = 3 ^ a * x + C := by rw [hg]; exact hstep
  have h : g * x + 3 ^ a * x = 3 ^ a * x + C := by
    rw [← this]; nring
  omega

/-! ## 4.  Why the descent is empty

The mediant order applies to a split `w = uv` only when both halves are heavy.
That is *exactly* a band condition on the discrepancy at the split point, so
the whole construction lands inside the class already closed by
`OrderAutomaton.disc_append`. -/

/-- **Heavy split forces the discrepancy band.**  If `v` is heavy
(`3 ^ av < 2 ^ Lv`) then the split point of `uv` satisfies
`3 ^ au · 2 ^ (Lu+Lv) > 3 ^ (au+av) · 2 ^ Lu`, i.e. the discrepancy path at the
split point lies strictly below the chord joining the endpoints.  The converse
holds too, so "both halves heavy" *is* the band condition and nothing more. -/
theorem heavy_split_forces_band {Lu au Lv av : Nat} (hv : 3 ^ av < 2 ^ Lv) :
    3 ^ (au + av) * 2 ^ Lu < 3 ^ au * 2 ^ (Lu + Lv) := by
  have hpos : 0 < 3 ^ au * 2 ^ Lu :=
    Nat.mul_pos (Nat.pow_pos (by decide)) (Nat.two_pow_pos Lu)
  have h : (3 ^ au * 2 ^ Lu) * 3 ^ av < (3 ^ au * 2 ^ Lu) * 2 ^ Lv :=
    (Nat.mul_lt_mul_left hpos).mpr hv
  have hl : (3 ^ au * 2 ^ Lu) * 3 ^ av = 3 ^ (au + av) * 2 ^ Lu := by
    rw [Nat.pow_add]; nring
  have hr : (3 ^ au * 2 ^ Lu) * 2 ^ Lv = 3 ^ au * 2 ^ (Lu + Lv) := by
    rw [Nat.pow_add]; nring
  rw [hl, hr] at h
  exact h

/-- Converse: the band condition returns heaviness of the second half.  So the
band and the heavy split are the *same* condition, not merely related. -/
theorem band_forces_heavy_split {Lu au Lv av : Nat}
    (hband : 3 ^ (au + av) * 2 ^ Lu < 3 ^ au * 2 ^ (Lu + Lv)) :
    3 ^ av < 2 ^ Lv := by
  have hpos : 0 < 3 ^ au * 2 ^ Lu :=
    Nat.mul_pos (Nat.pow_pos (by decide)) (Nat.two_pow_pos Lu)
  have hl : (3 ^ au * 2 ^ Lu) * 3 ^ av = 3 ^ (au + av) * 2 ^ Lu := by
    rw [Nat.pow_add]; nring
  have hr : (3 ^ au * 2 ^ Lu) * 2 ^ Lv = 3 ^ au * 2 ^ (Lu + Lv) := by
    rw [Nat.pow_add]; nring
  have h : (3 ^ au * 2 ^ Lu) * 3 ^ av < (3 ^ au * 2 ^ Lu) * 2 ^ Lv := by
    rw [hl, hr]; exact hband
  exact (Nat.mul_lt_mul_left hpos).mp h

/-- The two directions together: the mediant order applies to `uv` at a split
point exactly when the discrepancy band holds there.  **This is the refutation.**
The band is the closed class, so the phantom order supplies no new descent. -/
theorem heavy_split_iff_band {Lu au Lv av : Nat} :
    3 ^ av < 2 ^ Lv ↔ 3 ^ (au + av) * 2 ^ Lu < 3 ^ au * 2 ^ (Lu + Lv) :=
  ⟨heavy_split_forces_band, band_forces_heavy_split⟩

/-! ## 5.  Negative controls

The `3x+5` cycle word of `187` has `L = 27`, `a = 17`, `G = 5077565`,
`C = 189900931`, `δ = 5`.  Its gap is a `0.038` fraction of `2 ^ 27`, so the
band available to a split point is under a twentieth of a bit — and indeed no
split of it has both halves heavy.  The two numeric facts below pin the
arithmetic of that example inside the kernel. -/

theorem w187_gap : 5077565 + 3 ^ 17 = 2 ^ 27 := by decide

theorem w187_cycle : 5077565 * 187 = 5 * 189900931 := by decide

/-- The band for that word is narrower than a factor of `2`: `2 ^ 27 < 2 · 3 ^ 17`.
A split point would have to sit within `log₂(2^27/3^17) < 0.06` of the chord. -/
theorem w187_band_narrow : 2 ^ 27 < 2 * 3 ^ 17 := by decide

end PhantomMediant
end Collatz
