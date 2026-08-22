import Collatz.Strategy.ExtremalWord

/-!
# Geometry of numbers: the body is thinner than the lattice, and the only
# theorem with the right polarity is a certificate that cannot exist

Round III closed the lattice framing with the remark that `t ↦ 2 ^ t` is not
linear and the coefficient `3 ^ (a−i)` depends on the *rank* of `t` in the set,
so there is no lattice to run LLL or CVP against.  That reason is correct but it
is not the sharpest one, and it is not the one that matters, because there are
two coordinate changes that dodge it entirely.  This file carries both of them
out and reports where each dies.  Neither dies for the Round III reason.

## Coordinate change 1: exponent space.  The body is real, and too thin

Work in `(t₀, …, t_{a−1}) ∈ ℤ^a`, the odd-step times.  The admissible set is an
honest intersection of a simplicial cone `0 ≤ t₀ < t₁ < … < t_{a−1} < L` with the
box `t i ≤ fexp i` of `ExtremalWord`; that *is* a convex body, and the heavy
words are exactly its lattice points, so the Round III objection does not apply
to it.  What kills it is size.  In the gap coordinates `d i = t i − t (i−1) ≥ 1`
the body is the simplex of total slack `Σ (d i − 1) = t_{a−1} − (a−1)`, and

`five_fexp_lt`  : `5 · fexp i < 8 · i`   (`i ≥ 1`)
`slack_lt`      : `5 · (fexp i − i) < 3 · i`

so after the unimodular shear `u i = t i − i` — which turns the strict cone
`t₀ < t₁ < …` into the weak cone `u₀ ≤ u₁ ≤ …` and costs nothing, being an
integer shear — the box becomes `u i ≤ fexp i − i < 0.6 · i`.  The admissible
body is therefore the set of weakly increasing points of a cube of side
`M < 0.6 a`, whose volume is `M ^ a / a !` at most, hence

`vol ≤ (0.6 a) ^ a / a ! ≤ (0.6 e) ^ a = 1.632 ^ a < 2 ^ a`.

**Minkowski's convex body theorem therefore does not apply in any dimension**:
its hypothesis `vol ≥ 2 ^ a · det` fails by the exponential factor
`(2 / 1.632) ^ a`, and no sharpening recovers it.  The body is thinner than one
lattice spacing per direction — `0.6` of one, on average.  Worse, the first two
caps are `fexp 0 − 0 = 0` and `fexp 1 − 1 = 0`, so the `a`-dimensional volume is
*exactly zero*: the body is not even full dimensional.  Comparing in the
remaining `a − 2` coordinates, where it is, the lattice-point count against the
volume: `a = 24`: `2.6 · 10 ^ 8` against `251.2`; `a = 48`: `6.7 · 10 ^ 18`
against `5.5 · 10 ^ 6`, the ratio growing like `1.79 ^ a`.  So the count is
**not** the volume to leading order, in either direction, and the excess is
exactly the `(1 + 1/0.585) ^ a` that an `O(1)`-thick body always shows.
Geometry of numbers adds nothing because its entire regime — lattice points
equidistributing in a body large compared with the covering radius — is never
entered.

## Coordinate change 2: linearisation at the Beatty corner

The exponential `2 ^ t` is only nonlinear across large moves.  Fix a reference
word `t` and perturb by `e i ∈ {0,1}`.  Then `2 ^ (t i + e i) = 2 ^ t i + e i · 2 ^ t i`
exactly, so the accumulator becomes an **affine function of the perturbation**:

`Cw_shift` : `Cw (fun i => t i + e i) a = Cw t a + Csel t e a`,
             `Csel t e a = Σ_{i<a} e i · 3 ^ (a−1−i) · 2 ^ t i`.

This is a genuine linearisation — the Round III objection is answered, because
after fixing the reference word the coefficient `3 ^ (a−1−i)` is a *constant*,
not a function of the rank of a moving `t`.  The divisibility `G ∣ C` becomes a
**subset-sum problem modulo `G`** with the fixed weight vector
`wgt t a i = 3 ^ (a−1−i) · 2 ^ t i`, and `Λ = {z : ⟨wgt, z⟩ ≡ 0 mod G}` is now an
honest lattice of index `G` in `ℤ^a`.  The question "no cycle among these
perturbations" is "the coset `Λ − C₀` misses the cube `{0,1}^a`".

## Polarity, and the only theorem that has it

Minkowski, transference and Banaszczyk all produce lattice points; we need their
absence.  The unique classical statement in the absence direction is the
**flatness theorem**, and it is a *conditional*: a body containing no lattice
point is flat, i.e. some dual vector takes a short range on it.  Used
contrapositively it proves existence, which is the wrong way round.  Used
directly it demands a *certificate*: a dual vector of ℓ¹-norm below one.  For our
lattice the dual is `Λ* = ℤ^a + (1/G)·wgt·ℤ`, so a certificate is a single
integer `k`, and — because the perturbations `e i` are one-sided (`0` or `1`) —
the certificate condition collapses to an entirely elementary inequality,
proved here without any geometry at all:

`not_dvd_of_small` : if `0 < msum` and `2 · msum < G`, where
`msum = Σ_{i<a} (k · wgt t a i) % G`, then **no** perturbation `e ∈ {0,1}^a`
makes `G ∣ Cw (t + e) a`.

That is a real theorem with the right polarity, and it is the exact content of
"the cube is flat with respect to `Λ`".  It is also unusable, for two reasons
that are worth recording because they are structural, not technical.

**(i) The certificate does not exist.**  Exhaustively over *every* `k < G` at the
ledge pairs `L = fexp a + 1`, the minimum of `msum / G` is
`a = 3..20`: `1.200, 0.851, 1.846, 1.085, 0.664, 1.399, 1.047, 1.826, 1.330,
0.782, 1.493, 1.205, 1.820, 1.470, 2.039, 1.557, 1.054, 1.745`.
The threshold is `0.5` and it is never met — but the smallest miss is by a factor
of only `1.33` (at `a = 7`), which is the same "as near as arithmetic allows"
that every other route reports.  The minimising `k` grows like `G ^ (1 − 1/a)`,
so the search is exponential and no `k` of controllable size ever works: the
Minkowski bound for the dual lattice puts its shortest ℓ¹ vector at
`≈ (a! / G) ^ (1/a) ≈ a / (e · 3) > 1` as soon as `a ≥ 9`, so for `a ≥ 9`
a certificate provably cannot exist in a generic lattice of this determinant —
`log₂ 3 = 1.585` is simply too small to leave room for one.

**(ii) The certificate is the S-unit obstruction in disguise.**  The weights
satisfy `3 · wgt t a i = 2 ^ (t i − t (i−1)) · wgt t a (i−1)` (`wgt_step`), so the
whole dual vector is the orbit of the single number `k / G` under multiplication
by the `S`-units `3 ^ j 2 ^ −m`.  Demanding that all `a` of its coordinates be
simultaneously small **is** the simultaneous-approximation problem for
`{3 ^ j 2 ^ −m}` that `SUnitRelation`, `OneRunOrder` and `TwoRunOrder` already
close.  So the lattice route is not a new mechanism; it is the order obstruction
written in dual coordinates.

Nothing here uses `d`: every statement is about words and about a modulus `G`
supplied by the caller, so by the Round III soundness filter the file cannot
obstruct anything on its own.  It is recorded because it converts "no lattice
exists" into the sharper and more useful "the lattice exists in two different
coordinate systems, and in both the geometry of numbers has the wrong polarity
or the wrong scale".
-/

namespace Collatz
namespace LatticeGeometry

open RealizableBound ExtremalWord

/-! ## Part 1.  The body is thinner than one lattice spacing per direction -/

/-- `2 ^ i ≤ 3 ^ i`, so the cone floor `t i ≥ i` sits below the box lid. -/
theorem le_fexp_self (i : Nat) : i ≤ fexp i :=
  le_fexp_of_pow_le (Nat.pow_le_pow_left (by decide) i)

/-- **The lid is at most `1.6 i`.**  `243 = 3 ^ 5 < 2 ^ 8 = 256`, raised to the
`i`-th power, is the whole proof. -/
theorem five_fexp_lt {i : Nat} (hi : 0 < i) : 5 * fexp i < 8 * i := by
  have e3 : (3:Nat) ^ 5 = 243 := by decide
  have e2 : (2:Nat) ^ 8 = 256 := by decide
  have h1 : (2:Nat) ^ fexp i ≤ 3 ^ i := fexp_le i
  have h2 : ((2:Nat) ^ fexp i) ^ 5 ≤ (3 ^ i) ^ 5 := Nat.pow_le_pow_left h1 5
  have h3 : ((3:Nat) ^ i) ^ 5 = 243 ^ i := by
    rw [← Nat.pow_mul, Nat.mul_comm, Nat.pow_mul, e3]
  have h4 : (243:Nat) ^ i < 256 ^ i := Nat.pow_lt_pow_left (by decide) (by omega)
  have h5 : (256:Nat) ^ i = 2 ^ (8 * i) := by rw [Nat.pow_mul, e2]
  have h6 : ((2:Nat) ^ fexp i) ^ 5 = 2 ^ (5 * fexp i) := by
    rw [← Nat.pow_mul, Nat.mul_comm]
  have h7 : (2:Nat) ^ (5 * fexp i) < 2 ^ (8 * i) := by
    rw [← h6, ← h5]; omega
  rcases Nat.lt_or_ge (5 * fexp i) (8 * i) with hok | hcon
  · exact hok
  · exfalso
    have : (2:Nat) ^ (8 * i) ≤ 2 ^ (5 * fexp i) :=
      Arith.two_pow_le_two_pow hcon
    omega

/-- **The slack at coordinate `i` is under `0.6 i`.**  The box lid `fexp i` sits
above the cone floor `i` by less than `3 i / 5`; summed over the word this is the
statement that the admissible body has ℓ¹-radius `< 0.6 a` in dimension `a`. -/
theorem slack_lt {i : Nat} (hi : 0 < i) : 5 * (fexp i - i) < 3 * i := by
  have h1 := five_fexp_lt hi
  have h2 := le_fexp_self i
  omega

/-- The cone floor, in the form the body needs: a strictly increasing word has
`t i ≥ t 0 + i`. -/
theorem strictInc_floor {t : Nat → Nat} (h : StrictInc t) : ∀ i : Nat, t 0 + i ≤ t i := by
  intro i
  induction i with
  | zero => omega
  | succ i ih => have := h i; omega

/-- **The thickness theorem.**  For any heavy word, every coordinate of the
admissible body lies within `0.6 i` of the cone floor. -/
theorem word_slack_lt {t : Nat → Nat} (hst : StrictInc t)
    {a : Nat} (hbox : ∀ i : Nat, i < a → t i ≤ fexp i)
    {i : Nat} (hi : 0 < i) (hia : i < a) : 5 * (t i - i) < 3 * i := by
  have h1 := hbox i hia
  have h2 := five_fexp_lt hi
  have h3 := strictInc_floor hst i
  omega

/-! ## Part 2.  Linearisation at a reference word -/

/-- The perturbation part of the accumulator: `Σ_{i<a} e i · 3 ^ (a−1−i) · 2 ^ t i`,
written in the same Horner recursion as `Cw`. -/
def Csel (t e : Nat → Nat) : Nat → Nat
  | 0 => 0
  | a + 1 => 3 * Csel t e a + e a * 2 ^ t a

@[simp] theorem Csel_zero (t e : Nat → Nat) : Csel t e 0 = 0 := rfl

theorem Csel_succ (t e : Nat → Nat) (a : Nat) :
    Csel t e (a + 1) = 3 * Csel t e a + e a * 2 ^ t a := rfl

theorem Cw_eq_Csel_one (t : Nat → Nat) :
    ∀ a : Nat, Cw t a = Csel t (fun _ => 1) a := by
  intro a
  induction a with
  | zero => rfl
  | succ a ih => rw [Cw_succ, Csel_succ, ih]; omega

/-- **The linearisation.**  Moving each odd-step time up by `0` or `1` changes the
accumulator by an *affine* amount: `2 ^ (t i + e i) = 2 ^ t i + e i · 2 ^ t i`
exactly when `e i ≤ 1`.  This is the identity Round III's objection said could
not exist; it exists because the reference word is fixed. -/
theorem Cw_shift (t e : Nat → Nat) :
    ∀ a : Nat, (∀ i : Nat, i < a → e i ≤ 1) →
      Cw (fun i => t i + e i) a = Cw t a + Csel t e a := by
  intro a
  induction a with
  | zero => intro _; rfl
  | succ a ih =>
    intro he
    have ih' := ih (fun i hi => he i (Nat.lt_succ_of_lt hi))
    have hlast : (2:Nat) ^ (t a + e a) = 2 ^ t a + e a * 2 ^ t a := by
      rcases Nat.lt_or_ge (e a) 1 with h | h
      · have : e a = 0 := by omega
        rw [this]; simp
      · have : e a = 1 := by have := he a (Nat.lt_succ_self a); omega
        rw [this, Nat.pow_succ]
        omega
    show Cw (fun i => t i + e i) (a + 1) = _
    rw [Cw_succ, Cw_succ, Csel_succ, ih']
    show 3 * (Cw t a + Csel t e a) + 2 ^ (t a + e a) = _
    rw [hlast]
    omega

/-- The perturbation is bounded by the reference accumulator, so a `{0,1}`
perturbation at most doubles `C`. -/
theorem Csel_le_Cw (t e : Nat → Nat) :
    ∀ a : Nat, (∀ i : Nat, i < a → e i ≤ 1) → Csel t e a ≤ Cw t a := by
  intro a
  induction a with
  | zero => intro _; exact Nat.le_refl _
  | succ a ih =>
    intro he
    have ih' := ih (fun i hi => he i (Nat.lt_succ_of_lt hi))
    have h1 : e a * 2 ^ t a ≤ 2 ^ t a := by
      have := he a (Nat.lt_succ_self a)
      calc e a * 2 ^ t a ≤ 1 * 2 ^ t a := Nat.mul_le_mul_right _ this
        _ = 2 ^ t a := by omega
    rw [Csel_succ, Cw_succ]
    omega

theorem Cw_shift_le_two_mul (t e : Nat → Nat) (a : Nat)
    (he : ∀ i : Nat, i < a → e i ≤ 1) :
    Cw (fun i => t i + e i) a ≤ 2 * Cw t a := by
  rw [Cw_shift t e a he]
  have := Csel_le_Cw t e a he
  omega

/-! ## Part 3.  The subset-sum lattice, abstractly -/

/-- `Σ_{i<a} e i · w i`: the subset sum of the weight vector `w` selected by `e`. -/
def ssum (w e : Nat → Nat) : Nat → Nat
  | 0 => 0
  | a + 1 => ssum w e a + e a * w a

/-- `Σ_{i<a} (k · w i) % G`: the ℓ¹-norm of the dual vector `k · w / G`, scaled by
`G`.  A flatness certificate is exactly a `k` making this small. -/
def msum (w : Nat → Nat) (k G : Nat) : Nat → Nat
  | 0 => 0
  | a + 1 => msum w k G a + (k * w a) % G

@[simp] theorem ssum_zero (w e : Nat → Nat) : ssum w e 0 = 0 := rfl
@[simp] theorem msum_zero (w : Nat → Nat) (k G : Nat) : msum w k G 0 = 0 := rfl

theorem ssum_succ (w e : Nat → Nat) (a : Nat) :
    ssum w e (a + 1) = ssum w e a + e a * w a := rfl

theorem msum_succ (w : Nat → Nat) (k G a : Nat) :
    msum w k G (a + 1) = msum w k G a + (k * w a) % G := rfl

theorem ssum_congr {w v e : Nat → Nat} :
    ∀ a : Nat, (∀ i : Nat, i < a → w i = v i) → ssum w e a = ssum v e a := by
  intro a
  induction a with
  | zero => intro _; rfl
  | succ a ih =>
    intro h
    rw [ssum_succ, ssum_succ, ih (fun i hi => h i (Nat.lt_succ_of_lt hi)),
      h a (Nat.lt_succ_self a)]

theorem ssum_scale (v e : Nat → Nat) (c : Nat) :
    ∀ a : Nat, ssum (fun i => c * v i) e a = c * ssum v e a := by
  intro a
  induction a with
  | zero => rfl
  | succ a ih => rw [ssum_succ, ssum_succ, ih, Nat.mul_add, Nat.mul_left_comm]

/-- `msum` is the selected sum with all selectors on. -/
theorem msum_eq_ssum (w : Nat → Nat) (k G : Nat) :
    ∀ a : Nat, msum w k G a = ssum (fun i => (k * w i) % G) (fun _ => 1) a := by
  intro a
  induction a with
  | zero => rfl
  | succ a ih => rw [msum_succ, ssum_succ, ih]; omega

theorem ssum_le_msum (w e : Nat → Nat) (k G : Nat) :
    ∀ a : Nat, (∀ i : Nat, i < a → e i ≤ 1) →
      ssum (fun i => (k * w i) % G) e a ≤ msum w k G a := by
  intro a
  induction a with
  | zero => intro _; exact Nat.le_refl _
  | succ a ih =>
    intro he
    have ih' := ih (fun i hi => he i (Nat.lt_succ_of_lt hi))
    have h1 : e a * ((k * w a) % G) ≤ (k * w a) % G := by
      have := he a (Nat.lt_succ_self a)
      calc e a * ((k * w a) % G) ≤ 1 * ((k * w a) % G) := Nat.mul_le_mul_right _ this
        _ = (k * w a) % G := by omega
    rw [ssum_succ, msum_succ]
    omega

theorem add_mod_left' (x y G : Nat) : (x % G + y) % G = (x + y) % G := by
  rw [Nat.add_mod x y G, Nat.add_mod (x % G) y G, Nat.mod_mod_of_dvd x (Nat.dvd_refl G)]

theorem add_mod_right' (x y G : Nat) : (x + y % G) % G = (x + y) % G := by
  rw [Nat.add_mod x y G, Nat.add_mod x (y % G) G, Nat.mod_mod_of_dvd y (Nat.dvd_refl G)]

/-- **The dual reduction.**  Multiplying a subset sum by `k` and reducing mod `G`
is the same as reducing each weight first — the statement that `k · w / G` is a
vector of the dual lattice. -/
theorem ssum_mul_mod (w e : Nat → Nat) (k G : Nat) :
    ∀ a : Nat, (∀ i : Nat, i < a → e i ≤ 1) →
      (k * ssum w e a) % G = (ssum (fun i => (k * w i) % G) e a) % G := by
  intro a
  induction a with
  | zero => intro _; rfl
  | succ a ih =>
    intro he
    have ih' := ih (fun i hi => he i (Nat.lt_succ_of_lt hi))
    have hexp : k * ssum w e (a + 1) = k * ssum w e a + e a * (k * w a) := by
      rw [ssum_succ, Nat.mul_add, Nat.mul_left_comm]
    rw [hexp, ssum_succ, Nat.add_mod (k * ssum w e a), ih']
    rcases Nat.lt_or_ge (e a) 1 with h | h
    · have h0 : e a = 0 := by omega
      rw [h0]
      simp
    · have h1 : e a = 1 := by have := he a (Nat.lt_succ_self a); omega
      rw [h1, Nat.one_mul, Nat.one_mul, add_mod_left']

/-! ## Part 4.  The flatness certificate, and what it costs -/

/-- **The certificate lemma.**  If some `k` makes the dual vector short —
`msum`, the scaled ℓ¹-norm of `k · w / G`, together with the offset residue
fitting strictly inside one period — then no `{0,1}` selection of the weights can
be added to `C₀` to reach a multiple of `G`.

This is the flatness theorem for the cube `{0,1}^a` against the lattice
`{z : ⟨w,z⟩ ≡ 0 mod G}`, with all the geometry removed. -/
theorem not_dvd_of_certificate {w e : Nat → Nat} {k G C0 a : Nat}
    (he : ∀ i : Nat, i < a → e i ≤ 1)
    (hq : 0 < (k * C0) % G)
    (hsmall : (k * C0) % G + msum w k G a < G) :
    ¬ (G ∣ (C0 + ssum w e a)) := by
  intro hdvd
  have hT : ssum (fun i => (k * w i) % G) e a ≤ msum w k G a := ssum_le_msum w e k G a he
  obtain ⟨c, hc⟩ := hdvd
  have hzero : (k * (C0 + ssum w e a)) % G = 0 := by
    rw [hc, ← Nat.mul_assoc, Nat.mul_comm k G, Nat.mul_assoc]
    exact Nat.mul_mod_right G (k * c)
  have hmm : ∀ x : Nat, x % G % G = x % G := fun x => Nat.mod_mod_of_dvd x (Nat.dvd_refl G)
  have h1 : (k * (C0 + ssum w e a)) % G
      = ((k * C0) % G + ssum (fun i => (k * w i) % G) e a) % G := by
    rw [Nat.mul_add, Nat.add_mod (k * C0), ssum_mul_mod w e k G a he, add_mod_right']
  have hlt : (k * C0) % G + ssum (fun i => (k * w i) % G) e a < G := by omega
  rw [Nat.mod_eq_of_lt hlt] at h1
  omega

/-! ## Part 5.  The certificate, instantiated on the accumulator -/

/-- The weight vector of the linearised accumulator at reference word `t`:
`wgt t a i = 3 ^ (a−1−i) · 2 ^ t i`. -/
def wgt (t : Nat → Nat) (a i : Nat) : Nat := 3 ^ (a - 1 - i) * 2 ^ t i

theorem wgt_shift {t : Nat → Nat} {a i : Nat} (h : i < a) :
    wgt t (a + 1) i = 3 * wgt t a i := by
  have hexp : a + 1 - 1 - i = (a - 1 - i) + 1 := by omega
  rw [wgt, wgt, hexp, Nat.pow_succ, Nat.mul_comm (3 ^ (a - 1 - i)) 3, Nat.mul_assoc]

theorem wgt_top (t : Nat → Nat) (a : Nat) : wgt t (a + 1) a = 2 ^ t a := by
  have h : a + 1 - 1 - a = 0 := by omega
  rw [wgt, h, Nat.pow_zero, Nat.one_mul]

/-- **The weights are an `S`-unit orbit.**  Consecutive weights differ by
`3 / 2 ^ gap`, so the dual vector `k · wgt / G` is the orbit of the single number
`k / G` under multiplication by units generated by `2` and `3`.  This is why the
certificate below is the S-unit obstruction in different clothing. -/
theorem wgt_step {t : Nat → Nat} {a i : Nat} (hi : i + 1 < a) (hle : t i ≤ t (i + 1)) :
    3 * wgt t a (i + 1) = 2 ^ (t (i + 1) - t i) * wgt t a i := by
  have hexp : a - 1 - i = (a - 1 - (i + 1)) + 1 := by omega
  have hsplit : t (i + 1) = (t (i + 1) - t i) + t i := by omega
  rw [wgt, wgt, hexp, Nat.pow_succ, hsplit, Nat.pow_add]
  simp [Nat.mul_comm, Nat.mul_left_comm, Nat.mul_assoc]

theorem Csel_eq_ssum (t e : Nat → Nat) :
    ∀ a : Nat, Csel t e a = ssum (wgt t a) e a := by
  intro a
  induction a with
  | zero => rfl
  | succ a ih =>
    have hcongr : ssum (wgt t (a + 1)) e a = ssum (fun i => 3 * wgt t a i) e a :=
      ssum_congr a (fun i hi => wgt_shift hi)
    rw [Csel_succ, ssum_succ, wgt_top, hcongr, ssum_scale, ih]

theorem Cw_eq_ssum (t : Nat → Nat) (a : Nat) :
    Cw t a = ssum (wgt t a) (fun _ => 1) a := by
  rw [Cw_eq_Csel_one t a, Csel_eq_ssum]

/-- **The certificate, on the accumulator.**  A single `k` whose dual vector is
short forbids every `{0,1}` perturbation of the reference word from producing a
multiple of `G`. -/
theorem not_dvd_Cw_shift {t e : Nat → Nat} {k G a : Nat}
    (he : ∀ i : Nat, i < a → e i ≤ 1)
    (hq : 0 < (k * Cw t a) % G)
    (hsmall : (k * Cw t a) % G + msum (wgt t a) k G a < G) :
    ¬ (G ∣ Cw (fun i => t i + e i) a) := by
  rw [Cw_shift t e a he, Csel_eq_ssum]
  exact not_dvd_of_certificate he hq hsmall

/-- **The certificate in its final, purely one-sided form.**  Because the
perturbations are `0` or `1`, the offset residue equals the dual ℓ¹-norm itself,
and the whole hypothesis collapses to `0 < msum` and `2 · msum < G`: the cube is
flat with respect to the lattice as soon as the dual vector is shorter than half
a period.  Exhaustive search over every `k < G` at the ledge pairs `a ≤ 20`
shows `msum / G ≥ 0.66` always, so the hypothesis is never satisfiable there. -/
theorem not_dvd_of_small {t e : Nat → Nat} {k G a : Nat}
    (he : ∀ i : Nat, i < a → e i ≤ 1)
    (hpos : 0 < msum (wgt t a) k G a)
    (hhalf : 2 * msum (wgt t a) k G a < G) :
    ¬ (G ∣ Cw (fun i => t i + e i) a) := by
  have hq : (k * Cw t a) % G = msum (wgt t a) k G a := by
    rw [Cw_eq_ssum, ssum_mul_mod _ _ _ _ a (fun i _ => Nat.le_refl 1), ← msum_eq_ssum]
    exact Nat.mod_eq_of_lt (by omega)
  have h2 : 0 < (k * Cw t a) % G := by rw [hq]; exact hpos
  have h3 : (k * Cw t a) % G + msum (wgt t a) k G a < G := by rw [hq]; omega
  exact not_dvd_Cw_shift he h2 h3

end LatticeGeometry
end Collatz
