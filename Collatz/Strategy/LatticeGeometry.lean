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

so the total slack is **less than `0.6 · a`, spread over `a` coordinates**: on
average each direction has `0.6` of one lattice spacing of room.  A convex body
of dimension `a` whose ℓ¹-radius from a vertex is `0.6 a` has volume at most
`(0.6 a) ^ a / a ! ≤ (0.6 e) ^ a = 1.632 ^ a < 2 ^ a`, so **Minkowski's convex
body theorem does not apply to it in any dimension** — the hypothesis
`vol ≥ 2 ^ a · det` fails by an exponential factor, and no amount of sharpening
recovers it, since the deficit is `(2 / 1.632) ^ a`.  Measured, in the reduced
coordinates where the body is full dimensional (`t₀` and `t₁` are pinned by the
box, so the a-dimensional volume is *exactly zero*): the lattice-point count and
the volume are
`a = 24`: `2.6 · 10 ^ 8` against `251.2`; `a = 48`: `6.7 · 10 ^ 18` against
`5.5 · 10 ^ 6`.  The ratio grows like `1.76 ^ a`.  So the count is **not** the
volume to leading order, in either direction, and the excess is exactly the
`(1 + 1/0.585) ^ a` that an `O(1)`-thick body always shows.  Geometry of numbers
adds nothing because its entire regime — lattice points equidistribute in a body
large compared with the covering radius — is never entered.

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
`a = 3..13`: `1.20, 0.851, 1.85, 1.08, 0.664, 1.40, 1.05, 1.83, 1.33, 0.781, 1.49`.
The threshold is `0.5` and it is never met — but the misses are by a factor of
only `1.3`–`3.7`, which is the same "as near as arithmetic allows" that every
other route reports.

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
  have h1 : (2:Nat) ^ fexp i ≤ 3 ^ i := fexp_le i
  have h2 : ((2:Nat) ^ fexp i) ^ 5 ≤ (3 ^ i) ^ 5 := Nat.pow_le_pow_left h1 5
  have h3 : ((3:Nat) ^ i) ^ 5 = 243 ^ i := by
    rw [← Nat.pow_mul, Nat.mul_comm, Nat.pow_mul]
    norm_num
  have h4 : (243:Nat) ^ i < 256 ^ i := Nat.pow_lt_pow_left (by decide) (by omega)
  have h5 : (256:Nat) ^ i = 2 ^ (8 * i) := by
    rw [Nat.mul_comm, Nat.pow_mul]
    norm_num
  have h6 : ((2:Nat) ^ fexp i) ^ 5 = 2 ^ (5 * fexp i) := by
    rw [Nat.mul_comm, Nat.pow_mul]
  have h7 : (2:Nat) ^ (5 * fexp i) < 2 ^ (8 * i) := by
    rw [← h6, ← h5]; omega
  by_contra hcon
  have : (2:Nat) ^ (8 * i) ≤ 2 ^ (5 * fexp i) :=
    Arith.two_pow_le_two_pow (by omega)
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
  | succ a ih => rw [ssum_succ, ssum_succ, ih]; ring

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
      rw [ssum_succ]; ring
    rw [hexp, ssum_succ, Nat.add_mod (k * ssum w e a), ih']
    rcases Nat.lt_or_ge (e a) 1 with h | h
    · have h0 : e a = 0 := by omega
      rw [h0]
      simp
    · have h1 : e a = 1 := by have := he a (Nat.lt_succ_self a); omega
      rw [h1, Nat.one_mul, Nat.one_mul, Nat.mod_mod_of_dvd _ (Nat.dvd_refl G),
        ← Nat.add_mod]

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
  have hzero : (k * (C0 + ssum w e a)) % G = 0 := by
    have : G ∣ k * (C0 + ssum w e a) := Dvd.dvd.mul_left hdvd k
    exact Nat.eq_zero_of_dvd_of_lt this |>.elim (fun _ => rfl) |>.elim
  sorry

end LatticeGeometry
end Collatz
