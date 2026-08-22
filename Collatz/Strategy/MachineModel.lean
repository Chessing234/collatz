import Collatz.Strategy.RealizableBound

/-!
# Machine models beyond finite automata, and the semilinear ceiling

Round IX, Agent L.  The repo's only devices are finite automata, and every one of
them is vacuous here for one reason: `OrderAutomaton.disc_append` makes the
discrepancy **additive** along the word, so the admissible language is a monoid
language.  This file asks what the *weakest* machine model is that actually sees
a Collatz trajectory, and then kills the entire tier of models that sit just
above finite automata.

## 1.  The honest model is a two-dimensional weighted automaton

Reading a parity word left to right and tracking the pair `(C, Q)` — accumulator
and denominator — the update is **linear over the semiring `(Nat, +, ·)`**:

      `true`  (odd step, `x ↦ 3x+1`) :  `(C, Q) ↦ (3C + Q, Q)`
      `false` (even step, `x ↦ x/2`) :  `(C, Q) ↦ (C, 2Q)`

so `C` is a *rational series of dimension 2*: `C w = ⟨(0,1) · M w, e₁⟩` for the
two 2×2 matrices above.  This is `acc`/`Cw` below.  Three facts pin the model:

* **dimension ≥ 2** (`C_not_multiplicative`): a one-dimensional rational series
  is a monoid homomorphism into `(Nat, ·)`, and `C` is not one — that is exactly
  the escape from `disc_append`;
* **the composition law is skew, not additive** (`C_append`):
  `C (u ++ v) = 3 ^ oc v * C u + 2 ^ zc u * C v`.  Taking logarithms does *not*
  linearise it, so `C` is genuinely outside the additive/monoid class.
  *Credit where due:* this cocycle law is **already** in the development as
  `ImageDensity.wC_append`, in the Terras encoding.  Part A is therefore a
  re-presentation (`Cw_even_letter`/`Cw_odd_letter` are the bridge), not new
  mathematics; the new content of this file is Parts B and C;
* **`C` is not a function of the Parikh image** (`C_not_parikh`): two words of
  the same length with the same number of odd steps have different `C`.

The third point is the one that decides the round.  Parikh's theorem sees only
the commutative image `(L, a)` of a word.  The cycle condition is `G ∣ C` with
`G = 2^L − 3^a` a function of `(L, a)` — but `C` is *not*, so the Parikh image of
the cycle language discards precisely the coordinate that carries the condition.
Any semilinearity statement about `(L, a)` is therefore a statement about the
*ledge*, not about the language.

## 2.  The ledge is not semilinear — so the whole semilinear tier is dead

`Ledge L a := 3^a < 2^L ∧ 2^L ≤ 2·3^a`, i.e. `L = fexp a + 1`
(`ledge_iff_fexp`), is the set of `(L, a)` pairs a cycle may occupy
(`GapSandwich.cycle_length_determined`).  The main theorem here:

`ledge_not_semilinear` : the ledge is **not** a finite union of linear sets.

The proof is `no_arith_progression`: `fexp` is never exactly arithmetic along an
arithmetic progression of `a`, because that would force `3 ^ p = 2 ^ q`.  This is
irrationality of `log₂ 3` in the only form the kernel needs, and it is proved by
parity (`two_pow_ne_three_pow`) plus a Bernoulli growth estimate (`bern`).

By **Parikh's theorem** every context-free language has a semilinear Parikh
image.  So no context-free grammar, no pushdown automaton, no reversal-bounded
counter machine, no Parikh automaton and no one-counter machine generates the
heavy language or the ledge language: the tier immediately above finite automata
is closed, and closed for a *positive* reason (irrationality of `log₂ 3`) rather
than by the entropy count that closed the finite-state tier.

## 3.  The adversarial reading, recorded because it matters

Applying a context-free **pumping lemma** to the *cycle* language is worse than
hard, it points the wrong way.  If the Collatz cycle conjecture is true the cycle
language is a single word, hence finite, hence regular, hence context-free.  So
any proof that the cycle language is *not* context-free would prove the language
infinite — i.e. would **refute** the conjecture.  The non-context-freeness proved
here is therefore deliberately about the *heavy* language and the *ledge*, which
are unconditionally infinite, and it says nothing about cycles.  See the report.

## Soundness filter

Everything in this file is `d`-free.  That is legitimate because every result is
**negative**: it rules out a `d`-free class of devices.  `Ledge` is stated for
the gap `2^L − 3^a` of `3x+1`; the same statement holds verbatim for `3x+d`, and
the theorem is a non-existence theorem about machine models, so no asset is
consumed and none is needed.
-/

namespace Collatz
namespace MachineModel

open RealizableBound

/-! ## Part A.  The weighted automaton -/

/-- Number of odd (`true`) letters. -/
def oc : List Bool → Nat
  | [] => 0
  | b :: w => (if b then 1 else 0) + oc w

/-- Number of even (`false`) letters. -/
def zc : List Bool → Nat
  | [] => 0
  | b :: w => (if b then 0 else 1) + zc w

/-- One letter of the weighted automaton acting on the state `(C, Q)`. -/
def step (s : Nat × Nat) (b : Bool) : Nat × Nat :=
  if b then (3 * s.1 + s.2, s.2) else (s.1, 2 * s.2)

/-- Run the automaton from a state. -/
def run (s : Nat × Nat) : List Bool → Nat × Nat
  | [] => s
  | b :: w => run (step s b) w

/-- The accumulator run, from the initial state `(0, 1)`. -/
def acc (w : List Bool) : Nat × Nat := run (0, 1) w

/-- The accumulator `C` of a word: the numerator produced by reading it. -/
def Cw (w : List Bool) : Nat := (acc w).1

@[simp] theorem run_nil (s : Nat × Nat) : run s [] = s := rfl

theorem run_append : ∀ (u v : List Bool) (s : Nat × Nat),
    run s (u ++ v) = run (run s u) v := by
  intro u
  induction u with
  | nil => intro v s; rfl
  | cons b u ih => intro v s; simp only [List.cons_append, run]; exact ih v (step s b)

/-- **Linearity of the run.**  The state map of a word is an affine map of the
initial accumulator with multiplier `3 ^ oc` and additive term scaled by the
initial denominator.  This is the linear representation of the rational series. -/
theorem run_linear : ∀ (w : List Bool) (c q : Nat),
    run (c, q) w = (3 ^ oc w * c + q * Cw w, q * 2 ^ zc w) := by
  intro w
  induction w with
  | nil => intro c q; simp [Cw, acc, oc, zc]
  | cons b w ih =>
      intro c q
      cases b with
      | true =>
          have h1 : run (c, q) (true :: w) = run (3 * c + q, q) w := rfl
          have h2 : Cw (true :: w) = 3 ^ oc w * 1 + 1 * Cw w := by
            have : acc (true :: w) = run (1, 1) w := rfl
            rw [Cw, this, ih 1 1]
          have hoc : oc (true :: w) = oc w + 1 := by simp [oc]; omega
          rw [h1, ih (3 * c + q) q, h2, hoc]
          have e : 3 ^ (oc w + 1) * c + q * (3 ^ oc w * 1 + 1 * Cw w)
                 = 3 ^ oc w * (3 * c + q) + q * Cw w := by
            rw [Nat.pow_succ]
            have : 3 ^ oc w * (3 * c + q) = 3 ^ oc w * 3 * c + 3 ^ oc w * q := by
              rw [Nat.mul_add, Nat.mul_assoc]
            rw [this]
            have hq : q * (3 ^ oc w * 1 + 1 * Cw w) = 3 ^ oc w * q + q * Cw w := by
              rw [Nat.mul_add, Nat.mul_one, Nat.one_mul, Nat.mul_comm q (3 ^ oc w)]
            rw [hq]
            omega
          have hzc : zc (true :: w) = zc w := by simp [zc]
          rw [hzc]
          exact Prod.ext (by simpa using e.symm) rfl
      | false =>
          have h1 : run (c, q) (false :: w) = run (c, 2 * q) w := rfl
          have h2 : Cw (false :: w) = 2 * Cw w := by
            have hr : acc (false :: w) = run (0, 2) w := rfl
            rw [Cw, hr, ih 0 2]
            simp [Cw, acc]
          have hoc : oc (false :: w) = oc w := by simp [oc]
          have hzc : zc (false :: w) = zc w + 1 := by simp [zc]; omega
          rw [h1, ih c (2 * q), h2, hoc, hzc]
          simp only [Prod.mk.injEq]
          refine ⟨?_, ?_⟩
          · rw [Nat.mul_assoc, Nat.mul_left_comm]
          · rw [Nat.pow_succ, Nat.mul_assoc, Nat.mul_left_comm, Nat.mul_comm (2 ^ zc w) 2]

/-- The denominator coordinate of the accumulator is `2 ^ zc`. -/
theorem acc_snd (w : List Bool) : (acc w).2 = 2 ^ zc w := by
  have := run_linear w 0 1
  rw [acc, this]
  simp

/-- **The composition law: skew, not additive.**  This is the exact sense in
which the weighted model escapes `OrderAutomaton.disc_append`.  The discrepancy
satisfies `disc (u ++ v) = disc u + disc v`; the accumulator satisfies a
*crossed* law whose coefficients depend on the two factors, and no change of
variable turns it into a homomorphism. -/
theorem C_append (u v : List Bool) :
    Cw (u ++ v) = 3 ^ oc v * Cw u + 2 ^ zc u * Cw v := by
  have h : acc (u ++ v) = run (acc u) v := by
    rw [acc, acc, run_append]
  have hu : acc u = (Cw u, 2 ^ zc u) := by
    have := acc_snd u
    exact Prod.ext rfl (by simpa using this)
  rw [Cw, h, hu, run_linear]

/-! ### Bridge to the repo's accumulator

`RepetitionDescent.wC` uses the Terras encoding, one letter per `T`-step:
`wC (b :: t) = (if b = 1 then 3 ^ ones t else 0) + 2 * wC t`.  Translating an odd
letter to `true :: false` and an even letter to `false` turns that recursion into
the two corollaries below, so the weighted automaton computes *exactly* the
accumulator the rest of the development uses — it is a new *presentation* of `C`,
not a new quantity. -/

/-- An even Terras letter doubles the accumulator. -/
theorem Cw_even_letter (w : List Bool) : Cw (false :: w) = 2 * Cw w := by
  have h := C_append [false] w
  simpa [Cw, acc, run, step, oc, zc] using h

/-- An odd Terras letter (`true :: false`) reproduces `wC_cons`. -/
theorem Cw_odd_letter (w : List Bool) :
    Cw (true :: false :: w) = 3 ^ oc w + 2 * Cw w := by
  have h := C_append [true, false] w
  simpa [Cw, acc, run, step, oc, zc] using h

/-- `C` of the empty word is `0`, of `[true]` is `1`, of `[true, true]` is `4`.
Hence `C` is not multiplicative, so the rational series has dimension `≥ 2`:
a one-dimensional representation would make `C` a monoid homomorphism into
`(Nat, ·)`, which is the dead additive case in logarithmic form. -/
theorem C_not_multiplicative :
    Cw [] = 0 ∧ Cw [true] = 1 ∧ Cw [true, true] = 4 ∧
      Cw [true, true] ≠ Cw [true] * Cw [true] := by
  refine ⟨rfl, rfl, rfl, by decide⟩

/-- **`C` is not a function of the Parikh image.**  Two words of equal length
and equal odd-count with different accumulators.  Since `G = 2^L − 3^a` *is* a
function of `(L, a)`, the commutative image of the cycle language throws away
exactly the coordinate in which the cycle condition `G ∣ C` lives. -/
theorem C_not_parikh :
    ([true, false].length = [false, true].length) ∧
      oc [true, false] = oc [false, true] ∧
      Cw [true, false] ≠ Cw [false, true] := by
  refine ⟨rfl, rfl, by decide⟩

/-! ## Part B.  Growth, and the irrationality the kernel can see -/

/-- Every power of three is odd. -/
theorem three_pow_odd : ∀ p : Nat, 3 ^ p % 2 = 1 := by
  intro p
  induction p with
  | zero => decide
  | succ n ih =>
      have e : (3:Nat) ^ (n + 1) = 3 * 3 ^ n := Arith.three_pow_succ n
      omega

/-- Powers of two and powers of three never agree at a positive exponent. -/
theorem two_pow_ne_three_pow (p q : Nat) (hp : 1 ≤ p) : 2 ^ q ≠ 3 ^ p := by
  intro h
  cases q with
  | zero =>
      have h3 : (3:Nat) ^ 1 ≤ 3 ^ p := Arith.three_pow_le_three_pow hp
      simp at h3
      omega
  | succ q =>
      have he : (2:Nat) ^ (q + 1) = 2 * 2 ^ q := Arith.two_pow_succ q
      have hodd : 3 ^ p % 2 = 1 := three_pow_odd p
      omega

/-- **Bernoulli in `Nat`.**  If `A ≥ B + 1 ≥ 2` then `A ^ k` beats `B ^ k` by a
factor growing linearly in `k`.  This is the only growth input needed. -/
theorem bern (A B : Nat) (_hB : 1 ≤ B) (hA : B + 1 ≤ A) :
    ∀ k, B ^ k * (B + k) ≤ B * A ^ k := by
  intro k
  induction k with
  | zero => simp
  | succ k ih =>
      have hstep : B ^ k * (B + k) * (B + 1) ≤ B * A ^ k * A := by
        have h1 : B ^ k * (B + k) * (B + 1) ≤ B * A ^ k * (B + 1) :=
          Nat.mul_le_mul_right _ ih
        have h2 : B * A ^ k * (B + 1) ≤ B * A ^ k * A := Nat.mul_le_mul_left _ hA
        exact Nat.le_trans h1 h2
      have hinner : B * (B + (k + 1)) ≤ (B + k) * (B + 1) := by
        have e1 : (B + k) * (B + 1) = B * B + B * k + B + k := by
          rw [Nat.add_mul, Nat.mul_add, Nat.mul_add, Nat.mul_one, Nat.mul_one,
              Nat.mul_comm k B]
          omega
        have e2 : B * (B + (k + 1)) = B * B + B * k + B := by
          rw [Nat.mul_add, Nat.mul_add, Nat.mul_one]
          omega
        omega
      have hgoal : B ^ (k + 1) * (B + (k + 1)) ≤ B ^ k * (B + k) * (B + 1) := by
        have e : B ^ (k + 1) * (B + (k + 1)) = B ^ k * (B * (B + (k + 1))) := by
          rw [Nat.pow_succ, Nat.mul_assoc]
        rw [e, Nat.mul_assoc]
        exact Nat.mul_le_mul_left _ hinner
      have e : B * A ^ (k + 1) = B * A ^ k * A := by
        rw [Nat.pow_succ, Nat.mul_assoc]
      rw [e]
      exact Nat.le_trans hgoal hstep

/-- **The growth contradiction.**  A ratio that is bounded along all powers
forces the two bases to agree; here they cannot, so the hypothesis is absurd. -/
theorem growth_absurd (A B u v : Nat) (hB : 1 ≤ B) (hA : B + 1 ≤ A) (hu : 1 ≤ u)
    (h : ∀ k, u * A ^ k ≤ v * B ^ k) : False := by
  have key : ∀ k, u * (B + k) ≤ v * B := by
    intro k
    have h1 : u * (B ^ k * (B + k)) ≤ u * (B * A ^ k) :=
      Nat.mul_le_mul_left _ (bern A B hB hA k)
    have h2 : u * (B * A ^ k) ≤ B * (v * B ^ k) := by
      have : B * (u * A ^ k) ≤ B * (v * B ^ k) := Nat.mul_le_mul_left _ (h k)
      have e : u * (B * A ^ k) = B * (u * A ^ k) := by
        rw [Nat.mul_comm u (B * A ^ k), Nat.mul_assoc, Nat.mul_comm (A ^ k) u]
      rw [e]; exact this
    have h3 : (u * (B + k)) * B ^ k ≤ (v * B) * B ^ k := by
      have el : (u * (B + k)) * B ^ k = u * (B ^ k * (B + k)) := by
        rw [Nat.mul_assoc, Nat.mul_comm (B + k) (B ^ k)]
      have er : (v * B) * B ^ k = B * (v * B ^ k) := by
        rw [Nat.mul_assoc, Nat.mul_left_comm]
      rw [el, er]
      exact Nat.le_trans h1 h2
    have hpos : 0 < B ^ k := Nat.pow_pos (by omega)
    exact Nat.le_of_mul_le_mul_right h3 hpos
  have := key (v * B)
  have hge : B + v * B ≤ u * (B + v * B) := Nat.le_mul_of_pos_left _ hu
  omega

/-! ## Part C.  `fexp` is never arithmetic, and the ledge is not semilinear -/

/-- **The core theorem.**  `fexp` — the Beatty sequence `⌊a·log₂3⌋` — is never
exactly arithmetic along an arithmetic progression of `a`.  This is irrationality
of `log₂ 3` in the only form the ledge needs, and it is what kills every model
whose Parikh images are semilinear. -/
theorem no_arith_progression (a₀ p f₀ q : Nat) (hp : 1 ≤ p)
    (h : ∀ k, fexp (a₀ + k * p) = f₀ + k * q) : False := by
  have hspec := fexp_spec
  have hpow3 : ∀ k : Nat, (3:Nat) ^ (a₀ + k * p) = 3 ^ a₀ * (3 ^ p) ^ k := by
    intro k
    rw [Nat.pow_add, Nat.mul_comm k p, Nat.pow_mul]
  have hpow2 : ∀ (c k : Nat), (2:Nat) ^ (c + k * q) = 2 ^ c * (2 ^ q) ^ k := by
    intro c k
    rw [Nat.pow_add, Nat.mul_comm k q, Nat.pow_mul]
  rcases Nat.lt_trichotomy (3 ^ p) (2 ^ q) with hlt | heq | hgt
  · -- `2 ^ q` is the bigger base: use the lower half of `fexp_spec`
    refine growth_absurd (2 ^ q) (3 ^ p) (2 ^ f₀) (3 ^ a₀)
      (Arith.one_le_three_pow p) (by omega) (Arith.one_le_two_pow f₀) ?_
    intro k
    have hk := (hspec (a₀ + k * p)).1
    rw [h k] at hk
    have e2 : (2:Nat) ^ (f₀ + k * q) = 2 ^ f₀ * (2 ^ q) ^ k := hpow2 f₀ k
    rw [e2, hpow3 k] at hk
    exact hk
  · exact two_pow_ne_three_pow p q hp heq.symm
  · -- `3 ^ p` is the bigger base: use the upper half of `fexp_spec`
    refine growth_absurd (3 ^ p) (2 ^ q) (3 ^ a₀) (2 ^ (f₀ + 1))
      (Arith.one_le_two_pow q) (by omega) (Arith.one_le_three_pow a₀) ?_
    intro k
    have hk := (hspec (a₀ + k * p)).2
    rw [h k] at hk
    have e2 : (2:Nat) ^ (f₀ + k * q + 1) = 2 ^ (f₀ + 1) * (2 ^ q) ^ k := by
      have : f₀ + k * q + 1 = (f₀ + 1) + k * q := by omega
      rw [this, hpow2 (f₀ + 1) k]
    rw [e2, hpow3 k] at hk
    omega

/-- The ledge: the one-dimensional set of `(L, a)` pairs a cycle may occupy. -/
def Ledge (L a : Nat) : Prop := 3 ^ a < 2 ^ L ∧ 2 ^ L ≤ 2 * 3 ^ a

/-- Every `a` sits on the ledge at exactly `L = fexp a + 1`. -/
theorem ledge_fexp (a : Nat) : Ledge (fexp a + 1) a := by
  obtain ⟨h1, h2⟩ := fexp_spec a
  refine ⟨h2, ?_⟩
  have e : (2:Nat) ^ (fexp a + 1) = 2 * 2 ^ fexp a := Arith.two_pow_succ _
  omega

/-- …and only there. -/
theorem ledge_iff_fexp {L a : Nat} (h : Ledge L a) : L = fexp a + 1 := by
  obtain ⟨h1, h2⟩ := h
  obtain ⟨g1, g2⟩ := fexp_spec a
  have hlow : fexp a < L := by
    rcases Nat.lt_or_ge (fexp a) L with hc | hc
    · exact hc
    · have : (2:Nat) ^ L ≤ 2 ^ fexp a := Arith.two_pow_le_two_pow hc
      omega
  have hhigh : L < fexp a + 2 := by
    rcases Nat.lt_or_ge L (fexp a + 2) with hc | hc
    · exact hc
    · have hle : (2:Nat) ^ (fexp a + 2) ≤ 2 ^ L := Arith.two_pow_le_two_pow hc
      have e : (2:Nat) ^ (fexp a + 2) = 2 * 2 ^ (fexp a + 1) := Arith.two_pow_succ _
      omega
  omega

/-- A point of `Nat × Nat`. -/
abbrev Pt := Nat × Nat

/-- Membership in the linear set with base `b` and period list `ps`. -/
inductive InLin (b : Pt) (ps : List Pt) : Pt → Prop
  | base : InLin b ps b
  | step {p x} : p ∈ ps → InLin b ps x → InLin b ps (x.1 + p.1, x.2 + p.2)

/-- A semilinear set is a finite union of linear sets. -/
def Semilinear (S : Pt → Prop) : Prop :=
  ∃ cs : List (Pt × List Pt), ∀ x, S x ↔ ∃ c ∈ cs, InLin c.1 c.2 x

/-- The `k`-fold translate by a single period stays in the linear set. -/
theorem inLin_iterate {b : Pt} {ps : List Pt} {p : Pt} (hp : p ∈ ps) :
    ∀ k : Nat, InLin b ps (b.1 + k * p.1, b.2 + k * p.2) := by
  intro k
  induction k with
  | zero => simpa using InLin.base
  | succ k ih =>
      have := InLin.step (b := b) (ps := ps) hp ih
      have e1 : b.1 + k * p.1 + p.1 = b.1 + (k + 1) * p.1 := by
        rw [Nat.succ_mul]; omega
      have e2 : b.2 + k * p.2 + p.2 = b.2 + (k + 1) * p.2 := by
        rw [Nat.succ_mul]; omega
      simpa [e1, e2] using this

/-- If every period is zero, the linear set is the single base point. -/
theorem inLin_trivial {b : Pt} {ps : List Pt} (h : ∀ p ∈ ps, p = ((0:Nat), (0:Nat)))
    {x : Pt} (hx : InLin b ps x) : x = b := by
  induction hx with
  | base => rfl
  | step hp _ ih =>
      have := h _ hp
      subst this
      simpa using ih

/-- **No nontrivial arithmetic progression lies on the ledge.** -/
theorem ledge_no_progression (b p : Pt) (hp : p ≠ ((0:Nat), (0:Nat)))
    (h : ∀ k : Nat, Ledge (b.1 + k * p.1) (b.2 + k * p.2)) : False := by
  by_cases hpa : p.2 = 0
  · -- the `a` coordinate is constant, so `L` is forced constant, so `p.1 = 0`
    have h0 := ledge_iff_fexp (h 0)
    have h1 := ledge_iff_fexp (h 1)
    simp [hpa] at h0 h1
    have : p.1 = 0 := by omega
    exact hp (Prod.ext this hpa)
  · have hpa' : 1 ≤ p.2 := by omega
    have key : ∀ k : Nat, fexp (b.2 + k * p.2) = (b.1 - 1) + k * p.1 := by
      intro k
      have hk := ledge_iff_fexp (h k)
      have h0 := ledge_iff_fexp (h 0)
      simp at h0
      omega
    exact no_arith_progression b.2 p.2 (b.1 - 1) p.1 hpa' key

/-- The `a`-coordinates of a list of bases are bounded by their sum. -/
def sumSnd : List (Pt × List Pt) → Nat
  | [] => 0
  | c :: cs => c.1.2 + sumSnd cs

theorem sumSnd_bound : ∀ (cs : List (Pt × List Pt)) (c : Pt × List Pt),
    c ∈ cs → c.1.2 ≤ sumSnd cs := by
  intro cs
  induction cs with
  | nil => intro c hc; cases hc
  | cons d cs ih =>
      intro c hc
      rcases List.mem_cons.mp hc with h | h
      · subst h; simp [sumSnd]
      · have := ih c h; simp [sumSnd]; omega

/-- **THE THEOREM.**  The ledge is not semilinear.  By Parikh's theorem the
Parikh image of every context-free language is semilinear, so no context-free
grammar, pushdown automaton, one-counter machine, reversal-bounded counter
machine or Parikh automaton has the ledge as its commutative image.  The tier of
machine models immediately above finite automata is closed. -/
theorem ledge_not_semilinear : ¬ Semilinear (fun x : Pt => Ledge x.1 x.2) := by
  rintro ⟨cs, hcs⟩
  -- every period of every component must be zero
  have hzero : ∀ c ∈ cs, ∀ p ∈ c.2, p = ((0:Nat), (0:Nat)) := by
    intro c hc p hp
    rcases Classical.em (p = ((0:Nat), (0:Nat))) with hq | hq
    · exact hq
    · exact (ledge_no_progression c.1 p hq
        (fun k => (hcs _).mpr ⟨c, hc, inLin_iterate hp k⟩)).elim
  -- so the ledge is contained in the finite set of bases
  have hbnd : ∀ a : Nat, a ≤ sumSnd cs := by
    intro a
    have hL : Ledge (fexp a + 1) a := ledge_fexp a
    obtain ⟨c, hc, hx⟩ := (hcs (fexp a + 1, a)).mp hL
    have := inLin_trivial (hzero c hc) hx
    have ha : a = c.1.2 := congrArg Prod.snd this
    have := sumSnd_bound cs c hc
    omega
  have := hbnd (sumSnd cs + 1)
  omega

end MachineModel
end Collatz
