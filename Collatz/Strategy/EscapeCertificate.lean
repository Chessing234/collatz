import Collatz.Strategy.Escape
import Collatz.Strategy.NoFiniteRanking
import Collatz.Core.Minimum

/-!
# Round X, Sections VII–IX — termination certificates for escape dynamics

The brief: build a *divergence-half* filter, attacking **well-foundedness** rather
than recurrence, since a graph can have no cycles and still have infinite paths.
This file carries out that attack over the three standard termination
frameworks — ranking functions into rich well-founded orders, well-quasi-orders
(the WSTS toolkit), and size-change termination — and each one closes.  The
closures are sharp enough to name what is missing, which is the deliverable.

## The four results

**VII — the rank-target collapse.**  `rank_target_collapses`: for a
*deterministic unary* system on `ℕ`, a ranking certificate valued in an arbitrary
relation with no infinite descending chain exists **iff** one valued in `(ℕ, <)`
exists, and `rank_iff_halting` shows both are equivalent to "every orbit halts".
So lexicographic products, ordinal notations, multiset orders, tree embeddings
and matrix orders — every richer target `W` — buy exactly nothing.  A transfinite
rank pays off only when the transition relation **branches**; here the descending
chain a rank produces *is* the orbit, whose length is already a natural number.
`collatz_iff_rank` is the instance: producing any well-founded ranking for the
Collatz step map is the whole conjecture, not a step toward it.  **A ranking is
therefore never a half-filter** — it refutes cycles and divergence in one stroke,
which is precisely why the first objective of the round is unreachable as stated.

**VIII.1 — the WQO family is refuted outright.**  The divergence half is
literally "every orbit contains a repetition" (`Complexity.DivergenceHalf`), which
is a Ramsey-flavoured finiteness statement, not a well-foundedness one — so the
natural framework is well-quasi-orders and well-structured transition systems.
`no_wqo_divergence_filter` kills it: the principle *a monotone map on a
well-quasi-ordered state space has bounded orbits* is **false**, witnessed by the
successor map on `(ℕ, ≤)`, which is a WQO (`nat_le_wqo`) and for which successor
is strictly monotone and injective (`no_strict_wqo_divergence_filter`).  Dickson,
Higman and Kruskal deliver a **good pair** `x_i ⊑ x_j`; the divergence half needs
an **equality** `x_i = x_j`.  The gap between `⊑` and `=` is the whole content,
and no choice of WQO closes it.

**VIII.2 — size-change termination is vacuous over the mixed abstraction.**
`mixed_block_self_loop` produces, for every pair of moduli `2 ^ k, 3 ^ l` and
every block length `L`, a genuine `n > 1` whose next `L` states are *at every
intermediate time* congruent to `n` at both moduli **and** strictly larger than
`n`.  This strengthens `TransitionInvariant.exists_congruent_step` twice over:
from one step to a block of any length, and from congruence coordinates alone to
congruence coordinates together with magnitude coordinates — which is exactly the
coordinate list the brief asks for (`log₂ x`, `v₂`, `v₃`, odd-step count, residue
complexity, distance to a scale boundary).  `no_mixed_block_descent` and
`no_mixed_sct` draw the conclusion: no size-change, lexicographic, multiphase or
disjunctive certificate over such coordinates has a strict arc.

**IX — the record ladder, and the trichotomy that closes it.**  The one genuinely
asymptotic object available on the divergence half is the **record ladder**
`orbitMax n i`: it is non-decreasing, unbounded exactly when the orbit is
(`records_unbounded`), every rung is an actual orbit value
(`orbitMax_attained`), and it is *finite* on the cycle half — so it is not a
cycle-detector in disguise.  Reading the three natural kinds of size parameter
against it gives a complete kill:

| coordinate kind | verdict | theorem |
|---|---|---|
| congruence-definable | frozen along an arbitrarily long genuine block | `mixed_block_self_loop` |
| monotone in magnitude | strictly **increasing** along that same block | `no_mixed_block_descent` |
| anti-monotone in magnitude | eventually **constant** on the record ladder | `antitone_family_freezes` |

`no_antitone_certificate_on_divergent` assembles the third: past a finite index,
no anti-monotone coordinate ever strictly decreases again, while the ladder keeps
rising without bound.  A size-change certificate needs infinitely many strict arcs
on every infinite run; none of the three kinds can supply them.

The one *positive* theorem is `divergent_record_steps_odd`: along a divergent
orbit, for every `N` there is `i ≥ N` at which the running maximum jumps, the
orbit strictly grows, and the orbit value is **odd**.  The record ladder of a
divergent orbit is carried by odd steps, for ever.  Proved from unboundedness,
positivity and "the even branch halves" alone.

## The certificate shape the divergence half actually admits

`barrier_complete`: the orbit of `n` is bounded **iff** there is a bounded
inductive invariant — a set containing `n`, closed under the step map, contained
in a finite initial segment.  That is a *safety* certificate; there is no
well-foundedness anywhere in it, and the canonical one is the reachable set.

Put beside `rank_iff_halting`, this is the structural diagnosis the round asked
for:

> **The divergence half is a safety property and wants an invariant; a ranking
> certificate is sound *and complete* for the whole conjecture, so it can never
> isolate a half.  Termination machinery is liveness machinery.  That is why a
> repository this good at "no finite mechanism supports a cycle" has nothing
> aimed at "no orbit escapes".**

## Non-circularity

Everything in Sections VII and VIII.1 is proved for an **arbitrary** `f : ℕ → ℕ`
and never mentions the Collatz map, so no direction can be smuggling the
conjecture.  Section VIII.2 uses only `NoFiniteRanking`'s returning family.
Section IX uses only determinism, positivity of the orbit, and the fact that the
even branch halves.  The named independent principles are: well-founded induction
(VII), Dickson/Higman/Kruskal and the WSTS compatibility theorem (VIII.1), the
Lee–Jones–Ben-Amram size-change theorem and Podelski–Rybalchenko disjunctive
well-foundedness (VIII.2), and the least-element principle (IX).

**A caution recorded honestly.**  `barrier_complete` is *complete* for the
divergence half and therefore, on its own, **fails the round's non-circularity
test**: "exhibit a bounded inductive invariant" is a restatement of "the orbit is
bounded", so step (1) of the test would read "because divergence means...".  It is
recorded here as a *shape* theorem — it says what a divergence-half certificate
must look like — not as a filter.  No filter is claimed in this file.
-/

namespace Collatz
namespace EscapeCertificate

/-! ## Section VII.0 — abstract iteration -/

/-- Iteration of an arbitrary `f : Nat → Nat`. -/
def iter (f : Nat → Nat) : Nat → Nat → Nat
  | 0, x => x
  | k + 1, x => iter f k (f x)

@[simp] theorem iter_zero (f : Nat → Nat) (x : Nat) : iter f 0 x = x := rfl

@[simp] theorem iter_succ (f : Nat → Nat) (k x : Nat) :
    iter f (k + 1) x = iter f k (f x) := rfl

/-- Peeling the *last* step instead of the first. -/
theorem iter_succ' (f : Nat → Nat) (k x : Nat) :
    iter f (k + 1) x = f (iter f k x) := by
  induction k generalizing x with
  | zero => rfl
  | succ k ih => rw [iter_succ, ih (f x)]; rfl

/-! ## Section VII.1 — well-foundedness without `Acc` or choice -/

/-- `lt` admits **no infinite descending chain**.  This is the choice-free
rendering of well-foundedness, and it is all a ranking certificate ever supplies. -/
def NoDesc {W : Type} (lt : W → W → Prop) : Prop :=
  ¬ ∃ g : Nat → W, ∀ i : Nat, lt (g (i + 1)) (g i)

/-- Accessibility forbids a descending chain through the point. -/
theorem acc_no_desc {W : Type} {lt : W → W → Prop} {g : Nat → W}
    (hg : ∀ i : Nat, lt (g (i + 1)) (g i)) :
    ∀ w : W, Acc lt w → ∀ i : Nat, g i ≠ w := by
  intro w hw
  induction hw with
  | intro y _ ih =>
    intro i hi
    subst hi
    exact ih (g (i + 1)) (hg i) (i + 1) rfl

/-- A relation all of whose points are accessible has no infinite descending
chain. -/
theorem noDesc_of_acc {W : Type} {lt : W → W → Prop} (h : ∀ w : W, Acc lt w) :
    NoDesc lt := by
  intro hex
  obtain ⟨g, hg⟩ := hex
  exact acc_no_desc hg (g 0) (h (g 0)) 0 rfl

/-- There is no strictly decreasing sequence of naturals. -/
theorem no_nat_desc (g : Nat → Nat) (h : ∀ i : Nat, g (i + 1) < g i) : False := by
  have key : ∀ i : Nat, g i + i ≤ g 0 := by
    intro i
    induction i with
    | zero => omega
    | succ i ih => have := h i; omega
  have := key (g 0 + 1)
  omega

/-- `<` on `Nat` is well-founded in the `NoDesc` sense. -/
theorem noDesc_nat_lt : NoDesc (fun a b : Nat => a < b) := by
  intro hex
  obtain ⟨g, hg⟩ := hex
  exact no_nat_desc g hg


/-! ## Section VII.2 — the ranking certificate, and its collapse -/

/-- A **ranking certificate** for the system `(f, P)`: a map `R` into `(W, lt)`
that strictly decreases at every state still satisfying the "not yet halted"
predicate `P`. -/
def Ranking (f : Nat → Nat) (P : Nat → Prop) {W : Type} (lt : W → W → Prop)
    (R : Nat → W) : Prop :=
  ∀ x : Nat, P x → lt (R (f x)) (R x)

/-- The orbit of `x` leaves `P` at some finite time. -/
def Halts (f : Nat → Nat) (P : Nat → Prop) (x : Nat) : Prop :=
  ∃ n : Nat, ¬ P (iter f n x)

/-- **Soundness.**  Any ranking certificate, valued in any relation with no
infinite descending chain, forces every orbit to halt. -/
theorem halts_of_ranking {W : Type} {lt : W → W → Prop} (hwf : NoDesc lt)
    {f : Nat → Nat} {P : Nat → Prop} {R : Nat → W} (hR : Ranking f P lt R)
    (x : Nat) : Halts f P x := by
  by_cases h : Halts f P x
  · exact h
  · exfalso
    have hall : ∀ n : Nat, P (iter f n x) := by
      intro n
      by_cases hp : P (iter f n x)
      · exact hp
      · exact absurd ⟨n, hp⟩ h
    refine hwf ⟨fun i => R (iter f i x), fun i => ?_⟩
    have hstep := hR (iter f i x) (hall i)
    show lt (R (iter f (i + 1) x)) (R (iter f i x))
    rw [iter_succ' f i x]
    exact hstep

/-- The one-step-backwards relation: `a` is the successor of `b`, and `b` has not
halted.  Descending chains for it are exactly forward orbits. -/
def backStep (f : Nat → Nat) (P : Nat → Prop) : Nat → Nat → Prop :=
  fun a b => P b ∧ a = f b

/-- A halting orbit makes its start accessible for `backStep`. -/
theorem acc_backStep_of_halts {f : Nat → Nat} {P : Nat → Prop} :
    ∀ (n x : Nat), ¬ P (iter f n x) → Acc (backStep f P) x := by
  intro n
  induction n with
  | zero => exact fun x hx => Acc.intro x (fun _ ha => absurd ha.1 hx)
  | succ n ih =>
    intro x hx
    have hfx : Acc (backStep f P) (f x) := ih (f x) (by rw [iter_succ] at hx; exact hx)
    exact Acc.intro x (fun a ha => by rw [ha.2]; exact hfx)

/-- **Completeness, in `Acc` form.**  If every orbit halts then `backStep` has no
infinite descending chain, and the identity is a ranking certificate for it. -/
theorem ranking_of_halting {f : Nat → Nat} {P : Nat → Prop}
    (h : ∀ x : Nat, Halts f P x) :
    NoDesc (backStep f P) ∧ Ranking f P (backStep f P) id :=
  ⟨noDesc_of_acc (fun w => by
      obtain ⟨n, hn⟩ := h w; exact acc_backStep_of_halts n w hn),
   fun x hx => ⟨hx, rfl⟩⟩

/-- **Completeness, in `Nat` form.**  If every orbit halts then the *halting
time* is a ranking certificate valued in `(Nat, <)`. -/
theorem exists_nat_ranking {f : Nat → Nat} {P : Nat → Prop}
    (h : ∀ x : Nat, Halts f P x) :
    ∃ R : Nat → Nat, ∀ x : Nat, P x → R (f x) < R x := by
  have key : ∀ x : Nat, ∃ n : Nat,
      (¬ P (iter f n x)) ∧ ∀ k : Nat, k < n → ¬ ¬ P (iter f k x) :=
    fun x => Minimum.exists_min (h x)
  refine ⟨fun x => Classical.choose (key x), ?_⟩
  intro x hx
  have hspecx := Classical.choose_spec (key x)
  have hspecf := Classical.choose_spec (key (f x))
  have hmpos : 0 < Classical.choose (key x) := by
    by_cases h0 : 0 < Classical.choose (key x)
    · exact h0
    · exfalso
      have hz : Classical.choose (key x) = 0 := by omega
      have := hspecx.1
      rw [hz] at this
      exact this hx
  obtain ⟨m0, hm0⟩ : ∃ m0 : Nat, Classical.choose (key x) = m0 + 1 :=
    ⟨Classical.choose (key x) - 1, by omega⟩
  have hstop : ¬ P (iter f m0 (f x)) := by
    have := hspecx.1
    rw [hm0, iter_succ] at this
    exact this
  have hle : Classical.choose (key (f x)) ≤ m0 := by
    by_cases hle : Classical.choose (key (f x)) ≤ m0
    · exact hle
    · exact absurd (hspecf.2 m0 (by omega)) (fun hc => hc hstop)
  show Classical.choose (key (f x)) < Classical.choose (key x)
  omega

/-- **The collapse theorem.**  For a *deterministic* system on `ℕ`, a ranking
certificate valued in an arbitrary well-founded relation exists **iff** one
valued in `(Nat, <)` exists.

So lexicographic products, ordinal notations, multiset orders, matrix orders,
tree embeddings — every richer target `W` — buy exactly nothing here.  A
transfinite rank pays off only when the transition relation *branches*; a unary
deterministic map has one orbit per point, so the descending chain a rank
produces is the orbit itself, and its length is already a natural number. -/
theorem rank_target_collapses (f : Nat → Nat) (P : Nat → Prop) :
    (∃ (W : Type) (lt : W → W → Prop) (R : Nat → W), NoDesc lt ∧ Ranking f P lt R)
      ↔ (∃ R : Nat → Nat, ∀ x : Nat, P x → R (f x) < R x) := by
  constructor
  · intro hex
    obtain ⟨W, lt, R, hwf, hR⟩ := hex
    exact exists_nat_ranking (fun x => halts_of_ranking hwf hR x)
  · intro hex
    obtain ⟨R, hR⟩ := hex
    exact ⟨Nat, fun a b => a < b, R, noDesc_nat_lt, hR⟩

/-- **And both are equivalent to the conjecture itself.**  A ranking certificate
is therefore *never* a half-filter: it refutes cycles and divergence in one
stroke, so producing one is the entire problem, not a step towards it. -/
theorem rank_iff_halting (f : Nat → Nat) (P : Nat → Prop) :
    (∃ (W : Type) (lt : W → W → Prop) (R : Nat → W), NoDesc lt ∧ Ranking f P lt R)
      ↔ (∀ x : Nat, Halts f P x) := by
  constructor
  · intro hex x
    obtain ⟨W, lt, R, hwf, hR⟩ := hex
    exact halts_of_ranking hwf hR x
  · intro h
    obtain ⟨hwf, hR⟩ := ranking_of_halting h
    exact ⟨Nat, backStep f P, id, hwf, hR⟩

/-- The Collatz instance: a well-founded ranking for the step map above `1`
exists exactly when the conjecture holds. -/
theorem collatz_iff_rank :
    CollatzConjecture ↔
      ∃ (W : Type) (lt : W → W → Prop) (R : Nat → W),
        NoDesc lt ∧ ∀ x : Nat, 1 < x → lt (R (step x)) (R x) := by
  have hiter : ∀ (k n : Nat), iter step k n = orbit k n := by
    intro k
    induction k with
    | zero => intro n; rfl
    | succ k ih => intro n; rw [iter_succ]; exact ih (step n)
  constructor
  · intro hc
    refine (rank_iff_halting step (fun y => 1 < y)).mpr ?_
    intro x
    by_cases hx : 0 < x
    · obtain ⟨k, hk⟩ := hc x hx
      exact ⟨k, by rw [hiter]; omega⟩
    · exact ⟨0, by simp only [iter_zero]; omega⟩
  · intro hex
    intro n hn
    obtain ⟨W, lt, R, hwf, hR⟩ := hex
    obtain ⟨k, hk⟩ := halts_of_ranking (P := fun y => 1 < y) hwf hR n
    rw [hiter] at hk
    have := orbit_positive hn k
    exact ⟨k, by omega⟩


/-! ## Section VIII.1 — well-quasi-orders do not see divergence -/

/-- A quasi-order on `Nat` is a **well-quasi-order** when every infinite sequence
contains a *good pair* `i < j` with `g i ⊑ g j`.  This — not well-foundedness —
is the Ramsey-flavoured finiteness the divergence half is asking for, since the
divergence half is literally "every orbit contains a repetition". -/
def WQO (le : Nat → Nat → Prop) : Prop :=
  ∀ g : Nat → Nat, ∃ i j : Nat, i < j ∧ le (g i) (g j)

/-- `≤` on `Nat` is a well-quasi-order: a sequence with no good pair would be
strictly decreasing. -/
theorem nat_le_wqo : WQO (fun a b : Nat => a ≤ b) := by
  intro g
  by_cases h : ∃ i j : Nat, i < j ∧ g i ≤ g j
  · exact h
  · exfalso
    refine no_nat_desc g (fun i => ?_)
    by_cases hlt : g (i + 1) < g i
    · exact hlt
    · exact absurd ⟨i, i + 1, by omega, by omega⟩ h

/-- Iterating the successor map. -/
theorem iter_succ_map (n x : Nat) : iter (fun m => m + 1) n x = x + n := by
  induction n generalizing x with
  | zero => simp [iter]
  | succ n ih => rw [iter_succ, ih (x + 1)]; omega

/-- **The WQO family is refuted outright.**  The principle behind well-structured
transition systems — *a monotone map on a well-quasi-ordered state space has
bounded orbits* — is false, and the counterexample is the successor map on
`(ℕ, ≤)`, which is a WQO, and for which the successor is not merely monotone but
strictly monotone and injective.

Consequence: Dickson's lemma, Higman's lemma, Kruskal's tree theorem, and the
whole WSTS toolkit cannot by themselves exclude a divergent orbit, no matter
which WQO is placed on the state space.  What they deliver is a *good pair*
`x_i ⊑ x_j`, and what the divergence half needs is an *equality* `x_i = x_j`.
The gap between `⊑` and `=` is the entire content. -/
theorem no_wqo_divergence_filter :
    ¬ (∀ (f : Nat → Nat) (le : Nat → Nat → Prop), WQO le →
        (∀ x y : Nat, le x y → le (f x) (f y)) →
        ∀ x : Nat, ∃ B : Nat, ∀ n : Nat, iter f n x ≤ B) := by
  intro h
  obtain ⟨B, hB⟩ :=
    h (fun m => m + 1) (fun a b => a ≤ b) nat_le_wqo
      (fun x y hxy => by show x + 1 ≤ y + 1; omega) 0
  have hval := hB (B + 1)
  rw [iter_succ_map] at hval
  omega

/-- Strictness does not rescue it: the same witness is strictly monotone. -/
theorem no_strict_wqo_divergence_filter :
    (∀ x y : Nat, x < y → (fun m => m + 1) x < (fun m => m + 1) y) ∧
      (∀ B : Nat, ∃ n : Nat, B < iter (fun m => m + 1) n 0) :=
  ⟨fun x y h => by show x + 1 < y + 1; omega,
   fun B => ⟨B + 1, by rw [iter_succ_map]; omega⟩⟩

/-! ## Section VIII.2 — size-change termination over a mixed abstraction -/

open NoFiniteRanking in
/-- **The mixed block self-loop.**  For every pair of moduli `2 ^ k`, `3 ^ l` and
every block length `L` there is a genuine `n > 1` whose next `L` states are, at
*every* intermediate time,

* congruent to `n` modulo `2 ^ k` **and** modulo `3 ^ l` — so every
  congruence-definable coordinate is frozen along the whole block; and
* strictly **larger** than `n` — so every coordinate monotone in magnitude moves
  the wrong way along the whole block.

Witness: `n + 1 = 2 ^ (k+2+L) · 3 ^ l · s`, whose first `L` steps are one odd run,
`T^j(n) + 1 = 3 ^ j · 2 ^ (k+2+L−j) · 3 ^ l · s`.

This strengthens `TransitionInvariant.exists_congruent_step` in two directions at
once: from a single step to a block of any length, and from congruence
coordinates alone to congruence coordinates *together with* magnitude
coordinates. -/
theorem mixed_block_self_loop (k l L s : Nat) (hs : 0 < s) :
    ∃ n : Nat, 1 < n ∧
      (∀ j : Nat, j ≤ L →
        acceleratedOrbit j n % 2 ^ k = n % 2 ^ k ∧
        acceleratedOrbit j n % 3 ^ l = n % 3 ^ l) ∧
      (∀ j : Nat, 0 < j → j ≤ L → n < acceleratedOrbit j n) := by
  have h3 : (0:Nat) < 3 ^ l := Nat.pow_pos (by omega)
  have hM : (0:Nat) < 3 ^ l * s := Nat.mul_pos h3 hs
  have h1M : (1:Nat) ≤ 3 ^ l * s := hM
  have h4 : (4:Nat) ≤ 2 ^ (k + 2 + L) := by
    calc (4:Nat) = 2 ^ 2 := by decide
      _ ≤ 2 ^ (k + 2 + L) := Nat.pow_le_pow_right (by omega) (by omega)
  have hbig : (4:Nat) ≤ 2 ^ (k + 2 + L) * (3 ^ l * s) :=
    Nat.le_trans h4 (Nat.le_mul_of_pos_right _ hM)
  obtain ⟨n, hn⟩ : ∃ n : Nat, n + 1 = 2 ^ (k + 2 + L) * (3 ^ l * s) :=
    ⟨2 ^ (k + 2 + L) * (3 ^ l * s) - 1, by omega⟩
  have hk2 : (0:Nat) < 2 ^ k := Nat.pow_pos (by omega)
  -- the exact value at every intermediate time
  have hstage : ∀ j : Nat, j ≤ L →
      acceleratedOrbit j n + 1 = 3 ^ j * (2 ^ (k + 2 + L - j) * (3 ^ l * s)) := by
    intro j hj
    refine heavy_return_value (k := k + 2 + L - j) (L := j) ?_
    rw [show k + 2 + L - j + j = k + 2 + L by omega]
    exact hn
  refine ⟨n, by omega, ?_, ?_⟩
  · intro j hj
    have hval := hstage j hj
    have hpow : (2:Nat) ^ (k + 2 + L) = 2 ^ k * 2 ^ (2 + L) := by
      rw [← Nat.pow_add, show k + (2 + L) = k + 2 + L by omega]
    have hpowj : (2:Nat) ^ (k + 2 + L - j) = 2 ^ k * 2 ^ (k + 2 + L - j - k) := by
      rw [← Nat.pow_add, show k + (k + 2 + L - j - k) = k + 2 + L - j by omega]
    have hd2n : 2 ^ k ∣ (n + 1) := by
      refine ⟨2 ^ (2 + L) * (3 ^ l * s), ?_⟩
      rw [hn, hpow, Nat.mul_assoc]
    have hd3n : 3 ^ l ∣ (n + 1) := by
      refine ⟨2 ^ (k + 2 + L) * s, ?_⟩
      rw [hn]; simp [Nat.mul_comm, Nat.mul_assoc, Nat.mul_left_comm]
    have hd2v : 2 ^ k ∣ (acceleratedOrbit j n + 1) := by
      refine ⟨3 ^ j * (2 ^ (k + 2 + L - j - k) * (3 ^ l * s)), ?_⟩
      rw [hval, hpowj]; simp [Nat.mul_comm, Nat.mul_assoc, Nat.mul_left_comm]
    have hd3v : 3 ^ l ∣ (acceleratedOrbit j n + 1) := by
      refine ⟨3 ^ j * (2 ^ (k + 2 + L - j) * s), ?_⟩
      rw [hval]; simp [Nat.mul_comm, Nat.mul_assoc, Nat.mul_left_comm]
    exact ⟨by rw [pred_mod_of_dvd hk2 hd2v, pred_mod_of_dvd hk2 hd2n],
           by rw [pred_mod_of_dvd h3 hd3v, pred_mod_of_dvd h3 hd3n]⟩
  · intro j hj0 hjL
    refine heavy_return_grows (k := k + 2 + L - j) (L := j) (M := 3 ^ l * s) hj0 hM ?_
    rw [show k + 2 + L - j + j = k + 2 + L by omega]
    exact hn

/-- **Size-change termination is vacuous over the mixed abstraction.**  Let
`φ 0, …, φ (m−1)` be any finite family of size parameters, each of which is
either congruence-definable at the moduli `2 ^ k`, `3 ^ l`, or monotone in
magnitude.  Then there is a genuine `n > 1` such that along the whole block of
length `L` **no** parameter ever strictly decreases.

A size-change certificate needs a strict arc in every idempotent multipath; this
exhibits a multipath of arbitrary length whose entire arc matrix is
non-decreasing.  Lexicographic ranks, multiphase ranks and disjunctive
well-founded transition invariants over such coordinates are the special cases
`m = 2`, `m` arbitrary with a phase map, and the covering shape respectively. -/
theorem no_mixed_block_descent (k l L m : Nat) (φ : Nat → Nat → Nat)
    (hkind : ∀ i : Nat, i < m →
      (∀ x y : Nat, x % 2 ^ k = y % 2 ^ k → x % 3 ^ l = y % 3 ^ l → φ i x = φ i y)
      ∨ (∀ x y : Nat, x ≤ y → φ i x ≤ φ i y)) :
    ∃ n : Nat, 1 < n ∧ ∀ j : Nat, j ≤ L → ∀ i : Nat, i < m →
      ¬ (φ i (acceleratedOrbit j n) < φ i n) := by
  obtain ⟨n, hn1, hcong, hgrow⟩ := mixed_block_self_loop k l L 1 (by omega)
  refine ⟨n, hn1, ?_⟩
  intro j hj i hi
  rcases hkind i hi with hc | hmono
  · have := hc (acceleratedOrbit j n) n (hcong j hj).1 (hcong j hj).2
    omega
  · rcases Nat.eq_zero_or_pos j with hj0 | hjpos
    · subst hj0; rw [acceleratedOrbit_zero]; omega
    · have := hmono n (acceleratedOrbit j n) (Nat.le_of_lt (hgrow j hjpos hj))
      omega

/-- The same fact in the shape a termination prover emits: there is no block
length at which *some* coordinate of a mixed abstraction always decreases. -/
theorem no_mixed_sct (k l L m : Nat) (φ : Nat → Nat → Nat)
    (hkind : ∀ i : Nat, i < m →
      (∀ x y : Nat, x % 2 ^ k = y % 2 ^ k → x % 3 ^ l = y % 3 ^ l → φ i x = φ i y)
      ∨ (∀ x y : Nat, x ≤ y → φ i x ≤ φ i y)) :
    ¬ (∀ x : Nat, 1 < x →
        ∃ i : Nat, i < m ∧ φ i (acceleratedOrbit L x) < φ i x) := by
  intro hdec
  obtain ⟨n, hn1, hno⟩ := no_mixed_block_descent k l L m φ hkind
  obtain ⟨i, hi, hlt⟩ := hdec n hn1
  exact hno L (Nat.le_refl L) i hi hlt


/-! ## Section IX.1 — the record ladder, and what freezes on it -/

open Divergence

/-- A non-increasing sequence of naturals is eventually constant. -/
theorem antitone_seq_eventually_constant (ψ : Nat → Nat)
    (h : ∀ i : Nat, ψ (i + 1) ≤ ψ i) :
    ∃ N : Nat, ∀ i : Nat, N ≤ i → ψ i = ψ N := by
  have hmono : ∀ a b : Nat, a ≤ b → ψ b ≤ ψ a := by
    intro a b hab
    induction b with
    | zero => have : a = 0 := by omega
              subst this; exact Nat.le_refl _
    | succ b ih =>
      by_cases hb : a ≤ b
      · exact Nat.le_trans (h b) (ih hb)
      · have : a = b + 1 := by omega
        subst this; exact Nat.le_refl _
  obtain ⟨v, hv, hmin⟩ :=
    Minimum.exists_min_lt (P := fun v => ∃ i : Nat, ψ i = v) ⟨ψ 0, 0, rfl⟩
  obtain ⟨N, hN⟩ := hv
  refine ⟨N, fun i hi => ?_⟩
  have h1 : ψ i ≤ ψ N := hmono N i hi
  have h2 : v ≤ ψ i := hmin (ψ i) ⟨i, rfl⟩
  omega

/-- Every value of the running maximum is an actual orbit value. -/
theorem orbitMax_attained (n k : Nat) : ∃ j : Nat, j ≤ k ∧ orbitMax n k = orbit j n := by
  induction k with
  | zero => exact ⟨0, Nat.le_refl 0, rfl⟩
  | succ k ih =>
    rw [orbitMax_succ]
    by_cases hlt : orbitMax n k < orbit (k + 1) n
    · rw [if_pos hlt]; exact ⟨k + 1, Nat.le_refl _, rfl⟩
    · rw [if_neg hlt]
      obtain ⟨j, hj, hval⟩ := ih
      exact ⟨j, by omega, hval⟩

/-- **The record ladder of a divergent orbit is unbounded**, and every rung is an
orbit value.  This is the one genuinely asymptotic object a divergence-half
filter has to read: it exists *because* the orbit never returns to a bounded
region, and it is invisible to the cycle half, where the ladder is finite. -/
theorem records_unbounded {n : Nat} (h : Divergent n) (N B : Nat) :
    ∃ i : Nat, N ≤ i ∧ B < orbitMax n i := by
  obtain ⟨i, hi⟩ := h B
  refine ⟨if i ≤ N then N else i, ?_, ?_⟩
  · by_cases hle : i ≤ N
    · rw [if_pos hle]; exact Nat.le_refl N
    · rw [if_neg hle]; omega
  · have hstep : orbit i n ≤ orbitMax n i := le_orbitMax i (Nat.le_refl i)
    by_cases hle : i ≤ N
    · rw [if_pos hle]
      exact Nat.lt_of_lt_of_le hi (Nat.le_trans hstep (orbitMax_mono hle))
    · rw [if_neg hle]; omega

/-- **Anti-monotone coordinates freeze on the record ladder.**  If `φ` reverses
`≤` — the shape of every "distance to the top", "remaining headroom" or
"co-magnitude" coordinate — then `φ` composed with the running maximum is
non-increasing, hence eventually constant.

So an anti-monotone size parameter supplies only **finitely many** strict arcs
along a divergent orbit's record ladder, whatever the orbit does afterwards. -/
theorem antitone_freezes_on_records (n : Nat) (φ : Nat → Nat)
    (hanti : ∀ x y : Nat, x ≤ y → φ y ≤ φ x) :
    ∃ N : Nat, ∀ i : Nat, N ≤ i → φ (orbitMax n i) = φ (orbitMax n N) :=
  antitone_seq_eventually_constant (fun i => φ (orbitMax n i))
    (fun i => hanti (orbitMax n i) (orbitMax n (i + 1)) (orbitMax_mono (by omega)))

/-- The same for a whole finite family, with one common freezing index. -/
theorem antitone_family_freezes (n m : Nat) (φ : Nat → Nat → Nat)
    (hanti : ∀ c : Nat, c < m → ∀ x y : Nat, x ≤ y → φ c y ≤ φ c x) :
    ∃ N : Nat, ∀ i j : Nat, N ≤ i → N ≤ j → ∀ c : Nat, c < m →
      φ c (orbitMax n i) = φ c (orbitMax n j) := by
  induction m with
  | zero => exact ⟨0, fun _ _ _ _ c hc => absurd hc (by omega)⟩
  | succ m ih =>
    obtain ⟨N1, hN1⟩ := ih (fun c hc => hanti c (by omega))
    obtain ⟨N2, hN2⟩ := antitone_freezes_on_records n (φ m) (hanti m (by omega))
    refine ⟨N1 + N2, fun i j hi hj c hc => ?_⟩
    by_cases hcm : c < m
    · exact hN1 i j (by omega) (by omega) c hcm
    · have hcm' : c = m := by omega
      subst hcm'
      rw [hN2 i (by omega), hN2 j (by omega)]

/-- **The divergence-half coordinate theorem.**  Along the record ladder of a
divergent orbit, past a finite index, no anti-monotone coordinate ever strictly
decreases again.

Read together with `no_mixed_block_descent` this classifies the three natural
kinds of size parameter and kills all three:

* **congruence-definable** — frozen along an arbitrarily long genuine block
  (`mixed_block_self_loop`), so blind;
* **monotone in magnitude** — strictly *increasing* along that same block, so
  moving the wrong way;
* **anti-monotone in magnitude** — eventually constant on the record ladder of
  any divergent orbit, so carrying only finitely many strict arcs.

A size-change / lexicographic / transition-invariant certificate needs
*infinitely many* strict arcs on every infinite run.  None of the three kinds can
supply them. -/
theorem no_antitone_certificate_on_divergent {n : Nat} (hdiv : Divergent n) (m : Nat)
    (φ : Nat → Nat → Nat)
    (hanti : ∀ c : Nat, c < m → ∀ x y : Nat, x ≤ y → φ c y ≤ φ c x) :
    ∃ N : Nat,
      (∀ B : Nat, ∃ i : Nat, N ≤ i ∧ B < orbitMax n i) ∧
      (∀ i j : Nat, N ≤ i → N ≤ j → ∀ c : Nat, c < m →
        ¬ (φ c (orbitMax n j) < φ c (orbitMax n i))) := by
  obtain ⟨N, hN⟩ := antitone_family_freezes n m φ hanti
  refine ⟨N, fun B => records_unbounded hdiv N B, fun i j hi hj c hc => ?_⟩
  have := hN i j hi hj c hc
  omega


/-! ## Section IX.3 — what the record ladder is made of -/

/-- Between two record levels there is an index at which the running maximum
jumps. -/
theorem exists_max_jump {n N M : Nat} (h : orbitMax n N < orbitMax n M) :
    ∃ i : Nat, N ≤ i ∧ i < M ∧ orbitMax n i < orbitMax n (i + 1) := by
  induction M with
  | zero =>
    exact absurd (orbitMax_mono (n := n) (Nat.zero_le N)) (by omega)
  | succ M ih =>
    by_cases hstep : orbitMax n N < orbitMax n M
    · obtain ⟨i, hi1, hi2, hi3⟩ := ih hstep
      exact ⟨i, hi1, by omega, hi3⟩
    · have hNM : N ≤ M := by
        by_cases hle : N ≤ M
        · exact hle
        · exact absurd (orbitMax_mono (n := n) (show M + 1 ≤ N by omega)) (by omega)
      exact ⟨M, hNM, by omega, by omega⟩

/-- A jump of the running maximum is a genuine growth step of the orbit. -/
theorem growth_of_max_jump {n i : Nat} (h : orbitMax n i < orbitMax n (i + 1)) :
    orbit i n < orbit (i + 1) n := by
  have hmax : orbit i n ≤ orbitMax n i := le_orbitMax i (Nat.le_refl i)
  rw [orbitMax_succ] at h
  by_cases hlt : orbitMax n i < orbit (i + 1) n
  · omega
  · rw [if_neg hlt] at h; omega

/-- **Every growth step is an odd step.**  The even branch halves. -/
theorem odd_of_growth {y : Nat} (hy : 0 < y) (h : y < step y) : y % 2 = 1 := by
  by_cases hpar : y % 2 = 0
  · rw [Reach.step_even hy hpar] at h
    omega
  · omega

/-- **The record ladder of a divergent orbit is carried by odd steps, for ever.**
For every `N` there is an index `i ≥ N` at which the orbit is odd and strictly
grows, and at which the running maximum jumps.

This is the positive statement of Section IX.  It is proved from unboundedness
alone — no property of the Collatz map beyond determinism, positivity and "the
even branch halves" — so it assumes nothing about the conjecture, and it says
something about an orbit *that never comes back*: it must keep hitting odd
numbers at arbitrarily late record times.  It is exactly the kind of statement
the cycle-half machinery cannot make, because on a cycle the record ladder is
finite and stops jumping. -/
theorem divergent_record_steps_odd {n : Nat} (hn : 0 < n) (hdiv : Divergent n) (N : Nat) :
    ∃ i : Nat, N ≤ i ∧ orbit i n % 2 = 1 ∧ orbit i n < orbit (i + 1) n ∧
      orbitMax n i < orbitMax n (i + 1) := by
  obtain ⟨M, hM1, hM2⟩ := records_unbounded hdiv N (orbitMax n N)
  obtain ⟨i, hi1, _, hi3⟩ := exists_max_jump hM2
  have hgrow := growth_of_max_jump hi3
  have hstep : orbit (i + 1) n = step (orbit i n) := by
    rw [Nat.add_comm, orbit_add, orbit_succ_steps]; rfl
  refine ⟨i, hi1, ?_, hgrow, hi3⟩
  refine odd_of_growth (orbit_positive hn i) ?_
  rw [← hstep]; exact hgrow

/-! ## Section IX.2 — the certificate shape the divergence half actually admits -/

/-- A **bounded inductive invariant** for the orbit of `n`: a set containing `n`,
closed under the step map, and contained in a finite initial segment.  This is a
*safety* certificate — no well-foundedness anywhere. -/
def BoundedInvariant (n : Nat) (S : Nat → Prop) : Prop :=
  S n ∧ (∀ y : Nat, S y → S (step y)) ∧ ∃ B : Nat, ∀ y : Nat, S y → y ≤ B

/-- **Bounded inductive invariants are sound and complete for the divergence
half.**  The orbit of `n` is bounded exactly when such a certificate exists, and
the canonical one is the reachable set itself.

Contrast with `rank_iff_halting`: a ranking certificate is sound and complete for
the *whole* conjecture, so it can never isolate a half.  The divergence half is a
safety property and wants an invariant; the cycle half is what is left over, and
it is `Π⁰₁`, hence finitely refutable.  That asymmetry is the structural reason a
repository full of termination machinery has nothing aimed at divergence:
termination machinery is liveness machinery. -/
theorem barrier_complete (n : Nat) : Bounded n ↔ ∃ S : Nat → Prop, BoundedInvariant n S := by
  constructor
  · intro hb
    obtain ⟨B, hB⟩ := hb
    refine ⟨fun y => ∃ i : Nat, orbit i n = y, ⟨0, rfl⟩, ?_, B, ?_⟩
    · intro y hy
      obtain ⟨i, hi⟩ := hy
      exact ⟨i + 1, by rw [Nat.add_comm, orbit_add, orbit_succ_steps, hi]; rfl⟩
    · intro y hy
      obtain ⟨i, hi⟩ := hy
      rw [← hi]; exact hB i
  · intro hex
    obtain ⟨S, hS0, hSclosed, B, hB⟩ := hex
    refine ⟨B, fun i => hB _ ?_⟩
    induction i with
    | zero => exact hS0
    | succ i ih =>
      have : orbit (i + 1) n = step (orbit i n) := by
        rw [Nat.add_comm, orbit_add, orbit_succ_steps]; rfl
      rw [this]
      exact hSclosed _ ih

/-! ## Axiom audit -/

#print axioms rank_target_collapses
#print axioms rank_iff_halting
#print axioms collatz_iff_rank
#print axioms no_wqo_divergence_filter
#print axioms mixed_block_self_loop
#print axioms no_mixed_sct
#print axioms no_antitone_certificate_on_divergent
#print axioms barrier_complete
#print axioms divergent_record_steps_odd

end EscapeCertificate
end Collatz
