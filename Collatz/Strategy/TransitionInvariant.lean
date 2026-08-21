import Collatz.Strategy.NoFiniteRanking

/-!
# No congruence-definable termination certificate, of any shape

`NoFiniteRanking.no_class_ranking` says that a *ranking function* constant on
classes modulo `2 ^ k` and `3 ^ l` cannot decrease along windows, and
`AnyModulusRanking` removes the restriction on the modulus.  A natural response
is to reach for a stronger certificate shape: a lexicographic or multiphase
rank, a size-change-termination matrix, or a Podelski–Rybalchenko *transition
invariant* — a finite family of well-founded relations whose union covers the
transitive closure of the step relation.  Those shapes are strictly more general
than a single rank, and the first two are what termination provers actually
emit.

This file shows that the finite-quotient obstruction does not care.  All of them
die to the same witness, and for the same reason.

## The witness

Take `n + 1 = 2 ^ (k+1) · 3 ^ l · 4`.  Then `2 ∣ n + 1`, so `n` is odd, the next
step is the odd branch, and `NoFiniteRanking.heavy_return_value` evaluates it
exactly:

`T(n) + 1 = 3 · 2 ^ k · 3 ^ l · 4`.

Both `n + 1` and `T(n) + 1` are divisible by `2 ^ k` and by `3 ^ l`, so `n` and
`T(n)` are the *same* residue — namely `−1` — at both moduli
(`exists_congruent_step`).  A single genuine transition of the map is therefore
invisible to every congruence abstraction at those moduli: the abstraction sees
a self-loop.

That is the whole content.  A self-loop is fatal to every certificate shape that
demands progress somewhere:

* a relation determined by the residues of its two arguments and containing this
  transition also contains the reflexive pair `(n, n)`, hence the constant
  sequence is an infinite chain and the relation is not well-founded
  (`no_class_transition_invariant`);
* every congruence-definable measure takes *equal* values at the two endpoints,
  so no lexicographic tuple of them can strictly decrease, whatever the arity
  and whatever the phase map (`class_measures_all_constant`,
  `no_class_lex_ranking`).

## What is and is not claimed

The formal statement `no_class_transition_invariant` is deliberately narrow, and
it is worth being exact about the gap between it and the informal claim.

*Formally proved*: there is no finite family `Q 0, …, Q (N−1)` of binary
relations on `Nat` such that (i) membership in `Q c` depends only on the residues
of both arguments modulo `2 ^ k` and modulo `3 ^ l`, (ii) each `Q c` admits no
infinite chain, and (iii) every one-step transition `x → T(x)` with `x > 1` lies
in some `Q c`.

*Not formalised here*: the surrounding Ramsey argument.  A Podelski–Rybalchenko
certificate covers the *transitive* closure `R⁺`, not just the one-step relation,
and the soundness of that shape rests on infinite Ramsey for pairs (`RT²_N`),
which is not available here and which this file does not develop.  What is
proved is the strictly easier direction, and it is the one that matters: any
`R⁺`-covering family also covers `R`, so refuting the one-step version refutes
the transitive version.  Read the theorem as *"a disjunctive well-founded
covering of the step relation with congruence-definable components does not
exist"*; the Ramsey machinery would only be needed to go the other way, from a
covering to a termination proof, which nobody can do here anyway.

Likewise, "chain-free" is spelled as `NoInfChain` — the non-existence of a
sequence `f` with `Q (f i) (f (i+1))` for all `i` — rather than as `Acc`-based
well-foundedness, so that no Mathlib and no choice principle is needed.  Over
`Nat` with a classical metatheory the two agree; constructively `NoInfChain` is
the *weaker* hypothesis, which makes the negative theorem *stronger*.  The proof
exhibits an explicit constant sequence, so it is fully constructive.

`no_class_transition_invariant` is strictly stronger than `no_class_ranking`: a
rank `φ` constant on classes yields the single component
`Q 0 x y := φ y < φ x`, which is congruence-definable and chain-free, so the
ranking theorem is the case `N = 1`.  The converse fails — a transition
invariant need not come from any rank.  Via `class_measures_all_constant` the
same witness kills size-change-termination over a congruence control
abstraction (all size parameters are equal at the two endpoints, so no arc of
the self-loop can be strict) and lexicographic/multiphase ranks over any fixed
congruence abstraction, of any arity.

## The second negative result

`no_bounded_window_set` refutes a different and much more concrete shape: a
finite set `S` of window lengths with "every `x > 1` drops within `j` steps for
some `j ∈ S`".  This one needs no Ramsey argument and no abstraction at all, and
it is refuted outright rather than merely obstructed.  Witness: `2 ^ (M+2) − 1`.
Its first `M + 2` steps are a single odd run, and along an odd run the value
strictly *increases* at every intermediate time
(`NoFiniteRanking.heavy_return_grows`), so no window of length `≤ M` drops.
Corollary: the stopping time is unbounded, and no *finite* window-based
transition invariant exists either.

Together the two results say: a finite certificate for Collatz can use neither
congruence-definable components nor bounded windows.  What is left is
full-precision data, and the maximal-precision measure is the identity — which
is to say, the conjecture itself.  That is the same conclusion `Mirror` and
`NoFiniteRanking` reach from their own directions, and it is why
`Frontier.targetB`, whose hypothesis ties the scale `k` to the *size* of `x`
rather than to a residue, is the live target.
-/

namespace Collatz
namespace TransitionInvariant

open Reach NoFiniteRanking

/-! ## Chain-freeness without `Acc` -/

/-- `Q` admits **no infinite chain**: there is no sequence `f` with
`Q (f i) (f (i+1))` for every `i`.  This is the choice-free rendering of
"well-founded in the direction of the arrows"; it is implied by well-foundedness
and is all that a termination certificate can ever supply. -/
def NoInfChain (Q : Nat → Nat → Prop) : Prop :=
  ¬ ∃ f : Nat → Nat, ∀ i : Nat, Q (f i) (f (i + 1))

/-- A relation with a reflexive pair has an infinite chain: the constant
sequence. -/
theorem not_noInfChain_of_refl {Q : Nat → Nat → Prop} {a : Nat} (h : Q a a) :
    ¬ NoInfChain Q := fun hno => hno ⟨fun _ => a, fun _ => h⟩

/-! ## The invisible transition -/

/-- **A genuine step that every congruence abstraction sees as a self-loop.**
For any moduli `2 ^ k` and `3 ^ l` there is an `n > 1` with
`n ≡ T(n)` modulo `2 ^ k` and modulo `3 ^ l`.  Both residues are `−1`.

The witness is `n + 1 = 2 ^ (k+1) · 3 ^ l · 4`; only one step is needed, whereas
`no_class_ranking` is stated per-window. -/
theorem exists_congruent_step (k l : Nat) :
    ∃ n : Nat, 1 < n ∧
      n % 2 ^ k = acceleratedStep n % 2 ^ k ∧
      n % 3 ^ l = acceleratedStep n % 3 ^ l := by
  have h3 : (0:Nat) < 3 ^ l := Nat.pow_pos (by omega)
  have h2 : (2:Nat) ≤ 2 ^ (k + 1) := by
    calc (2:Nat) = 2 ^ 1 := by decide
      _ ≤ 2 ^ (k + 1) := Nat.pow_le_pow_right (by omega) (by omega)
  have hbig : (8:Nat) ≤ 2 ^ (k + 1) * (3 ^ l * 4) := by
    have hstep : (2:Nat) * (1 * 4) ≤ 2 ^ (k + 1) * (3 ^ l * 4) :=
      Nat.mul_le_mul h2 (Nat.mul_le_mul (by omega) (Nat.le_refl 4))
    omega
  obtain ⟨n, hn⟩ : ∃ n : Nat, n + 1 = 2 ^ (k + 1) * (3 ^ l * 4) :=
    ⟨2 ^ (k + 1) * (3 ^ l * 4) - 1, by omega⟩
  obtain ⟨hc2, hc3⟩ := heavy_return_congr (s := 4) (by omega) hn
  have hstep : acceleratedOrbit 1 n = acceleratedStep n := rfl
  exact ⟨n, by omega, by rw [← hstep]; exact hc2, by rw [← hstep]; exact hc3⟩

/-! ## No congruence-definable transition invariant -/

/-- **The main negative theorem.**  There is no finite disjunctive well-founded
covering of the step relation by congruence-definable components.

Concretely: let `Q 0, …, Q (N−1)` be binary relations on `Nat` such that
membership in each is determined by the residues of the two arguments modulo
`2 ^ k` and `3 ^ l` (`hdef`), each admits no infinite chain (`hwf`), and together
they cover every transition `x → T(x)` above `1` (`hcov`).  These three demands
are contradictory.

The proof is the witness of `exists_congruent_step` plus one substitution:
definability lets us replace `T(n)` by `n` on the right, producing the reflexive
pair `Q c n n`, whose constant sequence is an infinite chain.

Scope: this refutes coverings of the *one-step* relation, hence a fortiori
coverings of its transitive closure — the shape a Podelski–Rybalchenko
certificate actually has.  The Ramsey-theoretic soundness of that shape is not
developed here and is not needed for the negative direction; see the module
docstring. -/
theorem no_class_transition_invariant (k l N : Nat) (Q : Nat → Nat → Nat → Prop)
    (hdef : ∀ c x y x' y' : Nat,
      x % 2 ^ k = x' % 2 ^ k → x % 3 ^ l = x' % 3 ^ l →
      y % 2 ^ k = y' % 2 ^ k → y % 3 ^ l = y' % 3 ^ l →
      Q c x y → Q c x' y')
    (hwf : ∀ c : Nat, c < N → NoInfChain (Q c))
    (hcov : ∀ x : Nat, 1 < x → ∃ c : Nat, c < N ∧ Q c x (acceleratedStep x)) :
    False := by
  obtain ⟨n, hgt, hc2, hc3⟩ := exists_congruent_step k l
  obtain ⟨c, hcN, hQ⟩ := hcov n hgt
  have hQnn : Q c n n :=
    hdef c n (acceleratedStep n) n n rfl rfl hc2.symm hc3.symm hQ
  exact not_noInfChain_of_refl hQnn (hwf c hcN)

/-! ## Lexicographic, multiphase and size-change certificates -/

/-- **Every congruence-definable measure is constant across the witness step.**
Given any family of measures `φ i` (indexed by `Nat`, so of any arity), each
constant on classes modulo `2 ^ k` and `3 ^ l`, there is a genuine transition
`n → T(n)` with `n > 1` along which *no* component changes at all.

This is the form in which the obstruction kills the remaining certificate
shapes.  A lexicographic rank needs some component to strictly decrease; a
multiphase rank needs the phase to advance or the active measure to decrease; a
size-change-termination certificate needs the idempotent self-loop at this class
to carry a strict arc.  None of them can: the entire tuple is fixed while the
value grows. -/
theorem class_measures_all_constant (k l : Nat) (φ : Nat → Nat → Nat)
    (hclass : ∀ i x y : Nat, x % 2 ^ k = y % 2 ^ k → x % 3 ^ l = y % 3 ^ l →
      φ i x = φ i y) :
    ∃ n : Nat, 1 < n ∧ ∀ i : Nat, φ i (acceleratedStep n) = φ i n := by
  obtain ⟨n, hgt, hc2, hc3⟩ := exists_congruent_step k l
  exact ⟨n, hgt, fun i => hclass i _ _ hc2.symm hc3.symm⟩

/-- **No two-component lexicographic rank on a congruence quotient decreases.**
The general-arity statement is `class_measures_all_constant`; this is the
concrete instance, spelled out so that the shape is unmistakable.  Both
disjuncts of the lexicographic condition fail at the witness, because both
measures are *equal* at the two endpoints. -/
theorem no_class_lex_ranking (k l : Nat) (φ ψ : Nat → Nat)
    (hφ : ∀ x y : Nat, x % 2 ^ k = y % 2 ^ k → x % 3 ^ l = y % 3 ^ l → φ x = φ y)
    (hψ : ∀ x y : Nat, x % 2 ^ k = y % 2 ^ k → x % 3 ^ l = y % 3 ^ l → ψ x = ψ y) :
    ¬ (∀ x : Nat, 1 < x →
        φ (acceleratedStep x) < φ x ∨
          (φ (acceleratedStep x) = φ x ∧ ψ (acceleratedStep x) < ψ x)) := by
  intro hdec
  obtain ⟨n, hgt, hc2, hc3⟩ := exists_congruent_step k l
  have hφn : φ (acceleratedStep n) = φ n := hφ _ _ hc2.symm hc3.symm
  have hψn : ψ (acceleratedStep n) = ψ n := hψ _ _ hc2.symm hc3.symm
  rcases hdec n hgt with h | ⟨_, h⟩ <;> omega

/-! ## No finite set of window lengths -/

/-- Along an odd run the value strictly increases at every intermediate time.
If `n + 1 = 2 ^ L` then the first `L` steps are one odd run and each prefix
lands strictly above `n`. -/
theorem run_grows {L n : Nat} (hn : n + 1 = 2 ^ L) {j : Nat} (hj : 0 < j)
    (hjL : j ≤ L) : n < acceleratedOrbit j n := by
  have hn' : n + 1 = 2 ^ ((L - j) + j) * 1 := by
    rw [show L - j + j = L by omega, Nat.mul_one]; exact hn
  exact heavy_return_grows hj (by omega) hn'

/-- **No bounded window set.**  For every bound `M` there is an `n > 1` that
fails to drop within *any* window of length at most `M`.

So the certificate shape "there is a finite set `S` of window lengths such that
every `x > 1` satisfies `T^j(x) < x` for some `j ∈ S`" is refuted outright — not
obstructed, refuted.  Witness `n = 2 ^ (M+2) − 1`, for which
`T^j(n) + 1 = 3 ^ j · 2 ^ (M+2−j)` for `j ≤ M + 2`, strictly exceeding
`2 ^ (M+2)` at every `j ≥ 1`.

Two corollaries.  The stopping time is unbounded, since `σ(2 ^ K − 1) ≥ K`.  And
any transition invariant for Collatz assembled from window-drop relations must
have infinitely many components, hence is not a finite certificate — which,
combined with `no_class_transition_invariant`, leaves the components of a finite
certificate neither congruence-definable nor window-based. -/
theorem no_bounded_window_set (M : Nat) :
    ∃ n : Nat, 1 < n ∧ ∀ j : Nat, j ≤ M → ¬ acceleratedOrbit j n < n := by
  refine ⟨2 ^ (M + 2) - 1, ?_, ?_⟩
  · have h : (4:Nat) ≤ 2 ^ (M + 2) := by
      calc (4:Nat) = 2 ^ 2 := by decide
        _ ≤ 2 ^ (M + 2) := Nat.pow_le_pow_right (by omega) (by omega)
    omega
  · intro j hj
    have hn : (2 ^ (M + 2) - 1) + 1 = 2 ^ (M + 2) := by
      have : (1:Nat) ≤ 2 ^ (M + 2) := Nat.one_le_two_pow
      omega
    rcases Nat.eq_zero_or_pos j with h0 | hpos
    · subst h0
      rw [acceleratedOrbit_zero]
      omega
    · have := run_grows hn hpos (by omega)
      omega

/-- The stopping time is unbounded: for every `M` some number above `1` survives
`M` windows without dropping.  This is `no_bounded_window_set` restated as the
fact that shape S7 has no chance. -/
theorem stopping_time_unbounded (M : Nat) :
    ∃ n : Nat, 1 < n ∧ ∀ j : Nat, 0 < j → j ≤ M → n < acceleratedOrbit j n := by
  refine ⟨2 ^ (M + 2) - 1, ?_, ?_⟩
  · have h : (4:Nat) ≤ 2 ^ (M + 2) := by
      calc (4:Nat) = 2 ^ 2 := by decide
        _ ≤ 2 ^ (M + 2) := Nat.pow_le_pow_right (by omega) (by omega)
    omega
  · intro j hpos hj
    have hn : (2 ^ (M + 2) - 1) + 1 = 2 ^ (M + 2) := by
      have : (1:Nat) ≤ 2 ^ (M + 2) := Nat.one_le_two_pow
      omega
    exact run_grows hn hpos (by omega)

end TransitionInvariant
end Collatz
