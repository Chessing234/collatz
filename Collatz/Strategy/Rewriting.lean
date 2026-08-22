import Collatz.Accelerated

/-!
# Termination-prover machinery, and exactly where it dies

Automated termination provers for rewrite systems carry a standard toolbox:
simplification orders (recursive/lexicographic path orders, Knuth–Bendix
orders), polynomial and matrix interpretations, size-change graphs, and the
dependency-pair framework.  Rounds III–VIII closed the *ranking* half of that
toolbox: `NoFiniteRanking.no_class_ranking` and
`AnyModulusRanking.no_ranking_general` kill any measure constant on a finite
quotient, into any irreflexive order, and `TransitionInvariant` kills the
disjunctive (Podelski–Rybalchenko) and lexicographic shapes over congruence
abstractions.  Size-change termination is a special case of the last.

What those results do *not* touch is the family of certificates that read the
**digits of `x`** rather than a residue class.  A simplification order on binary
numerals is not a finite-quotient rank; neither is a matrix interpretation.
This file settles the simplification-order half of that gap, for every
reasonable encoding at once, and sets up the dependency-pair reduction.

## The encoding

Three encodings are natural: unary numerals, binary numerals with a
carry-propagating rewrite, and the parity word as a string rewriting system.
The third is a decoy — the parity word of `x` is not finitely computable from
`x` without already knowing the orbit terminates, so a rewrite system on parity
words is not an encoding of the problem at all.  The other two are honest, and
the theorem below applies to both: `bits` for binary, `List.replicate x true`
for unary.

## The obstruction: the numeral of `x` embeds in the numeral of `T x`

Every simplification order contains the homeomorphic embedding order (Higman);
that is what "simplification" means, and it is the property every path order and
every strictly monotone polynomial interpretation has by construction.  So a
simplification order can orient a rule `ℓ → r` only when `ℓ` does *not* embed in
`r`.

For the accelerated map the odd branch violates this on a whole family:

    x = 2 ^ (L+1) − 1     bits x     = 1^(L+1)
    T x = 3 · 2 ^ L − 1   bits (T x) = 1^L ++ [0, 1]

and `1^(L+1)` is a subsequence of `1^L ++ [0,1]` — take the `L` leading ones and
the trailing one.  The numeral *grows*, and it grows by embedding.  Smallest
instance: `3 = 11`, `T 3 = 5 = 101`.  Unary is even more direct: an odd step
increases the value, hence lengthens a unary numeral.

Consequences, all corollaries of `no_simplification_order`:

* RPO, LPO, MPO, KBO, and every strictly monotone polynomial interpretation over
  `Nat` fail on every faithful numeral encoding, at `x = 3`;
* `no_kbo_weight` states the Knuth–Bendix case separately, since it needs no
  order at all: for *every* assignment of letter weights the total weight of the
  numeral of `3` is at most that of the numeral of `5`.

## What survives, and why it is not a closure

A matrix interpretation of dimension `≥ 2` need not be strictly monotone, so it
escapes the embedding argument.  Unwound, a matrix interpretation for the binary
encoding is exactly an `Nat`-weighted automaton reading the binary digits of `x`
whose value strictly drops at every accelerated step — that is, a ranking
function that is a rational series in base two.  This is not a finite-quotient
rank, so nothing in `AnyModulusRanking` applies to it.  But `rank_terminates`
below shows any such object *proves the conjecture*: it is an attack, not a
hypothesis to be closed, and the search for one is the bounded-dimension search
that termination provers have run on the TPDB Collatz instances for two decades.

## The dependency-pair framework is vacuous here

`DPChain` is a dependency-pair chain for the single defined symbol of the
system.  Its dependency graph has one strongly connected component containing
both branches (the even branch feeds the odd one and back), so the DP framework
performs no decomposition at all: `dpChain_iff_never_one` says an infinite chain
is *literally* an orbit that never reaches `1`.  Every reduction-pair processor
applied to that component then demands a ranking function, and
`rank_no_dpChain` is the statement that the processor is sound.  So the DP
framework returns the conjecture unchanged.
-/

namespace Collatz
namespace Rewriting

/-! ## Binary numerals -/

/-- Binary digits of `n`, least significant first; `bits 0 = []`. -/
def bits (n : Nat) : List Bool :=
  if h : n = 0 then [] else (decide (n % 2 = 1)) :: bits (n / 2)
termination_by n
decreasing_by exact Nat.div_lt_self (Nat.pos_of_ne_zero h) (by omega)

@[simp] theorem bits_zero : bits 0 = [] := by
  rw [bits]; simp

/-- Appending a `1` digit at the least significant end. -/
theorem bits_odd (n : Nat) : bits (2 * n + 1) = true :: bits n := by
  have h1 : ¬ (2 * n + 1 = 0) := by omega
  have h2 : (2 * n + 1) % 2 = 1 := by omega
  have h3 : (2 * n + 1) / 2 = n := by omega
  rw [bits, dif_neg h1, h2, h3]
  simp

/-- Appending a `0` digit at the least significant end (only meaningful for `n > 0`). -/
theorem bits_even {n : Nat} (hn : 0 < n) : bits (2 * n) = false :: bits n := by
  have h1 : ¬ (2 * n = 0) := by omega
  have h2 : (2 * n) % 2 = 0 := by omega
  have h3 : (2 * n) / 2 = n := by omega
  rw [bits, dif_neg h1, h2, h3]
  simp

/-- `2 ^ L − 1` is the all-ones numeral of length `L`. -/
theorem bits_ones (L : Nat) : bits (2 ^ L - 1) = List.replicate L true := by
  induction L with
  | zero => simp
  | succ L ih =>
      have hp : 1 ≤ 2 ^ L := Nat.one_le_two_pow
      have hpow : 2 ^ (L + 1) = 2 * 2 ^ L := by
        rw [Nat.pow_succ]; omega
      have hx : 2 ^ (L + 1) - 1 = 2 * (2 ^ L - 1) + 1 := by omega
      rw [hx, bits_odd, ih, List.replicate_succ]

/-- `3 · 2 ^ L − 1` is `L` ones followed by `0`, `1`. -/
theorem bits_three (L : Nat) :
    bits (3 * 2 ^ L - 1) = List.replicate L true ++ [false, true] := by
  induction L with
  | zero =>
      have h0 : (3 : Nat) * 2 ^ 0 - 1 = 2 * 1 := by decide
      rw [h0, bits_even (by omega)]
      have h1 : (1 : Nat) = 2 * 0 + 1 := by omega
      rw [h1, bits_odd]
      simp
  | succ L ih =>
      have hp : 1 ≤ 2 ^ L := Nat.one_le_two_pow
      have hpow : 2 ^ (L + 1) = 2 * 2 ^ L := by
        rw [Nat.pow_succ]; omega
      have hx : 3 * 2 ^ (L + 1) - 1 = 2 * (3 * 2 ^ L - 1) + 1 := by omega
      rw [hx, bits_odd, ih, List.replicate_succ, List.cons_append]

/-! ## The step on the witness family -/

/-- The odd branch on the all-ones numeral. -/
theorem step_ones (L : Nat) :
    acceleratedStep (2 ^ (L + 1) - 1) = 3 * 2 ^ L - 1 := by
  have hp : 1 ≤ 2 ^ L := Nat.one_le_two_pow
  have hpow : 2 ^ (L + 1) = 2 * 2 ^ L := by rw [Nat.pow_succ]; omega
  have hne : ¬ ((2 ^ (L + 1) - 1) % 2 = 0) := by omega
  rw [acceleratedStep, if_neg hne]
  omega

/-! ## Homeomorphic embedding, and simplification orders -/

/-- `Emb a b` : `a` is a subsequence of `b`.  This is Higman's embedding order
restricted to strings, which every simplification order contains. -/
inductive Emb : List Bool → List Bool → Prop
  | nil (l : List Bool) : Emb [] l
  | cons {a : Bool} {l₁ l₂ : List Bool} : Emb l₁ l₂ → Emb (a :: l₁) (a :: l₂)
  | skip {a : Bool} {l₁ l₂ : List Bool} : Emb l₁ l₂ → Emb l₁ (a :: l₂)

theorem emb_refl (l : List Bool) : Emb l l := by
  induction l with
  | nil => exact Emb.nil []
  | cons a l ih => exact Emb.cons ih

theorem emb_replicate {m n : Nat} (h : m ≤ n) :
    Emb (List.replicate m true) (List.replicate n true) := by
  induction n generalizing m with
  | zero =>
      have : m = 0 := Nat.le_zero.mp h
      subst this; exact Emb.nil _
  | succ n ih =>
      cases m with
      | zero => exact Emb.nil _
      | succ m =>
          rw [List.replicate_succ, List.replicate_succ]
          exact Emb.cons (ih (by omega))

/-- **The embedding of the witness step, binary encoding.** -/
theorem bits_step_emb (L : Nat) :
    Emb (bits (2 ^ (L + 1) - 1)) (bits (acceleratedStep (2 ^ (L + 1) - 1))) := by
  rw [step_ones, bits_ones, bits_three]
  induction L with
  | zero =>
      simp only [List.replicate_succ, List.replicate_zero, List.nil_append]
      exact Emb.skip (Emb.cons (Emb.nil []))
  | succ L ih =>
      rw [List.replicate_succ (n := L + 1), List.replicate_succ (n := L),
        List.cons_append]
      exact Emb.cons ih

/-- The numeral strictly lengthens across the witness step. -/
theorem bits_step_length (L : Nat) :
    (bits (2 ^ (L + 1) - 1)).length
      < (bits (acceleratedStep (2 ^ (L + 1) - 1))).length := by
  rw [step_ones, bits_ones, bits_three]
  simp [List.length_replicate]

/-- A **simplification order** on numerals: irreflexive, transitive, and
containing the proper embedding order.  Every path order (RPO, LPO, MPO), the
Knuth–Bendix order, and every strictly monotone polynomial interpretation
induces one. -/
structure SimpOrder (R : List Bool → List Bool → Prop) : Prop where
  irrefl : ∀ s, ¬ R s s
  trans : ∀ {a b c}, R a b → R b c → R a c
  embed : ∀ {a b}, Emb a b → a.length < b.length → R b a

/-- **No simplification order orients the accelerated map on binary numerals.**
The failure is already at `x = 3`. -/
theorem no_simplification_order {R : List Bool → List Bool → Prop}
    (hR : SimpOrder R) :
    ¬ (∀ x : Nat, 1 < x → R (bits x) (bits (acceleratedStep x))) := by
  intro hdec
  have hx : (1 : Nat) < 2 ^ (1 + 1) - 1 := by decide
  have h1 := hdec (2 ^ (1 + 1) - 1) hx
  have h2 := hR.embed (bits_step_emb 1) (bits_step_length 1)
  exact hR.irrefl _ (hR.trans h1 h2)

/-- The same for **unary** numerals: an odd step increases the value, hence
lengthens the numeral, hence embeds. -/
theorem unary_step_emb {x : Nat} (hx : x % 2 = 1) :
    Emb (List.replicate x true)
      (List.replicate (acceleratedStep x) true) := by
  have hne : ¬ (x % 2 = 0) := by omega
  rw [acceleratedStep, if_neg hne]
  exact emb_replicate (by omega)

theorem unary_step_length {x : Nat} (hx : x % 2 = 1) (_hx1 : 0 < x) :
    (List.replicate x true).length
      < (List.replicate (acceleratedStep x) true).length := by
  have hne : ¬ (x % 2 = 0) := by omega
  rw [acceleratedStep, if_neg hne]
  simp only [List.length_replicate]
  omega

theorem no_simplification_order_unary {R : List Bool → List Bool → Prop}
    (hR : SimpOrder R) :
    ¬ (∀ x : Nat, 1 < x →
        R (List.replicate x true) (List.replicate (acceleratedStep x) true)) := by
  intro hdec
  have h1 := hdec 3 (by omega)
  have h2 := hR.embed (unary_step_emb (x := 3) (by omega))
    (unary_step_length (x := 3) (by omega) (by omega))
  exact hR.irrefl _ (hR.trans h1 h2)

/-! ## Knuth–Bendix weights, with no order at all -/

/-- Total weight of a numeral under an arbitrary assignment of letter weights. -/
def weight (w : Bool → Nat) : List Bool → Nat
  | [] => 0
  | a :: l => w a + weight w l

theorem weight_mono {w : Bool → Nat} {a b : List Bool} (h : Emb a b) :
    weight w a ≤ weight w b := by
  induction h with
  | nil l =>
      induction l with
      | nil => exact Nat.le_refl 0
      | cons c l ih => simp only [weight]; omega
  | cons _ ih => simp only [weight]; omega
  | skip _ ih => simp only [weight]; omega

/-- **No Knuth–Bendix weight decreases along the map**, for any letter weights.
KBO compares total weight first and only breaks ties by precedence, so a
non-decrease of the weight is already fatal. -/
theorem no_kbo_weight (w : Bool → Nat) :
    ¬ (∀ x : Nat, 1 < x →
        weight w (bits (acceleratedStep x)) < weight w (bits x)) := by
  intro hdec
  have hx : (1 : Nat) < 2 ^ (1 + 1) - 1 := by decide
  have h1 := hdec (2 ^ (1 + 1) - 1) hx
  have h2 : weight w (bits (2 ^ (1 + 1) - 1))
      ≤ weight w (bits (acceleratedStep (2 ^ (1 + 1) - 1))) :=
    weight_mono (bits_step_emb 1)
  omega

/-! ## Matrix interpretations: the one-dimensional case dies -/

/-- A **one-dimensional matrix interpretation** of the binary encoding: each
digit acts on the value by an affine map over `Nat`, `V (2n + d) = a d · V n + b d`.
This is exactly a linear polynomial interpretation of the two digit symbols, and
exactly a one-state weighted automaton reading the binary digits of `x`.

Unlike a simplification order it is *not* required to be monotone, so
`no_simplification_order` does not apply to it — and unlike a congruence rank it
is not constant on any finite quotient, so `AnyModulusRanking` does not apply
either.  It still dies, and in four evaluations. -/
theorem no_linear_interpretation (a₀ a₁ b₀ b₁ : Nat) (V : Nat → Nat)
    (heven : ∀ n : Nat, 0 < n → V (2 * n) = a₀ * V n + b₀)
    (hodd : ∀ n : Nat, V (2 * n + 1) = a₁ * V n + b₁) :
    ¬ (∀ x : Nat, 1 < x → V (acceleratedStep x) < V x) := by
  intro hdec
  -- `3 → 5` forces the even digit to contract: `V 2 < V 1`.
  have h35 : V 5 < V 3 := by
    have := hdec 3 (by omega)
    rwa [show acceleratedStep 3 = 5 from by decide] at this
  have e3 : V 3 = a₁ * V 1 + b₁ := by
    have := hodd 1; rwa [show 2 * 1 + 1 = 3 from by omega] at this
  have e5 : V 5 = a₁ * V 2 + b₁ := by
    have := hodd 2; rwa [show 2 * 2 + 1 = 5 from by omega] at this
  have e2 : V 2 = a₀ * V 1 + b₀ := by
    have := heven 1 (by omega); rwa [show 2 * 1 = 2 from by omega] at this
  have hcontract : a₀ * V 1 + b₀ < V 1 := by
    have h : a₁ * V 2 < a₁ * V 1 := by omega
    have ha : V 2 < V 1 := by
      rcases Nat.lt_or_ge (V 2) (V 1) with h1 | h1
      · exact h1
      · exact absurd h (Nat.not_lt.mpr (Nat.mul_le_mul_left a₁ h1))
    rw [e2] at ha
    exact ha
  -- If the even digit does not annihilate, the contraction is impossible.
  cases Nat.eq_zero_or_pos a₀ with
  | inr hpos =>
      have : V 1 ≤ a₀ * V 1 := Nat.le_mul_of_pos_left _ hpos
      omega
  | inl hzero =>
      -- If it does annihilate, every even value is the constant `b₀`,
      -- and `8 → 4` has nowhere to fall.
      have e4 : V 4 = a₀ * V 2 + b₀ := by
        have := heven 2 (by omega); rwa [show 2 * 2 = 4 from by omega] at this
      have e8 : V 8 = a₀ * V 4 + b₀ := by
        have := heven 4 (by omega); rwa [show 2 * 4 = 8 from by omega] at this
      have h84 : V 4 < V 8 := by
        have := hdec 8 (by omega)
        rwa [show acceleratedStep 8 = 4 from by decide] at this
      subst hzero
      omega

/-! ## The dependency-pair framework -/

/-- A dependency-pair chain for the one defined symbol of the system: an
infinite sequence of genuine steps above the fixed point. -/
def DPChain (f : Nat → Nat) : Prop :=
  ∀ i : Nat, 1 < f i ∧ f (i + 1) = acceleratedStep (f i)

theorem orbit_succ_step (j n : Nat) :
    acceleratedOrbit (j + 1) n = acceleratedStep (acceleratedOrbit j n) := by
  induction j generalizing n with
  | zero => rfl
  | succ j ih => simpa using ih (acceleratedStep n)

theorem acceleratedStep_pos {x : Nat} (hx : 1 < x) : 0 < acceleratedStep x := by
  rw [acceleratedStep]
  by_cases h : x % 2 = 0
  · rw [if_pos h]; omega
  · rw [if_neg h]; omega

/-- **The dependency graph has one component, and its chains are orbits.**
An infinite dependency-pair chain exists exactly when some orbit never reaches
`1`.  The DP framework therefore returns the conjecture unchanged. -/
theorem dpChain_iff_never_one :
    (∃ f : Nat → Nat, DPChain f)
      ↔ (∃ x : Nat, ∀ i : Nat, 1 < acceleratedOrbit i x) := by
  constructor
  · intro ⟨f, hf⟩
    refine ⟨f 0, ?_⟩
    intro i
    have key : ∀ i : Nat, acceleratedOrbit i (f 0) = f i := by
      intro i
      induction i with
      | zero => rfl
      | succ i ih => rw [orbit_succ_step, ih, (hf i).2]
    rw [key i]; exact (hf i).1
  · intro ⟨x, hx⟩
    refine ⟨fun i => acceleratedOrbit i x, ?_⟩
    intro i
    exact ⟨hx i, orbit_succ_step i x⟩

/-- **Soundness of the reduction-pair processor.**  A ranking function on the
single component removes it — and thereby proves the conjecture.  This is what
every matrix or polynomial interpretation would supply, and why such an object
is an attack rather than a hypothesis to be closed. -/
theorem rank_no_dpChain (V : Nat → Nat)
    (h : ∀ x : Nat, 1 < x → V (acceleratedStep x) < V x) :
    ¬ (∃ f : Nat → Nat, DPChain f) := by
  intro ⟨f, hf⟩
  have desc : ∀ i : Nat, V (f (i + 1)) < V (f i) := by
    intro i
    have := h (f i) (hf i).1
    rw [(hf i).2]; exact this
  have nodesc : ∀ n : Nat, ∀ g : Nat → Nat,
      (∀ i : Nat, V (g (i + 1)) < V (g i)) → V (g 0) ≤ n → False := by
    intro n
    induction n with
    | zero =>
        intro g hg h0
        exact Nat.not_succ_le_zero _ (Nat.le_trans (hg 0) h0)
    | succ n ih =>
        intro g hg h0
        refine ih (fun i => g (i + 1)) (fun i => hg (i + 1)) ?_
        have := hg 0
        omega
  exact nodesc (V (f 0)) f desc (Nat.le_refl _)

/-- A ranking function proves that every orbit reaches `1`. -/
theorem rank_terminates (V : Nat → Nat)
    (h : ∀ x : Nat, 1 < x → V (acceleratedStep x) < V x) :
    ∀ x : Nat, 0 < x → ∃ k : Nat, acceleratedOrbit k x = 1 := by
  have main : ∀ n x : Nat, V x ≤ n → 0 < x → ∃ k : Nat, acceleratedOrbit k x = 1 := by
    intro n
    induction n with
    | zero =>
        intro x hV hx
        by_cases h1 : 1 < x
        · have := h x h1; omega
        · exact ⟨0, by rw [acceleratedOrbit_zero]; omega⟩
    | succ n ih =>
        intro x hV hx
        by_cases h1 : 1 < x
        · have hlt := h x h1
          obtain ⟨k, hk⟩ := ih (acceleratedStep x) (by omega) (acceleratedStep_pos h1)
          exact ⟨k + 1, by rw [acceleratedOrbit_succ]; exact hk⟩
        · exact ⟨0, by rw [acceleratedOrbit_zero]; omega⟩
  intro x hx
  exact main (V x) x (Nat.le_refl _) hx

end Rewriting
end Collatz
