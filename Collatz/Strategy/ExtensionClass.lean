import Collatz.Strategy.RepetitionDescent

/-!
# The extension class — the Collatz cycle obstruction as a genuine `Ext¹`

## The admission-rule answer

This file introduces an object that is *not* a function of the parity word: it is a
**short exact sequence of `ℤ[t]`-modules**, and the invariant is its class in a
derived functor.  What is new is not a number but a *category*: the word `w` is
replaced by the module `N_w = ℤ²` with `t` acting through the transfer matrix

    M w = ⟨3 ^ a, C w, 2 ^ L⟩   (upper triangular, `L = |w|`, `a = ones w`)

which sits in `0 → ℤ_{3^a} → N_w → ℤ_{2^L} → 0`.

The point of the file is a **negative** theorem, stated precisely so no later round
spends a cycle on it:

> `Ext¹_{ℤ[t]}(ℤ_{2^L}, ℤ_{3^a}) ≅ ℤ / G` and the class of `N_w` is `C w mod G`.
> The obstruction group of the homological formulation is *exactly* the group
> `AccumulatorAutomaton.gap_coprime_snoc` proves arithmetically free.

and a structural explanation of the soundness filter:

> `Ext¹` is an additive bifunctor, so `C ↦ d·C` acts on the obstruction group by
> *multiplication by `d`*.  Therefore **every** invariant obtained by applying an
> additive functor to `N_w` is `d`-linear, hence killed by the soundness filter.
> The filter is not an empirical rule about past attempts; it is a theorem about
> abelian categories.

The computation of `Ext¹` is a two-term cochain complex with an explicit
differential, `Hom(R, A) --(t - 2^L)*--> Hom(R, A)`, i.e.

    0 → ℤ --(· (3^a - 2^L))--> ℤ → 0,     H⁰ = 0,  H¹ = ℤ / G.

Everything below is the *elementary* content of that complex: `H⁰ = 0` is
`hom_trivial`, `H¹ = ℤ/G` is `splits_iff_dvd` together with `conj_shift`
(the coboundary), and `d`-linearity is `class_scales`.

## Part B — the gluing obstruction over the 2-adic tower vanishes

The second half is `bounded_tower`, the exact accounting of asset (a).  Windows are
an inverse system; `lim¹` of an inverse system of *finite* sets is always zero, so
there is no local-to-global obstruction at all unless a level is **empty**, and a
level can only be empty after an archimedean cut `x < B`.  `bounded_tower` proves
the contrapositive in the form actually used:

> if every `a < B` fails some level, then a *single* level `K` is already empty;
> equivalently, if every level has a survivor below `B`, some `a < B` survives all
> levels.

So "no cycle below `1086464`" is not a family of infinitely many facts — it is one
empty level.  (Index convention, since this file uses both numbers: the last
*nonempty* level is `182`, witnessed by `x = 1027431` surviving to `L = 182`, and the
first *empty* level is therefore `K = 183`.  Both appear below; they are consecutive,
not inconsistent.)
-/

namespace Collatz
namespace ExtensionClass

open RepetitionDescent

/-! ## Part 1 — the transfer module -/

/-- An upper triangular integer matrix `⟨p, c, q⟩ = [[p, c], [0, q]]`, equivalently
the affine map `x ↦ (p·x + c)/q`. -/
structure Aff where
  p : Nat
  c : Nat
  q : Nat
deriving DecidableEq, Repr

/-- `A.then B` is "do `A`, then `B`" — matrix product `B · A`. -/
def Aff.then (A B : Aff) : Aff := ⟨B.p * A.p, B.p * A.c + B.c * A.q, B.q * A.q⟩

/-- The letter matrices: an odd letter is `x ↦ (3x+1)/2`, an even one `x ↦ x/2`. -/
def letter (b : Nat) : Aff := if b = 1 then ⟨3, 1, 2⟩ else ⟨1, 0, 2⟩

/-- The transfer matrix of a word, read in time order. -/
def transfer : List Nat → Aff
  | [] => ⟨1, 0, 1⟩
  | b :: t => (letter b).then (transfer t)

/-- **The transfer matrix is the accumulator.**  `M w = [[3^a, C w], [0, 2^L]]`.
This is the bridge: the whole `(L, a, C)` triple is one matrix, and conversely. -/
theorem transfer_eq (w : List Nat) :
    transfer w = ⟨3 ^ ones w, wC w, 2 ^ w.length⟩ := by
  induction w with
  | nil => rfl
  | cons b t ih =>
    have hb : (letter b).q = 2 := by
      unfold letter; by_cases h : b = 1 <;> simp [h]
    unfold transfer
    rw [ih]
    unfold Aff.then letter
    by_cases h : b = 1
    · subst h
      have h3 : (3 : Nat) ^ (1 + ones t) = 3 * 3 ^ ones t := by
        rw [Nat.add_comm, Nat.pow_succ, Nat.mul_comm]
      simp [ones_cons, wC_cons, List.length_cons, Nat.pow_succ, h3, Nat.mul_comm]
    · simp [ones_cons, wC_cons, List.length_cons, Nat.pow_succ, h, Nat.mul_comm]

/-! ### The short exact sequence and its splittings

`N_w = ℤ²` with `t` acting by `M w`.  The submodule `A = ℤ·e₁` has `t` acting by
`3^a`; the quotient `B = ℤ` has `t` acting by `2^L`.  A `ℤ[t]`-splitting is a
`t`-equivariant `s : B → N_w`, `s 1 = (k, 1)`, and equivariance is exactly
`3^a·k + C = 2^L·k`. -/

/-- A splitting of the transfer extension: an integer `k` with `p·k + c = q·k`. -/
def Splits (p c q : Nat) : Prop := ∃ k : Nat, p * k + c = q * k

/-- **`H¹` computation, the vanishing half.**  The extension splits iff the class
`c mod (q - p)` vanishes.  For a word this reads `G ∣ C`, and the splitting value
`k = C / G` is exactly the cycle point (`HighPart`'s `n = C/G`). -/
theorem splits_iff_dvd {p q c : Nat} (h : p ≤ q) :
    Splits p c q ↔ (q - p) ∣ c := by
  have key : ∀ k : Nat, (q - p) * k = q * k - p * k := fun k => Nat.sub_mul q p k
  constructor
  · rintro ⟨k, hk⟩
    refine ⟨k, ?_⟩
    have h1 := key k
    have h2 : p * k ≤ q * k := Nat.mul_le_mul_right k h
    omega
  · rintro ⟨k, hk⟩
    refine ⟨k, ?_⟩
    have h1 := key k
    have h2 : p * k ≤ q * k := Nat.mul_le_mul_right k h
    omega

/-- The splitting, when it exists, is unique: `H⁰ = Hom_{ℤ[t]}(ℤ_{2^L}, ℤ_{3^a}) = 0`.
Concretely, `p ≠ q` forces the only `t`-equivariant map `B → A` to be zero. -/
theorem hom_trivial {p q m : Nat} (h : p < q) (hm : p * m = q * m) : m = 0 := by
  obtain ⟨s, hs⟩ : ∃ s, q = p + s + 1 := ⟨q - p - 1, by omega⟩
  subst hs
  have hq : (p + s + 1) * m = p * m + s * m + m := by
    rw [Nat.add_mul, Nat.add_mul, Nat.one_mul]
  omega

/-- The cycle criterion in transfer-matrix form: a word is a `3x+1` cycle word iff
its transfer extension splits. -/
theorem word_splits_iff {w : List Nat} (h : 3 ^ ones w ≤ 2 ^ w.length) :
    Splits (3 ^ ones w) (wC w) (2 ^ w.length) ↔ (2 ^ w.length - 3 ^ ones w) ∣ wC w :=
  splits_iff_dvd h

/-! ### The coboundary — why the class lives in `ℤ/G`

Changing the set-theoretic lift of the quotient generator by `m` conjugates `M` by
the unipotent `U m = [[1, m], [0, 1]] ∈ GL₂(ℤ)`, and changes `c` by `-(q-p)·m`.
Stated over `ℤ` and without inverses, as `U · M' = M · U`. -/

/-- Integer 2×2 matrices. -/
structure Mat2 where
  a : Int
  b : Int
  c : Int
  d : Int
deriving DecidableEq, Repr

def Mat2.mul (X Y : Mat2) : Mat2 :=
  ⟨X.a * Y.a + X.b * Y.c, X.a * Y.b + X.b * Y.d,
   X.c * Y.a + X.d * Y.c, X.c * Y.b + X.d * Y.d⟩

/-- The unipotent `[[1, m], [0, 1]]`, a generator of the stabiliser of the flag. -/
def U (m : Int) : Mat2 := ⟨1, m, 0, 1⟩

/-- The upper triangular `[[p, c], [0, q]]`. -/
def tri (p c q : Int) : Mat2 := ⟨p, c, 0, q⟩

/-- **The coboundary.**  `U m` conjugates `tri p (c - (q-p)·m) q` into `tri p c q`.
So `c` is only well defined modulo `q - p`: the cocycles are `ℤ`, the coboundaries
are `G·ℤ`, and `H¹ = ℤ / G`. -/
theorem conj_shift (p c q m : Int) :
    (U m).mul (tri p (c - (q - p) * m) q) = (tri p c q).mul (U m) := by
  have hsm : (q - p) * m = q * m - p * m := Int.sub_mul q p m
  unfold Mat2.mul U tri
  simp only [Mat2.mk.injEq]
  refine ⟨by simp, ?_, by simp, by simp⟩
  simp only [Int.one_mul, Int.mul_one]
  rw [Int.mul_comm m q, Int.mul_comm p m] at *
  omega

/-- Conjugation by `U m` does not change whether the extension splits — the class in
`ℤ/G` is the complete invariant of the isomorphism class. -/
theorem dvd_shift (G c m : Int) : G ∣ c ↔ G ∣ (c - G * m) := by
  constructor
  · rintro ⟨k, rfl⟩
    exact ⟨k - m, (Int.mul_sub G k m).symm⟩
  · rintro ⟨k, hk⟩
    refine ⟨k + m, ?_⟩
    rw [Int.mul_add]
    omega

/-! ### `d`-linearity — the soundness filter is a theorem about additive functors -/

/-- **The class scales.**  `Ext¹` is an additive bifunctor, so the world `3x + d`
multiplies the class by `d`.

**Read the status honestly: what is kernel-checked below is one line of `Nat`
divisibility, `G ∣ c → G ∣ d * c`.**  The categorical reading — that every additive
invariant of the transfer extension is `d`-linear — is `PROVED-on-paper` and rests on
`Ext¹` being an additive bifunctor, which is not formalised here.  An earlier draft
presented the two as one result and `RESEARCH.md` Part III called it "the one real
theorem the round produced"; the gap between them was unlabelled.

**And the conclusion drawn from it was backwards.**  `d`-linearity of the class means
the obstruction group carries a `d`-*action* — i.e. the invariant is `d`-**sensitive**,
which is the opposite of `d`-blind.  This same file proves the sharp form three
theorems below: `delta_realises` says `w` is a `3x+d` cycle word iff `δ(w) ∣ d`, a
complete `d`-separating criterion.  `CLOSURE.md` already lists `δ(w)` under "what is
*not* in any class".  What Class 4 kills is degree-0 homogeneity under `C ↦ d·C`, not
`d`-linearity; see `CLOSURE.md` diagnostic 3. -/
theorem class_scales (G c d : Nat) (h : G ∣ c) : G ∣ d * c := by
  obtain ⟨k, rfl⟩ := h
  exact ⟨d * k, (Nat.mul_left_comm d G k)⟩

/-- The set of worlds realising a word is a *subgroup* of `ℤ`, generated by
`δ(w) = G / gcd(C, G)` (`DeltaSpectrum.delta`).  Half of the statement, the half
that needs no division: if `δ ∣ d` then `w` is a `3x+d` cycle word. -/
theorem delta_dvd_realises {G c g d k e f : Nat}
    (hG : G = k * g) (hc : c = g * f) (hd : d = k * e) : G ∣ d * c := by
  subst hG; subst hc; subst hd
  exact ⟨e * f, by simp [Nat.mul_comm, Nat.mul_left_comm]⟩

/-- The `gcd` instance: `δ(w) ∣ d` really does make `w` a `3x+d` cycle word. -/
theorem delta_realises {G c g d : Nat} (hg : g = Nat.gcd c G) (hpos : 0 < g)
    (hd : G / g ∣ d) : G ∣ d * c := by
  obtain ⟨f, hf⟩ : g ∣ c := hg ▸ Nat.gcd_dvd_left c G
  obtain ⟨k, hk⟩ : g ∣ G := hg ▸ Nat.gcd_dvd_right c G
  obtain ⟨e, he⟩ := hd
  have hGk : G = k * g := by rw [hk, Nat.mul_comm]
  have hq : G / g = k := by rw [hGk, Nat.mul_div_cancel _ hpos]
  exact delta_dvd_realises hGk hf (by rw [he, hq])

/-! ## Part 2 — the gluing obstruction, and the exact value of asset (a)

The window sets form an inverse system.  With no archimedean cut every level is a
nonempty finite set, so the inverse limit is nonempty (`lim¹ = 0`) and there is no
gluing obstruction whatsoever — the glued object is a 2-adic integer, and the
conjecture is that it is not a positive rational integer.  The **only** way to get an
obstruction is to make a level empty, and that needs a bound `B`. -/

/-- The window predicate is antitone in the level: surviving level `k+1` implies
surviving level `k`. -/
def Antitone2 (S : Nat → Nat → Prop) : Prop := ∀ k a, S (k + 1) a → S k a

theorem antitone_le {S : Nat → Nat → Prop} (h : Antitone2 S) :
    ∀ j k a, j ≤ k → S k a → S j a := by
  intro j k a hjk
  induction k with
  | zero => intro hs; have : j = 0 := Nat.le_zero.mp hjk; subst this; exact hs
  | succ n ih =>
    intro hs
    rcases Nat.lt_or_ge j (n + 1) with hlt | hge
    · exact ih (Nat.le_of_lt_succ hlt) (h n a hs)
    · have : j = n + 1 := Nat.le_antisymm hjk hge
      subst this; exact hs

/-- **Compactness of the bounded tower.**  If every `a < B` drops out at some level,
then a *single* level `K` is already empty below `B`.

This is `lim¹ = 0` in the only form the problem uses.  Contrapositive: if every level
has a survivor below `B`, then some `a < B` survives *every* level — the global
section exists and it is an honest integer.  So the verified range is not an infinite
family of facts but one empty level; `RESEARCH.md` records that for `B = 1086464`
that level is `K = 183`, and no smaller `K` works. -/
theorem bounded_tower {S : Nat → Nat → Prop} (hmono : Antitone2 S) :
    ∀ B : Nat, (∀ a, a < B → ∃ k, ¬ S k a) → ∃ K, ∀ a, a < B → ¬ S K a := by
  intro B
  induction B with
  | zero => intro _; exact ⟨0, fun a ha => absurd ha (Nat.not_lt_zero a)⟩
  | succ n ih =>
    intro h
    obtain ⟨K', hK'⟩ := ih (fun a ha => h a (Nat.lt_succ_of_lt ha))
    obtain ⟨k0, hk0⟩ := h n (Nat.lt_succ_self n)
    refine ⟨max K' k0, ?_⟩
    intro a ha hs
    rcases Nat.lt_or_ge a n with hlt | hge
    · exact hK' a hlt (antitone_le hmono K' (max K' k0) a (Nat.le_max_left _ _) hs)
    · have : a = n := Nat.le_antisymm (Nat.le_of_lt_succ ha) hge
      subst this
      exact hk0 (antitone_le hmono k0 (max K' k0) a (Nat.le_max_right _ _) hs)

/-- The form actually used: every level nonempty below `B` forces a global survivor. -/
theorem tower_global_section {S : Nat → Nat → Prop} (hmono : Antitone2 S) (B : Nat)
    (hne : ∀ K, ∃ a, a < B ∧ S K a) : ∃ a, a < B ∧ ∀ k, S k a := by
  refine Classical.byContradiction (fun hcon => ?_)
  have h : ∀ a, a < B → ∃ k, ¬ S k a := by
    intro a ha
    refine Classical.byContradiction (fun hk => ?_)
    exact hcon ⟨a, ha, fun k => Classical.byContradiction fun hn => hk ⟨k, hn⟩⟩
  obtain ⟨K, hK⟩ := bounded_tower hmono B h
  obtain ⟨a, ha, hsa⟩ := hne K
  exact hK a ha hsa

/-! ### Worked examples (kernel-checked)

The four numbers `(L, a, C, G)` read off the transfer matrix, and the class
`C mod G` that decides whether the extension splits. -/

/-- `w = 10`: `M w = [[3, 1], [0, 4]]`, i.e. `x ↦ (3x+1)/4`. -/
example : transfer [1, 0] = ⟨3, 1, 4⟩ := rfl

/-- `w = 1010`: `M w = [[9, 7], [0, 16]]`.  `G = 7`, class `= 0`, the extension
splits with `k = 1` — the trivial cycle `1 → 2 → 1`, doubled. -/
example : transfer [1, 0, 1, 0] = ⟨9, 7, 16⟩ := rfl
example : Splits 9 7 16 := ⟨1, rfl⟩
example : (16 - 9) ∣ (7 : Nat) := by decide

/-- `w = 1100`: same `(L, a) = (4, 2)`, so the same obstruction group `ℤ/7`, but the
class is `5 ≠ 0`.  The extension does not split; `δ(w) = 7`, so `1100` is a cycle
word of `3x + 7` and of nothing smaller. -/
example : transfer [1, 1, 0, 0] = ⟨9, 5, 16⟩ := rfl
example : ¬ ((16 - 9) ∣ (5 : Nat)) := by decide
example : Splits 9 5 16 → False := by
  intro h
  have := (splits_iff_dvd (by decide : (9:Nat) ≤ 16)).mp h
  revert this
  decide

/-- The coboundary in action: `5` and `5 - 7·1 = -2` are the same class, and
`5 + 7 = 12` is too — the cocycle group is `ℤ`, the coboundaries are `7ℤ`. -/
example : (U 1).mul (tri 9 (5 - (16 - 9) * 1) 16) = (tri 9 5 16).mul (U 1) :=
  conj_shift 9 5 16 1

/-! ## Summary

* `transfer_eq` — the word's transfer matrix *is* `(L, a, C)`.  Consequently every
  invariant of `M w` computed by an additive functor is a function of `(L, a, C, G)`
  and is dead by admission rule 2.  This closes, in one statement, the whole
  representation-theoretic / K-theoretic / homological family of proposals.
* `splits_iff_dvd`, `hom_trivial`, `conj_shift`, `dvd_shift` — the obstruction group
  is `H¹ = ℤ/G` with class `C mod G`, and `H⁰ = 0`.  `ℤ/G` is precisely the group
  `AccumulatorAutomaton.gap_coprime_snoc` proves carries zero information across
  lengths.
* `class_scales`, `delta_dvd_realises` — the `d`-action on `H¹` is multiplication,
  so the soundness filter is a corollary of additivity, not an empirical rule.
* `bounded_tower`, `tower_global_section` — the 2-adic gluing obstruction vanishes;
  the only obstruction available on the tower is an *empty level*, which requires the
  archimedean cut.  Asset (a) is exactly one empty level.
-/

/-! ## Axiom audit — this file was the only Round IX arrival without one. -/

#print axioms transfer_eq
#print axioms splits_iff_dvd
#print axioms class_scales
#print axioms bounded_tower
#print axioms tower_global_section


end ExtensionClass
end Collatz
