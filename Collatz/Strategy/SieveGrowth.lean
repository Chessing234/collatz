import Collatz.Structure.SieveDensity
import Collatz.Strategy.AccumulatorArith

/-!
# The sieve's survivors multiply

`Collatz/Structure/SieveDensity.lean` records a measurement.  At levels `4`, `6`,
`8`, `10` the residue sieve retains `3`, `8`, `19`, `64` classes, and the file
concludes — from those four numbers and the shape of the table — that "the
surviving set grows without bound".  That conclusion was an extrapolation.  The
kernel had checked four rows, and nothing in the development ruled out the
possibility that the count levels off, or even falls back to the single class
`2 ^ k − 1` that `Obstruction.sieve_never_clears` pins down by hand.

This file removes the extrapolation.  The count really does grow, at every
level, and it grows exponentially, with a rate proved rather than observed.

## The mechanism: safety concatenates

Call a residue `r` **safe to level `k`** when its whole parity history is
expanding: for every `i ≤ k`,

`2 ^ i ≤ 3 ^ (number of odd steps in the first i steps out of r)`.

Safety is the first half of the sieve's escape condition — the descent criterion
`Descends i s` asks for `3 ^ a < 2 ^ i` *and* a non-increasing iterate, so a safe
residue fails it on the first clause alone and therefore survives.  Safety is
strictly a sufficient condition for survival, which is exactly what a lower
bound needs.  (Numerically the two coincide through level `14`; nothing here
depends on that.)

The point of safety, and the reason it is worth isolating from `survives`, is
that it is **closed under concatenation of orbits**.  Suppose `r` is safe to
level `k`, that `s` is safe to level `L`, and that `r'` is a residue whose first
`k` steps reproduce `r` and whose next `L` steps reproduce `s`.  Then for a time
`k + j` past the join, the odd-step counts simply add — this is the cocycle law
`AccumulatorArith.oddCount_add` — and

`2 ^ (k + j) = 2 ^ k · 2 ^ j ≤ 3 ^ a · 3 ^ b = 3 ^ (a + b)`.

Two multiplications of `Nat` inequalities.  Nothing archimedean, no logarithms,
no reals: the product of two expanding histories is an expanding history.

The joins exist because parity vectors are unconstrained.  Terras' bijection —
already in this development as `parityVector_surjective_mod_pow_two` and
`parityVector_injective_mod_pow_two` — says every `{0,1}`-word of length `k + L`
is the parity word of exactly one residue modulo `2 ^ (k + L)`.  Concatenating
the word of `r` with the word of `s` therefore names a residue `r'`, and the
pair `(r, s)` is recovered from `r'` as `(r' mod 2 ^ k, T^k(r') mod 2 ^ L)`.  So
the join is injective on pairs, and

`safeCount k · safeCount L ≤ safeCount (k + L)`.

## From supermultiplicativity to a rate

Supermultiplicativity converts any single measured level into a rate for all
levels.  The cheapest useful measurement is level `10`, where kernel evaluation
gives `safeCount 10 = 64 = 2 ^ 6`, and induction then gives

`2 ^ (6 m) ≤ safeCount (10 m) ≤ survivorCount (10 m)`,

i.e. the sieve retains at least `2 ^ (0.6 k)` classes along `10 ∣ k`.  Deeper
base cases give better exponents — `safeCount 14 = 734 > 2 ^ 9` would give
`9/14 = 0.643` — but level `14` exhausts the kernel's default budget, while
level `10` costs a few seconds and level `12` is both slower and *worse*
(`226 > 2 ^ 7` gives only `7/12 = 0.583`).  Ten is the sweet spot.  The true
growth rate is `2 ^ (H(θ) k)` with `θ = log 2 / log 3` and `H` the binary
entropy, `H(θ) = 0.94996…`; that constant is analytic and is not formalized
here.  `0.6` is a lower bound on it, and any positive lower bound suffices for
the conclusion below.

## A note on the formulation

Counting without `Finset` means counting lists.  The survivor count is a
`List.countP` over `List.range (2 ^ k)`, exactly as `SieveDensity` defines it,
and supermultiplicativity is proved by exhibiting the join list

`safeList k |>.flatMap (fun r₀ => (safeList L).map (join k L r₀))`

whose length is the product, showing it has no repetitions — the pair `(r₀, s)`
is recovered from the join by two `mod`s — and applying a pigeonhole lemma
proved here from `List.erase`.  The join itself is computable: rather than
choosing a residue from Terras' surjectivity with a choice principle, it is
found by `List.find?` over the range, and surjectivity only supplies the proof
that the search succeeds.  Nothing in this file is noncomputable.

## What this is, honestly

This is a **lower bound on an obstruction**, not a step toward descent.  It
proves the residue sieve hopeless rather than proving anything about Collatz.
Read it as the negative companion to `Obstruction.sieve_never_clears`: that
theorem says the sieve keeps at least one class forever, and one class might
conceivably be attacked by hand; this theorem says the sieve keeps
exponentially many, so no finite deepening and no bookkeeping over the survivor
list can ever finish.  The work of running the sieve to level `k` grows like
`2 ^ k`, and the residue left standing grows like `2 ^ (0.6 k)` at least.  The
method does not converge; it diverges more slowly than it costs.

A sharper way to say the same thing: the sieve's survivors form a *semigroup*
under concatenation of orbit windows.  A method whose failure set is closed
under concatenation cannot be finished by refinement, because refinement is
precisely concatenation.  That is the structural reason, and it is what the
supermultiplicativity lemma below says formally.
-/

namespace Collatz
namespace SieveGrowth

open Congruence

/-! ## Counting infrastructure

Two facts about lists that the argument needs and that the core library does not
supply in this form: `countP` is monotone in the predicate, and a duplicate-free
list embeds in no shorter list. -/

/-- A weaker predicate is satisfied at least as often. -/
theorem countP_mono {α : Type} {p q : α → Bool} (h : ∀ a, p a = true → q a = true) :
    ∀ l : List α, l.countP p ≤ l.countP q := by
  intro l
  induction l with
  | nil => simp
  | cons a t ih =>
    rw [List.countP_cons, List.countP_cons]
    by_cases hp : p a = true
    · rw [if_pos hp, if_pos (h a hp)]; omega
    · rw [if_neg hp]
      by_cases hq : q a = true
      · rw [if_pos hq]; omega
      · rw [if_neg hq]; omega

/-- **Pigeonhole.**  A list without repetitions is no longer than any list
containing all of its entries. -/
theorem length_le_of_nodup_subset {α : Type} [BEq α] [LawfulBEq α] :
    ∀ {l₁ l₂ : List α}, l₁.Nodup → l₁ ⊆ l₂ → l₁.length ≤ l₂.length := by
  intro l₁
  induction l₁ with
  | nil => intro l₂ _ _; simp
  | cons a t ih =>
    intro l₂ hnd hsub
    obtain ⟨hant, hndt⟩ := List.nodup_cons.mp hnd
    have ha : a ∈ l₂ := hsub (List.mem_cons_self)
    have hsub' : t ⊆ l₂.erase a := by
      intro b hb
      have hbne : b ≠ a := by
        intro hba
        exact hant (hba ▸ hb)
      exact (List.mem_erase_of_ne hbne).mpr (hsub (List.mem_cons_of_mem _ hb))
    have h1 := ih hndt hsub'
    have h2 : (l₂.erase a).length = l₂.length - 1 := List.length_erase_of_mem ha
    have h3 : 0 < l₂.length := List.length_pos_of_mem ha
    have h4 : (a :: t).length = t.length + 1 := by simp
    omega

/-- A map with a left inverse on the list preserves duplicate-freeness. -/
theorem nodup_map_of_leftInv {α β : Type} {f : α → β} {g : β → α} :
    ∀ {l : List α}, l.Nodup → (∀ a ∈ l, g (f a) = a) → (l.map f).Nodup := by
  intro l
  induction l with
  | nil => intro _ _; simp
  | cons a t ih =>
    intro hnd hinv
    obtain ⟨hant, hndt⟩ := List.nodup_cons.mp hnd
    rw [List.map_cons, List.nodup_cons]
    refine ⟨?_, ih hndt (fun b hb => hinv b (List.mem_cons_of_mem _ hb))⟩
    intro hmem
    obtain ⟨b, hb, hfb⟩ := List.mem_map.mp hmem
    have hba : b = a := by
      have h1 : g (f b) = b := hinv b (List.mem_cons_of_mem _ hb)
      have h2 : g (f a) = a := hinv a List.mem_cons_self
      rw [hfb] at h1
      exact h1.symm.trans h2
    exact hant (hba ▸ hb)

/-- The join of two duplicate-free lists is duplicate-free when both coordinates
of a pair can be read back off the joined value. -/
theorem nodup_flatMap_map {B : List Nat} {J : Nat → Nat → Nat} {g h : Nat → Nat}
    (hB : B.Nodup) :
    ∀ {A : List Nat}, A.Nodup →
      (∀ a ∈ A, ∀ b ∈ B, g (J a b) = a) →
      (∀ a ∈ A, ∀ b ∈ B, h (J a b) = b) →
      (A.flatMap (fun a => B.map (J a))).Nodup := by
  intro A
  induction A with
  | nil => intro _ _ _; simp
  | cons a t ih =>
    intro hnd hg hh
    obtain ⟨hant, hndt⟩ := List.nodup_cons.mp hnd
    have hgt : ∀ a' ∈ t, ∀ b ∈ B, g (J a' b) = a' :=
      fun a' ha' b hb => hg a' (List.mem_cons_of_mem _ ha') b hb
    have hht : ∀ a' ∈ t, ∀ b ∈ B, h (J a' b) = b :=
      fun a' ha' b hb => hh a' (List.mem_cons_of_mem _ ha') b hb
    rw [List.flatMap_cons, List.nodup_append]
    refine ⟨?_, ih hndt hgt hht, ?_⟩
    · exact nodup_map_of_leftInv (f := J a) (g := h) hB
        (fun b hb => hh a List.mem_cons_self b hb)
    · intro x hx y hy
      obtain ⟨b, hb, hxb⟩ := List.mem_map.mp hx
      obtain ⟨a', ha', hy'⟩ := List.mem_flatMap.mp hy
      obtain ⟨b', hb', hyb⟩ := List.mem_map.mp hy'
      intro hxy
      have hgx : g x = a := by rw [← hxb]; exact hg a List.mem_cons_self b hb
      have hgy : g y = a' := by rw [← hyb]; exact hgt a' ha' b' hb'
      have : a = a' := by rw [← hgx, ← hgy, hxy]
      exact hant (this ▸ ha')

/-- The join list has exactly the product length. -/
theorem length_flatMap_map {B : List Nat} {J : Nat → Nat → Nat} :
    ∀ A : List Nat, (A.flatMap (fun a => B.map (J a))).length = A.length * B.length := by
  intro A
  induction A with
  | nil => simp
  | cons a t ih =>
    rw [List.flatMap_cons, List.length_append, List.length_map, ih, List.length_cons,
      Nat.succ_mul]
    omega

/-! ## Splitting a parity vector at a time

The parity word of a window of length `j + k` is the word of the first `j` steps
followed by the word of the next `k` steps, read from the state reached at time
`j`.  This is the list-level form of the cocycle law. -/

/-- Parity vectors concatenate along a split of the window. -/
theorem parityVector_add (n j k : Nat) :
    parityVector n (j + k) = parityVector n j ++ parityVector (acceleratedOrbit j n) k := by
  unfold parityVector
  rw [List.range_add, List.map_append, List.map_map]
  congr 1
  refine List.map_congr_left ?_
  intro i _
  simp only [Function.comp_apply]
  rw [acceleratedOrbit_add i j n, Nat.add_comm i j]

/-- Parity vectors have the length of their window. -/
@[simp] theorem length_parityVector (n j : Nat) : (parityVector n j).length = j := by
  simp [parityVector]

/-- Parity vectors are `{0,1}`-words. -/
theorem parityVector_mem_zero_or_one {n j x : Nat} (hx : x ∈ parityVector n j) :
    x = 0 ∨ x = 1 := by
  rw [parityVector, List.mem_map] at hx
  obtain ⟨i, _, hi⟩ := hx
  omega

/-! ## Safe residues

A residue is *safe* to level `k` when every prefix of its orbit is expanding.
This is the first clause of the descent criterion, negated, and it is the
half that concatenates. -/

/-- `safeB k r` says that `2 ^ i ≤ 3 ^ a(r, i)` for every `i ≤ k`: every window
out of `r` up to length `k` is expanding. -/
def safeB (k r : Nat) : Bool :=
  (List.range (k + 1)).all (fun i => decide (2 ^ i ≤ 3 ^ oddCount r i))

/-- The propositional reading of `safeB`. -/
theorem safeB_iff {k r : Nat} :
    safeB k r = true ↔ ∀ i, i ≤ k → 2 ^ i ≤ 3 ^ oddCount r i := by
  rw [safeB, List.all_eq_true]
  constructor
  · intro h i hi
    have := h i (List.mem_range.mpr (by omega))
    simpa using this
  · intro h i hi
    have hik : i ≤ k := by have := List.mem_range.mp hi; omega
    simpa using h i hik

/-- **Safety implies survival.**  A safe residue fails the descent criterion on
its first clause at every level, so the sieve keeps it.  The converse is not
claimed: safety is a sufficient condition, which is what a lower bound on the
survivor count needs. -/
theorem survives_of_safeB {k r : Nat} (h : safeB k r = true) : survives k r = true := by
  refine survives_of_not_descends (fun i hi hd => ?_)
  have h1 : 3 ^ oddCount (r % 2 ^ i) i < 2 ^ i := hd.1
  have h2 : 2 ^ i ≤ 3 ^ oddCount r i := safeB_iff.mp h i hi
  rw [← Density.oddCount_mod] at h1
  omega

/-- Safety only depends on the residue modulo `2 ^ k`, and is inherited by
shallower levels. -/
theorem safeB_of_mod {k j r r' : Nat} (hjk : j ≤ k) (hmod : r % 2 ^ k = r' % 2 ^ k)
    (h : safeB k r = true) : safeB j r' = true := by
  refine safeB_iff.mpr (fun i hi => ?_)
  have hdvd : (2 : Nat) ^ i ∣ 2 ^ k := Arith.two_pow_dvd_two_pow (by omega)
  have h1 : r % 2 ^ i = r' % 2 ^ i := by
    rw [← Nat.mod_mod_of_dvd r hdvd, ← Nat.mod_mod_of_dvd r' hdvd, hmod]
  have h2 : oddCount r i = oddCount r' i := by
    rw [Density.oddCount_mod r i, Density.oddCount_mod r' i, h1]
  rw [← h2]
  exact safeB_iff.mp h i (by omega)

/-! ## Joining two safe residues

Terras' bijection says every `{0,1}`-word is a parity word.  Concatenating the
word of `r₀` with the word of `s` therefore names a residue whose first `k`
steps are those of `r₀` and whose next `L` steps are those of `s`. -/

/-- **Existence of the join.**  For any residues `r₀` mod `2 ^ k` and `s` mod
`2 ^ L` there is a residue mod `2 ^ (k + L)` reducing to `r₀`, whose state after
`k` steps reduces to `s`. -/
theorem exists_join (k L r0 s : Nat) (h0 : r0 < 2 ^ k) (hs : s < 2 ^ L) :
    ∃ r : Nat, r < 2 ^ (k + L) ∧ r % 2 ^ k = r0 ∧ acceleratedOrbit k r % 2 ^ L = s := by
  have hlen : (parityVector r0 k ++ parityVector s L).length = k + L := by simp
  have hval : ∀ x ∈ parityVector r0 k ++ parityVector s L, x = 0 ∨ x = 1 := by
    intro x hx
    rcases List.mem_append.mp hx with h | h
    · exact parityVector_mem_zero_or_one h
    · exact parityVector_mem_zero_or_one h
  obtain ⟨r, hrlt, hrpv⟩ :=
    parityVector_surjective_mod_pow_two (k + L) _ hlen hval
  rw [parityVector_add r k L] at hrpv
  obtain ⟨hhead, htail⟩ := List.append_inj hrpv (by simp)
  refine ⟨r, hrlt, ?_, ?_⟩
  · have e1 : parityVector (r % 2 ^ k) k = parityVector (r0 % 2 ^ k) k := by
      rw [← parityVector_mod_pow_two, ← parityVector_mod_pow_two]; exact hhead
    have e2 : r % 2 ^ k = r0 % 2 ^ k :=
      parityVector_injective_mod_pow_two k _ _
        (Nat.mod_lt _ (Arith.two_pow_pos k)) (Nat.mod_lt _ (Arith.two_pow_pos k)) e1
    rw [e2, Nat.mod_eq_of_lt h0]
  · have e1 : parityVector (acceleratedOrbit k r % 2 ^ L) L = parityVector (s % 2 ^ L) L := by
      rw [← parityVector_mod_pow_two, ← parityVector_mod_pow_two]; exact htail
    have e2 : acceleratedOrbit k r % 2 ^ L = s % 2 ^ L :=
      parityVector_injective_mod_pow_two L _ _
        (Nat.mod_lt _ (Arith.two_pow_pos L)) (Nat.mod_lt _ (Arith.two_pow_pos L)) e1
    rw [e2, Nat.mod_eq_of_lt hs]

/-- A computable choice of join: the least residue below `2 ^ (k + L)` with the
prescribed head and tail.  Kept computable so that no choice principle enters
the development. -/
def joinPred (k L r0 s : Nat) : Nat → Bool :=
  fun r => decide (r % 2 ^ k = r0) && decide (acceleratedOrbit k r % 2 ^ L = s)

def join (k L r0 s : Nat) : Nat :=
  ((List.range (2 ^ (k + L))).find? (joinPred k L r0 s)).getD 0

/-- The join has the three properties it was built for. -/
theorem join_spec {k L r0 s : Nat} (h0 : r0 < 2 ^ k) (hs : s < 2 ^ L) :
    join k L r0 s < 2 ^ (k + L) ∧ join k L r0 s % 2 ^ k = r0 ∧
      acceleratedOrbit k (join k L r0 s) % 2 ^ L = s := by
  obtain ⟨r, hrlt, hrm, hro⟩ := exists_join k L r0 s h0 hs
  have hne : (List.range (2 ^ (k + L))).find? (joinPred k L r0 s) ≠ none := by
    intro hnone
    have hcon := (List.find?_eq_none.mp hnone) r (List.mem_range.mpr hrlt)
    exact hcon (by simp [joinPred, hrm, hro])
  obtain ⟨a, ha⟩ : ∃ a, (List.range (2 ^ (k + L))).find? (joinPred k L r0 s) = some a := by
    cases hfind : (List.range (2 ^ (k + L))).find? (joinPred k L r0 s) with
    | none => exact absurd hfind hne
    | some a => exact ⟨a, rfl⟩
  have hpa : joinPred k L r0 s a = true := List.find?_some ha
  have hmem : a ∈ List.range (2 ^ (k + L)) := List.mem_of_find?_eq_some ha
  have hjoin : join k L r0 s = a := by rw [join, ha]; rfl
  simp only [joinPred, Bool.and_eq_true, decide_eq_true_eq] at hpa
  rw [hjoin]
  exact ⟨List.mem_range.mp hmem, hpa.1, hpa.2⟩

/-- **Safety concatenates.**  If the head residue is safe to level `k` and the
tail residue is safe to level `L`, the join is safe to level `k + L`.

This is the whole mechanism.  Below the join the odd-step count is that of the
head; above it the counts add, and `2 ^ k · 2 ^ j ≤ 3 ^ a · 3 ^ b`. -/
theorem safeB_join {k L r r0 s : Nat} (hr0 : r % 2 ^ k = r0)
    (hs : acceleratedOrbit k r % 2 ^ L = s)
    (h0 : safeB k r0 = true) (h1 : safeB L s = true) : safeB (k + L) r = true := by
  refine safeB_iff.mpr (fun i hi => ?_)
  by_cases hik : i ≤ k
  · have hdvd : (2 : Nat) ^ i ∣ 2 ^ k := Arith.two_pow_dvd_two_pow hik
    have hmod : r % 2 ^ i = r0 % 2 ^ i := by
      rw [← Nat.mod_mod_of_dvd r hdvd, hr0]
    have hcnt : oddCount r i = oddCount r0 i := by
      rw [Density.oddCount_mod r i, Density.oddCount_mod r0 i, hmod]
    rw [hcnt]
    exact safeB_iff.mp h0 i hik
  · obtain ⟨j, hij⟩ : ∃ j : Nat, i = k + j := ⟨i - k, by omega⟩
    have hjL : j ≤ L := by omega
    have hsplit : oddCount r (k + j) = oddCount r k + oddCount (acceleratedOrbit k r) j :=
      AccumulatorArith.oddCount_add r k j
    have hcnt0 : oddCount r k = oddCount r0 k := by
      rw [Density.oddCount_mod r k, hr0]
    have hdvd : (2 : Nat) ^ j ∣ 2 ^ L := Arith.two_pow_dvd_two_pow hjL
    have hmodt : acceleratedOrbit k r % 2 ^ j = s % 2 ^ j := by
      rw [← Nat.mod_mod_of_dvd (acceleratedOrbit k r) hdvd, hs]
    have hcnt1 : oddCount (acceleratedOrbit k r) j = oddCount s j := by
      rw [Density.oddCount_mod (acceleratedOrbit k r) j, Density.oddCount_mod s j, hmodt]
    have hA : 2 ^ k ≤ 3 ^ oddCount r0 k := safeB_iff.mp h0 k (Nat.le_refl k)
    have hB : 2 ^ j ≤ 3 ^ oddCount s j := safeB_iff.mp h1 j hjL
    have hmul : 2 ^ k * 2 ^ j ≤ 3 ^ oddCount r0 k * 3 ^ oddCount s j :=
      Nat.mul_le_mul hA hB
    rw [hij, hsplit, hcnt0, hcnt1, Arith.two_pow_add, Nat.pow_add]
    exact hmul

/-! ## The survivor count is supermultiplicative -/

/-- The residues below `2 ^ k` that are safe to level `k`. -/
def safeList (k : Nat) : List Nat := (List.range (2 ^ k)).filter (safeB k)

/-- The number of safe residues at level `k`. -/
def safeCount (k : Nat) : Nat := (safeList k).length

theorem mem_safeList {k r : Nat} : r ∈ safeList k ↔ r < 2 ^ k ∧ safeB k r = true := by
  rw [safeList, List.mem_filter, List.mem_range]

theorem safeList_nodup (k : Nat) : (safeList k).Nodup :=
  List.Pairwise.filter _ List.nodup_range

/-- **Supermultiplicativity.**  Safe residues at level `k` pair with safe
residues at level `L` to give distinct safe residues at level `k + L`. -/
theorem safeCount_super (k L : Nat) : safeCount k * safeCount L ≤ safeCount (k + L) := by
  have hg : ∀ a ∈ safeList k, ∀ b ∈ safeList L, (fun r => r % 2 ^ k) (join k L a b) = a := by
    intro a ha b hb
    exact (join_spec (mem_safeList.mp ha).1 (mem_safeList.mp hb).1).2.1
  have hh : ∀ a ∈ safeList k, ∀ b ∈ safeList L,
      (fun r => acceleratedOrbit k r % 2 ^ L) (join k L a b) = b := by
    intro a ha b hb
    exact (join_spec (mem_safeList.mp ha).1 (mem_safeList.mp hb).1).2.2
  have hnd : ((safeList k).flatMap (fun a => (safeList L).map (join k L a))).Nodup :=
    nodup_flatMap_map (g := fun r => r % 2 ^ k)
      (h := fun r => acceleratedOrbit k r % 2 ^ L) (safeList_nodup L) (safeList_nodup k) hg hh
  have hsub : (safeList k).flatMap (fun a => (safeList L).map (join k L a)) ⊆ safeList (k + L) := by
    intro x hx
    obtain ⟨a, ha, hx'⟩ := List.mem_flatMap.mp hx
    obtain ⟨b, hb, hxb⟩ := List.mem_map.mp hx'
    obtain ⟨halt, hasafe⟩ := mem_safeList.mp ha
    obtain ⟨hblt, hbsafe⟩ := mem_safeList.mp hb
    obtain ⟨hlt, hmod, horb⟩ := join_spec (k := k) (L := L) halt hblt
    rw [← hxb]
    exact mem_safeList.mpr ⟨hlt, safeB_join hmod horb hasafe hbsafe⟩
  have hlen := length_flatMap_map (B := safeList L) (J := join k L) (safeList k)
  have := length_le_of_nodup_subset hnd hsub
  rw [hlen] at this
  exact this

/-! ## The base case and the rate -/

set_option maxRecDepth 100000 in
/-- Level ten, by kernel evaluation: `64` of the `1024` residues are safe.  The
same number the sieve table records as `survivorCount 10`. -/
theorem safeCount_ten : safeCount 10 = 64 := by decide

theorem safeCount_zero : safeCount 0 = 1 := by decide

/-- **The rate.**  Safety at level `10` compounds: at level `10 m` there are at
least `64 ^ m` safe residues. -/
theorem safeCount_pow (m : Nat) : 64 ^ m ≤ safeCount (10 * m) := by
  induction m with
  | zero =>
    rw [Nat.pow_zero, Nat.mul_zero, safeCount_zero]
    omega
  | succ m ih =>
    have hstep : safeCount (10 * m) * safeCount 10 ≤ safeCount (10 * m + 10) :=
      safeCount_super (10 * m) 10
    have hidx : 10 * (m + 1) = 10 * m + 10 := by omega
    have hmul : 64 ^ m * 64 ≤ safeCount (10 * m) * safeCount 10 := by
      rw [safeCount_ten]
      exact Nat.mul_le_mul ih (Nat.le_refl 64)
    rw [hidx, Nat.pow_succ]
    omega

/-- The same bound in base two: `2 ^ (0.6 k)` safe residues along `10 ∣ k`. -/
theorem two_pow_le_safeCount (m : Nat) : 2 ^ (6 * m) ≤ safeCount (10 * m) := by
  have h64 : ∀ n : Nat, (64 : Nat) ^ n = 2 ^ (6 * n) := by
    intro n
    induction n with
    | zero => rfl
    | succ n ih =>
      have hidx : 6 * (n + 1) = 6 * n + 6 := by omega
      rw [Nat.pow_succ, ih, hidx, Nat.pow_add]
  rw [← h64 m]
  exact safeCount_pow m

/-! ## The consequence for the sieve -/

/-- Safe residues are survivors, so they bound the sieve's survivor count from
below. -/
theorem safeCount_le_survivorCount (k : Nat) : safeCount k ≤ SieveDensity.survivorCount k := by
  rw [safeCount, safeList, SieveDensity.survivorCount, ← List.countP_eq_length_filter,
    ← List.countP_eq_length_filter]
  exact countP_mono (fun r h => survives_of_safeB h) _

/-- **The sieve retains exponentially many classes.**  At level `10 m` at least
`2 ^ (6 m)` residues survive.  `Obstruction.sieve_never_clears` exhibits one
survivor; this exhibits `2 ^ (0.6 k)` of them. -/
theorem survivorCount_ge (m : Nat) :
    2 ^ (6 * m) ≤ SieveDensity.survivorCount (10 * m) :=
  Nat.le_trans (two_pow_le_safeCount m) (safeCount_le_survivorCount (10 * m))

/-- **The sieve never terminates.**  For every bound `B` there is a level whose
survivor count exceeds `B`.  The table in `SieveDensity` is no longer an
extrapolation: the count really does grow without bound, and exponentially.

This is a lower bound on the obstruction, not progress on descent.  It says the
residue sieve cannot be finished by deepening — the survivors form a semigroup
under concatenation of orbit windows, and refinement is concatenation. -/
theorem sieve_never_terminates (B : Nat) :
    ∃ k : Nat, B < SieveDensity.survivorCount k := by
  refine ⟨10 * B, Nat.lt_of_lt_of_le ?_ (survivorCount_ge B)⟩
  have h1 : B < 2 ^ B := Nat.lt_two_pow_self
  have h2 : (2 : Nat) ^ B ≤ 2 ^ (6 * B) := Nat.pow_le_pow_right (by omega) (by omega)
  omega

/-- The two halves together: survival is closed under concatenation, and the
count therefore grows at a proved exponential rate. -/
theorem sieve_growth :
    (∀ k L : Nat, safeCount k * safeCount L ≤ safeCount (k + L)) ∧
    (∀ m : Nat, 2 ^ (6 * m) ≤ SieveDensity.survivorCount (10 * m)) ∧
    (∀ B : Nat, ∃ k : Nat, B < SieveDensity.survivorCount k) :=
  ⟨safeCount_super, survivorCount_ge, sieve_never_terminates⟩


end SieveGrowth
end Collatz
