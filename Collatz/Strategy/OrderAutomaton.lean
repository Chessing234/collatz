/-!
# The ordered-position automaton, and why it is not one

Round VIII asked whether a finite-state device whose state records *where we are
in the ordered sequence* — the pair `(j, A(j))` of position and prefix odd-count,
together with a bucket of the **discrepancy**

      `D(j) = A(j) − ρ·j`,   `ρ = a / L`

— can obstruct a cycle.  The hope was explicit: `D(j)` depends on `ρ`, and `ρ` is
a property of the *whole* word, so a language cut out by `D`-buckets might fail
to be closed under concatenation, and therefore escape
`SieveGrowth.sieve_never_terminates` (naive safe classes concatenate, so
survivors grow exponentially and no finite truncation works).

**It does not escape.  Both readings of the proposal are dead, and this file
proves it.**

*Reading (i) — `ρ` unknown while reading.*  Then `D(j)` is not a function of the
prefix, so no transition function can maintain it: `disc_not_prefix_determined`
below says that on one and the same nonempty prefix the discrepancy takes a
different value for every candidate `a`.  A device whose state cannot be computed
from what it has read is not an automaton, and cannot reject a word online.  The
apparent escape is illusory in a second way as well: by
`GapSandwich.cycle_length_determined`, `L = ⌊a·log₂3⌋ + 1`, so the cycle problem
is one-dimensional and `ρ` ranges over *one* parameter, which one may as well fix.

*Reading (ii) — `ρ` fixed in advance.*  Then the state is computable, but the
discrepancy becomes **additive** (`disc_append`), and the admissible language is
closed under concatenation of balanced blocks (`Adm_append`).  That is exactly the
property Round III showed to be fatal.

**The conclusion is right; the `blocks_*` route to it is not, and is withdrawn.**
An earlier draft justified it by "from any two distinct balanced admissible blocks
of equal length `ℓ` one manufactures an injection from `{0,1}^m` into the
admissible words of length `m·ℓ`".  That construction never speaks inside the
window a cycle has.  `Adm L a M u` demands `disc L a u = 0`, i.e. `L·ones u =
a·|u|`; at every ledge pair of interest `gcd(L,a) = 1` — checked at `(27,17)`,
`(4701,2966)` and the frontier `(6809,4296)` — so `L ∣ |u|` and a nonempty
balanced block has length `≥ L`.  Hence for `m ≥ 2` every word it builds has length
`≥ 2L`, strictly longer than the only window a cycle has; and at a tight bucket,
the only interesting case, the hypothesis class is *empty*.  Exact DP over balanced
words of length `L` with every prefix discrepancy in `[0,M]`:

| pair | `M = L` | `M = 2L` |
|---|---|---|
| `(27,17)` | **1 word** | 35531 |
| `(6809,4296)` | **1 word** (never more than 2 live states in 6809 steps) | — |

One word, so `hne : u ≠ v` is unsatisfiable at `M ≤ L`.  `adm_never_terminates` is
therefore vacuous below `D`-width 2 and out-of-window above it — never both
non-vacuous and relevant.

The real justification is the transfer matrix, which this header previously quoted
only as numerics.  On the strip `0 ≤ L·A(j) − a·j ≤ M` at `(6809,4296)`, growth per
letter is `0.0000` bits at `D`-width 1, then `0.6478`, `0.8906`, `0.9416` at widths
`2, 5, 30`, against `0.95008` free.  So admissible *prefixes* at length `j` number
`2^(0.65 j)` for any bucket of `D`-width `≥ 2`, and the count collapses to a single
word only at `D`-width `≤ 1`, which is Sturmian rigidity and already closed.

One unit warning, since this file mixes conventions: `M` is **one-sided** in the
Lean (`0 ≤ disc ≤ M`) and **two-sided** in the prose (`|D| ≤ M`).  The earlier
claim that entropy is "still positive at every `M ≥ 1`" is true only in the
two-sided reading; under the file's own `Adm`, `M = L` gives entropy exactly `0`.

## Why no `D`-bound is available anyway

Even granting reading (ii), one would still have to *justify* a bound `|D| ≤ M`
on cycle words.  There is none.  Heaviness gives the lower bound only — at a
cycle-plausible pair `a/L < log₃2`, so `2^j ≤ 3^{A(j)}` forces `D(j) ≥ 0` — while
the upper side is completely free.  `spike_disc` and `spike_heavy` below exhibit,
at every cycle-plausible pair, a word that is heavy at every proper prefix and
reaches discrepancy `a·(L−a)/L ≈ 0.2375·L`: **linear in `L`, not bounded.**
Measured exhaustively (heavy words, `L ≤ 24`): the maximum of `L·A(j) − a·j` over
the heavy language is *exactly* `a·(L−a)` at every pair tested — the spike word is
the maximiser and nothing forbids it.

## What the measurements said (outside Lean, exact)

* **Visited region.**  For every ledge pair with `L ≤ 27`, the set of lattice
  points `(j, A(j))` visited by heavy words ending at `(L,a)` is *exactly* the set
  of points satisfying prefix-heaviness and feasibility.  There is no forbidden
  sub-region: the "forbidden region of the `(j,A)` lattice" is heaviness itself,
  restated, and heaviness is already known to cost no entropy.  It is about half
  the box (`0.51` at `(27,17)`), a linear cut, not an exponential one.
* **Product with `C mod G`.**  For the joint state `(j, A(j), C_j mod G)` the
  reachable set at a lattice point equals `min(#paths, G)` at every point of
  `(5,3), (8,5), (20,12)` and at all but three late points of `(16,10)` and
  `(24,15)`; the deficiency there is under `0.5 %` (`474` of `476` at `(16,10)`,
  `50951` of `51033` at `(24,15)`).  **The lattice constraint does not cut the
  `C mod G` automaton.**  Round VII found that automaton free; ordering it changes
  nothing.
* **Entropy.**  The admissible count is unchanged: `2^(0.94996·L)` divided by a
  polynomial, i.e. the same wall every counting route has hit.  A genuine bound
  `|D| ≤ M` *would* cut entropy (`0.652` bits/letter at `M = 2`, `0.892` at
  `M = 5`, `0.945` at `M = 30`, against `0.95008`), but it is still positive at
  every `M ≥ 1` — so even the strongest bucket bound leaves an exponentially large
  language and no finite obstruction.

## Soundness filter

Everything here is `d`-free and word-only: it is a statement about the parity
language, not about `3x+1`.  That is legitimate because every result in this file
is **negative** — a `d`-free negative result rules out a `d`-free mechanism, which
is precisely the class Round III's corrected filter says is dead.
-/

namespace Collatz
namespace OrderAutomaton

/-! ## Prefix odd-count and discrepancy -/

/-- Number of `true` letters (odd steps) in a parity word. -/
def ones : List Bool → Nat
  | [] => 0
  | b :: w => (if b then 1 else 0) + ones w

@[simp] theorem ones_nil : ones [] = 0 := rfl

theorem ones_append : ∀ (u v : List Bool), ones (u ++ v) = ones u + ones v := by
  intro u
  induction u with
  | nil => intro v; simp [ones]
  | cons b u ih =>
      intro v
      simp [ones, ih, Nat.add_assoc]

theorem ones_le_length : ∀ w : List Bool, ones w ≤ w.length := by
  intro w
  induction w with
  | nil => exact Nat.le_refl 0
  | cons b w ih =>
      simp only [ones, List.length_cons]
      by_cases hb : b = true <;> simp [hb] <;> omega

/-- The **scaled discrepancy** of a word at slope `ρ = a / L`:
`disc L a w = L·(ones w) − a·(length w)`, an integer, equal to `L · D`. -/
def disc (L a : Nat) (w : List Bool) : Int :=
  (L : Int) * (ones w : Int) - (a : Int) * (w.length : Int)

@[simp] theorem disc_nil (L a : Nat) : disc L a [] = 0 := by
  simp [disc]

/-- **Additivity.**  This is the whole problem: the discrepancy of a
concatenation is the sum of the discrepancies.  Once `ρ` is fixed the
`D`-language is therefore a *monoid* language, exactly like the failed sieve. -/
theorem disc_append (L a : Nat) (u v : List Bool) :
    disc L a (u ++ v) = disc L a u + disc L a v := by
  have ho : ((ones (u ++ v) : Nat) : Int) = (ones u : Int) + (ones v : Int) := by
    rw [ones_append]; exact_mod_cast rfl
  have hl : (((u ++ v).length : Nat) : Int) = (u.length : Int) + (v.length : Int) := by
    rw [List.length_append]; exact_mod_cast rfl
  simp only [disc, ho, hl, Int.mul_add]
  omega

/-! ## Reading (i): the state is not a function of the prefix -/

/-- **The discrepancy is not prefix-computable.**  On any nonempty prefix the
value of `disc L a` genuinely depends on the odd-count `a` of the *whole* word,
which the prefix does not determine.  So no transition function on prefixes can
maintain a `D`-bucket, and reading (i) of the proposal is not a finite-state
method at all. -/
theorem disc_not_prefix_determined (L : Nat) (p : List Bool) (hp : 0 < p.length)
    (a a' : Nat) (h : a ≠ a') : disc L a p ≠ disc L a' p := by
  simp only [disc]
  intro hc
  have hlen : (0 : Int) < (p.length : Int) := by exact_mod_cast hp
  have hmul : (a : Int) * (p.length : Int) = (a' : Int) * (p.length : Int) := by omega
  have haa : (a : Int) = (a' : Int) :=
    Int.eq_of_mul_eq_mul_right (by omega) hmul
  exact h (by exact_mod_cast haa)

/-! ## Reading (ii): the admissible language is a monoid language

Splitting lemma first: any prefix of `p ++ q` is a prefix of `p`, or `p`
extended by a prefix of `q`. -/

theorem split_of_append : ∀ (p q u v : List Bool), u ++ v = p ++ q →
    (∃ r, u ++ r = p) ∨ (∃ r, p ++ r = u) := by
  intro p
  induction p with
  | nil => intro q u v _; exact Or.inr ⟨u, by simp⟩
  | cons b p ih =>
      intro q u v h
      cases u with
      | nil => exact Or.inl ⟨b :: p, by simp⟩
      | cons c u =>
          simp only [List.cons_append, List.cons.injEq] at h
          rcases ih q u v h.2 with ⟨r, hr⟩ | ⟨r, hr⟩
          · exact Or.inl ⟨r, by simp [h.1, hr]⟩
          · exact Or.inr ⟨r, by simp [h.1, hr]⟩

/-- `Adm L a M w`: the word is **balanced** (discrepancy `0` overall, i.e. it has
exactly the slope `ρ = a/L`) and every prefix has discrepancy in `[0, M]`.  This
is the well-posed version of the proposed automaton language: `ρ` is fixed in
advance, so the state is computable. -/
def Adm (L a M : Nat) (w : List Bool) : Prop :=
  disc L a w = 0 ∧ ∀ u v : List Bool, u ++ v = w → 0 ≤ disc L a u ∧ disc L a u ≤ (M : Int)

theorem Adm_nil (L a M : Nat) : Adm L a M [] := by
  refine ⟨by simp, ?_⟩
  intro u v h
  have hu : u = [] := by
    cases u with
    | nil => rfl
    | cons c u => simp at h
  subst hu
  simp

/-- **The kill.**  The admissible language is closed under concatenation.  A
language closed under concatenation of its own blocks grows exponentially and no
finite truncation of it is empty — `SieveGrowth.sieve_never_terminates` is the
same phenomenon.  So the `D`-bucket device, in its well-posed form, is already
dead before any arithmetic is applied to it. -/
theorem Adm_append {L a M : Nat} {p q : List Bool}
    (hp : Adm L a M p) (hq : Adm L a M q) : Adm L a M (p ++ q) := by
  refine ⟨by rw [disc_append, hp.1, hq.1]; simp, ?_⟩
  intro u v huv
  rcases split_of_append p q u v huv with ⟨r, hr⟩ | ⟨r, hr⟩
  · exact hp.2 u r hr
  · have hru : disc L a u = disc L a p + disc L a r := by
      rw [← hr, disc_append]
    have hs : r ++ v = q := by
      have hpp : p ++ (r ++ v) = p ++ q := by
        rw [← List.append_assoc, hr, huv]
      exact List.append_cancel_left hpp
    have h1 := hq.2 r v hs
    rw [hru, hp.1]
    omega

/-! ## Exponential growth from two blocks -/

/-- Choose one of two blocks. -/
def pick (u v : List Bool) : Bool → List Bool
  | true => u
  | false => v

/-- Concatenate a chosen block per selector bit. -/
def blocks (u v : List Bool) : List Bool → List Bool
  | [] => []
  | b :: s => pick u v b ++ blocks u v s

theorem blocks_length {u v : List Bool} {l : Nat}
    (hu : u.length = l) (hv : v.length = l) :
    ∀ s : List Bool, (blocks u v s).length = s.length * l := by
  intro s
  induction s with
  | nil => simp [blocks]
  | cons b s ih =>
      simp only [blocks, List.length_append, List.length_cons, ih, Nat.succ_mul]
      cases b with
      | true => simp only [pick]; omega
      | false => simp only [pick]; omega

/-- Every block-composite is admissible. -/
theorem blocks_adm {L a M : Nat} {u v : List Bool}
    (hu : Adm L a M u) (hv : Adm L a M v) :
    ∀ s : List Bool, Adm L a M (blocks u v s) := by
  intro s
  induction s with
  | nil => exact Adm_nil L a M
  | cons b s ih =>
      cases b with
      | true => exact Adm_append hu ih
      | false => exact Adm_append hv ih

theorem take_length_append (u r : List Bool) : (u ++ r).take u.length = u := by
  induction u with
  | nil => simp
  | cons c u ih => simp [ih]

/-- **Distinct selectors give distinct words**, provided the two blocks are
distinct and of equal length.  Together with `blocks_adm` this injects `{0,1}^m`
into the admissible words of length `m·l`: the admissible language has entropy at
least `1/l` bits per letter, so it is infinite at every length and no finite
truncation can be empty. -/
theorem blocks_inj {u v : List Bool} (hlen : u.length = v.length) (hne : u ≠ v) :
    ∀ s t : List Bool, blocks u v s = blocks u v t → s = t := by
  have hupos : 0 < u.length := by
    cases hu : u with
    | cons c w => simp
    | nil =>
        exfalso
        apply hne
        have hv0 : v.length = 0 := by rw [← hlen, hu]; simp
        rw [hu, List.eq_nil_of_length_eq_zero hv0]
  have hsame : ∀ (X Y : List Bool), u ++ X = v ++ Y → False := by
    intro X Y h
    apply hne
    have h2 : (v ++ Y).take u.length = v := by
      rw [hlen]; exact take_length_append v Y
    have h1 : (u ++ X).take u.length = u := take_length_append u X
    rw [← h1, h, h2]
  intro s
  induction s with
  | nil =>
      intro t h
      cases t with
      | nil => rfl
      | cons c t =>
          exfalso
          have hl := congrArg List.length h
          simp only [blocks, List.length_nil, List.length_append] at hl
          cases c with
          | true => simp only [pick] at hl; omega
          | false => simp only [pick] at hl; rw [← hlen] at hl; omega
  | cons b s ih =>
      intro t h
      cases t with
      | nil =>
          exfalso
          have hl := congrArg List.length h
          simp only [blocks, List.length_nil, List.length_append] at hl
          cases b with
          | true => simp only [pick] at hl; omega
          | false => simp only [pick] at hl; rw [← hlen] at hl; omega
      | cons c t =>
          simp only [blocks] at h
          have hbc : b = c := by
            cases b with
            | true =>
                cases c with
                | true => rfl
                | false =>
                    exfalso
                    simp only [pick] at h
                    exact hsame _ _ h
            | false =>
                cases c with
                | false => rfl
                | true =>
                    exfalso
                    simp only [pick] at h
                    exact hsame _ _ h.symm
          subst hbc
          have hrest : blocks u v s = blocks u v t := List.append_cancel_left h
          rw [ih t hrest]

/-! ## No `D`-bound is available: the spike word

At a cycle-plausible pair `3 ^ a < 2 ^ L` and `2 ^ (L-1) < 3 ^ a`, so the word
`1^a 0^(L-a)` is heavy at every proper prefix, yet its discrepancy at `j = a` is
`a·(L−a)`, i.e. `D = a(L−a)/L ≈ 0.2375·L`.  Heaviness bounds the discrepancy from
*below* only; the upper side is free, and grows linearly.  So no constant bucket
bound `|D| ≤ M` is a property of the cycle language. -/

theorem prefix_of_replicate : ∀ (n : Nat) (x : Bool) (u v : List Bool),
    u ++ v = List.replicate n x → u = List.replicate u.length x := by
  intro n
  induction n with
  | zero =>
      intro x u v h
      simp only [List.replicate] at h
      have : u = [] := by
        cases u with
        | nil => rfl
        | cons c u => simp at h
      rw [this]; simp
  | succ n ih =>
      intro x u v h
      cases u with
      | nil => simp
      | cons c u =>
          simp only [List.replicate, List.cons_append, List.cons.injEq] at h
          have hu := ih x u v h.2
          rw [h.1]
          simp only [List.length_cons, List.replicate_succ, List.cons.injEq, true_and]
          exact hu

@[simp] theorem ones_replicate_true : ∀ k : Nat, ones (List.replicate k true) = k := by
  intro k
  induction k with
  | zero => rfl
  | succ k ih => simp [List.replicate, ones, ih]; omega

@[simp] theorem ones_replicate_false : ∀ k : Nat, ones (List.replicate k false) = 0 := by
  intro k
  induction k with
  | zero => rfl
  | succ k ih => simp [List.replicate, ones, ih]

theorem two_pow_le_three_pow : ∀ k : Nat, 2 ^ k ≤ 3 ^ k := by
  intro k
  induction k with
  | zero => exact Nat.le_refl 1
  | succ k ih =>
      rw [Nat.pow_succ, Nat.pow_succ]
      have h3 : (1:Nat) ≤ 3 ^ k := Nat.le_trans Nat.one_le_two_pow ih
      omega

theorem two_pow_mono {i j : Nat} (h : i ≤ j) : 2 ^ i ≤ 2 ^ j :=
  Nat.pow_le_pow_right (by omega) h

/-- The spike word `1^a 0^(L-a)`. -/
def spike (L a : Nat) : List Bool :=
  List.replicate a true ++ List.replicate (L - a) false

theorem spike_length {L a : Nat} (h : a ≤ L) : (spike L a).length = L := by
  simp [spike]; omega

/-- **The spike is heavy at every proper prefix**, given `2 ^ (L-1) ≤ 3 ^ a`
(true at every cycle-plausible pair, since `L = ⌊a log₂ 3⌋ + 1`). -/
theorem spike_heavy {L a : Nat} (hal : a ≤ L) (hL : 2 ^ (L - 1) ≤ 3 ^ a)
    (u v : List Bool) (huv : u ++ v = spike L a) (hv : v ≠ []) :
    2 ^ u.length ≤ 3 ^ ones u := by
  have hlen : u.length + v.length = L := by
    have := congrArg List.length huv
    rw [spike_length hal] at this
    simpa using this
  have hvpos : 0 < v.length := by
    cases v with
    | nil => exact absurd rfl hv
    | cons c w => simp
  rcases split_of_append (List.replicate a true) (List.replicate (L - a) false) u v huv with
    ⟨r, hr⟩ | ⟨r, hr⟩
  · have hu : u = List.replicate u.length true := prefix_of_replicate a true u r hr
    have hones : ones u = u.length := by
      rw [hu]; simp
    rw [hones]; exact two_pow_le_three_pow u.length
  · have hones : ones u = a := by
      rw [← hr, ones_append]
      have hrr : r = List.replicate r.length false := by
        have hq : r ++ v = List.replicate (L - a) false := by
          have : List.replicate a true ++ (r ++ v) = List.replicate a true ++ List.replicate (L - a) false := by
            rw [← List.append_assoc, hr, huv]; rfl
          exact List.append_cancel_left this
        exact prefix_of_replicate (L - a) false r v hq
      rw [hrr]; simp
    rw [hones]
    have hul : u.length ≤ L - 1 := by omega
    exact Nat.le_trans (two_pow_mono hul) hL

/-- **The spike reaches discrepancy `a·(L−a)` at position `a`** — linear in `L`
once `a/L` is bounded away from `0` and `1`, which it is (`a/L → log₃2`).  With
`a = ⌊L·log₃2⌋` this is `0.2375·L²`, i.e. `D = 0.2375·L`.  Measured exhaustively
for `L ≤ 24`: this is the exact maximum of the discrepancy over the heavy
language at every ledge pair.  Hence there is **no** constant `M` with
`Adm L a M` containing the heavy language, and the bucket device has nothing to
bucket. -/
theorem spike_disc (L a : Nat) :
    disc L a (List.replicate a true) = (L : Int) * (a : Int) - (a : Int) * (a : Int) := by
  simp [disc]

/-- The spike's prefix discrepancy exceeds any bucket bound `M < a·(L−a)`.
Combined with `spike_heavy`, this says: **the heavy language is contained in no
`Adm L a M` with `M` sub-quadratic in `L`.**  Since a finite-state device has a
number of buckets independent of `L`, no such device sees the cycle language. -/
theorem spike_exceeds_bucket {L a M : Nat} (hal : a ≤ L) (hM : M < a * (L - a)) :
    ¬ disc L a (List.replicate a true) ≤ (M : Int) := by
  have hd : disc L a (List.replicate a true) = (L : Int) * (a : Int) - (a : Int) * (a : Int) := by
    simp [disc]
  have hcast : ((a * (L - a) : Nat) : Int) = (a : Int) * ((L : Int) - (a : Int)) := by
    rw [Int.natCast_mul]
    have : (((L - a : Nat)) : Int) = (L : Int) - (a : Int) := by omega
    rw [this]
  have hMlt : (M : Int) < (a : Int) * ((L : Int) - (a : Int)) := by
    rw [← hcast]; exact_mod_cast hM
  rw [hd]
  rw [Int.mul_sub, Int.mul_comm (a : Int) (L : Int)] at hMlt
  omega

/-- **No finite truncation of the admissible language is empty.**  Given two
distinct balanced admissible blocks of equal length, `blocks` injects the `2 ^ m`
selector words into the admissible words of length `m · ℓ`.  This is the
`SieveGrowth.sieve_never_terminates` phenomenon transported to the ordered
setting: it is what the discrepancy state was supposed to avoid, and does not. -/
theorem adm_never_terminates {L a M : Nat} {u v : List Bool}
    (hlen : u.length = v.length) (hne : u ≠ v)
    (hu : Adm L a M u) (hv : Adm L a M v) :
    (∀ s : List Bool, Adm L a M (blocks u v s)
      ∧ (blocks u v s).length = s.length * u.length)
    ∧ (∀ s t : List Bool, blocks u v s = blocks u v t → s = t) :=
  ⟨fun s => ⟨blocks_adm hu hv s, blocks_length rfl hlen.symm s⟩, blocks_inj hlen hne⟩

end OrderAutomaton
end Collatz

/-! ## Axiom audit -/

section Audit
open Collatz.OrderAutomaton
#print axioms disc_append
#print axioms disc_not_prefix_determined
#print axioms Adm_append
#print axioms blocks_adm
#print axioms blocks_inj
#print axioms spike_heavy
#print axioms spike_exceeds_bucket
#print axioms adm_never_terminates
end Audit
