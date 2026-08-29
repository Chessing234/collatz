import Collatz.Strategy.ExtremalTime

/-!
# The cycle lemma, from first principles — the last link

This is Halbeisen–Hungerbühler Lemma 5 part 1, the only gap left in the criterion
chain after Round XXVI.  It is proved here from scratch rather than cited, and the
proof needs no list surgery at all.

## The idea

For a `0-1` word `w` of length `l` with `n` ones, write `S(k) = Σ_{i<k} w(i)` and

`d(k) = l·S(k) − k·n`.

Then `d(0) = d(l) = 0`, and if `w` is extended periodically, **`d` is periodic with
period `l`** (`disc_period`): the `l·n` gained over a full period is exactly
cancelled by the `l·n` subtracted.

Rotating the word by `r` replaces `S(k)` by `S(r+k) − S(r)`, hence `d(k)` by
`d(r+k) − d(r)`.  So **choosing `r` to minimise `d` makes every rotated
discrepancy non-negative** — and by periodicity, minimising over `[0, l)` already
minimises globally (`disc_min_global`).

That is the whole lemma.  No rotation of lists, no permutation reasoning: only
index shifting on a periodic function, and a fold that finds the minimiser.

## In time coordinates it becomes immediate

Round XXVI showed the domination condition is `t_j · n ≤ j · l` in time
coordinates.  If `t` is a position of the rotated word with exactly `j` ones
before it — `S(r+t) = S(r) + j` — then `cycle_lemma` at `k = t` gives

`t·n + l·S(r) ≤ l·S(r+t) = l·S(r) + l·j`,

so `t·n ≤ j·l` (`rotation_time_dominates`).  Combined with
`ExtremalTime.dominating_Crel_le` this discharges Lemma 5.

## Testing before formalising

The statement was checked exhaustively over **every** `0-1` word of length `l ≤ 14`
with any number of ones — 32 752 words — in both the partial-sum form and the time
form, with zero failures, and the periodicity of `d` was verified over four
periods for `l ≤ 11`.
-/

namespace Collatz
namespace CycleLemma

/-! ## Partial sums and the discrepancy -/

/-- `S(k) = Σ_{i<k} w(i)`. -/
def partialSum (w : Nat → Nat) : Nat → Nat
  | 0 => 0
  | k + 1 => w k + partialSum w k

/-- `d(k) = l·S(k) − k·n`, the deviation of the word from the line of slope `n/l`. -/
def disc (w : Nat → Nat) (l n k : Nat) : Int :=
  ((l * partialSum w k : Nat) : Int) - ((k * n : Nat) : Int)

@[simp] theorem partialSum_zero (w : Nat → Nat) : partialSum w 0 = 0 := rfl

/-- A full period adds exactly `n` to the partial sum. -/
theorem partialSum_period {w : Nat → Nat} {l n : Nat}
    (hper : ∀ i, w (i + l) = w i) (hn : partialSum w l = n) :
    ∀ m, partialSum w (m + l) = partialSum w m + n := by
  intro m
  induction m with
  | zero => simpa using hn
  | succ m ih =>
    have hidx : m + 1 + l = (m + l) + 1 := by omega
    show partialSum w (m + 1 + l) = w m + partialSum w m + n
    rw [hidx]
    show w (m + l) + partialSum w (m + l) = w m + partialSum w m + n
    rw [hper m, ih]
    omega

/-- **The discrepancy is periodic.**  The `l·n` gained over a period is exactly the
`l·n` subtracted. -/
theorem disc_period {w : Nat → Nat} {l n : Nat}
    (hper : ∀ i, w (i + l) = w i) (hn : partialSum w l = n) :
    ∀ m, disc w l n (m + l) = disc w l n m := by
  intro m
  have hS := partialSum_period hper hn m
  have h1 : l * partialSum w (m + l) = l * partialSum w m + l * n := by
    rw [hS, Nat.mul_add]
  have h2 : (m + l) * n = m * n + l * n := by rw [Nat.add_mul]
  unfold disc
  omega

/-- Periodicity over any number of periods. -/
theorem disc_period_mul {w : Nat → Nat} {l n : Nat}
    (hper : ∀ i, w (i + l) = w i) (hn : partialSum w l = n) :
    ∀ q m, disc w l n (m + l * q) = disc w l n m := by
  intro q
  induction q with
  | zero => intro m; simp
  | succ q ih =>
    intro m
    have hidx : m + l * (q + 1) = (m + l * q) + l := by
      rw [Nat.mul_add, Nat.mul_one]; omega
    rw [hidx, disc_period hper hn, ih m]

/-! ## The minimiser -/

/-- The least index in `[0, K]` at which `f` attains its minimum. -/
def argMin (f : Nat → Int) : Nat → Nat
  | 0 => 0
  | k + 1 => if f (k + 1) < f (argMin f k) then k + 1 else argMin f k

theorem argMin_le (f : Nat → Int) : ∀ K : Nat, argMin f K ≤ K := by
  intro K
  induction K with
  | zero => exact Nat.le_refl 0
  | succ K ih =>
    show (if f (K + 1) < f (argMin f K) then K + 1 else argMin f K) ≤ K + 1
    split
    · exact Nat.le_refl _
    · omega

theorem argMin_min (f : Nat → Int) : ∀ K k : Nat, k ≤ K → f (argMin f K) ≤ f k := by
  intro K
  induction K with
  | zero =>
    intro k hk
    have hk0 : k = 0 := by omega
    rw [hk0]
    exact Int.le_refl _
  | succ K ih =>
    intro k hk
    show f (if f (K + 1) < f (argMin f K) then K + 1 else argMin f K) ≤ f k
    rcases Nat.lt_or_ge k (K + 1) with hlt | hge
    · have hrec := ih k (by omega)
      split
      · rename_i h
        omega
      · exact hrec
    · have hk1 : k = K + 1 := by omega
      rw [hk1]
      split
      · exact Int.le_refl _
      · rename_i h
        omega

/-! ## The minimum over one period is global -/

theorem disc_min_global {w : Nat → Nat} {l n : Nat} (hl : 0 < l)
    (hper : ∀ i, w (i + l) = w i) (hn : partialSum w l = n) :
    ∀ k : Nat, disc w l n (argMin (disc w l n) (l - 1)) ≤ disc w l n k := by
  intro k
  obtain ⟨q, s, hs, hk⟩ : ∃ q s, s < l ∧ k = s + l * q :=
    ⟨k / l, k % l, Nat.mod_lt k hl, (Nat.mod_add_div k l).symm⟩
  subst hk
  rw [disc_period_mul hper hn q s]
  exact argMin_min _ (l - 1) s (by omega)

/-! ## The cycle lemma -/

/-- **The cycle lemma.**  Every `0-1` word of length `l` with `n` ones has a
rotation whose partial sums dominate the line of slope `n/l`:

`k·n + l·S(r) ≤ l·S(r+k)`  for every `k`.

Stated without subtraction; `S(r+k) − S(r)` is the rotated partial sum. -/
theorem cycle_lemma {w : Nat → Nat} {l n : Nat} (hl : 0 < l)
    (hper : ∀ i, w (i + l) = w i) (hn : partialSum w l = n) :
    ∃ r : Nat, r < l ∧
      ∀ k : Nat, k * n + l * partialSum w r ≤ l * partialSum w (r + k) := by
  obtain ⟨r, hr⟩ : ∃ r, r = argMin (disc w l n) (l - 1) := ⟨_, rfl⟩
  have hrlt : r < l := by
    have hle := argMin_le (disc w l n) (l - 1)
    omega
  refine ⟨r, hrlt, ?_⟩
  intro k
  have hmin : disc w l n r ≤ disc w l n (r + k) := by
    rw [hr]
    exact disc_min_global hl hper hn (argMin (disc w l n) (l - 1) + k)
  have hnat : l * partialSum w r + (r + k) * n
      ≤ l * partialSum w (r + k) + r * n := by
    unfold disc at hmin
    omega
  have hexp : (r + k) * n = r * n + k * n := Nat.add_mul r k n
  omega

/-- **The time form.**  If `t` is a position of the rotated word with exactly `j`
ones before it, then `t·n ≤ j·l` — which is `ExtremalTime.dom_iff_mul_le`, the
hypothesis `dominating_Crel_le` consumes. -/
theorem rotation_time_dominates {w : Nat → Nat} {l n r t j : Nat}
    (hdom : ∀ k : Nat, k * n + l * partialSum w r ≤ l * partialSum w (r + k))
    (hcount : partialSum w (r + t) = partialSum w r + j) :
    t * n ≤ j * l := by
  have h := hdom t
  rw [hcount, Nat.mul_add] at h
  have hc : j * l = l * j := Nat.mul_comm j l
  omega

/-- **Lemma 5, assembled.**  Combining the cycle lemma with the time form and
`ExtremalTime.dom_iff_mul_le`: the rotated word's times all satisfy
`t_j ≤ ⌊jl/n⌋`, which is exactly the hypothesis of
`ExtremalTime.dominating_Crel_le`. -/
theorem cycle_lemma_time {w : Nat → Nat} {l n : Nat} (hl : 0 < l) (hn0 : 0 < n)
    (hper : ∀ i, w (i + l) = w i) (hn : partialSum w l = n) :
    ∃ r : Nat, r < l ∧
      ∀ t j : Nat, partialSum w (r + t) = partialSum w r + j →
        t ≤ ExtremalTime.tildeTime l n j := by
  obtain ⟨r, hrlt, hdom⟩ := cycle_lemma hl hper hn
  refine ⟨r, hrlt, ?_⟩
  intro t j hcount
  exact (ExtremalTime.dom_iff_mul_le hn0).mpr (rotation_time_dominates hdom hcount)

end CycleLemma
end Collatz
