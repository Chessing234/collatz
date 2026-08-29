import Collatz.Structure.AccCycle
import Collatz.Strategy.AccumulatorArith
import Collatz.Strategy.AffineExact

/-!
# Rotating a cycle changes nothing the criterion can see

`HalbeisenHungerbuhler.HHExtremal` hypothesises that `x` is the **minimum** of
its orbit.  `CycleLemma.cycle_lemma` picks its *own* rotation `r` — the `argMin`
of the discrepancy — and concludes about `acceleratedOrbit r x`.  The two
statements are about different points and never meet.  That mismatch is gap (4),
the last of the four between `CycleLemma` and `HHExtremal`, and this file removes
the part of it that is genuine mathematics.

## What is proved

* **`oddCount_rotation_invariant`** — on a cycle, `oddCount` over a full period is
  the same at every rotation.  This is the content: `oddCount_add` split two ways
  around `i + L = L + i`, with `acceleratedOrbit L n = n` collapsing the second,
  and the shared `oddCount n i` cancelling.  So the exponent `a`, and with it the
  gap `2 ^ L − 3 ^ a`, is a property of the *cycle*, not of the point chosen to
  represent it.
* `accIsCycleOf_rotation` — every rotation is a cycle of the same length
  (`accIsCycleOf_orbit`, repackaged).
* **`affine_cycle_eq_rotation`** — hence the affine cycle equation
  `(2 ^ L − 3 ^ a) · y = affineC L y` holds at *every* rotation `y`, with the same
  `a` throughout.
* **`gap_mul_le_affineC_rotation`** — and if `x` is the orbit minimum, then
  `(2 ^ L − 3 ^ a) · x ≤ affineC L (acceleratedOrbit i x)` for every `i`.  This is
  the transport the criterion needs: a bound proved at *any* rotation bounds the
  minimum.

## What is still missing

`cycle_lemma_time` bounds the abstract times of the word `w x`.  `HHExtremal`'s
conclusion is about `affineC L (acceleratedOrbit r x)`, which `HHBridge.affineC_eq_C`
turns into `C (word (acceleratedOrbit r x) L)`.  Joining them needs one more
identity: the one-positions of the *rotated point's own word* are the one-positions
of `w x` on `[r, r + L)` read cyclically — index surgery on `times` under a shift
by `r` mod `L`.  That is a lemma, not a chaining step, and it is not in the
repository.

So `HHExtremal` remains an assumed `Prop`.  Gaps (1), (2), (3) are closed
(`HHBridge`, `HHMinTime`); gap (4) is reduced from "the rotation law is missing"
to "one cyclic-reindexing identity for `word` is missing".
-/

namespace Collatz
namespace RotationLaw

open AccCycle AffineExact

/-! ## (a) The odd-step count is rotation-invariant on a cycle. -/

theorem oddCount_rotation_invariant {n L : Nat} (h : AccIsCycleOf n L) (i : Nat) :
    oddCount (acceleratedOrbit i n) L = oddCount n L := by
  have h1 := AccumulatorArith.oddCount_add n i L
  have h2 := AccumulatorArith.oddCount_add n L i
  rw [h.2] at h2
  have h3 : i + L = L + i := Nat.add_comm i L
  rw [h3] at h1
  -- h1 : oddCount n (L + i) = oddCount n i + oddCount (acceleratedOrbit i n) L
  -- h2 : oddCount n (L + i) = oddCount n L + oddCount n i
  omega

/-! ## (a') every rotation is a cycle point of the same length -/

theorem accIsCycleOf_rotation {n L : Nat} (h : AccIsCycleOf n L) (i : Nat) :
    AccIsCycleOf (acceleratedOrbit i n) L :=
  accIsCycleOf_orbit h i

/-! ## (b) the affine cycle equation holds at the rotated point -/

/-- The gap `2^L - 3^a` is well-defined (i.e. `3^a ≤ 2^L`) for any positive
accelerated cycle, from `accCycle_bounds`. -/
theorem gap_pos_or_le {n L : Nat} (hn : 0 < n) (h : AccIsCycleOf n L) :
    3 ^ oddCount n L ≤ 2 ^ L := by
  obtain ⟨_, _, h3⟩ := accCycle_bounds hn h
  omega

/-- **The rotated affine cycle equation.**  Writing `a = oddCount n L` (which by
(a) is the same at every rotation), the affine cycle identity
`(2^L - 3^a) * x = affineC L x` — normally stated only at the chosen cycle point
`n` — holds equally at every rotation `acceleratedOrbit i n`. -/
theorem affine_cycle_eq_rotation {n L : Nat} (hn : 0 < n) (h : AccIsCycleOf n L) (i : Nat) :
    (2 ^ L - 3 ^ oddCount n L) * acceleratedOrbit i n = affineC L (acceleratedOrbit i n) := by
  have hrot : AccIsCycleOf (acceleratedOrbit i n) L := accIsCycleOf_rotation h i
  have hcount : oddCount (acceleratedOrbit i n) L = oddCount n L :=
    oddCount_rotation_invariant h i
  have hex := affine_exact (acceleratedOrbit i n) L
  rw [hrot.2, hcount] at hex
  -- hex : 2 ^ L * acceleratedOrbit i n
  --         = 3 ^ oddCount n L * acceleratedOrbit i n + affineC L (acceleratedOrbit i n)
  have hge : 3 ^ oddCount n L ≤ 2 ^ L := gap_pos_or_le hn h
  have hsub : (2 ^ L - 3 ^ oddCount n L) * acceleratedOrbit i n
      = 2 ^ L * acceleratedOrbit i n - 3 ^ oddCount n L * acceleratedOrbit i n :=
    Nat.sub_mul _ _ _
  rw [hsub, hex]
  omega

/-! ## (c) minimality of `x` transports through the gap -/

/-- **Minimality of `x` over its orbit forces `gap * x` to be a lower bound for
`affineC L` at every rotation.**  Combines (b) with `x ≤ acceleratedOrbit i x`. -/
theorem gap_mul_le_affineC_rotation {n L : Nat} (hn : 0 < n) (h : AccIsCycleOf n L)
    (hmin : ∀ k : Nat, n ≤ acceleratedOrbit k n) (i : Nat) :
    (2 ^ L - 3 ^ oddCount n L) * n ≤ affineC L (acceleratedOrbit i n) := by
  have heq := affine_cycle_eq_rotation hn h i
  have hle : n ≤ acceleratedOrbit i n := hmin i
  have hmono : (2 ^ L - 3 ^ oddCount n L) * n ≤ (2 ^ L - 3 ^ oddCount n L) * acceleratedOrbit i n :=
    Nat.mul_le_mul_left _ hle
  rw [heq] at hmono
  exact hmono

end RotationLaw
end Collatz
