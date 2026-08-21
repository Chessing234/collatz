import Collatz.Strategy.AccumulatorSharp

/-!
# Where the accumulator keeps its information

The cocycle law `affineC_add` splits a window at any time `k`:

`C_{k+m}(x) = 3 ^ a' · C_k(x) + 2 ^ k · C_m(T^k x)`,  `a' = a(T^k x, m)`.

Read modulo `2 ^ k` the *second* term vanishes, and read modulo `3 ^ a'` the
*first* one does.  So the two reductions of the accumulator look in opposite
directions along the window:

* `C mod 2 ^ k` is decided by the **first `k` steps**, up to multiplication by a
  power of three — which is a unit modulo `2 ^ k` (`affineC_mod_two_pow`);
* `C mod 3 ^ a'` is decided by the **last `m` steps**, up to multiplication by a
  power of two — a unit modulo `3 ^ a'` (`affineC_mod_three_pow`).

Neither statement is deep; both are worth having named, because they say exactly
which part of a parity word a given congruence on `C` can possibly constrain.
The 2-adic reduction cannot see the tail, and the 3-adic reduction cannot see the
head.  Attempts to build a sieve on `C` are therefore looking at one end of the
word or the other, never at the interaction between them — which is the same
message `ThreeResidue` delivers for the orbit point, and the reason the round's
sparsity searches came back empty.
-/

namespace Collatz
namespace AccumulatorLocal

open Congruence AffineExact AccumulatorArith

/-- **The 2-adic reduction reads the head of the word.**  Modulo `2 ^ k` the
accumulator of the whole window is the accumulator of the first `k` steps, scaled
by the power of three contributed by the tail. -/
theorem affineC_mod_two_pow (x k m : Nat) :
    affineC (k + m) x % 2 ^ k
      = (3 ^ oddCount (acceleratedOrbit k x) m * affineC k x) % 2 ^ k := by
  rw [affineC_add x k m, Nat.mul_comm (2 ^ k) (affineC m (acceleratedOrbit k x)),
    Nat.add_mul_mod_self_right]

/-- **The 3-adic reduction reads the tail of the word.**  Modulo the power of
three contributed by the tail, the accumulator is the tail's own accumulator
scaled by `2 ^ k`. -/
theorem affineC_mod_three_pow (x k m : Nat) :
    affineC (k + m) x % 3 ^ oddCount (acceleratedOrbit k x) m
      = (2 ^ k * affineC m (acceleratedOrbit k x)) % 3 ^ oddCount (acceleratedOrbit k x) m := by
  rw [affineC_add x k m, Nat.add_comm, Nat.add_mul_mod_self_left]

/-- The head-reading form as a divisibility, with the unit made explicit: the
difference between the whole accumulator and the scaled head is a multiple of
`2 ^ k`. -/
theorem two_pow_dvd_affineC_sub_head (x k m : Nat) :
    ∃ c : Nat, affineC (k + m) x
      = 3 ^ oddCount (acceleratedOrbit k x) m * affineC k x + 2 ^ k * c :=
  ⟨affineC m (acceleratedOrbit k x), affineC_add x k m⟩

/-- An even prefix contributes no head at all, so the whole accumulator is
divisible by `2 ^ k` — the divisibility half of `AccumulatorValuation`, recovered
from the localisation. -/
theorem two_pow_dvd_of_head_trivial {x k : Nat} (h : affineC k x = 0) (m : Nat) :
    2 ^ k ∣ affineC (k + m) x := by
  refine ⟨affineC m (acceleratedOrbit k x), ?_⟩
  rw [affineC_add x k m, h, Nat.mul_zero, Nat.zero_add]

end AccumulatorLocal
end Collatz
