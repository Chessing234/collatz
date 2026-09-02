import Collatz.Search.Descent

/-!
# The tail cannot depend on the run length alone

`PROGRAM_STATUS` asks whether `n > T^(r(n) + s(n))(n)` for explicit `s`, where
`r(n) = v₂(n+1)` is the length of the initial run of odd accelerated steps.  It
notes that `DensitySaturation.no_uniform_block` does not refute this shape,
"because `r(n)` is unbounded" — that theorem's witness is `2^(B+1) − 1`, whose
run length grows with `B`, so it only rules out a tail uniform in everything.

The natural refined reading is that the tail may depend on the run length:
is there `s : ℕ → ℕ` with `T^(r(n) + s(r(n)))(n) < n` for every odd `n > 1`?

**This file gives witnesses against that reading.**  All five have `r(n) = 2`
exactly — they are `≡ 3 (mod 8)` — yet their stopping times are `72, 123, 176,
222, 308`.  The run length is pinned while the descent time is not, so no `s`
depending only on `r` can cover them.

## What is proved here, and what is not

Proved: five explicit `n ≡ 3 (mod 8)` that do **not** descend within the stated
number of steps.  Since each has `r(n) = 2`, any candidate tail `s` must satisfy
`s(2) ≥ 306`; the witnesses were found by searching `n < 10^8`, and the largest
forces exactly that.

Not proved: that `s(2)` cannot be finite.  That needs `σ` unbounded on the single
class `n ≡ 3 (mod 8)`, which is an infinite statement.  The evidence is a search
over `n < 10^8`, where the maximum of `σ` on the class rises steadily —
`72, 123, 176, 222, 308` at bounds `10^4, 10^5, 10^6, 10^7, 10^8` — with no sign
of levelling.  Turning that into a theorem would need a construction placing an
arbitrarily long rise downstream of a fixed two-step opening, in the shape of
`no_uniform_block` but with the class constraint; that is not attempted here.

Contrast `r(n) = 1`, where the question has a clean positive answer already in
the repository: `Structure.CycleMinClass.two_step_descent` gives `σ = 2` for
every `n ≡ 1 (mod 4)` with `n > 1`.  So the classes genuinely differ — `r = 1`
is bounded, `r = 2` appears not to be.

Contrast also `Strategy.MersenneDescent`, which checks the family the question
proposed first, `n = 2^j − 1`.  That family does *not* refute the shape: its
stopping time stays within `12j`.  The obstruction is not where the question
expected it.
-/

namespace Collatz
namespace RunLengthTail

open Search

/-! ## Five witnesses with run length exactly two

`n % 8 = 3` says `v₂(n+1) = 2`: the opening run is two odd steps, no more. -/

theorem mod_7963 : 7963 % 8 = 3 := by decide
theorem mod_57115 : 57115 % 8 = 3 := by decide
theorem mod_626331 : 626331 % 8 = 3 := by decide
theorem mod_6631675 : 6631675 % 8 = 3 := by decide
theorem mod_56924955 : 56924955 % 8 = 3 := by decide

/-! ## …that nevertheless take that long to descend -/

theorem slow_7963 : dropsWithin 71 7963 = false := by decide
theorem slow_57115 : dropsWithin 122 57115 = false := by decide
theorem slow_626331 : dropsWithin 175 626331 = false := by decide
theorem slow_6631675 : dropsWithin 221 6631675 = false := by decide

set_option maxRecDepth 10000 in
theorem slow_56924955 : dropsWithin 307 56924955 = false := by decide

/-- Each does descend one step later, so these are exact stopping times and not
merely lower bounds. -/
theorem drops_7963 : dropsWithin 72 7963 = true := by decide
theorem drops_57115 : dropsWithin 123 57115 = true := by decide
theorem drops_626331 : dropsWithin 176 626331 = true := by decide
theorem drops_6631675 : dropsWithin 222 6631675 = true := by decide

set_option maxRecDepth 10000 in
theorem drops_56924955 : dropsWithin 308 56924955 = true := by decide

/-- **A tail of `305` does not suffice at run length two.**  `56924955` opens
with exactly two odd steps and has not descended after `307` accelerated steps,
so any `s` with `T^(r(n) + s(r(n)))(n) < n` for all odd `n > 1` needs
`s(2) ≥ 306`. -/
theorem tail_at_two_exceeds_305 :
    56924955 % 8 = 3 ∧ dropsWithin 307 56924955 = false :=
  ⟨mod_56924955, slow_56924955⟩

end RunLengthTail
end Collatz
