namespace Collatz

/-!
# Program G: Function-field prototype and Z descent

This file formalizes the Hicks–Mullen–Yucas–Zavislak / Behajaina–Paran
Collatz map on polynomials over F_2, demonstrates its strict degree drop,
and then attempts the same descent logic on integers (Z) where it hits
the famous failing step.
-/

/-- Polynomials over F_2 represented as a list of boolean coefficients, lowest degree first. -/
def Poly := List Bool

/-- Polynomial addition over F_2 is bitwise XOR. -/
def Poly.add : Poly → Poly → Poly
| [], ys => ys
| xs, [] => xs
| (x::xs), (y::ys) => (x != y) :: Poly.add xs ys

/-- Multiplication by x (shifting coefficients up). -/
def Poly.shift : Poly → Poly
| [] => []
| xs => false :: xs

/--
The polynomial Collatz map:
- If x | P, return P / x
- If x ∤ P, return (x + 1) * P + 1
-/
def polyStep : Poly → Poly
| [] => []
| false :: xs => xs  -- Division by x
| true :: xs =>
  -- P = true :: xs (non-zero constant term, meaning x ∤ P)
  -- (x + 1)P + 1 = xP + P + 1
  -- xP = false :: true :: xs
  -- P + 1 = false :: xs
  -- Sum = false :: ((true :: xs) + xs)
  false :: Poly.add (true :: xs) xs

/-- Replaying the degree drop: one odd step followed by an even step drops the degree back down. -/
theorem poly_two_steps (xs : Poly) :
    polyStep (polyStep (true :: xs)) = Poly.add (true :: xs) xs := by
  rfl


/-!
## Would-be proof for Z
-/

/-- The integer Collatz map. -/
def intStep (n : Int) : Int :=
  if n % 2 = 0 then n / 2 else 3 * n + 1

/--
The failing step for Z.
In the polynomial world, (x+1)P+1 has a zero constant term and immediately divides by x without increasing degree.
In Z, (3n+1)/2 is evaluated as size, but it is actually strictly greater than n (for n >= 2).
This is the only lemma we mark as sorry.
-/
lemma int_drop (n : Int) (h : n % 2 = 1) : (3 * n + 1) / 2 < n := by
  sorry

/-- The "would-be proof" for Z using the exact same descent logic. -/
theorem int_collatz_drop (n : Int) (h : n > 1) (h_odd : n % 2 = 1) :
    intStep (intStep n) < n := by
  have h1 : intStep n = 3 * n + 1 := by
    dsimp [intStep]
    have h_not_even : ¬(n % 2 = 0) := by
      intro hc
      omega
    rw [if_neg h_not_even]
  rw [h1]
  
  have h2 : (3 * n + 1) % 2 = 0 := by
    omega
    
  have h3 : intStep (3 * n + 1) = (3 * n + 1) / 2 := by
    dsimp [intStep]
    rw [if_pos h2]
  rw [h3]
  
  exact int_drop n h_odd

end Collatz
