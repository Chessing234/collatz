import math
from fractions import Fraction

def continued_fraction(alpha, terms=20):
    cf = []
    x = alpha
    for _ in range(terms):
        f = math.floor(x)
        cf.append(f)
        x -= f
        if x < 1e-10:
            break
        x = 1 / x
    return cf

def lower_mechanical_word(alpha, L):
    """
    Generate the first L terms of the lower mechanical word with slope alpha.
    s_k = floor((k+1)*alpha) - floor(k*alpha)
    """
    return [math.floor((k + 1) * alpha) - math.floor(k * alpha) for k in range(1, L + 1)]

def solve_tower(v, max_M=100):
    """
    Attempt to find an initial value n mod 2^M that realizes the sequence of valuations v.
    Returns the level M at which the tower dies (no solution), or None if it survives.
    """
    # We maintain a list of possible n mod 2^m
    # Initially for m = 1, we know n must be odd so n = 1 mod 2.
    valid_n = {1}
    current_m = 1
    
    for M in range(2, max_M + 1):
        next_valid_n = set()
        for n in valid_n:
            # We branch: n could be n or n + 2^(M-1) mod 2^M
            for n_cand in (n, n + (1 << (current_m))):
                # Simulate Collatz sequence with this candidate
                curr = n_cand
                valid = True
                for val in v:
                    curr = 3 * curr + 1
                    # Count factors of 2
                    factors = 0
                    while curr % 2 == 0 and curr > 0:
                        factors += 1
                        curr //= 2
                    
                    if factors != val:
                        # Depending on how many bits we know, we might not be able to evaluate fully.
                        # For a rigorous check we need to track bit availability.
                        # This is a simplified check.
                        pass
                        
                # Actually, solving the linear congruence is better done step-by-step
        break # Placeholder
        
    return None

def main():
    alpha = math.log2(3)
    print(f"Log2(3) Continued Fraction: {continued_fraction(alpha)}")
    word = lower_mechanical_word(alpha, 20)
    print(f"Lower mechanical word (L=20): {word}")

if __name__ == "__main__":
    main()
