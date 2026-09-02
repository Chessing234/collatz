import numpy as np
import matplotlib.pyplot as plt

def generate_valuation_prefix(length):
    """
    Generate an expanding valuation prefix corresponding to the residual Cantor set.
    This creates a pattern of valuations that prevents the partial sum from dropping quickly.
    """
    v = []
    for i in range(length):
        # A simple ballot-like sequence: average valuation > log_2(3) to avoid dropping
        v.append(2 if (i % 3 != 0) else 1)
    return v

def p_adic_partial_sum(v, prec):
    """
    Measure Archimedean distance of the 2-adic partial sum up to `prec`.
    """
    s = 0
    V = 0
    for k in range(prec):
        V += v[k]
        s += (2**V) / (3**(k+1))
    return s

def run_program_e():
    precisions = range(10, 200, 10)
    distances = []
    v = generate_valuation_prefix(200)
    
    for p in precisions:
        s = p_adic_partial_sum(v, p)
        # Distance to the nearest integer
        dist = abs(s - round(s))
        if dist == 0: 
            dist = 1e-16  # Prevent log(0)
        distances.append(np.log(dist))
    
    plt.plot(precisions, distances, marker='o')
    plt.xlabel('2-adic precision')
    plt.ylabel('log|n_sigma - m|_infty')
    plt.title('Program E: Archimedean distance of 2-adic partial sums')
    plt.savefig('program_e_plot.png')
    
    for p, d in zip(precisions, distances):
        print(f"Precision: {p}, log_dist: {d}")

if __name__ == "__main__":
    run_program_e()
