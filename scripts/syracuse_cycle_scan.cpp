// Exact integer interval scan of the actual Syracuse probability laws.
// This executable is a research calculation, not a Lean certificate.
// See Devices/SyracuseCycleScan.md for the recurrence and error proof.
#include <algorithm>
#include <cstdint>
#include <cstdlib>
#include <iostream>
#include <stdexcept>
#include <vector>

using U = std::uint64_t;
using W = __uint128_t;

int main(int argc, char **argv) {
  const unsigned levels = argc > 1 ? std::stoul(argv[1]) : 15;
  const unsigned precision = argc > 2 ? std::stoul(argv[2]) : 60;
  const bool atoms = argc > 3 && std::string(argv[3]) == "atoms";
  if (levels < 1 || levels > 18 || precision < 8 || precision > 60)
    throw std::invalid_argument("levels must be 1..18; precision 8..60");
  if (atoms && levels > 8)
    throw std::invalid_argument("atom output is limited to 8 levels");
  const U scale = U{1} << precision;
  std::vector<U> previous(1, scale);
  U modulus = 1, priorMinimum = scale;
  for (unsigned n = 1; n <= levels; ++n) {
    const U priorModulus = modulus;
    modulus *= 3;
    std::vector<U> lower(modulus, 0);
    U residue = 1, value = 0;
    const auto advance = [&]() {
      const U input = residue % 3 == 1 ? previous[(residue - 1) / 3] : 0;
      value = (value + input) / 2;
      residue = residue % 2 == 0 ? residue / 2 : (residue + modulus) / 2;
    };
    // After this burn-in the atom error is at most 2*n / scale.
    for (unsigned j = 0; j < precision; ++j) advance();
    // Multiplication by 1/2 permutes all units in a single cycle.
    for (U j = 0; j < 2 * priorModulus; ++j) {
      advance();
      lower[residue] = value;
    }
    U minimum = scale, minimizer = 0, pair = 5 * scale, pairResidue = 0;
    for (U r = 1; r < modulus; ++r) {
      if (r % 3 && lower[r] < minimum) {
        minimum = lower[r];
        minimizer = r;
      }
      if (r % 3 == 1) {
        const U candidate = 4 * lower[r] + lower[(4 * r + 1) % modulus];
        if (candidate < pair) { pair = candidate; pairResidue = r; }
      }
    }
    const U error = 2 * n;
    const U priorUpper = priorMinimum + 2 * (n - 1);
    const bool logisticCertified =
      W{3} * minimum * (scale + W{3} * priorModulus * priorUpper)
        >= W{priorUpper} * scale;
    const bool logisticRefuted =
      W{3} * (minimum + error) * (scale + W{3} * priorModulus * priorMinimum)
        < W{priorMinimum} * scale;
    const bool pairRefuted =
      W{pair + 5 * error} * (scale + W{3} * modulus * minimum)
        < W{21} * minimum * scale;
    std::cout << "{\"level\":" << n << ",\"modulus\":" << modulus
      << ",\"scale\":" << scale << ",\"atom_error_numerator\":" << error
      << ",\"minimum_atom_lower\":" << minimum
      << ",\"minimizer_of_lower_array\":" << minimizer
      << ",\"pair_numerator_lower\":" << pair
      << ",\"pair_residue\":" << pairResidue
      << ",\"logistic_certified\":" << (logisticCertified ? "true" : "false")
      << ",\"logistic_refuted\":" << (logisticRefuted ? "true" : "false")
      << ",\"sufficient_pair_bound_refuted\":" << (pairRefuted ? "true" : "false");
    if (atoms) {
      std::cout << ",\"atoms\":[";
      for (U r = 0; r < modulus; ++r) {
        if (r) std::cout << ',';
        std::cout << lower[r];
      }
      std::cout << ']';
    }
    std::cout << "}" << std::endl;
    previous.swap(lower);
    priorMinimum = minimum;
  }
}
