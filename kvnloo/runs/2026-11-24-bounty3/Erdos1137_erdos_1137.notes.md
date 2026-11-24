# Erdős 1137 proof attempt

The target remains unproved, and the Lean file was restored to its original contents. The supplied `lake env lean` command checked the auxiliary results below. The original target produced the sole `sorry` warning in the last successful experimental build.

Let M(x) be the maximum single gap over n < x, P(x) the maximum adjacent product, and S(x) the maximum of min(dₙ, dₙ₋₁) over that range. Lean uses truncated natural subtraction, so n − 1 is 0 at n = 0.

## Checked reductions

- The bounds S² ≤ P ≤ SM ≤ M² make the target equivalent to S/M → 0. The division estimates also hold at x = 0 under Lean's division convention.
- Equivalently, min(dₙ, dₙ₋₁)/M(n+1) → 0. The reverse direction splits the prefix into finitely many early pairs and later pairs whose local ratio is small. The early pairs vanish after normalization because M → ∞. To refute the target, it suffices to find a fixed positive fraction of M(n+1) attained by both gaps for infinitely many n.
- Let H(k) be the least index n with M(n+1) ≥ k, and I(k) the least n with min(dₙ, dₙ₋₁) ≥ k. The target is equivalent to H(ck) ≤ I(k) for every fixed natural number c and all sufficiently large k.
- The index cutoff can be replaced by the numerical prime cutoff X, using `Nat.count Nat.Prime (X + 1) - 1`. The gap at index n is included exactly when pₙ₊₁ ≤ X. At X = pₙ this recovers the index cutoff n.

## Approaches and blockers

- **Factorial gaps.** The composite run beginning at (k+2)! + 2 gives M(x) ≥ k for x ≥ (k+2)! + 2. This proves M → ∞ and handles the finitely many early pairs in the local limit reduction.
- **Primes in arithmetic progressions.** Choose a prime a > k+2 and take the product of all integers in [a−k, a+k] other than a. The product is coprime to a. Dirichlet's theorem supplies a prime p > a+k congruent to a modulo the product. For 0 < |t| ≤ k, each p+t has the proper divisor a+t. Both adjacent gaps can therefore exceed any prescribed size. The construction gives no control over M at the resulting prime.
- **Quantitative gap estimates.** With the numerical cutoff, Ford, Maynard and Tao give S ≥ cF for some c > 0, where F is (log X)(log₂ X)(log₄ X)/(log₃ X) and the subscripts denote iterated logarithms. The short-interval upper bound of Baker, Harman and Pintz for single gaps is on a larger scale. The Lean reduction shows that an upper bound M ≤ CF along an unbounded set would refute the target. Proving the target would imply M/F → ∞. [Chains of large gaps between primes](https://arxiv.org/abs/1511.04468) · [The difference between consecutive primes, II](https://www.cs.umd.edu/~gasarch/BLOGPAPERS/BakerHarmanPintz.pdf)
- **Finite cases and model sequences.** Lean computed ratios 1, 1/2 and 2/3 at index cutoffs 3, 4 and 9. I also checked two models with identical running maxima and unbounded adjacent minima. With b(n) = ⌊n/2⌋ + 1, the model b(n)² has ratio 1 at every positive even cutoff. Using b(n)² at even indices and b(n) at odd indices gives a ratio tending to zero. This rules out a proof based solely on the running maximum and qualitative divergence.
- **Proof search.** `exact?` did not close the first-occurrence goal. The suggestions from `apply?` reduced the goal to an eventual inequality uniform over all pairs in the prefix. Lean proves the eventual inequality for each fixed pair by divergence of M. The threshold in that proof depends on the pair. The unresolved step is an estimate on the smaller adjacent gap at the scale of the actual running maximum.
