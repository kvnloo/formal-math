# Erdős 1142 proof attempt

I did not prove `Erdos1142.erdos_1142`. Its positive statement would imply the twin prime conjecture. For arbitrarily large $n$ satisfying `Erdos1142Prop`, the exponents 1 and 2 give the primes $n-2$ and $n-4$. I checked this reduction in Lean with the repository imports.

```lean
private theorem infinite_twin_primes_of_erdos1142
    (h : Infinite {n | Erdos1142Prop n}) :
    Infinite {p : ℕ | p.Prime ∧ (p + 2).Prime} := by
  apply Set.infinite_coe_iff.mpr
  apply Set.infinite_iff_exists_gt.mpr
  intro b
  obtain ⟨n, hn, hbn⟩ := Set.Infinite.exists_gt (Set.infinite_coe_iff.mp h) (b + 4)
  change Erdos1142Prop n at hn
  have h₁ := hn.2 1 (by decide) (by omega)
  have h₂ := hn.2 2 (by decide) (by omega)
  refine ⟨n - 4, ⟨h₂, ?_⟩, by omega⟩
  convert h₁ using 1
  omega
```

## Approaches checked in Lean

- **Simultaneous prime values.** For each fixed $K$, the target would give infinitely many $m$ for which all $m+2^K-2^k$ with $1\le k\le K$ are prime. These offsets are admissible. For an odd trial prime $p$, take $m\equiv-2^K\pmod p$. For $p=2$, take $m$ odd. I used Dirichlet's theorem to prove the first-shift case with $n$ arbitrarily large and divisible by any prescribed odd modulus. The second shift already calls for simultaneous primality. A fixed-prefix result would also need a bound on the size of its witnesses to control the number of applicable exponents.
- **Congruence sieve.** If $p+2^k<n$, a solution must avoid $n\equiv 2^k\pmod p$, since the congruence makes $p$ a proper divisor. If a prefix covers every nonzero residue modulo $p$, then $p\mid n$. I checked the product of these forced primes divides $n$ and that the full-coverage primes lie in the classes 3 and 5 modulo 8. Every solution above 21 is an odd multiple of 15. Any fixed list of trial primes leaves arbitrarily large candidates even after imposing $n-2^k>1$ for every applicable $k$. For an odd product $M$ of trial primes, the numbers $M^2(4B+7)$ are such candidates. A sieve proof needs a uniform argument with growing trial primes.
- **Factorization and distance from powers.** A solution above 4 cannot be a perfect power. If $n=a^d$ with $d\ge2$, oddness forces $a\ge3$. For $a>3$, the term $a^d-2^d$ has the proper divisor $a-2$. The remaining base $a=3$ is excluded by $9-8=1$ or by the necessary divisibility by 5. Fermat's little theorem also gives $n-2^k>k$. If the prime $p=n-2^k$ were at most $k$, reducing the exponent by $p-1$ would give an earlier term with proper divisor $p$. The case $p=2$ follows from parity. These restrictions still allow unbounded candidate values.

Converting the original goal with `Set.infinite_iff_exists_gt` leaves `∀ b, ∃ n, Erdos1142Prop n ∧ b < n`. Library search and `aesop` left the witness goal open. The final source was restored and the requested compiler command reported the two pre-existing placeholder warnings.

## Bounded checks

Lean verified that there are no solutions with $105<n<1024$. The proof reduces to odd multiples of 15 and checks a concrete divisor of one difference for each multiple. Direct `decide` on the composite differences hit Lean's recursion limit. Checking their small divisors through modular equalities compiled.

A separate exact-integer Python sieve found only $4,7,15,21,45,75,105$ below $2^{94}$. It used direct trial division below 1024. For each dyadic interval with lower endpoint $a$, it gathered $2^k\bmod p$ for trial primes $p<5000$ under the strict cutoff $p+2^k<a$. The product $D$ of full-coverage primes forced $n=D(2t+1)$, and the remaining residue classes excluded values of $t$. At higher intervals I split near the lower endpoint so the largest eligible power could be used safely for most candidates. Any candidates remaining after the modular sieve were checked for an explicit divisor, a difference of 1, or a Fermat compositeness witness. This finite computation was outside Lean and gives no bound for all solutions.
