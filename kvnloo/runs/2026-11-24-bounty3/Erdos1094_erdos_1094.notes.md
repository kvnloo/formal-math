# Erdős 1094 proof attempt

The target remains open in this file. The helper proofs reduce finiteness to a uniform upper bound on the second coordinate.

## Verified reductions

Let (q=lfloor n/k
floor), (r=nmod k), and (m=kq). Then (m=n-r) lies among the (k) numerator factors. In an exception every prime factor of (m) is at most (max(q,k)), so (m) is coprime to (inom nk).

- If (p^amid m) and (p^a>k), then (nmod p^a=r<k). Kummer's theorem gives (pmidinom nk), a contradiction. Consequently (mmidoperatorname{lcm}(1,ldots,k)), so (n<operatorname{lcm}(1,ldots,k)+k). This gives finiteness over any bounded range of (k).
- The stronger residue-dependent condition is (qmidinom{k-1}{r}). For every (1le ile v_p(m)), absence of a carry gives (kmod p^ile rmod p^i). With (s=k-1-r), the contribution at this position to (v_p(k!)-v_p(r!)-v_p(s!)) is at least one. Legendre's formula gives (mmid kinom{k-1}{r}). In particular (0<r<k-1).
- Every prime divisor (p) of an exceptional binomial satisfies (p>k) and (p>q), hence (p^2>n). The binomial coefficient is squarefree.
- For (kle4), Lean checks that the exceptions are exactly ((7,3),(13,4),(14,4)).

## Search and remaining obstacle

I enumerated divisors (m) of (operatorname{lcm}(1,ldots,k)) with (kmid m), checked the base-(p) carry conditions, and then stripped primes at most (k) from each numerator factor. An exceptional factor's residual part is either 1 or a prime greater than (max(q,k)), since two such primes have product greater than (n). The exploratory Python run through (k=110) found 14 exceptions, with largest second coordinate (28). Only the classification for (kle4) was checked in Lean.

The lcm and quotient constraints can still leave large candidates. For example, (k=70), (n=314071326474420095) satisfies both divisibility constraints and has no carries for primes at most (70). Here (nmod71=41<70), so (71) divides the binomial and rules out the candidate. This illustrates the need for control of primes above (k) in the large-(n) regime.

I also considered using the distribution of primes to force a carry for primes near (k). Konyagin's lower bound for the first (n>k+1) with no prime factor at most (k) excludes a range up to (exp(clog^2 k)) for large (k). This leaves a gap before the exponential upper bounds from the divisibility constraints. I found no argument closing the gap or proving that the surviving (k) are bounded. [Konyagin, *Estimates of the least prime factor of a binomial coefficient*](https://doi.org/10.1112/S0025579300007555)

The prescribed Lean command checks the helpers and warns only about the original placeholder. The helper declarations have no `sorryAx` dependency. Lean's `exact?` search did not close the target.
