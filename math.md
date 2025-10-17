# Mathematical Theorems Behind Stochastic Computing REPL Core

## 1. Stochastic Number Representation

A stochastic number is represented by a sequence of bits where the probability of '1' encodes the value.

For a number \( x \in [0,1] \), the stochastic bitstream \( S \) has \( P(S_i = 1) = x \) for each bit \( i \), assuming uncorrelated bits.

## 2. Multiplication Theorem

The product of two stochastic numbers can be computed using the AND operation.

If \( A \) and \( B \) are stochastic representations of \( x \) and \( y \) respectively, then the bitstream \( C = A \wedge B \) is a stochastic representation of \( x \cdot y \).

**Proof:** \( P(C = 1) = P(A=1 \wedge B=1) = P(A=1) \cdot P(B=1) = x \cdot y \), assuming independence.

## 3. Addition Theorem

Addition is more complex. One way is using a multiplexer (MUX) for scaled addition.

To compute \( a \cdot x + b \cdot y \) (where \( a + b = 1 \), \( a, b \in [0,1] \)), use a MUX with control stream \( C \) where \( P(C=1) = a \).

The output \( O = \text{MUX}(C, A, B) \) has:
\[
P(O=1) = P(C=1) \cdot P(A=1) + P(C=0) \cdot P(B=1) = a \cdot x + (1-a) \cdot y
\]

For unscaled addition \( x + y \) (assuming \( x + y \leq 1 \)), set \( a = 0.5 \), but this gives \( 0.5x + 0.5y \), which is not exact. More sophisticated circuits are needed for general addition.

## 4. Inversion Theorem

The inversion (1 - x) can be computed using the NOT operation.

If \( A \) is a stochastic representation of \( x \), then \( \neg A \) is a stochastic representation of \( 1 - x \).

**Proof:** \( P(\neg A = 1) = P(A = 0) = 1 - P(A=1) = 1 - x \).

## 5. Progressive Precision and Convergence

As the length of the bitstream increases, the estimate of the probability converges to the true value by the Law of Large Numbers.

For a stream of length \( n \), the proportion of 1's \( \hat{x} = \frac{1}{n} \sum S_i \) satisfies \( \hat{x} \to x \) in probability as \( n \to \infty \).

The variance is \( \frac{x(1-x)}{n} \), so precision improves with \( \sqrt{n} \).

## 6. Fault Tolerance

Single-bit errors have minimal impact because information is distributed across the stream. A flipped bit changes the count by at most 1/n, which is negligible for large n.

## Challenges

- Long streams needed for high precision increase latency.
- Generating uncorrelated random streams requires hardware overhead.
