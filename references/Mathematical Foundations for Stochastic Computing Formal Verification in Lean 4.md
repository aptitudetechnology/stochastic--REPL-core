# **Mathematical Foundations for Stochastic Computing Formal Verification in Lean 4**

This report outlines the core mathematical theorems, proof strategies, and Lean 4 (Mathlib) components required to formally verify a Stochastic Computing (SC) system. The verification focuses on the correctness of expected values and the analysis of error bounds for finite-length bitstreams.

## **1\. Core Stochastic Computing Theory**

### **Fundamental Theorem of Stochastic Representation**

A real number $v \\in \[0, 1\]$ (unipolar format) is represented by an infinite sequence of independent and identically distributed (i.i.d.) random variables (bits) $X \= (X\_1, X\_2, X\_3, \\dots)$, where each $X\_i \\sim \\text{Bernoulli}(v)$.

* Formal Statement: The value v is defined as the expected value of any single bit:  
  $$\\forall i, v \= \\mathbb{E}\[X\_i\] \= \\mathbb{P}(X\_i \= 1)$$  
* Correctness Proof: The law of large numbers (specifically the Strong Law of Large Numbers, SLLN) proves that the empirical mean (the measured value) converges to the true value v almost surely as the bitstream length N→∞.  
  $$\\hat{V}\_N \= \\frac{1}{N} \\sum\_{i=1}^N X\_i \\xrightarrow{a.s.} v$$  
* **Independence Assumption:** The core mathematical justification for simplicity in SC circuits is the assumption that input bitstreams are **statistically independent** *and* that the bits within each stream are **i.i.d.** (independent and identically distributed). This is the **minimum assumption** required for both multiplication and scaled addition correctness.  
* **LFSR Theorems:** LFSRs generate pseudo-random sequences. Their statistical justification relies on theorems about maximum-length sequences ($m$-sequences), detailed in Section 5\.

## **2\. Stochastic Multiplication (AND Gate)**

### **Theorem 2.1: Correctness of Stochastic Multiplication (Unipolar)**

Let $A$ and $B$ be two independent stochastic bitstreams representing $P\_A$ and $P\_B$ respectively. The output stream $Z \= A \\land B$ (bitwise AND) represents $P\_Z \= P\_A \\cdot P\_B$.

* **Proof Sketch (Expected Value):**  
  1. Define the output bit $Z\_i \= A\_i \\land B\_i$.  
  2. The expected value of the output bit is $\\mathbb{E}\[Z\_i\] \= \\mathbb{P}(Z\_i \= 1)$.  
  3. By the definition of the AND operation: $\\mathbb{P}(Z\_i \= 1\) \= \\mathbb{P}(A\_i \= 1 \\text{ and } B\_i \= 1)$.  
  4. **Crucial Condition (Minimal Assumption):** Assume the bits $A\_i$ and $B\_i$ are statistically independent.  
  5. By the definition of independence: $\\mathbb{P}(A\_i \= 1 \\text{ and } B\_i \= 1\) \= \\mathbb{P}(A\_i \= 1\) \\cdot \\mathbb{P}(B\_i \= 1)$.  
  6. Since $\\mathbb{P}(A\_i \= 1\) \= P\_A$ and $\\mathbb{P}(B\_i \= 1\) \= P\_B$, we have $\\mathbb{P}(Z\_i \= 1\) \= P\_A P\_B$.  
  7. Therefore, the expected value is $\\mathbb{E}\[Z\_i\] \= P\_A P\_B$.

### **Correlation Effects (Question 2\)**

If Ai​ and Bi​ are correlated, the multiplication theorem fails:

$$\\mathbb{P}(Z\_i \= 1\) \= \\mathbb{P}(A\_i \= 1 \\text{ and } B\_i \= 1\) \= P\_A P\_B \+ \\text{Cov}(A\_i, B\_i)$$

The output value deviates from PA​PB​ by the covariance of the input bits. Correlation introduces a bias error, which does not diminish with increasing bitstream length N.

### **Error and Convergence (Finite Length $N$)**

For a finite bitstream of length N, the Mean Squared Error (MSE) of the measured product P^Z​ is:

$$\\text{Var}\[\\hat{P}\_Z\] \= \\frac{P\_Z (1 \- P\_Z)}{N} \= \\frac{P\_A P\_B (1 \- P\_A P\_B)}{N}$$

* **Theorem:** The accuracy convergence for finite-length bitstreams follows the **Inverse Length Law**, $\\text{MSE} \\propto O(1/N)$.

## **3\. Stochastic Addition (MUX-Based)**

### **Theorem 3.1: Correctness of Scaled Addition (MUX)**

Let $A$ and $B$ be two independent stochastic bitstreams representing $P\_A$ and $P\_B$. Let $S$ be a third independent stream where $S\_i \\sim \\text{Bernoulli}(P\_S)$, with $P\_S \= 0.5$. The MUX operation, $Z \= (S \\land A) \\lor (\\neg S \\land B)$, implements a scaled sum: $P\_Z \= P\_S P\_A \+ (1 \- P\_S) P\_B$.

* **Expected Value Proof Sketch:**  
  1. The output bit $Z\_i$ is a disjoint union of two events: $(S\_i \\land A\_i)$ or $(\\neg S\_i \\land B\_i)$.  
  2. $\\mathbb{P}(Z\_i \= 1\) \= \\mathbb{P}(S\_i \\land A\_i) \+ \\mathbb{P}(\\neg S\_i \\land B\_i)$  
  3. Assuming mutual independence of Si​, Ai​, and Bi​:  
     $$\\mathbb{P}(Z\_i \= 1\) \= \\mathbb{P}(S\_i) \\mathbb{P}(A\_i) \+ \\mathbb{P}(\\neg S\_i) \\mathbb{P}(B\_i)$$$$\\mathbb{P}(Z\_i \= 1\) \= P\_S P\_A \+ (1 \- P\_S) P\_B$$  
  4. Since $P\_S \= 0.5$, we get the desired scaled addition: $P\_Z \= \\frac{P\_A \+ P\_B}{2}$.

### **Variance and Error Propagation**

The output bit Zi​ also follows a Bernoulli distribution Bernoulli(PZ​). Therefore, the variance of the measured sum P^Z​ is:

$$\\text{Var}\[\\hat{P}\_Z\] \= \\frac{P\_Z (1 \- P\_Z)}{N} \= \\frac{(\\frac{P\_A \+ P\_B}{2}) (1 \- \\frac{P\_A \+ P\_B}{2})}{N}$$

### **Unscaled Addition Limitations**

Unscaled addition ($P\_A \+ P\_B$) cannot be implemented with simple logic gates while remaining restricted to the $\[0, 1\]$ range. A common approach is to use a counter/accumulator and a saturation function, which shifts the problem back to the binary domain or requires more complex, non-purely stochastic logic.

## **4\. Error Analysis and Convergence**

### **Concentration Inequalities (Question 3\)**

Since the bitstream count is the sum of i.i.d. Bernoulli random variables, concentration inequalities provide the tightest probabilistic error bounds for finite bitstreams of length $N$. These bounds quantify the probability of the empirical mean $\\hat{P}\_N$ deviating from the true mean $P$.

* Hoeffding's Inequality (Tightest Bound):  
  For a bitstream X of length N representing PX​:  
  $$\\mathbb{P}(|\\hat{P}\_X \- P\_X| \\ge \\epsilon) \\le 2e^{-2N\\epsilon^2}$$

  This inequality answers Question 3 by providing the tightest theoretical upper bound on the probability of a deviation ϵ for a given length N. It is independent of PX​.  
* Application: To guarantee ϵ accuracy, the required bitstream length N can be calculated. For example, to ensure ϵ=0.01 with 99% confidence (δ=0.01):  
  $$N \\ge \\frac{1}{2\\epsilon^2} \\ln \\left(\\frac{2}{\\delta}\\right)$$  
* Central Limit Theorem (CLT) Application: For large N, the empirical mean P^X​ is approximately normally distributed:  
  $$\\hat{P}\_X \\sim \\mathcal{N}\\left(P\_X, \\frac{P\_X(1-P\_X)}{N}\\right)$$

  The CLT provides better error estimates near the true value but requires a large N assumption, making Hoeffding's bound generally more robust for formal verification of finite systems.

### **Cumulative Error**

Chained operations (e.g., $A \\times B \\times C$) cause the variance to accumulate. Since the variance scales as $O(1/N)$, the error accumulates linearly with the number of operations $k$.

* **Theorem:** If an operation chain has $k$ components, the total MSE of the result is $\\text{MSE}\_{total} \\approx k \\cdot \\text{MSE}\_{single\\\_op}$. This rapid error accumulation is a known limitation of SC.

### **Information-Theoretic Limits (Question 4\)**

There are no "information-theoretic limits" on *computable* accuracy beyond the $O(1/N)$ relationship established by the Central Limit Theorem and Hoeffding's bounds. The main limit is **time/latency**—accuracy scales linearly with time (length $N$), which is significantly slower than the exponential scaling ($O(2^{-B})$) of fixed-point binary systems, where $B$ is the bit width.

## **5\. Bitstream Generation**

### **LFSR Mathematical Properties**

An $n$-stage Linear Feedback Shift Register (LFSR) is mathematically modeled by a linear recurrence relation over the Galois Field $\\mathbb{F}\_2$.

* Theorem 5.1: Maximum-Length Sequence (m-sequence):  
  An n-stage LFSR produces a maximum-length pseudo-random sequence (period 2n−1) if and only if its characteristic polynomial f(x) is primitive over the field F2​.  
* **Statistical Properties (Solomon Golomb's Postulates):** For $m$-sequences, these properties justify their use as practical sources of independence:  
  1. **Balance Property:** In one cycle, the number of 1s is exactly $2^{n-1}$ and the number of 0s is $2^{n-1} \- 1$. This ensures the empirical probability $\\hat{P}\_X$ is $\\frac{2^{n-1}}{2^n-1} \\approx 0.5$.  
  2. **Run Property:** The lengths of consecutive 1s and 0s follow a near-perfect geometric distribution.  
  3. **Autocorrelation Property:** The circular autocorrelation function is nearly a Dirac delta function. This proves that the sequence is highly uncorrelated with shifted copies of itself, which is vital when using multiple taps from a single LFSR to generate different, supposedly independent bitstreams.

## **6\. Comparison and Conversion Operations**

### **Binary-to-Stochastic Conversion**

The core method compares the target binary number $B$ (representing $P\_B$) against a sequence of random numbers $R\_i \\sim \\text{Uniform}\[0, 1)$. The output bit $X\_i \= (B \> R\_i)$.

* **Theorem (Expected Value):** $\\mathbb{P}(X\_i \= 1\) \= \\mathbb{P}(B \> R\_i)$. Since $B$ is fixed and $R\_i$ is uniform, this probability is exactly $B$. This conversion is statistically exact.  
* **Bitstream-to-Binary Conversion:** This is simply calculating the empirical mean: $\\hat{P}\_B \= \\frac{1}{N} \\sum\_{i=1}^N X\_i$. The accuracy is bounded by the concentration inequalities in Section 4\.

### **Comparison Operation**

Stochastic comparison ($P\_A \> P\_B$) is performed by bitwise subtraction and checking the sign bit of an accumulator, or by using a dedicated circuit called a stochastic comparator (XOR \+ counter/integrator). The output of an XOR gate, $Z=A \\oplus B$, has an expected value $P\_Z \= P\_A(1-P\_B) \+ P\_B(1-P\_A)$. This value is minimized when $P\_A \= P\_B$, allowing comparison via minimizing the XOR output's frequency.

## **7\. Advanced Operations**

| Operation | Stochastic Implementation | Expected Value Theorem | Theoretical Foundation |
| :---- | :---- | :---- | :---- |
| **Division (**$A/B$**)** | Successive approximation/recursive feedback using multiplication and subtraction primitives. | Requires convergence proof of the feedback loop. | Geometric series and control theory principles. |
| **Square Root (**$\\sqrt{A}$**)** | Iterative methods (e.g., Newton-Raphson) implemented with SC primitives. | Requires proof of convergence of the iterative process. | Standard numerical analysis on functions $f(x) \= x^2 \- A$. |
| **Exponentiation** | Approximated by cascades of multipliers (for powers $x^k$) or specialized circuits (for $e^x$). | Relies on the identity $e^x \= \\sum\_{k=0}^\\infty x^k/k\!$. | Taylor series approximation and implementation of polynomial evaluation. |

## **8\. Lean 4 Formalization Considerations**

### **Probability Space Construction (Question 5\)**

For verifying SC, the probability space $\\Omega$ must be formally defined to contain the bitstreams.

1. **Idealized SC (Infinite Streams):**  
   * **Space:** $\\Omega \= \\{0, 1\\}^\\mathbb{N}$, the space of infinite binary sequences.  
   * **Measure:** The product measure $\\mu$ on $\\Omega$, where each coordinate is a Bernoulli variable. This uses measure theory.  
   * **Mathlib Module:** Mathlib.Probability.Measure.Product, Mathlib.Probability.Independence  
2. **Practical SC (Finite Streams \- Recommended):**  
   * **Space:** $\\Omega \= \\{0, 1\\}^N$, the finite set of length $N$ bitstreams.  
   * **Measure:** The discrete measure. This shifts the focus from "convergence" (SLLN) to **"error bounds"** (Hoeffding).  
   * **Mathlib Module:** Mathlib.Probability.Distributions.Bernoulli, Mathlib.Probability.IdentDistrib, Mathlib.Data.Fintype.Card

### **Data Representation Strategy**

* **Input Values:** Represent $P\_A$ and $P\_B$ as Real numbers in $\[0, 1\]$.  
* **Bitstreams:** Represent finite streams as Fin N → Bool or Vector N Bool.  
* **Operators:** Define the logic gates (\\land, \\lor, \\neg) as functions on the bitstream type.  
* **Measured Value:** The empirical probability $\\hat{P}\_X$ is a function from the bitstream to a Real number.

### **Proof Strategies (Question 6\)**

* **Expected Value Correctness (Ideal):** Use the definition of expected value (measure.integral) and properties of product measures (measure\_theory.measure.prod).  
* **Expected Value Correctness (Finite):** Use combinatorics and finite set cardinality, or the moment calculation theorem for the Bernoulli distribution.  
* **Error Bounds (Finite):**  
  * **Hoeffding/Chernoff:** These are formalized in Mathlib and are the most useful. Search for modules related to hoeffding or chernoff in the Probability namespace. You will need the version of the inequality applicable to sums of bounded random variables.  
  * **Central Limit Theorem:** Mathlib.Probability.Limit.Central exists, but is less useful for proving *guarantees* for a specific, finite $N$.

| Mathlib Component | Utility for SC Formalization |
| :---- | :---- |
| Data.Real.Basic | Representation of numeric values $P\_X \\in \[0, 1\]$. |
| Probability.Distributions.Bernoulli | Definition of the underlying probability distribution for bit generation. |
| Probability.Independence | Formalizing the assumption of independence for multiplication/addition inputs. |
| Probability.Concentration.Hoeffding | **Crucial** for proving practical accuracy bounds (Question 3). |
| FieldTheory.Finite.Basic | Needed for the LFSR mathematical proofs (primitive polynomials over $\\mathbb{F}\_2$). |

### **Alternative Frameworks (Question 7\)**

While **Measure Theory** provides the rigorous foundation for the infinite case (SLLN), the **Algebraic/Computable** framework (focused on $\\mathbb{F}\_2$ for LFSRs and finite probability spaces) is better suited for hardware verification and constructive Lean 4 proofs. Your focus should be on formalizing the **Hoeffding bound** on finite bitstreams, as this directly translates to a quantifiable guarantee for your FPGA system.

### **Known Limitations / Open Problems**

* **Correlation Management:** Generating multiple, truly independent pseudo-random streams on an FPGA is expensive. The correlation between two LFSR outputs (even from different taps) is an open area of practical research, which limits the real-world accuracy guarantee.  
* **Complex Functions:** Proving the convergence and bounds for advanced, iterative functions (like division or square root) is significantly more complex than the basic operations and often requires bounds on function derivatives (Lipschitz continuity) to track error propagation.

**Key Papers to Inform Lean 4 Proofs:**

* **SC Primer:** *Stochastic Computing: A Review* by *Alaghi* and *Hayes* (Modern survey).  
* **Error Analysis:** *Stochastic Computing Systems* by *B. R. Gaines* (Original foundations, 1967).  
* **Concentration:** Any modern text on Probability or Concentration Inequalities for the Hoeffding/Chernoff proofs.  
* **LFSR:** *Shift Register Sequences* by *Solomon Golomb* (Definitive text on $m$-sequences).