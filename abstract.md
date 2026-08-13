We formalize the Erdős–Hajnal theorem for the five-cycle, following
Chudnovsky, Scott, Seymour, and Spirkl, *Erdős–Hajnal for graphs with no
5-hole* (2021).  The conclusion is stated in the equivalent
integer-exponent form: there is a positive integer $q$ such that every finite
induced-$C_5$-free graph $G$ satisfies

$$|V(G)| \leq \max(\alpha(G),\omega(G))^q.$$

The Lean development isolates the quantitative consequence of Rödl's theorem
and the paper's key comb lemma, and formalizes the remainder of the proof:
minimal-counterexample induction, the induced-$C_5$ obstruction between two
comb blocks, the independent-set aggregation across anticomplete blocks, and
the final power inequality.
