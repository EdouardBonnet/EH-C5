This submission formalizes the proof of Chudnovsky, Scott, Seymour, and
Spirkl that the five-cycle has the Erdős–Hajnal property. Its main theorem
states that there is a positive integer $q$ such that every finite graph $G$
with no induced $C_5$ satisfies

$$|V(G)| \leq \max(\alpha(G),\omega(G))^q.$$

Equivalently, every such graph contains a clique or stable set of order at
least $|V(G)|^{1/q}$.

The submission formalizes every argument in the paper required for this
conclusion. It also derives the form of Rödl's theorem used there from
mathlib's formalization of Szemerédi's regularity lemma, a finite Ramsey
argument, and an induced-embedding lemma. The formalized arguments include the
$d=1/2$ case of the bipartite comb lemma (Theorem 2.1), the critical-graph comb
lemma (Lemma 3.1), the averaging and maximum-degree reductions (Lemmas 4.2 and
4.3), and the final minimal-counterexample argument (Theorem 4.4). The Lean
statements parameterize densities by reciprocals of positive integers and
clear all denominators. Some absolute constants are enlarged to avoid
rounding; neither modification affects the Erdős–Hajnal conclusion.

The annotated paper covers the five-cycle argument in Sections 2–4 and its
introductory statement. The later results about other excluded graphs are
outside this submission’s scope. Annotation links use the integral versions
described in the concept cards.
