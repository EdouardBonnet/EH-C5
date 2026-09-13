This submission formalizes the proof of Chudnovsky, Scott, Seymour, and
Spirkl that the five-cycle has the Erdős–Hajnal property. Its [main theorem](https://laxarchive.org/lax-54/paper.html#m14)
states that there is a positive integer $q$ such that every finite graph $G$
with no induced $C_5$ satisfies

$$|V(G)| \leq \max(\alpha(G),\omega(G))^q.$$

Equivalently, every such graph contains a clique or stable set of order at
least $|V(G)|^{1/q}$.

The submission formalizes every argument in the paper required for this
conclusion. It also derives the form of [Rödl's theorem](https://laxarchive.org/lax-54/paper.html#m9) used there from
mathlib's formalization of Szemerédi's regularity lemma, a finite Ramsey
argument, and an induced-embedding lemma. The formalized arguments include the
$d=1/2$ case of the bipartite comb lemma ([Theorem 2.1](https://laxarchive.org/lax-54/paper.html#m4)), the critical-graph comb
lemma ([Lemma 3.1](https://laxarchive.org/lax-54/paper.html#m7)), the averaging and maximum-degree reductions ([Lemma 4.2](https://laxarchive.org/lax-54/paper.html#m10) and
[Lemma 4.3](https://laxarchive.org/lax-54/paper.html#m12)), and the final minimal-counterexample argument ([Theorem 4.4](https://laxarchive.org/lax-54/paper.html#m14)). The Lean
statements parameterize densities by reciprocals of positive integers and
clear all denominators. Some absolute constants are enlarged to avoid
rounding; neither modification affects the Erdős–Hajnal conclusion.

The annotated paper covers the five-cycle argument in Sections 2–4 and its
introductory statement. The later results about other excluded graphs are
outside this submission’s scope. Annotation links use the integral versions
described in the concept cards.
