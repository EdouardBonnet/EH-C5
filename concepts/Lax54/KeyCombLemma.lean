import Lax54.GraphDefinitions

/-!
---
title: Stable hubbed comb in a critical graph
type: lemma
---
Lemma 3.1 of the paper, with reciprocal integer parameters. Let
$K=2^{20}$. For every sufficiently large $E$, every $D>0$, and every lower
bound $Q$, there is an exponent $q\geq\max\{3,Q\}$ with the following
property. If $G$ is $q$-critical, $|V(G)|\leq D|X|$, and
$E\deg_{G[X]}(x)<|X|$ for every $x\in X$, then $G$ contains a stable hubbed
comb such that $E\leq Kt$ and
$E|X|\leq Kt^2|B_i|$ for every block $B_i$.

The absolute constant $K$ replaces the constant $400$ in the paper to
accommodate the integral form of Theorem 2.1. Its value does not affect the
Erdős–Hajnal conclusion.
-/

namespace Lax54.KeyCombLemma

open Lax54.GraphDefinitions

universe u

/-- The absolute constant in the integral form of the key comb lemma. -/
def keyCombConstant : ℕ := 2 ^ 20

/-- A sufficient lower bound on the sparsity parameter for obtaining at least two teeth. -/
def keySparsityThreshold : ℕ := 2 * keyCombConstant

/-- Lemma 3.1, with reciprocal integer parameters and cleared denominators. -/
axiom key_comb_lemma :
    ∀ E D Q : ℕ, keySparsityThreshold ≤ E → 0 < D →
      ∃ q : ℕ, 3 ≤ q ∧ Q ≤ q ∧
        ∀ {V : Type u} [Fintype V] [DecidableEq V]
          (G : SimpleGraph V) [DecidableRel G.Adj] (X : Finset V),
          IsQCritical q G →
          Fintype.card V ≤ D * X.card →
          (∀ x : {v : V // v ∈ X},
            E * (G.induce (X : Set V)).degree x < X.card) →
          ∃ (t : ℕ) (C : StableHubComb G t),
            E ≤ keyCombConstant * t ∧
              ∀ i : Fin t,
                E * X.card ≤ keyCombConstant * t ^ 2 * (C.block i).card

end Lax54.KeyCombLemma
