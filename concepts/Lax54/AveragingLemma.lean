import Lax54.GraphDefinitions

/-!
---
title: Sparse graph thinning lemma
type: lemma
---
Lemma 4.2 of the paper, with denominators cleared. Let $Z$ induce a graph of
edge density at most $1/E$, and suppose $2m \leq |Z|+1$. Then $Z$ contains an
$m$-element set $X$ such that
$E\deg_{G[X]}(x) \leq 4(m-1)$ for every $x\in X$. The factor $4$ results from
first selecting $2m-1$ vertices by averaging and then retaining $m$ vertices
of low degree.
-/

namespace Lax54.AveragingLemma

open Lax54.GraphDefinitions

universe u

/-- Lemma 4.2, with all inequalities written over the natural numbers. -/
axiom sparse_graph_thinning :
    ∀ {V : Type u} [Fintype V] [DecidableEq V] (G : SimpleGraph V)
      [DecidableRel G.Adj] (Z : Finset V) (E m : ℕ),
      0 < E → 2 * m ≤ Z.card + 1 →
      E * 2 * (G.induce (Z : Set V)).edgeFinset.card ≤
        Z.card * (Z.card - 1) →
      ∃ X : Finset V, X ⊆ Z ∧ X.card = m ∧
        ∀ x : {v : V // v ∈ X},
          E * (G.induce (X : Set V)).degree x ≤ 4 * (m - 1)

end Lax54.AveragingLemma
