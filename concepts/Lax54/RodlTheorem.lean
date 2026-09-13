import Lax54.GraphDefinitions

/-!
---
title: Rödl's theorem for induced-subgraph-free graphs
type: lemma
---
For every finite graph $H$ and every positive integer $E$, there is a positive
integer $D$ such that every finite induced-$H$-free graph $G$ contains a set
$X$ satisfying $|V(G)|\leq D|X|$ and such that either $G[X]$ or its complement
has edge density at most $1/E$. This is the cleared-denominator finite form of
Rödl's theorem cited as Theorem 4.1 in the paper.
-/

open scoped SimpleGraph

namespace Lax54.RodlTheorem

open Lax54.GraphDefinitions

universe u v

/-- Rödl's theorem, with a reciprocal integer density parameter. -/
axiom rodl_theorem :
    ∀ {W : Type u} [Fintype W] (H : SimpleGraph W) (E : ℕ),
      0 < E → ∃ D : ℕ, 0 < D ∧
        ∀ {V : Type v} [Fintype V] [DecidableEq V] (G : SimpleGraph V)
          [DecidableRel G.Adj],
          ¬ H ⊴ G →
            ∃ X : Finset V, Fintype.card V ≤ D * X.card ∧
              HasSparseSide (G.induce (X : Set V)) E

end Lax54.RodlTheorem
