import Mathlib.Combinatorics.SimpleGraph.Copy
import Lax54.GraphDefinitions

/-!
---
title: Maximum-degree form of Rödl's theorem
type: lemma
---
Lemma 4.3 of the paper, with denominators cleared. For every finite graph $H$
and every $E>0$, there is a positive integer $D$ such that every finite
induced-$H$-free graph $G$ contains a set $X$ satisfying
$|V(G)|\leq D|X|$ and, either in $G[X]$ or in its complement,
$E\deg(x)<|X|$ for every $x\in X$.
-/

namespace Lax54.MaximumDegreeReduction

open Lax54.GraphDefinitions
open scoped SimpleGraph

universe u v

/-- The maximum-degree form of Rödl's theorem used in Section 4. -/
axiom maximum_degree_reduction :
    ∀ {W : Type u} [Fintype W] (H : SimpleGraph W) (E : ℕ),
      0 < E → ∃ D : ℕ, 0 < D ∧
        ∀ {V : Type v} [Fintype V] [DecidableEq V] (G : SimpleGraph V)
          [DecidableRel G.Adj],
          ¬ H ⊴ G → HasLowDegreeSide G E D

end Lax54.MaximumDegreeReduction
