import Mathlib.Combinatorics.SimpleGraph.Circulant
import Mathlib.Combinatorics.SimpleGraph.Clique
import Mathlib.Combinatorics.SimpleGraph.Copy

/-!
---
title: Finite graph notions for the five-cycle Erdős–Hajnal theorem
type: definition
---
This module defines the graph-theoretic notions used in the formalization.
The graph $C_5$ is the cycle on five vertices, and induced-$C_5$-freeness is
expressed using mathlib's induced-containment relation. For a finite graph
$G$, the homogeneous number is
$h(G)=\max\{\alpha(G),\omega(G)\}$ and
$\kappa(G)=\alpha(G)\omega(G)$. The module also defines $q$-critical graphs,
the stable hubbed comb of Lemma 3.1, and the sparse-side and low-degree-side
conclusions used in Rödl's theorem and Lemma 4.3.
-/

open Finset
open scoped SimpleGraph

namespace Lax54.GraphDefinitions

universe u

/-- The five-cycle. -/
abbrev C5 : SimpleGraph (Fin 5) := SimpleGraph.cycleGraph 5

/-- A graph has no induced copy of the five-cycle. -/
def IsC5Free {V : Type u} (G : SimpleGraph V) : Prop :=
  ¬ C5 ⊴ G

/-- The largest cardinality of a clique or stable set in a finite graph. -/
noncomputable def homogeneousNumber {V : Type u} (G : SimpleGraph V) : ℕ :=
  max G.cliqueNum G.indepNum

/-- The product `ω(G) · α(G)` used in the critical-graph argument. -/
noncomputable def kappa {V : Type u} (G : SimpleGraph V) : ℕ :=
  G.cliqueNum * G.indepNum

/--
A graph is `q`-critical if `kappa G ^ q < |V(G)|`, while every proper
vertex-induced subgraph `G[S]` satisfies `|S| ≤ kappa (G[S]) ^ q`.
-/
def IsQCritical {V : Type u} [Fintype V] (q : ℕ) (G : SimpleGraph V) : Prop :=
  kappa G ^ q < Fintype.card V ∧
    ∀ S : Finset V, S.card < Fintype.card V →
      S.card ≤ kappa (G.induce (S : Set V)) ^ q

/--
A comb whose teeth form a stable set, together with the hub vertex from
Lemma 3.1. The hub is adjacent to every tooth and nonadjacent to every block.
The tooth `a_i` is adjacent to its block `B_i` and nonadjacent to every other
block.
-/
structure StableHubComb {V : Type u} [DecidableEq V]
    (G : SimpleGraph V) (t : ℕ) where
  tooth : Fin t → V
  block : Fin t → Finset V
  hub : V
  tooth_injective : Function.Injective tooth
  blocks_disjoint : ∀ {i j : Fin t}, i ≠ j → Disjoint (block i) (block j)
  tooth_not_mem : ∀ i j : Fin t, tooth i ∉ block j
  hub_not_mem : ∀ i : Fin t, hub ∉ block i
  tooth_adj_block : ∀ i : Fin t, ∀ x ∈ block i, G.Adj (tooth i) x
  tooth_nonadj_other : ∀ {i j : Fin t}, i ≠ j →
    ∀ x ∈ block j, ¬ G.Adj (tooth i) x
  teeth_stable : ∀ {i j : Fin t}, i ≠ j → ¬ G.Adj (tooth i) (tooth j)
  hub_adj_tooth : ∀ i : Fin t, G.Adj hub (tooth i)
  hub_nonadj_block : ∀ i : Fin t, ∀ x ∈ block i, ¬ G.Adj hub x

/-- The vertices of `G` all have degree at most `d`. -/
def MaximumDegreeAtMost {V : Type u} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj] (d : ℕ) : Prop :=
  ∀ v : V, G.degree v ≤ d

/--
The low-density alternative in Rödl's theorem. Either the graph or its
complement has edge density at most `1/E`; the definition clears the
denominator.
-/
def HasSparseSide {V : Type u} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj] (E : ℕ) : Prop :=
  E * 2 * G.edgeFinset.card ≤ Fintype.card V * (Fintype.card V - 1) ∨
    E * 2 * Gᶜ.edgeFinset.card ≤ Fintype.card V * (Fintype.card V - 1)

/--
The maximum-degree version of the sparse-side conclusion. The witness `X`
satisfies `|V(G)| ≤ D|X|`; in either `G[X]` or its complement, every degree
`d(x)` satisfies `E d(x) < |X|`.
-/
def HasLowDegreeSide {V : Type u} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj] (E D : ℕ) : Prop :=
  ∃ X : Finset V,
    Fintype.card V ≤ D * X.card ∧
      ((∀ x : {v : V // v ∈ X},
          E * (G.induce (X : Set V)).degree x < X.card) ∨
       (∀ x : {v : V // v ∈ X},
          E * (Gᶜ.induce (X : Set V)).degree x < X.card))

end Lax54.GraphDefinitions
