import Mathlib.Combinatorics.SimpleGraph.Circulant
import Mathlib.Combinatorics.SimpleGraph.Clique
import Mathlib.Combinatorics.SimpleGraph.Copy

/-!
---
title: Finite graph notions for the five-cycle Erdős–Hajnal theorem
---
The graph-theoretic definitions used in the formalization.  An induced
five-cycle is represented by mathlib's induced-containment relation from the
cycle graph on five vertices.  The homogeneous number is the larger of the
independence and clique numbers, and `kappa` is their product.  A `q`-critical
graph violates the product bound at exponent `q`, while every proper induced
subgraph satisfies it.  The stable hubbed comb is the configuration delivered
by the key lemma in Section 3 of the paper.
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

/-- The maximum of the clique and independence numbers of a finite graph. -/
noncomputable def homogeneousNumber {V : Type u} (G : SimpleGraph V) : ℕ :=
  max G.cliqueNum G.indepNum

/-- The product `ω(G) · α(G)` used throughout the paper. -/
noncomputable def kappa {V : Type u} (G : SimpleGraph V) : ℕ :=
  G.cliqueNum * G.indepNum

/--
The integer-exponent version of `τ`-criticality.  The inequality
`kappa G ^ q < |G|` is the same obstruction as
`kappa G < |G|^(1/q)`; every proper vertex-induced subgraph obeys the desired
bound.
-/
def IsQCritical {V : Type u} [Fintype V] (q : ℕ) (G : SimpleGraph V) : Prop :=
  kappa G ^ q < Fintype.card V ∧
    ∀ S : Finset V, S.card < Fintype.card V →
      S.card ≤ kappa (G.induce (S : Set V)) ^ q

/--
A comb whose teeth form a stable set and which has the additional hub vertex
from Lemma 3.1.  `block i` is the set denoted `B_i` in the paper and `tooth i`
is `a_i`.
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

end Lax54.GraphDefinitions
