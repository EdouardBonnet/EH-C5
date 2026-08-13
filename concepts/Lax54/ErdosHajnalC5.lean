import Lax54.GraphDefinitions

/-!
---
title: Erdős–Hajnal theorem for the five-cycle
type: theorem
---
There is a positive integer `q` such that every finite graph with no induced
five-cycle has a clique or stable set of size polynomial in its number of
vertices, in the equivalent integer-exponent form
`|V(G)| ≤ max(α(G), ω(G))^q`.
-/

namespace Lax54.ErdosHajnalC5

open Lax54.GraphDefinitions

universe u

/-- The Erdős–Hajnal conjecture holds for `C₅`. -/
axiom erdos_hajnal_C5 :
    ∃ q : ℕ, 0 < q ∧
      ∀ {V : Type u} [Fintype V] (G : SimpleGraph V),
        IsC5Free G → Fintype.card V ≤ homogeneousNumber G ^ q

end Lax54.ErdosHajnalC5
