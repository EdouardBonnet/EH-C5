import Lax54.GraphDefinitions

/-!
---
title: Erdős–Hajnal theorem for the five-cycle
type: theorem
---
The five-cycle has the Erdős–Hajnal property. Equivalently, there is a
positive integer $q$ such that every finite graph $G$ with no induced
five-cycle satisfies
$|V(G)|\leq \max\{\alpha(G),\omega(G)\}^q$.
-/

namespace Lax54.ErdosHajnalC5

open Lax54.GraphDefinitions

universe u

/-- The Erdős–Hajnal property for the five-cycle, in integer-exponent form. -/
axiom erdos_hajnal_C5 :
    ∃ q : ℕ, 0 < q ∧
      ∀ {V : Type u} [Fintype V] (G : SimpleGraph V),
        IsC5Free G → Fintype.card V ≤ homogeneousNumber G ^ q

end Lax54.ErdosHajnalC5
