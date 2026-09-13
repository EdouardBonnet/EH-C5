import Lax54.GraphDefinitions

/-!
---
title: Quantitative critical-comb consequence
type: lemma
---
This statement combines Lemmas 3.1 and 4.3 with the choice of parameters in
the proof of Theorem 4.4. There are integers $q\geq 3$ and
$A\leq 2^{q-2}$ such that every $q$-critical induced-$C_5$-free graph $G$
contains, either in $G$ or in its complement, a stable hubbed comb with
$t\geq 2$ teeth and
$|V(G)|\leq At^2|B_i|$ for every block $B_i$. The complementary alternative
is required because Lemma 4.3 gives low maximum degree in either $G$ or its
complement; both induced-$C_5$-freeness and $q$-criticality are invariant
under complementation.
-/

open scoped SimpleGraph

namespace Lax54.CriticalCombInput

open Lax54.GraphDefinitions

universe u

/-- The quantitative critical-comb statement used in the proof of Theorem 4.4. -/
axiom exists_critical_comb_parameters :
    ∃ q A : ℕ, 3 ≤ q ∧ A ≤ 2 ^ (q - 2) ∧
      ∀ {V : Type u} [Fintype V] [DecidableEq V] (G : SimpleGraph V),
        IsC5Free G → IsQCritical q G →
          (∃ (t : ℕ) (C : StableHubComb G t),
              2 ≤ t ∧
                ∀ i : Fin t, Fintype.card V ≤ A * t ^ 2 * (C.block i).card) ∨
          (∃ (t : ℕ) (C : StableHubComb Gᶜ t),
              2 ≤ t ∧
                ∀ i : Fin t, Fintype.card V ≤ A * t ^ 2 * (C.block i).card)

end Lax54.CriticalCombInput
