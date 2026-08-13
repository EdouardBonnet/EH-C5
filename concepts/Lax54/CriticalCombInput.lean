import Lax54.GraphDefinitions

/-!
---
title: Quantitative critical-comb consequence
---
This is the combined quantitative consequence of Rödl's theorem (in the
maximum-degree form 4.3), the key comb lemma 3.1, closure of induced-$C_5$-free
graphs under complementation, and the choice of constants at the start of the
proof of Theorem 4.4.  In reciprocal integer-exponent form it supplies a
stable hubbed comb in every critical counterexample.  The constants are
normalized to natural numbers: every block has size at least
`|G| / (A t²)`, and `q` is chosen large enough that `A ≤ 2^(q-2)`.
-/

open scoped SimpleGraph

namespace Lax54.CriticalCombInput

open Lax54.GraphDefinitions

universe u

/-- The quantitative input obtained from Theorems 3.1 and 4.3 of the paper. -/
axiom exists_critical_comb_parameters :
    ∃ q A : ℕ, 3 ≤ q ∧ A ≤ 2 ^ (q - 2) ∧
      ∀ {V : Type u} [Fintype V] [DecidableEq V] (G : SimpleGraph V),
        IsC5Free G → IsQCritical q G →
          ∃ (t : ℕ) (C : StableHubComb G t),
            2 ≤ t ∧
              ∀ i : Fin t, Fintype.card V ≤ A * t ^ 2 * (C.block i).card

end Lax54.CriticalCombInput
