import Lax54.GraphDefinitions
import Mathlib.Tactic

namespace Lax54Proofs

open scoped SimpleGraph Matrix
open Lax54.GraphDefinitions

universe u

/-- Taking an induced subgraph commutes with graph complementation. -/
theorem compl_induce_eq_induce_compl
    {V : Type u} (G : SimpleGraph V) (S : Set V) :
    (G.induce S)ᶜ = Gᶜ.induce S := by
  ext x y
  simp [SimpleGraph.compl_adj, Subtype.ext_iff]

/-- The permutation of `Fin 5` given by multiplication by two modulo five. -/
def c5ComplementEquiv : Fin 5 ≃ Fin 5 where
  toFun := ![0, 2, 4, 1, 3]
  invFun := ![0, 3, 1, 4, 2]
  left_inv i := by fin_cases i <;> rfl
  right_inv i := by fin_cases i <;> rfl

/-- The five-cycle is self-complementary. -/
def c5ComplementIso : C5 ≃g C5ᶜ where
  toEquiv := c5ComplementEquiv
  map_rel_iff' := by
    intro i j
    fin_cases i <;> fin_cases j <;>
      decide

/-- Induced-`C₅`-freeness is invariant under graph complementation. -/
theorem IsC5Free.compl {V : Type u} {G : SimpleGraph V}
    (hfree : IsC5Free G) : IsC5Free Gᶜ := by
  intro hcopy
  apply hfree
  have hc : C5ᶜ ⊴ G := by
    simpa using hcopy.compl
  exact c5ComplementIso.isIndContained.trans hc

/-- The product `κ = ωα` is invariant under complementation. -/
@[simp] theorem kappa_compl {V : Type u} (G : SimpleGraph V) :
    kappa Gᶜ = kappa G := by
  simp [kappa, mul_comm]

/-- `q`-criticality is invariant under graph complementation. -/
theorem IsQCritical.compl {V : Type u} [Fintype V]
    {G : SimpleGraph V} {q : ℕ} (hcritical : IsQCritical q G) :
    IsQCritical q Gᶜ := by
  constructor
  · simpa using hcritical.1
  · intro S hS
    have h := hcritical.2 S hS
    simpa [← compl_induce_eq_induce_compl] using h

end Lax54Proofs
