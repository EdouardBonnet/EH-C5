import Lax54.GraphDefinitions
import Mathlib.Tactic

namespace Lax54Proofs

open Finset
open scoped SimpleGraph Matrix
open Lax54.GraphDefinitions

universe u

/-- Distinct blocks of a stable hubbed comb in a `C₅`-free graph are anticomplete. -/
theorem StableHubComb.blocks_anticomplete_of_c5Free
    {V : Type u} [Fintype V] [DecidableEq V] {G : SimpleGraph V}
    {t : ℕ} (C : StableHubComb G t) (hfree : IsC5Free G) :
    ∀ {i j : Fin t}, i ≠ j →
      ∀ x ∈ C.block i, ∀ y ∈ C.block j, ¬ G.Adj x y := by
  intro i j hij x hx y hy hxy
  apply hfree
  have hxy_ne : x ≠ y := by
    intro h
    subst y
    exact (Finset.disjoint_left.mp (C.blocks_disjoint hij)) hx hy
  have hx_tj : x ≠ C.tooth j := by
    intro h
    exact C.tooth_not_mem j i (h ▸ hx)
  have hx_hub : x ≠ C.hub := by
    intro h
    exact C.hub_not_mem i (h ▸ hx)
  have hx_ti : x ≠ C.tooth i := by
    intro h
    exact C.tooth_not_mem i i (h ▸ hx)
  have hy_tj : y ≠ C.tooth j := by
    intro h
    exact C.tooth_not_mem j j (h ▸ hy)
  have hy_hub : y ≠ C.hub := by
    intro h
    exact C.hub_not_mem j (h ▸ hy)
  have hy_ti : y ≠ C.tooth i := by
    intro h
    exact C.tooth_not_mem i j (h ▸ hy)
  have htj_hub : C.tooth j ≠ C.hub := by
    intro h
    exact G.loopless.irrefl _ (h ▸ C.hub_adj_tooth j)
  have htj_ti : C.tooth j ≠ C.tooth i :=
    C.tooth_injective.ne hij.symm
  have hhub_ti : C.hub ≠ C.tooth i := by
    intro h
    exact G.loopless.irrefl _ (h ▸ C.hub_adj_tooth i)
  have hy_tj_adj : G.Adj y (C.tooth j) :=
    (C.tooth_adj_block j y hy).symm
  have htj_hub_adj : G.Adj (C.tooth j) C.hub :=
    (C.hub_adj_tooth j).symm
  have hhub_ti_adj : G.Adj C.hub (C.tooth i) :=
    C.hub_adj_tooth i
  have hti_x_adj : G.Adj (C.tooth i) x :=
    C.tooth_adj_block i x hx
  have hx_tj_nonadj : ¬ G.Adj x (C.tooth j) := by
    simpa [G.adj_comm] using C.tooth_nonadj_other hij.symm x hx
  have hx_hub_nonadj : ¬ G.Adj x C.hub := by
    simpa [G.adj_comm] using C.hub_nonadj_block i x hx
  have hy_hub_nonadj : ¬ G.Adj y C.hub := by
    simpa [G.adj_comm] using C.hub_nonadj_block j y hy
  have hy_ti_nonadj : ¬ G.Adj y (C.tooth i) := by
    simpa [G.adj_comm] using C.tooth_nonadj_other hij y hy
  have htj_ti_nonadj : ¬ G.Adj (C.tooth j) (C.tooth i) :=
    C.teeth_stable hij.symm
  let f : Fin 5 → V := ![x, y, C.tooth j, C.hub, C.tooth i]
  refine ⟨{
    toFun := f
    inj' := ?_
    map_rel_iff' := ?_
  }⟩
  · intro a b hab
    fin_cases a <;> fin_cases b <;>
      simp_all [f, Matrix.cons_val_zero, Matrix.cons_val_one]
  · intro a b
    change G.Adj (f a) (f b) ↔ _
    fin_cases a <;> fin_cases b <;>
      simp_all [f, SimpleGraph.cycleGraph_adj, Fin.ext_iff, G.adj_comm] <;>
      decide

end Lax54Proofs
