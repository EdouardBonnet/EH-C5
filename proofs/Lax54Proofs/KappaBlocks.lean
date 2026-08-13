import Lax54.GraphDefinitions
import Mathlib.Tactic

namespace Lax54Proofs

open Finset
open scoped BigOperators SimpleGraph
open Lax54.GraphDefinitions

universe u

/-- Taking a vertex-induced subgraph cannot increase the clique number. -/
theorem cliqueNum_induce_finset_le
    {V : Type u} [Fintype V] [DecidableEq V] (G : SimpleGraph V) (B : Finset V) :
    (G.induce (B : Set V)).cliqueNum ≤ G.cliqueNum := by
  classical
  obtain ⟨K, hK⟩ := (G.induce (B : Set V)).exists_isNClique_cliqueNum
  let e : {x : V // x ∈ B} ↪ V := ⟨Subtype.val, Subtype.val_injective⟩
  let K' : Finset V := K.map e
  have hK'_clique : G.IsClique (K' : Set V) := by
    intro x hx y hy hxy
    change x ∈ K' at hx
    change y ∈ K' at hy
    obtain ⟨x', hx', rfl⟩ := Finset.mem_map.mp hx
    obtain ⟨y', hy', rfl⟩ := Finset.mem_map.mp hy
    exact hK.isClique hx' hy' (by simpa [e] using hxy)
  calc
    (G.induce (B : Set V)).cliqueNum = K.card := hK.card_eq.symm
    _ = K'.card := by simp [K']
    _ ≤ G.cliqueNum := hK'_clique.card_le_cliqueNum

/--
Independent sets chosen inside pairwise anticomplete blocks can be united; in
particular, the sum of the blocks' independence numbers is at most that of the
ambient graph.
-/
theorem sum_indepNum_induce_le
    {V : Type u} [Fintype V] [DecidableEq V] {G : SimpleGraph V}
    {t : ℕ} (B : Fin t → Finset V)
    (hdisj : ∀ {i j : Fin t}, i ≠ j → Disjoint (B i) (B j))
    (hanti : ∀ {i j : Fin t}, i ≠ j →
      ∀ x ∈ B i, ∀ y ∈ B j, ¬ G.Adj x y) :
    ∑ i : Fin t, (G.induce (B i : Set V)).indepNum ≤ G.indepNum := by
  classical
  let I (i : Fin t) : Finset {x : V // x ∈ B i} :=
    Classical.choose (G.induce (B i : Set V)).exists_isNIndepSet_indepNum
  have hI (i : Fin t) :
      (G.induce (B i : Set V)).IsNIndepSet
        (G.induce (B i : Set V)).indepNum (I i) :=
    Classical.choose_spec (G.induce (B i : Set V)).exists_isNIndepSet_indepNum
  let e (i : Fin t) : {x : V // x ∈ B i} ↪ V :=
    ⟨Subtype.val, Subtype.val_injective⟩
  let J (i : Fin t) : Finset V := (I i).map (e i)
  have hJ_subset (i : Fin t) : J i ⊆ B i := by
    intro x hx
    obtain ⟨x', -, rfl⟩ := Finset.mem_map.mp hx
    exact x'.property
  have hJ_indep (i : Fin t) : G.IsIndepSet (J i : Set V) := by
    intro x hx y hy hxy
    change x ∈ J i at hx
    change y ∈ J i at hy
    obtain ⟨x', hx', rfl⟩ := Finset.mem_map.mp hx
    obtain ⟨y', hy', rfl⟩ := Finset.mem_map.mp hy
    exact (hI i).isIndepSet hx' hy' (by simpa [e] using hxy)
  have hJ_disj :
      Set.PairwiseDisjoint (↑(Finset.univ : Finset (Fin t)) : Set (Fin t)) J := by
    intro i _ j _ hij
    exact (hdisj hij).mono (hJ_subset i) (hJ_subset j)
  let U : Finset V := Finset.univ.biUnion J
  have hU_indep : G.IsIndepSet (U : Set V) := by
    intro x hx y hy hxy
    change x ∈ U at hx
    change y ∈ U at hy
    obtain ⟨i, -, hxi⟩ := Finset.mem_biUnion.mp hx
    obtain ⟨j, -, hyj⟩ := Finset.mem_biUnion.mp hy
    by_cases hij : i = j
    · subst j
      exact hJ_indep i hxi hyj hxy
    · exact hanti hij x (hJ_subset i hxi) y (hJ_subset j hyj)
  have hJ_card (i : Fin t) :
      (J i).card = (G.induce (B i : Set V)).indepNum := by
    simpa [J] using (hI i).card_eq
  calc
    ∑ i : Fin t, (G.induce (B i : Set V)).indepNum =
        ∑ i : Fin t, (J i).card := by simp_rw [hJ_card]
    _ = U.card := by
      symm
      simpa [U] using Finset.card_biUnion hJ_disj
    _ ≤ G.indepNum := hU_indep.card_le_indepNum

/-- The sum of `κ` over pairwise anticomplete induced blocks is at most `κ(G)`. -/
theorem sum_kappa_induce_le
    {V : Type u} [Fintype V] [DecidableEq V] {G : SimpleGraph V}
    {t : ℕ} (B : Fin t → Finset V)
    (hdisj : ∀ {i j : Fin t}, i ≠ j → Disjoint (B i) (B j))
    (hanti : ∀ {i j : Fin t}, i ≠ j →
      ∀ x ∈ B i, ∀ y ∈ B j, ¬ G.Adj x y) :
    ∑ i : Fin t, kappa (G.induce (B i : Set V)) ≤ kappa G := by
  classical
  calc
    ∑ i : Fin t, kappa (G.induce (B i : Set V)) =
        ∑ i : Fin t, (G.induce (B i : Set V)).cliqueNum *
          (G.induce (B i : Set V)).indepNum := by rfl
    _ ≤ ∑ i : Fin t, G.cliqueNum *
          (G.induce (B i : Set V)).indepNum := by
      exact Finset.sum_le_sum fun i _ ↦
        Nat.mul_le_mul_right _ (cliqueNum_induce_finset_le G (B i))
    _ = G.cliqueNum * ∑ i : Fin t, (G.induce (B i : Set V)).indepNum := by
      rw [Finset.mul_sum]
    _ ≤ G.cliqueNum * G.indepNum :=
      Nat.mul_le_mul_left _ (sum_indepNum_induce_le B hdisj hanti)
    _ = kappa G := rfl

end Lax54Proofs
