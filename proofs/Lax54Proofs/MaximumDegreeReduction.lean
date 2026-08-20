import Lax54.AveragingLemma
import Lax54.MaximumDegreeReduction
import Lax54Proofs.AveragingLemma
import Lax54Proofs.RodlTheorem
import Mathlib.Tactic

namespace Lax54Proofs

open Finset
open scoped SimpleGraph
open Lax54.GraphDefinitions

universe u v

/-- Taking an induced subgraph commutes with graph complementation. -/
theorem compl_induce_eq_induce_compl
    {V : Type u} (G : SimpleGraph V) (S : Set V) :
    (G.induce S)ᶜ = Gᶜ.induce S := by
  ext x y
  simp [SimpleGraph.compl_adj, Subtype.ext_iff]

/--
---
conclusion: Lax54.MaximumDegreeReduction.maximum_degree_reduction
---
Proof of Lemma 4.3. Apply Rödl's theorem with density parameter $4E$, then
apply Lemma 4.2 with $m=\lceil |Z|/2\rceil$. The resulting set loses at most
a factor of two in size and satisfies the required degree bound.
-/
theorem maximum_degree_reduction :
    ∀ {W : Type u} [Fintype W] (H : SimpleGraph W) (E : ℕ),
      0 < E → ∃ D : ℕ, 0 < D ∧
        ∀ {V : Type v} [Fintype V] [DecidableEq V] (G : SimpleGraph V)
          [DecidableRel G.Adj],
          ¬ H ⊴ G → HasLowDegreeSide G E D := by
  intro W _ H E hE
  obtain ⟨D₀, hD₀, hrodl⟩ :=
    Lax54Proofs.RodlTheorem.rodl_theorem H (4 * E) (by positivity)
  refine ⟨2 * D₀, by positivity, ?_⟩
  intro V _ _ G _ hfree
  by_cases hV : Fintype.card V = 0
  · refine ⟨∅, by simp [hV], Or.inl ?_⟩
    intro x
    exact (Finset.notMem_empty x.1 x.2).elim
  obtain ⟨Z, hlarge, hsparse⟩ := hrodl G hfree
  have hZpos : 0 < Z.card := by
    by_contra hz
    have hz0 : Z.card = 0 := by omega
    simp [hz0] at hlarge
    exact hV hlarge
  let m := (Z.card + 1) / 2
  have hmpos : 0 < m := by
    dsimp [m]
    omega
  have hmsize : 2 * m ≤ Z.card + 1 := by
    dsimp [m]
    omega
  have hZle : Z.card ≤ 2 * m := by
    dsimp [m]
    omega
  have horder (X : Finset V) (hXcard : X.card = m) :
      Fintype.card V ≤ (2 * D₀) * X.card := by
    calc
      Fintype.card V ≤ D₀ * Z.card := hlarge
      _ ≤ D₀ * (2 * m) := Nat.mul_le_mul_left D₀ hZle
      _ = (2 * D₀) * X.card := by rw [hXcard]; ring
  rcases hsparse with hsparse | hsparse
  · have hsparse' : (4 * E) * 2 * (G.induce (Z : Set V)).edgeFinset.card ≤
        Z.card * (Z.card - 1) := by
      simpa [← Set.toFinset_card] using hsparse
    obtain ⟨X, hXZ, hXcard, hdegree⟩ :=
      Lax54Proofs.sparse_graph_thinning G Z (4 * E) m
        (by positivity) hmsize hsparse'
    refine ⟨X, horder X hXcard, Or.inl ?_⟩
    intro x
    have hx := hdegree x
    have hx' : 4 * (E * (G.induce (X : Set V)).degree x) ≤
        4 * (m - 1) := by
      simpa [mul_assoc] using hx
    have hle : E * (G.induce (X : Set V)).degree x ≤ m - 1 := by
      omega
    rw [hXcard]
    omega
  · have hsparse' : (4 * E) * 2 * ((G.induce (Z : Set V))ᶜ).edgeFinset.card ≤
        Z.card * (Z.card - 1) := by
      simpa [← Set.toFinset_card] using hsparse
    have hedgeFinset : ((G.induce (Z : Set V))ᶜ).edgeFinset =
        (Gᶜ.induce (Z : Set V)).edgeFinset := by
      ext e
      simp only [SimpleGraph.mem_edgeFinset]
      rw [compl_induce_eq_induce_compl]
    rw [hedgeFinset] at hsparse'
    obtain ⟨X, hXZ, hXcard, hdegree⟩ :=
      Lax54Proofs.sparse_graph_thinning Gᶜ Z (4 * E) m
        (by positivity) hmsize hsparse'
    refine ⟨X, horder X hXcard, Or.inr ?_⟩
    intro x
    have hx := hdegree x
    have hx' : 4 * (E * (Gᶜ.induce (X : Set V)).degree x) ≤
        4 * (m - 1) := by
      simpa [mul_assoc] using hx
    have hle : E * (Gᶜ.induce (X : Set V)).degree x ≤ m - 1 := by
      omega
    rw [hXcard]
    omega

end Lax54Proofs
