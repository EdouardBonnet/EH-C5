import Lax18.SzemerediRegularityLemma
import Mathlib.Combinatorics.SimpleGraph.Regularity.Lemma
import Mathlib.Tactic

/-!
# Adapter for the [lax-18](https://laxarchive.org/lax-18/) regularity lemma

[lax-18](https://laxarchive.org/lax-18/) states Szemerédi's regularity lemma using indexed vertex partitions
and non-strict regular pairs.  The Rödl argument in this submission uses
mathlib's unlabelled finite partitions and strict uniform pairs.  This file
relates the two formulations.  Passing from parameter `ε` to any larger
parameter `η` accounts for the difference between `≤ ε` and `< η`.
-/

open Finset Fintype
open scoped SimpleGraph

namespace Lax54Proofs.RegularityAdapter

open Lax18.FiniteGraphPartitions
open Lax18.RegularPairs
open Lax18.RegularPartitions

universe u

variable {V : Type u} [Fintype V] [DecidableEq V]

/-- Distinct indices of a vertex partition name distinct parts. -/
lemma part_injective (P : VertexPartition V) : Function.Injective P.part := by
  intro i j hij
  by_contra hne
  obtain ⟨v, hv⟩ := P.nonempty_part i
  have hdis := P.pairwise_disjoint i j hne
  exact (Finset.disjoint_left.1 hdis hv) (hij ▸ hv)

/-- Regard an indexed vertex partition as a mathlib `Finpartition`. -/
noncomputable def finpartitionOfVertexPartition (P : VertexPartition V) :
    Finpartition (Finset.univ : Finset V) := by
  classical
  refine Finpartition.ofExistsUnique
    (Finset.univ.image P.part) (fun _ _ => Finset.subset_univ _) ?_ ?_
  · intro v _
    obtain ⟨i, hvi⟩ := P.covers v
    refine ⟨P.part i, ⟨Finset.mem_image.2 ⟨i, Finset.mem_univ _, rfl⟩, hvi⟩, ?_⟩
    intro A hA
    obtain ⟨j, -, rfl⟩ := Finset.mem_image.1 hA.1
    apply congrArg P.part
    by_contra hji
    exact (Finset.disjoint_left.1 (P.pairwise_disjoint j i hji) hA.2) hvi
  · intro hempty
    obtain ⟨i, -, hi⟩ := Finset.mem_image.1 hempty
    exact (P.nonempty_part i).ne_empty hi

@[simp]
lemma finpartitionOfVertexPartition_parts (P : VertexPartition V) :
    (finpartitionOfVertexPartition P).parts = Finset.univ.image P.part :=
  rfl

@[simp]
lemma card_finpartitionOfVertexPartition_parts (P : VertexPartition V) :
    (finpartitionOfVertexPartition P).parts.card = P.partCount := by
  classical
  simp [finpartitionOfVertexPartition, Finset.card_image_of_injective _ (part_injective P)]

/-- Equitability is unchanged when the indexing of the parts is forgotten. -/
lemma isEquipartition_finpartitionOfVertexPartition
    (P : VertexPartition V) (hP : P.Equitable) :
    (finpartitionOfVertexPartition P).IsEquipartition := by
  classical
  intro A B hA hB
  rw [finpartitionOfVertexPartition_parts] at hA hB
  obtain ⟨i, -, rfl⟩ := Finset.mem_image.1 hA
  obtain ⟨j, -, rfl⟩ := Finset.mem_image.1 hB
  exact (hP j i).2

/-- [lax-18](https://laxarchive.org/lax-18/)'s real-valued density agrees with mathlib's edge density. -/
lemma density_eq_mathlib_edgeDensity
    (G : SimpleGraph V) [DecidableRel G.Adj] (A B : Finset V) :
    Lax18.EdgeDensity.density G A B = (G.edgeDensity A B : ℝ) := by
  classical
  by_cases hA : A.card = 0
  · have : A = ∅ := Finset.card_eq_zero.mp hA
    subst A
    simp [Lax18.EdgeDensity.density]
  by_cases hB : B.card = 0
  · have : B = ∅ := Finset.card_eq_zero.mp hB
    subst B
    simp [Lax18.EdgeDensity.density]
  simp only [Lax18.EdgeDensity.density, hA, hB, false_or, if_false,
    SimpleGraph.edgeDensity_def, Rat.cast_div, Rat.cast_natCast, Rat.cast_mul]
  congr 1
  norm_cast
  apply congrArg Finset.card
  ext p
  simp [SimpleGraph.interedges, Rel.interedges]

/-- A non-strict [lax-18](https://laxarchive.org/lax-18/) regular pair is a strict mathlib-uniform pair at any
larger parameter. -/
lemma isUniform_of_isRegularPair
    (G : SimpleGraph V) [DecidableRel G.Adj]
    {epsilon eta : ℝ} (hεη : epsilon < eta) (A B : Finset V)
    (h : IsRegularPair G epsilon A B) :
    G.IsUniform eta A B := by
  intro X hXA Y hYB hX hY
  rw [← density_eq_mathlib_edgeDensity, ← density_eq_mathlib_edgeDensity]
  refine (h.2.2 X Y ⟨hXA, ?_⟩ ⟨hYB, ?_⟩).trans_lt hεη
  · calc
      epsilon * (A.card : ℝ) ≤ eta * (A.card : ℝ) := by gcongr
      _ ≤ (X.card : ℝ) := by simpa [mul_comm] using hX
  · calc
      epsilon * (B.card : ℝ) ≤ eta * (B.card : ℝ) := by gcongr
      _ ≤ (Y.card : ℝ) := by simpa [mul_comm] using hY

/-- Ordered pairs of distinct indices whose parts are not `eta`-uniform. -/
noncomputable def orderedNonUniformIndices
    (G : SimpleGraph V) [DecidableRel G.Adj] (eta : ℝ)
    (P : VertexPartition V) :
    Finset (Fin P.partCount × Fin P.partCount) := by
  classical
  exact (Finset.univ.product Finset.univ).filter fun p =>
    p.1 ≠ p.2 ∧ ¬ G.IsUniform eta (P.part p.1) (P.part p.2)

/-- Send a pair of part indices to the corresponding pair of parts. -/
noncomputable def partPairEmbedding (P : VertexPartition V) :
    (Fin P.partCount × Fin P.partCount) ↪ (Finset V × Finset V) where
  toFun p := (P.part p.1, P.part p.2)
  inj' p q h := by
    apply Prod.ext
    · exact part_injective P (congrArg Prod.fst h)
    · exact part_injective P (congrArg Prod.snd h)

/-- The ordered nonuniform pairs of the unlabelled partition are exactly the
images of the ordered nonuniform index pairs. -/
lemma map_orderedNonUniformIndices
    (G : SimpleGraph V) [DecidableRel G.Adj] (eta : ℝ)
    (P : VertexPartition V) :
    (orderedNonUniformIndices G eta P).map (partPairEmbedding P) =
      (finpartitionOfVertexPartition P).nonUniforms G eta := by
  classical
  ext uv
  constructor
  · intro huv
    obtain ⟨p, hp, rfl⟩ := Finset.mem_map.1 huv
    have hp' := (Finset.mem_filter.1 hp).2
    rw [Finpartition.mk_mem_nonUniforms]
    refine ⟨?_, ?_, ?_, hp'.2⟩
    · change P.part p.1 ∈ (finpartitionOfVertexPartition P).parts
      rw [finpartitionOfVertexPartition_parts]
      exact Finset.mem_image.2 ⟨p.1, Finset.mem_univ _, rfl⟩
    · change P.part p.2 ∈ (finpartitionOfVertexPartition P).parts
      rw [finpartitionOfVertexPartition_parts]
      exact Finset.mem_image.2 ⟨p.2, Finset.mem_univ _, rfl⟩
    · exact fun h => hp'.1 (part_injective P h)
  · intro huv
    rcases uv with ⟨A, B⟩
    have huv' := (Finpartition.mk_mem_nonUniforms
      (P := finpartitionOfVertexPartition P) (G := G)).1 huv
    rw [finpartitionOfVertexPartition_parts] at huv'
    obtain ⟨i, -, hi⟩ := Finset.mem_image.1 huv'.1
    obtain ⟨j, -, hj⟩ := Finset.mem_image.1 huv'.2.1
    subst A
    subst B
    rw [Finset.mem_map]
    refine ⟨(i, j), ?_, rfl⟩
    change (i, j) ∈ (Finset.univ.product Finset.univ).filter
      (fun p : Fin P.partCount × Fin P.partCount =>
        p.1 ≠ p.2 ∧ ¬ G.IsUniform eta (P.part p.1) (P.part p.2))
    rw [Finset.mem_filter]
    refine ⟨Finset.mem_product.2 ⟨Finset.mem_univ _, Finset.mem_univ _⟩, ?_, huv'.2.2.2⟩
    exact fun hij => huv'.2.2.1 (congrArg P.part hij)

lemma card_orderedNonUniformIndices
    (G : SimpleGraph V) [DecidableRel G.Adj] (eta : ℝ)
    (P : VertexPartition V) :
    (orderedNonUniformIndices G eta P).card =
      ((finpartitionOfVertexPartition P).nonUniforms G eta).card := by
  rw [← map_orderedNonUniformIndices G eta P, Finset.card_map]

/-- Swapping the two coordinates is an embedding. -/
def swapPairEmbedding (A : Type*) : (A × A) ↪ (A × A) where
  toFun := Prod.swap
  inj' p q h := by
    exact congrArg Prod.swap h

/-- Every ordered non-`eta`-uniform pair gives one of the two orientations of
an unordered [lax-18](https://laxarchive.org/lax-18/)-irregular pair at the smaller parameter `epsilon`. -/
lemma card_orderedNonUniformIndices_le_two_mul_irregularPairCount
    (G : SimpleGraph V) [DecidableRel G.Adj]
    {epsilon eta : ℝ} (hεη : epsilon < eta)
    (P : VertexPartition V) :
    (orderedNonUniformIndices G eta P).card ≤
      2 * irregularPairCount G epsilon P := by
  classical
  let S := orderedNonUniformIndices G eta P
  let I := irregularPairIndices G epsilon P
  have hforward : (S.filter fun p => p.1 < p.2).card ≤ I.card := by
    apply Finset.card_le_card
    intro p hp
    have hpS := (Finset.mem_filter.1 hp).1
    have hplt := (Finset.mem_filter.1 hp).2
    have hpbad := (Finset.mem_filter.1 hpS).2.2
    change p ∈ (Finset.univ.product Finset.univ).filter
      (fun q : Fin P.partCount × Fin P.partCount => q.1 < q.2 ∧
        ¬ IsRegularPair G epsilon (P.part q.1) (P.part q.2))
    rw [Finset.mem_filter]
    refine ⟨Finset.mem_product.2 ⟨Finset.mem_univ _, Finset.mem_univ _⟩, hplt, ?_⟩
    intro hregular
    exact hpbad (isUniform_of_isRegularPair G hεη _ _ hregular)
  have hbackward : (S.filter fun p => ¬ p.1 < p.2).card ≤ I.card := by
    calc
      (S.filter fun p => ¬ p.1 < p.2).card =
          ((S.filter fun p => ¬ p.1 < p.2).map
            (swapPairEmbedding (Fin P.partCount))).card :=
        (Finset.card_map _).symm
      _ ≤ I.card := by
        apply Finset.card_le_card
        intro p hp
        obtain ⟨q, hq, rfl⟩ := Finset.mem_map.1 hp
        have hqS := (Finset.mem_filter.1 hq).1
        have hnlt := (Finset.mem_filter.1 hq).2
        have hqbad' := (Finset.mem_filter.1 hqS).2
        have hqgt : q.2 < q.1 := lt_of_le_of_ne (not_lt.mp hnlt) hqbad'.1.symm
        change (q.2, q.1) ∈ (Finset.univ.product Finset.univ).filter
          (fun p : Fin P.partCount × Fin P.partCount => p.1 < p.2 ∧
            ¬ IsRegularPair G epsilon (P.part p.1) (P.part p.2))
        rw [Finset.mem_filter]
        refine ⟨Finset.mem_product.2 ⟨Finset.mem_univ _, Finset.mem_univ _⟩, hqgt, ?_⟩
        intro hregular
        exact hqbad'.2 (isUniform_of_isRegularPair G hεη _ _ hregular).symm
  have hsplit := Finset.card_filter_add_card_filter_not
    (s := S) (fun p => p.1 < p.2)
  change S.card ≤ 2 * I.card
  omega

/-- A [lax-18](https://laxarchive.org/lax-18/) regular partition at parameter `eta / 4` is a mathlib-uniform
partition at parameter `eta`, provided that it has at least two parts. -/
lemma isUniform_finpartitionOfVertexPartition
    (G : SimpleGraph V) [DecidableRel G.Adj]
    {eta : ℝ} (hη : 0 < eta) (P : VertexPartition V)
    (hk : 2 ≤ P.partCount)
    (hP : IsRegularPartition G (eta / 4) P) :
    (finpartitionOfVertexPartition P).IsUniform G eta := by
  classical
  rw [Finpartition.IsUniform]
  rw [← card_orderedNonUniformIndices G eta P]
  have hεη : eta / 4 < eta := by linarith
  have hcount := card_orderedNonUniformIndices_le_two_mul_irregularPairCount
    G hεη P
  have hregular :
      (irregularPairCount G (eta / 4) P : ℝ) ≤
        (eta / 4) * (P.partCount : ℝ) ^ 2 := hP
  have hkR : (2 : ℝ) ≤ P.partCount := by exact_mod_cast hk
  have hkone : 1 ≤ P.partCount := by omega
  simp only [card_finpartitionOfVertexPartition_parts]
  calc
    ((orderedNonUniformIndices G eta P).card : ℝ) ≤
        2 * (irregularPairCount G (eta / 4) P : ℝ) := by
      exact_mod_cast hcount
    _ ≤ 2 * ((eta / 4) * (P.partCount : ℝ) ^ 2) := by gcongr
    _ = eta * (P.partCount : ℝ) * ((P.partCount : ℝ) / 2) := by ring
    _ ≤ eta * (P.partCount : ℝ) * ((P.partCount : ℝ) - 1) := by
      gcongr
      linarith
    _ = ((P.partCount * (P.partCount - 1) : ℕ) : ℝ) * eta := by
      rw [Nat.cast_mul, Nat.cast_sub hkone]
      ring

end Lax54Proofs.RegularityAdapter
