import Lax54.BipartiteCombLemma
import Mathlib.Data.Fin.Tuple.Embedding
import Mathlib.Tactic

namespace Lax54Proofs

open Finset
open scoped BigOperators SimpleGraph
open Lax54.BipartiteCombLemma

universe u

namespace BipartiteComb

variable {V : Type u} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj]

/-- Neighbors first acquired by the `i`th tooth of an ordered peeling sequence. -/
def privateNeighbors {k : ℕ} (D : Finset V) (tooth : Fin k → V)
    (i : Fin k) : Finset V :=
  D.filter fun b ↦ G.Adj (tooth i) b ∧
    ∀ j : Fin k, j < i → ¬ G.Adj (tooth j) b

/-- An initial segment of the greedy sequence in the proof of Theorem 2.1. -/
structure PeelingSequence (A D : Finset V) (L k : ℕ) where
  tooth : Fin k ↪ V
  tooth_mem : ∀ i, tooth i ∈ A
  private_large : ∀ i, L ≤ (privateNeighbors G D tooth i).card

/-- Vertices not adjacent to any tooth of a peeling sequence. -/
def PeelingSequence.remainder {A D : Finset V} {L k : ℕ}
    (S : PeelingSequence G A D L k) : Finset V :=
  D.filter fun b ↦ ∀ i : Fin k, ¬ G.Adj (S.tooth i) b

lemma PeelingSequence.tooth_ne_of_remainder_neighbor
    {A D : Finset V} {L k : ℕ} (hL : 0 < L)
    (S : PeelingSequence G A D L k) {a : V}
    (ha : L ≤ ((S.remainder G).filter fun b ↦ G.Adj a b).card) :
    a ∉ Set.range S.tooth := by
  rintro ⟨i, rfl⟩
  have hzero : ((S.remainder G).filter fun b ↦ G.Adj (S.tooth i) b) = ∅ := by
    ext b
    simp only [PeelingSequence.remainder, mem_filter]
    constructor
    · rintro ⟨⟨-, hnone⟩, hadj⟩
      exact (hnone i hadj).elim
    · intro hb
      simpa using hb
  rw [hzero] at ha
  simp at ha
  omega

lemma privateNeighbors_snoc_castSucc
    {D : Finset V} {k : ℕ} (tooth : Fin k → V) (a : V) (i : Fin k) :
    privateNeighbors G D (Fin.snoc tooth a) i.castSucc =
      privateNeighbors G D tooth i := by
  ext b
  simp only [privateNeighbors, mem_filter]
  constructor
  · rintro ⟨hbD, hib, hprev⟩
    refine ⟨hbD, ?_, fun j hj ↦ ?_⟩
    · simpa using hib
    · simpa using hprev j.castSucc (by simpa using hj)
  · rintro ⟨hbD, hib, hprev⟩
    refine ⟨hbD, by simpa using hib, ?_⟩
    intro j hj
    cases j using Fin.lastCases with
    | last => exact (not_lt_of_ge (Fin.le_last _) hj).elim
    | cast j' =>
        simpa only [Fin.snoc_castSucc] using hprev j' (by simpa using hj)

lemma privateNeighbors_snoc_last
    {D : Finset V} {k : ℕ} (tooth : Fin k → V) (a : V) :
    privateNeighbors G D (Fin.snoc tooth a) (Fin.last k) =
      (D.filter fun b ↦ ∀ i : Fin k, ¬ G.Adj (tooth i) b).filter
        fun b ↦ G.Adj a b := by
  ext b
  simp only [privateNeighbors, mem_filter, Fin.snoc_last]
  constructor
  · rintro ⟨hbD, haba, hprev⟩
    exact ⟨⟨hbD, fun i ↦ by simpa using hprev i.castSucc (by simp)⟩, haba⟩
  · rintro ⟨⟨hbD, hprev⟩, haba⟩
    refine ⟨hbD, haba, ?_⟩
    intro j hj
    cases j using Fin.lastCases with
    | last => exact (lt_irrefl _ hj).elim
    | cast i => simpa only [Fin.snoc_castSucc] using hprev i

noncomputable def PeelingSequence.snoc
    {A D : Finset V} {L k : ℕ} (hL : 0 < L)
    (S : PeelingSequence G A D L k) {a : V} (haA : a ∈ A)
    (ha : L ≤ ((S.remainder G).filter fun b ↦ G.Adj a b).card) :
    PeelingSequence G A D L (k + 1) := by
  let e : Fin (k + 1) ↪ V :=
    Fin.Embedding.snoc S.tooth (S.tooth_ne_of_remainder_neighbor G hL ha)
  refine ⟨e, ?_, ?_⟩
  · intro i
    refine Fin.lastCases ?_ (fun j ↦ ?_) i
    · simpa [e] using haA
    · simpa [e] using S.tooth_mem j
  · intro i
    refine Fin.lastCases ?_ (fun j ↦ ?_) i
    · simpa [e, PeelingSequence.remainder,
        privateNeighbors_snoc_last (G := G)] using ha
    · simpa [e, privateNeighbors_snoc_castSucc (G := G)] using S.private_large j

/-- A maximal greedy peeling sequence leaves maximum cross-degree below `L`. -/
lemma exists_maximal_peeling (A D : Finset V) (L : ℕ) (hL : 0 < L) :
    ∃ (k : ℕ) (S : PeelingSequence G A D L k),
      ∀ a ∈ A, ((S.remainder G).filter fun b ↦ G.Adj a b).card < L := by
  let T := Σ k : ℕ, PeelingSequence G A D L k
  have hbound : ∀ z : T, z.1 ≤ A.card := by
    rintro ⟨k, S⟩
    let teeth : Finset V := Finset.univ.map S.tooth
    have hsubset : teeth ⊆ A := by
      intro a ha
      obtain ⟨i, -, rfl⟩ := Finset.mem_map.mp ha
      exact S.tooth_mem i
    calc
      k = teeth.card := by simp [teeth]
      _ ≤ A.card := Finset.card_le_card hsubset
  have hfinite : ((fun z : T ↦ z.1) '' Set.univ).Finite := by
    apply (Set.finite_Iic A.card).subset
    rintro k ⟨z, -, rfl⟩
    exact hbound z
  have hempty : T :=
    ⟨0, ⟨⟨Fin.elim0, fun i ↦ Fin.elim0 i⟩,
      fun i ↦ Fin.elim0 i, fun i ↦ Fin.elim0 i⟩⟩
  letI : Nonempty T := ⟨hempty⟩
  obtain ⟨z, -, hzmax⟩ :=
    hfinite.exists_maximalFor' (fun z : T ↦ z.1) Set.univ Set.univ_nonempty
  refine ⟨z.1, z.2, ?_⟩
  intro a haA
  by_contra hnot
  have ha : L ≤ ((z.2.remainder G).filter fun b ↦ G.Adj a b).card :=
    Nat.le_of_not_gt hnot
  let z' : T := ⟨z.1 + 1, z.2.snoc G hL haA ha⟩
  have hz'le : z'.1 ≤ z.1 := hzmax (by simp) (by simp [z'])
  simp [z'] at hz'le

/-- Moving to a larger `Fin k` index strictly decreases its distance from the end. -/
lemma reverseMeasure_lt {k : ℕ} {i j : Fin k} (h : i < j) :
    k - j.1 < k - i.1 := by
  apply Nat.sub_lt_sub_left i.isLt
  exact h

/-- Reverse greedy selection of the teeth used in the proof of Theorem 2.1. -/
noncomputable def goodIndex {k : ℕ} (P Q : Fin k → Finset V) : Fin k → Bool :=
  (InvImage.wf (fun i : Fin k ↦ k - i.1) Nat.lt_wfRel.wf).fix fun i rec ↦
    decide (4 * ((P i).filter fun x ↦
      ∃ j : {j : Fin k // i < j},
        rec j.1 (reverseMeasure_lt j.property) = true ∧ x ∈ Q j.1).card ≤
      3 * (P i).card)

lemma goodIndex_eq {k : ℕ} (P Q : Fin k → Finset V) (i : Fin k) :
    goodIndex P Q i =
      decide (4 * ((P i).filter fun x ↦
        ∃ j : {j : Fin k // i < j},
          goodIndex P Q j.1 = true ∧ x ∈ Q j.1).card ≤
        3 * (P i).card) := by
  rw [goodIndex, WellFounded.fix_eq]

/-- The indices retained by the reverse greedy selection. -/
noncomputable def goodIndices {k : ℕ} (P Q : Fin k → Finset V) : Finset (Fin k) :=
  Finset.univ.filter fun i ↦ goodIndex P Q i = true

lemma goodIndex_eq_true_iff {k : ℕ} (P Q : Fin k → Finset V) (i : Fin k) :
    goodIndex P Q i = true ↔
      4 * ((P i).filter fun x ↦
        ∃ j : {j : Fin k // i < j}, goodIndex P Q j.1 = true ∧ x ∈ Q j.1).card ≤
      3 * (P i).card := by
  rw [goodIndex_eq]
  simp

lemma mem_goodIndices_iff {k : ℕ} (P Q : Fin k → Finset V) (i : Fin k) :
    i ∈ goodIndices P Q ↔ goodIndex P Q i = true := by
  simp [goodIndices]

lemma laterGood_eq_laterIndices {k : ℕ} (P Q : Fin k → Finset V) (i : Fin k) :
    ((P i).filter fun x ↦
      ∃ j : {j : Fin k // i < j}, goodIndex P Q j.1 = true ∧ x ∈ Q j.1) =
    ((P i).filter fun x ↦
      ∃ j : {j : Fin k // i < j}, j.1 ∈ goodIndices P Q ∧ x ∈ Q j.1) := by
  ext x
  simp only [Finset.mem_filter]
  constructor
  · rintro ⟨hxP, j, hj, hxj⟩
    exact ⟨hxP, j, (mem_goodIndices_iff P Q j.1).mpr hj, hxj⟩
  · rintro ⟨hxP, j, hj, hxj⟩
    exact ⟨hxP, j, (mem_goodIndices_iff P Q j.1).mp hj, hxj⟩

/-- All neighbors in the current residual set. -/
def neighborsIn {k : ℕ} (D : Finset V) (tooth : Fin k → V)
    (i : Fin k) : Finset V :=
  D.filter fun b ↦ G.Adj (tooth i) b

/-- Neighbors already acquired by an earlier tooth. -/
def otherNeighbors {k : ℕ} (D : Finset V) (tooth : Fin k → V)
    (i : Fin k) : Finset V :=
  neighborsIn G D tooth i \ privateNeighbors G D tooth i

lemma privateNeighbors_subset_neighborsIn {k : ℕ} (D : Finset V)
    (tooth : Fin k → V) (i : Fin k) :
    privateNeighbors G D tooth i ⊆ neighborsIn G D tooth i := by
  intro x hx
  exact Finset.mem_filter.mpr
    ⟨(Finset.mem_filter.mp hx).1, (Finset.mem_filter.mp hx).2.1⟩

lemma privateNeighbors_pairwise_disjoint {k : ℕ} (D : Finset V)
    (tooth : Fin k → V) :
    Set.PairwiseDisjoint (Set.univ : Set (Fin k)) (privateNeighbors G D tooth) := by
  intro i _ j _ hij
  change Disjoint (privateNeighbors G D tooth i) (privateNeighbors G D tooth j)
  rw [Finset.disjoint_left]
  intro x hxi hxj
  rcases lt_or_gt_of_ne hij with hij' | hji'
  · exact ((Finset.mem_filter.mp hxj).2.2 i hij')
      (Finset.mem_filter.mp hxi).2.1
  · exact ((Finset.mem_filter.mp hxi).2.2 j hji')
      (Finset.mem_filter.mp hxj).2.1

lemma private_mem_other_implies_lt {k : ℕ} (D : Finset V)
    (tooth : Fin k → V) {i j : Fin k} {x : V}
    (hxi : x ∈ privateNeighbors G D tooth i)
    (hxj : x ∈ otherNeighbors G D tooth j) : i < j := by
  have hxjN : x ∈ neighborsIn G D tooth j := (Finset.mem_sdiff.mp hxj).1
  have hadj : G.Adj (tooth j) x := (Finset.mem_filter.mp hxjN).2
  by_contra hnlt
  have hji : j ≤ i := le_of_not_gt hnlt
  rcases hji.eq_or_lt with rfl | hji'
  · exact (Finset.mem_sdiff.mp hxj).2 hxi
  · exact ((Finset.mem_filter.mp hxi).2.2 j hji') hadj

/-- The union of the `Q_i` belonging to selected good teeth. -/
def contamination {k : ℕ} (D : Finset V) (tooth : Fin k → V)
    (I : Finset (Fin k)) : Finset V :=
  I.biUnion (otherNeighbors G D tooth)

/-- The vertices retained for one selected tooth. -/
def retainedBlock {k : ℕ} (D : Finset V) (tooth : Fin k → V)
    (I : Finset (Fin k)) (i : Fin k) : Finset V :=
  privateNeighbors G D tooth i \ contamination G D tooth I

lemma private_inter_contamination_eq_later {k : ℕ} (D : Finset V)
    (tooth : Fin k → V) (I : Finset (Fin k)) (i : Fin k) :
    privateNeighbors G D tooth i ∩ contamination G D tooth I =
      (privateNeighbors G D tooth i).filter fun x ↦
        ∃ j : {j : Fin k // i < j}, j.1 ∈ I ∧
          x ∈ otherNeighbors G D tooth j.1 := by
  ext x
  simp only [Finset.mem_inter, contamination, Finset.mem_biUnion,
    Finset.mem_filter]
  constructor
  · rintro ⟨hxi, ⟨j, hjI, hxj⟩⟩
    exact ⟨hxi, ⟨⟨j, private_mem_other_implies_lt G D tooth hxi hxj⟩,
      hjI, hxj⟩⟩
  · rintro ⟨hxi, ⟨j, hjI, hxj⟩⟩
    exact ⟨hxi, ⟨j.1, hjI, hxj⟩⟩

lemma retainedBlock_add_later_card {k : ℕ} (D : Finset V)
    (tooth : Fin k → V) (I : Finset (Fin k)) (i : Fin k) :
    (retainedBlock G D tooth I i).card +
        ((privateNeighbors G D tooth i).filter fun x ↦
          ∃ j : {j : Fin k // i < j}, j.1 ∈ I ∧
            x ∈ otherNeighbors G D tooth j.1).card =
      (privateNeighbors G D tooth i).card := by
  let P := privateNeighbors G D tooth i
  let R := contamination G D tooth I
  have hpart := Finset.card_sdiff_add_card_eq_card (Finset.inter_subset_left : P ∩ R ⊆ P)
  have hdiff : P \ (P ∩ R) = P \ R := by
    ext x
    simp
  rw [hdiff, private_inter_contamination_eq_later (G := G)] at hpart
  exact hpart

lemma retainedBlock_large_of_good {k : ℕ} {A D : Finset V}
    {L : ℕ} (S : PeelingSequence G A D L k)
    (i : Fin k) (hi : i ∈ goodIndices
      (privateNeighbors G D S.tooth) (otherNeighbors G D S.tooth)) :
    L ≤ 4 * (retainedBlock G D S.tooth
      (goodIndices (privateNeighbors G D S.tooth) (otherNeighbors G D S.tooth)) i).card := by
  let P : Fin k → Finset V := privateNeighbors G D S.tooth
  let Q : Fin k → Finset V := otherNeighbors G D S.tooth
  let I : Finset (Fin k) := goodIndices P Q
  have hgood : goodIndex P Q i = true :=
    (mem_goodIndices_iff P Q i).mp (by simpa [I, P, Q] using hi)
  have hineq := (goodIndex_eq_true_iff P Q i).mp hgood
  have hlater := laterGood_eq_laterIndices P Q i
  rw [hlater] at hineq
  change 4 * ((P i).filter fun x ↦
      ∃ j : {j : Fin k // i < j}, j.1 ∈ I ∧ x ∈ Q j.1).card ≤
    3 * (P i).card at hineq
  have hpart :
      (retainedBlock G D S.tooth I i).card +
          ((P i).filter fun x ↦
            ∃ j : {j : Fin k // i < j}, j.1 ∈ I ∧ x ∈ Q j.1).card =
        (P i).card := by
    simpa [P, Q] using retainedBlock_add_later_card (G := G) D S.tooth I i
  have hprivate : L ≤ (P i).card := S.private_large i
  change L ≤ 4 * (retainedBlock G D S.tooth I i).card
  omega

/-- At least one eleventh of a maximal peeling sequence survives the reverse pruning. -/
lemma peeling_card_le_nine_good {k : ℕ} {A D : Finset V} {L Delta : ℕ}
    (hL : 0 < L) (hDeltaL : Delta ≤ 8 * L)
    (S : PeelingSequence G A D L k)
    (hdegree : ∀ i : Fin k, (neighborsIn G D S.tooth i).card ≤ Delta) :
    k ≤ 11 * (goodIndices
      (privateNeighbors G D S.tooth) (otherNeighbors G D S.tooth)).card := by
  let P : Fin k → Finset V := privateNeighbors G D S.tooth
  let Q : Fin k → Finset V := otherNeighbors G D S.tooth
  let I : Finset (Fin k) := goodIndices P Q
  let Bad : Finset (Fin k) := Finset.univ \ I
  let R : Finset V := I.biUnion Q
  let T : Fin k → Finset V := fun i ↦
    (P i).filter fun x ↦
      ∃ j : {j : Fin k // i < j}, j.1 ∈ I ∧ x ∈ Q j.1
  have hQ (i : Fin k) : (Q i).card ≤ 7 * L := by
    have hsubset : P i ⊆ neighborsIn G D S.tooth i :=
      privateNeighbors_subset_neighborsIn G D S.tooth i
    have hpart := Finset.card_sdiff_add_card_eq_card hsubset
    have hprivate : L ≤ (P i).card := S.private_large i
    have hdeg := hdegree i
    change (Q i).card + (P i).card = (neighborsIn G D S.tooth i).card at hpart
    omega
  have hR : R.card ≤ I.card * (7 * L) := by
    calc
      R.card ≤ ∑ i ∈ I, (Q i).card := by
        simpa [R] using Finset.card_biUnion_le (s := I) (t := Q)
      _ ≤ ∑ _i ∈ I, 7 * L :=
        Finset.sum_le_sum fun i _ ↦ hQ i
      _ = I.card * (7 * L) := by simp
  have hbad (i : Fin k) (hi : i ∈ Bad) : 3 * L ≤ 4 * (T i).card := by
    have hiI : i ∉ I := (Finset.mem_sdiff.mp hi).2
    have hnotgood : goodIndex P Q i ≠ true := by
      intro h
      exact hiI ((mem_goodIndices_iff P Q i).mpr h)
    have hnotineq : ¬ 4 * ((P i).filter fun x ↦
        ∃ j : {j : Fin k // i < j},
          goodIndex P Q j.1 = true ∧ x ∈ Q j.1).card ≤ 3 * (P i).card := by
      intro h
      exact hnotgood ((goodIndex_eq_true_iff P Q i).mpr h)
    have hlater := laterGood_eq_laterIndices P Q i
    rw [hlater] at hnotineq
    have hprivate : L ≤ (P i).card := S.private_large i
    change ¬4 * (T i).card ≤ 3 * (P i).card at hnotineq
    omega
  have hTdisj : Set.PairwiseDisjoint (↑Bad : Set (Fin k)) T := by
    intro i _ j _ hij
    change Disjoint (T i) (T j)
    exact (privateNeighbors_pairwise_disjoint G D S.tooth
      (Set.mem_univ i) (Set.mem_univ j) hij).mono
        (by intro x hx; exact (Finset.mem_filter.mp hx).1)
        (by intro x hx; exact (Finset.mem_filter.mp hx).1)
  have hTsubset : Bad.biUnion T ⊆ R := by
    intro x hx
    obtain ⟨i, hiBad, hxi⟩ := Finset.mem_biUnion.mp hx
    obtain ⟨-, j, hjI, hxj⟩ := Finset.mem_filter.mp hxi
    exact Finset.mem_biUnion.mpr ⟨j.1, hjI, hxj⟩
  have hsumT : ∑ i ∈ Bad, (T i).card ≤ R.card := by
    calc
      ∑ i ∈ Bad, (T i).card = (Bad.biUnion T).card := by
        symm
        exact Finset.card_biUnion hTdisj
      _ ≤ R.card := Finset.card_le_card hTsubset
  have hsumBad : Bad.card * (3 * L) ≤ 4 * R.card := by
    calc
      Bad.card * (3 * L) = ∑ _i ∈ Bad, 3 * L := by simp
      _ ≤ ∑ i ∈ Bad, 4 * (T i).card :=
        Finset.sum_le_sum fun i hi ↦ hbad i hi
      _ = 4 * ∑ i ∈ Bad, (T i).card := by
        rw [Finset.mul_sum]
      _ ≤ 4 * R.card := Nat.mul_le_mul_left 4 hsumT
  have hbadI : Bad.card ≤ 10 * I.card := by
    have hcombined : Bad.card * (3 * L) ≤ 4 * (I.card * (7 * L)) :=
      hsumBad.trans (Nat.mul_le_mul_left 4 hR)
    have hcancel : L * (3 * Bad.card) ≤ L * (28 * I.card) := by
      calc
        L * (3 * Bad.card) = Bad.card * (3 * L) := by ring
        _ ≤ 4 * (I.card * (7 * L)) := hcombined
        _ = L * (28 * I.card) := by ring
    have := Nat.le_of_mul_le_mul_left hcancel hL
    omega
  have hpartition : Bad.card + I.card = k := by
    simpa [Bad] using
      (Finset.card_sdiff_add_card_eq_card (Finset.subset_univ I))
  change k ≤ 11 * I.card
  omega

/-- Reindex the good teeth and their retained private neighborhoods as a comb. -/
noncomputable def combOfPeeling {k : ℕ} {A D B : Finset V} {L : ℕ}
    (hDB : D ⊆ B) (S : PeelingSequence G A D L k) :
    CombBetween G A B
      (goodIndices (privateNeighbors G D S.tooth)
        (otherNeighbors G D S.tooth)).card := by
  let P : Fin k → Finset V := privateNeighbors G D S.tooth
  let Q : Fin k → Finset V := otherNeighbors G D S.tooth
  let I : Finset (Fin k) := goodIndices P Q
  let e : Fin I.card → Fin k := fun i ↦ (I.orderIsoOfFin rfl i).1
  have he_mem (i : Fin I.card) : e i ∈ I := (I.orderIsoOfFin rfl i).2
  have he_inj : Function.Injective e := by
    intro i j hij
    apply (I.orderIsoOfFin rfl).injective
    exact Subtype.ext hij
  refine
    { tooth := fun i ↦ S.tooth (e i)
      block := fun i ↦ retainedBlock G D S.tooth I (e i)
      tooth_mem := fun i ↦ S.tooth_mem (e i)
      tooth_injective := S.tooth.injective.comp he_inj
      block_subset := ?_
      blocks_disjoint := ?_
      tooth_adj_block := ?_
      tooth_nonadj_other := ?_ }
  · intro i x hx
    apply hDB
    exact (Finset.mem_filter.mp
      ((Finset.mem_sdiff.mp hx).1)).1
  · intro i j hij
    have he_ne : e i ≠ e j := he_inj.ne hij
    exact (privateNeighbors_pairwise_disjoint G D S.tooth
      (Set.mem_univ _) (Set.mem_univ _) he_ne).mono
        (fun _ hx ↦ (Finset.mem_sdiff.mp hx).1)
        (fun _ hx ↦ (Finset.mem_sdiff.mp hx).1)
  · intro i x hx
    exact (Finset.mem_filter.mp (Finset.mem_sdiff.mp hx).1).2.1
  · intro i j hij x hx
    have he_ne : e i ≠ e j := he_inj.ne hij
    have hxP : x ∈ P (e j) := Finset.mem_sdiff.mp hx |>.1
    have hxnotR : x ∉ contamination G D S.tooth I :=
      Finset.mem_sdiff.mp hx |>.2
    rcases lt_or_gt_of_ne he_ne with hlt | hgt
    · exact (Finset.mem_filter.mp hxP).2.2 (e i) hlt
    · intro hadj
      have hxN : x ∈ neighborsIn G D S.tooth (e i) :=
        Finset.mem_filter.mpr ⟨(Finset.mem_filter.mp hxP).1, hadj⟩
      have hxnotP : x ∉ P (e i) := by
        intro hxPi
        exact (Finset.disjoint_left.mp
          (privateNeighbors_pairwise_disjoint G D S.tooth
            (Set.mem_univ _) (Set.mem_univ _) he_ne)) hxPi hxP
      have hxQ : x ∈ Q (e i) := Finset.mem_sdiff.mpr ⟨hxN, hxnotP⟩
      exact hxnotR (Finset.mem_biUnion.mpr ⟨e i, he_mem i, hxQ⟩)

/-- Enlarging the allowed right vertex class preserves a comb. -/
def CombBetween.mono_right {A B B' : Finset V} {t : ℕ}
    (C : CombBetween G A B t) (hBB' : B ⊆ B') : CombBetween G A B' t where
  tooth := C.tooth
  block := C.block
  tooth_mem := C.tooth_mem
  tooth_injective := C.tooth_injective
  block_subset i := (C.block_subset i).trans hBB'
  blocks_disjoint := C.blocks_disjoint
  tooth_adj_block := C.tooth_adj_block
  tooth_nonadj_other := C.tooth_nonadj_other

lemma combOfPeeling_block_large {k : ℕ} {A D B : Finset V} {L : ℕ}
    (hDB : D ⊆ B) (S : PeelingSequence G A D L k)
    (i : Fin (goodIndices (privateNeighbors G D S.tooth)
      (otherNeighbors G D S.tooth)).card) :
    L ≤ 4 * ((combOfPeeling G hDB S).block i).card := by
  let P : Fin k → Finset V := privateNeighbors G D S.tooth
  let Q : Fin k → Finset V := otherNeighbors G D S.tooth
  let I : Finset (Fin k) := goodIndices P Q
  let e : Fin I.card → Fin k := fun i ↦ (I.orderIsoOfFin rfl i).1
  have hei : e i ∈ I := (I.orderIsoOfFin rfl i).2
  simpa [combOfPeeling, P, Q, I, e] using
    retainedBlock_large_of_good (G := G) S (e i) (by simpa [P, Q, I] using hei)

/-- Vertices removed by one peeling level. -/
def PeelingSequence.covered {A D : Finset V} {L k : ℕ}
    (S : PeelingSequence G A D L k) : Finset V :=
  Finset.univ.biUnion (neighborsIn G D S.tooth)

lemma PeelingSequence.covered_card_le {A D : Finset V} {L k Delta : ℕ}
    (S : PeelingSequence G A D L k)
    (hdegree : ∀ i : Fin k, (neighborsIn G D S.tooth i).card ≤ Delta) :
    (S.covered G).card ≤ k * Delta := by
  calc
    (S.covered G).card ≤ ∑ i : Fin k, (neighborsIn G D S.tooth i).card := by
      simpa [PeelingSequence.covered] using
        Finset.card_biUnion_le
          (s := (Finset.univ : Finset (Fin k)))
          (t := neighborsIn G D S.tooth)
    _ ≤ ∑ _i : Fin k, Delta :=
      Finset.sum_le_sum fun i _ ↦ hdegree i
    _ = k * Delta := by simp

lemma PeelingSequence.covered_union_remainder {A D : Finset V} {L k : ℕ}
    (S : PeelingSequence G A D L k) :
    S.covered G ∪ S.remainder G = D := by
  ext x
  simp only [PeelingSequence.covered, Finset.mem_union, Finset.mem_biUnion,
    Finset.mem_univ, true_and, neighborsIn, Finset.mem_filter,
    PeelingSequence.remainder]
  constructor
  · rintro (⟨i, hxD, -⟩ | ⟨hxD, -⟩) <;> exact hxD
  · intro hxD
    by_cases h : ∃ i : Fin k, G.Adj (S.tooth i) x
    · exact Or.inl ⟨h.choose, hxD, h.choose_spec⟩
    · exact Or.inr ⟨hxD, fun i hi ↦ h ⟨i, hi⟩⟩

lemma PeelingSequence.covered_disjoint_remainder {A D : Finset V} {L k : ℕ}
    (S : PeelingSequence G A D L k) :
    Disjoint (S.covered G) (S.remainder G) := by
  rw [Finset.disjoint_left]
  intro x hxC hxR
  obtain ⟨i, -, hix⟩ := Finset.mem_biUnion.mp hxC
  exact (Finset.mem_filter.mp hxR).2 i (Finset.mem_filter.mp hix).2

lemma PeelingSequence.card_eq_covered_add_remainder {A D : Finset V} {L k : ℕ}
    (S : PeelingSequence G A D L k) :
    D.card = (S.covered G).card + (S.remainder G).card := by
  have hunion := S.covered_union_remainder G
  have hcard := Finset.card_union_of_disjoint (S.covered_disjoint_remainder G)
  calc
    D.card = (S.covered G ∪ S.remainder G).card := congrArg Finset.card hunion.symm
    _ = (S.covered G).card + (S.remainder G).card := hcard

/-- The four-adic peeling proof of the square-form bipartite comb lemma. -/
theorem bipartite_comb_lemma_aux
    (A B : Finset V) (Gamma Delta : ℕ)
    (hAB : Disjoint A B) (hGamma : 0 < Gamma)
    (hcoverage : ∀ b ∈ B, ∃ a ∈ A, G.Adj a b)
    (hdegree : ∀ a ∈ A, (B.filter fun b ↦ G.Adj a b).card ≤ Delta) :
    (∃ (t : ℕ) (Cmb : CombBetween G A B t),
        0 < t ∧ ∀ i : Fin t, Gamma ≤ t ^ 2 * (Cmb.block i).card) ∨
      SmallSideBound 128 Gamma Delta B.card := by
  induction Delta using Nat.strong_induction_on generalizing B with
  | h Delta ih =>
      by_cases hDelta : Delta = 0
      · subst Delta
        have hB : B = ∅ := by
          apply Finset.not_nonempty_iff_eq_empty.mp
          rintro ⟨b, hb⟩
          obtain ⟨a, haA, hab⟩ := hcoverage b hb
          have hbN : b ∈ B.filter fun x ↦ G.Adj a x :=
            Finset.mem_filter.mpr ⟨hb, hab⟩
          have hpos : 0 < (B.filter fun x ↦ G.Adj a x).card :=
            Finset.card_pos.mpr ⟨b, hbN⟩
          have hzero := hdegree a haA
          omega
        right
        subst B
        simp [SmallSideBound]
      · have hDeltaPos : 0 < Delta := Nat.pos_of_ne_zero hDelta
        let L : ℕ := (Delta + 7) / 8
        have hL : 0 < L := by
          dsimp [L]
          omega
        have hDeltaL : Delta ≤ 8 * L := by
          dsimp [L]
          omega
        have hnext : L - 1 < Delta := by
          dsimp [L]
          omega
        have hnextScale : 8 * (L - 1) ≤ Delta := by
          dsimp [L]
          omega
        obtain ⟨k, S, hremdegree⟩ := exists_maximal_peeling G A B L hL
        have hseqdegree : ∀ i : Fin k,
            (neighborsIn G B S.tooth i).card ≤ Delta := by
          intro i
          simpa [neighborsIn] using hdegree (S.tooth i) (S.tooth_mem i)
        let t : ℕ := (goodIndices (privateNeighbors G B S.tooth)
          (otherNeighbors G B S.tooth)).card
        let C : CombBetween G A B t := combOfPeeling G (Finset.Subset.rfl) S
        have hblock (i : Fin t) : L ≤ 4 * (C.block i).card := by
          simpa [C, t] using
            combOfPeeling_block_large (G := G) (Finset.Subset.rfl) S i
        by_cases hsuccess : 0 < t ∧
            ∀ i : Fin t, Gamma ≤ t ^ 2 * (C.block i).card
        · exact Or.inl ⟨t, C, hsuccess⟩
        have htL : t ^ 2 * L < 4 * Gamma := by
          by_cases htzero : t = 0
          · simp [htzero, hGamma]
          · have htpos : 0 < t := Nat.pos_of_ne_zero htzero
            have hnall : ¬∀ i : Fin t,
                Gamma ≤ t ^ 2 * (C.block i).card := by
              intro hall
              exact hsuccess ⟨htpos, hall⟩
            obtain ⟨i, hi⟩ := not_forall.mp hnall
            have hi' : t ^ 2 * (C.block i).card < Gamma :=
              Nat.lt_of_not_ge hi
            calc
              t ^ 2 * L ≤ t ^ 2 * (4 * (C.block i).card) :=
                Nat.mul_le_mul_left _ (hblock i)
              _ = 4 * (t ^ 2 * (C.block i).card) := by ring
              _ < 4 * Gamma :=
                (Nat.mul_lt_mul_left (by norm_num : 0 < 4)).2 hi'
        have hkt : k ≤ 11 * t := by
          simpa [t] using peeling_card_le_nine_good (G := G)
            hL hDeltaL S hseqdegree
        let Covered : Finset V := S.covered G
        let R : Finset V := S.remainder G
        have hcoveredCard : Covered.card ≤ k * Delta := by
          simpa [Covered] using S.covered_card_le G hseqdegree
        have hkSqL : k ^ 2 * L < 484 * Gamma := by
          calc
            k ^ 2 * L ≤ (11 * t) ^ 2 * L :=
              Nat.mul_le_mul_right L (Nat.pow_le_pow_left hkt 2)
            _ = 121 * (t ^ 2 * L) := by ring
            _ < 121 * (4 * Gamma) :=
              (Nat.mul_lt_mul_left (by norm_num : 0 < 121)).2 htL
            _ = 484 * Gamma := by ring
        have hkSqDelta : k ^ 2 * Delta ≤ 3872 * Gamma := by
          calc
            k ^ 2 * Delta ≤ k ^ 2 * (8 * L) :=
              Nat.mul_le_mul_left _ hDeltaL
            _ = 8 * (k ^ 2 * L) := by ring
            _ ≤ 8 * (484 * Gamma) :=
              Nat.mul_le_mul_left 8 (Nat.le_of_lt hkSqL)
            _ = 3872 * Gamma := by ring
        have hcoveredSq : Covered.card ^ 2 ≤ 3872 * Gamma * Delta := by
          calc
            Covered.card ^ 2 ≤ (k * Delta) ^ 2 :=
              Nat.pow_le_pow_left hcoveredCard 2
            _ = (k ^ 2 * Delta) * Delta := by ring
            _ ≤ (3872 * Gamma) * Delta :=
              Nat.mul_le_mul_right Delta hkSqDelta
        have hRsub : R ⊆ B := by
          intro x hx
          exact (Finset.mem_filter.mp hx).1
        have hAR : Disjoint A R := hAB.mono_right hRsub
        have hRcoverage : ∀ b ∈ R, ∃ a ∈ A, G.Adj a b := by
          intro b hb
          exact hcoverage b (hRsub hb)
        have hRdegree : ∀ a ∈ A,
            (R.filter fun b ↦ G.Adj a b).card ≤ L - 1 := by
          intro a haA
          have := hremdegree a haA
          simpa [R] using (show
            ((S.remainder G).filter fun b ↦ G.Adj a b).card ≤ L - 1 by omega)
        rcases ih (L - 1) hnext R hAR hRcoverage hRdegree with
          hcombR | hsmallR
        · left
          obtain ⟨t', C', ht', hblocks'⟩ := hcombR
          exact ⟨t', Lax54Proofs.BipartiteComb.CombBetween.mono_right G C' hRsub,
            ht', hblocks'⟩
        · right
          have hremSq : R.card ^ 2 ≤ 128 ^ 2 * Gamma * (L - 1) := hsmallR
          have hcoveredTwice :
              2 * Covered.card ^ 2 ≤ 7744 * Gamma * Delta := by
            calc
              2 * Covered.card ^ 2 ≤ 2 * (3872 * Gamma * Delta) :=
                Nat.mul_le_mul_left 2 hcoveredSq
              _ = 7744 * Gamma * Delta := by ring
          have hremTwice : 2 * R.card ^ 2 ≤ 4096 * Gamma * Delta := by
            calc
              2 * R.card ^ 2 ≤ 2 * (128 ^ 2 * Gamma * (L - 1)) :=
                Nat.mul_le_mul_left 2 hremSq
              _ = 4096 * Gamma * (8 * (L - 1)) := by norm_num; ring
              _ ≤ 4096 * Gamma * Delta :=
                Nat.mul_le_mul_left (4096 * Gamma) hnextScale
          have haddSquare : (Covered.card + R.card) ^ 2 ≤
              2 * Covered.card ^ 2 + 2 * R.card ^ 2 := by
            calc
              (Covered.card + R.card) ^ 2 =
                  Covered.card ^ 2 + R.card ^ 2 +
                    2 * Covered.card * R.card := by ring
              _ ≤ Covered.card ^ 2 + R.card ^ 2 +
                    (Covered.card ^ 2 + R.card ^ 2) :=
                Nat.add_le_add_left (two_mul_le_add_sq Covered.card R.card) _
              _ = 2 * Covered.card ^ 2 + 2 * R.card ^ 2 := by ring
          have hBcard : B.card = Covered.card + R.card := by
            simpa [Covered, R] using S.card_eq_covered_add_remainder G
          unfold SmallSideBound
          rw [hBcard]
          calc
            (Covered.card + R.card) ^ 2 ≤
                2 * Covered.card ^ 2 + 2 * R.card ^ 2 := haddSquare
            _ ≤ 7744 * Gamma * Delta + 4096 * Gamma * Delta :=
              Nat.add_le_add hcoveredTwice hremTwice
            _ = 11840 * Gamma * Delta := by ring
            _ ≤ 128 ^ 2 * Gamma * Delta := by
              norm_num
              exact Nat.mul_le_mul_right Delta (Nat.mul_le_mul_right Gamma (by omega))

end BipartiteComb

/--
---
conclusion: Lax54.BipartiteCombLemma.bipartite_comb_lemma
---
Proof of the $d=1/2$ case of Theorem 2.1. At each four-adic degree scale, a
maximal peeling sequence is pruned in reverse order to form a comb. If no
block has the required size, strong induction on the degree bound, together
with $(a+b)^2\leq 2a^2+2b^2$, yields the sparse alternative.
-/
theorem bipartite_comb_lemma :
    ∀ {V : Type u} [Fintype V] [DecidableEq V]
      (G : SimpleGraph V) [DecidableRel G.Adj]
      (A B : Finset V) (Gamma Delta : ℕ),
      Disjoint A B → 0 < Gamma →
      (∀ b ∈ B, ∃ a ∈ A, G.Adj a b) →
      (∀ a ∈ A, (B.filter fun b ↦ G.Adj a b).card ≤ Delta) →
      (∃ (t : ℕ) (Cmb : CombBetween G A B t),
          0 < t ∧ ∀ i : Fin t, Gamma ≤ t ^ 2 * (Cmb.block i).card) ∨
        SmallSideBound 128 Gamma Delta B.card := by
  intro V _ _ G _ A B Gamma Delta hAB hGamma hcoverage hdegree
  exact BipartiteComb.bipartite_comb_lemma_aux G A B Gamma Delta
    hAB hGamma hcoverage hdegree

end Lax54Proofs
