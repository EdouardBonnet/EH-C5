import Lax54.BipartiteCombLemma
import Lax54.KeyCombLemma
import Lax54Proofs.KappaBlocks
import Mathlib.Algebra.Order.Floor.Div
import Mathlib.Analysis.MeanInequalities
import Mathlib.Tactic

namespace Lax54Proofs

open Finset
open scoped BigOperators SimpleGraph
open Lax54.GraphDefinitions
open Lax54.BipartiteCombLemma
open Lax54.KeyCombLemma

universe u

namespace KeyComb

variable {V : Type u} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj]

/-- The neighbors of `v` in a specified finite vertex set. -/
def neighborsWithin (X : Finset V) (v : V) : Finset V :=
  X.filter fun x ↦ G.Adj v x

lemma neighborsWithin_card_eq_degree (X : Finset V) {v : V} (hv : v ∈ X) :
    (neighborsWithin G X v).card =
      (G.induce (X : Set V)).degree ⟨v, hv⟩ := by
  classical
  let e : {x : V // x ∈ X} ↪ V := ⟨Subtype.val, Subtype.val_injective⟩
  have heq : ((G.induce (X : Set V)).neighborFinset ⟨v, hv⟩).map e =
      neighborsWithin G X v := by
    ext x
    simp [neighborsWithin, e, and_comm]
  rw [← SimpleGraph.card_neighborFinset_eq_degree]
  simpa using (congrArg Finset.card heq).symm

/-- A maximum stable set in the subgraph induced by `A`, viewed in `V`. -/
noncomputable def maximumStableIn (A : Finset V) : Finset V :=
  let I : Finset {x : V // x ∈ A} :=
    Classical.choose (G.induce (A : Set V)).exists_isNIndepSet_indepNum
  I.map ⟨Subtype.val, Subtype.val_injective⟩

lemma maximumStableIn_subset (A : Finset V) : maximumStableIn G A ⊆ A := by
  classical
  intro x hx
  obtain ⟨x', -, rfl⟩ := Finset.mem_map.mp hx
  exact x'.property

lemma maximumStableIn_card (A : Finset V) :
    (maximumStableIn G A).card = (G.induce (A : Set V)).indepNum := by
  classical
  let I : Finset {x : V // x ∈ A} :=
    Classical.choose (G.induce (A : Set V)).exists_isNIndepSet_indepNum
  have hI : (G.induce (A : Set V)).IsNIndepSet
      (G.induce (A : Set V)).indepNum I :=
    Classical.choose_spec (G.induce (A : Set V)).exists_isNIndepSet_indepNum
  simpa [maximumStableIn, I] using hI.card_eq

lemma maximumStableIn_isIndep (A : Finset V) :
    G.IsIndepSet (maximumStableIn G A : Set V) := by
  classical
  let I : Finset {x : V // x ∈ A} :=
    Classical.choose (G.induce (A : Set V)).exists_isNIndepSet_indepNum
  have hI : (G.induce (A : Set V)).IsNIndepSet
      (G.induce (A : Set V)).indepNum I :=
    Classical.choose_spec (G.induce (A : Set V)).exists_isNIndepSet_indepNum
  intro x hx y hy hxy
  change x ∈ maximumStableIn G A at hx
  change y ∈ maximumStableIn G A at hy
  obtain ⟨x', hx', rfl⟩ := Finset.mem_map.mp hx
  obtain ⟨y', hy', rfl⟩ := Finset.mem_map.mp hy
  exact hI.isIndepSet hx' hy' (by simpa using hxy)

/--
The finite decomposition constructed in the proof of Lemma 3.1. Each layer
consists of a hub, its neighborhood `A`, a maximum stable set `C ⊆ A`, and
the vertices `D` reached from `C` outside the hub's neighborhood.
-/
structure CriticalPartition (q : ℕ) (X : Finset V) where
  s : ℕ
  hub : Fin s → V
  A : Fin s → Finset V
  C : Fin s → Finset V
  D : Fin s → Finset V
  hub_mem : ∀ i, hub i ∈ X
  A_subset : ∀ i, A i ⊆ X
  A_subset_neighbors : ∀ i, A i ⊆ neighborsWithin G X (hub i)
  C_subset_A : ∀ i, C i ⊆ A i
  D_subset : ∀ i, D i ⊆ X
  hub_injective : Function.Injective hub
  hubs_stable : ∀ {i j}, i ≠ j → ¬G.Adj (hub i) (hub j)
  C_disjoint : ∀ {i j}, i ≠ j → Disjoint (C i) (C j)
  C_stable : ∀ {i j} {x y : V}, x ∈ C i → y ∈ C j → x ≠ y → ¬G.Adj x y
  hub_adj_C : ∀ i, ∀ x ∈ C i, G.Adj (hub i) x
  hub_not_mem_D : ∀ i, hub i ∉ D i
  hub_nonadj_D : ∀ i, ∀ x ∈ D i, ¬G.Adj (hub i) x
  C_D_disjoint : ∀ i, Disjoint (C i) (D i)
  D_covered : ∀ i, ∀ x ∈ D i, ∃ c ∈ C i, G.Adj c x
  C_degree_D : ∀ i, ∀ c ∈ C i,
    ((D i).filter fun x ↦ G.Adj c x).card ≤ (A i).card
  A_power_bound : ∀ i, (A i).card ≤ (G.cliqueNum * (C i).card) ^ q
  card_partition : X.card = s + ∑ i : Fin s, ((A i).card + (D i).card)

/-- The empty vertex set has the empty critical partition. -/
def CriticalPartition.empty (q : ℕ) : CriticalPartition G q ∅ where
  s := 0
  hub := Fin.elim0
  A := Fin.elim0
  C := Fin.elim0
  D := Fin.elim0
  hub_mem := fun i ↦ Fin.elim0 i
  A_subset := fun i ↦ Fin.elim0 i
  A_subset_neighbors := fun i ↦ Fin.elim0 i
  C_subset_A := fun i ↦ Fin.elim0 i
  D_subset := fun i ↦ Fin.elim0 i
  hub_injective := fun i ↦ Fin.elim0 i
  hubs_stable := fun {i} ↦ Fin.elim0 i
  C_disjoint := fun {i} ↦ Fin.elim0 i
  C_stable := fun {i} ↦ Fin.elim0 i
  hub_adj_C := fun i ↦ Fin.elim0 i
  hub_not_mem_D := fun i ↦ Fin.elim0 i
  hub_nonadj_D := fun i ↦ Fin.elim0 i
  C_D_disjoint := fun i ↦ Fin.elim0 i
  D_covered := fun i ↦ Fin.elim0 i
  C_degree_D := fun i ↦ Fin.elim0 i
  A_power_bound := fun i ↦ Fin.elim0 i
  card_partition := by simp

/-- Every vertex set admits the iterative critical decomposition from Section 3. -/
theorem exists_criticalPartition (q : ℕ) (hcritical : IsQCritical q G)
    (X : Finset V) : Nonempty (CriticalPartition G q X) := by
  classical
  apply Finset.strongInduction (p := fun Y : Finset V ↦
    Nonempty (CriticalPartition G q Y))
  intro X ih
  ·
      by_cases hX : X = ∅
      · subst X
        exact ⟨CriticalPartition.empty G q⟩
      have hXne : X.Nonempty := Finset.nonempty_iff_ne_empty.mpr hX
      obtain ⟨v, hvX, hvmax⟩ :=
        Finset.exists_max_image X (fun x ↦ (neighborsWithin G X x).card) hXne
      let A : Finset V := neighborsWithin G X v
      let C : Finset V := maximumStableIn G A
      let X' : Finset V := X.filter fun x ↦
        x ≠ v ∧ ¬G.Adj v x ∧ ∀ c ∈ C, ¬G.Adj c x
      let U : Finset V := insert v (A ∪ X')
      let D : Finset V := X \ U
      have hAsub : A ⊆ X := by
        intro x hx
        exact (Finset.mem_filter.mp hx).1
      have hCsubA : C ⊆ A := maximumStableIn_subset G A
      have hX'sub : X' ⊆ X := by
        intro x hx
        exact (Finset.mem_filter.mp hx).1
      have hvnotA : v ∉ A := by
        intro hv
        exact G.loopless.irrefl v (Finset.mem_filter.mp hv).2
      have hvnotX' : v ∉ X' := by
        simp [X']
      have hAX' : Disjoint A X' := by
        rw [Finset.disjoint_left]
        intro x hxA hxX'
        exact (Finset.mem_filter.mp hxX').2.2.1 (Finset.mem_filter.mp hxA).2
      have hUsub : U ⊆ X := by
        intro x hx
        rcases Finset.mem_insert.mp hx with rfl | hx
        · exact hvX
        · rcases Finset.mem_union.mp hx with hxA | hxX'
          · exact hAsub hxA
          · exact hX'sub hxX'
      have hDsub : D ⊆ X := Finset.sdiff_subset
      have hX'ssubset : X' ⊂ X := by
        exact Finset.ssubset_iff_subset_ne.mpr ⟨hX'sub, fun heq ↦ hvnotX' (heq ▸ hvX)⟩
      let P : CriticalPartition G q X' := Classical.choice (ih X' hX'ssubset)
      have hCindep : G.IsIndepSet (C : Set V) := maximumStableIn_isIndep G A
      have hDnotU {x : V} (hx : x ∈ D) : x ∉ U := (Finset.mem_sdiff.mp hx).2
      have hDnotA {x : V} (hx : x ∈ D) : x ∉ A := by
        intro hxA
        exact hDnotU hx (Finset.mem_insert.mpr
          (Or.inr (Finset.mem_union.mpr (Or.inl hxA))))
      have hDnotv {x : V} (hx : x ∈ D) : x ≠ v := by
        intro h
        subst x
        exact hDnotU hx (Finset.mem_insert_self _ _)
      have hDnotX' {x : V} (hx : x ∈ D) : x ∉ X' := by
        intro hxX'
        exact hDnotU hx (Finset.mem_insert.mpr
          (Or.inr (Finset.mem_union.mpr (Or.inr hxX'))))
      have hDnonadj {x : V} (hx : x ∈ D) : ¬G.Adj v x := by
        intro hvx
        exact hDnotA hx (Finset.mem_filter.mpr ⟨hDsub hx, hvx⟩)
      have hDcovered {x : V} (hx : x ∈ D) : ∃ c ∈ C, G.Adj c x := by
        by_contra hn
        have hnone : ∀ c ∈ C, ¬G.Adj c x := by
          intro c hc hcx
          exact hn ⟨c, hc, hcx⟩
        exact hDnotX' hx (Finset.mem_filter.mpr
          ⟨hDsub hx, hDnotv hx, hDnonadj hx, hnone⟩)
      have hCD : Disjoint C D := by
        exact Finset.disjoint_left.mpr fun x hxC hxD ↦
          hDnotA hxD (hCsubA hxC)
      have hAproper : A.card < Fintype.card V := by
        rw [← Finset.card_univ]
        apply Finset.card_lt_card
        exact Finset.ssubset_iff_subset_ne.mpr
          ⟨hAsub.trans (Finset.subset_univ _), fun heq ↦ hvnotA (heq ▸ Finset.mem_univ v)⟩
      have hApower : A.card ≤ (G.cliqueNum * C.card) ^ q := by
        have hcriticalA := hcritical.2 A hAproper
        have hclique := cliqueNum_induce_finset_le G A
        calc
          A.card ≤ kappa (G.induce (A : Set V)) ^ q := hcriticalA
          _ = ((G.induce (A : Set V)).cliqueNum * C.card) ^ q := by
            rw [maximumStableIn_card (G := G) A]
            rfl
          _ ≤ (G.cliqueNum * C.card) ^ q :=
            Nat.pow_le_pow_left (Nat.mul_le_mul_right C.card hclique) q
      have hCdegree : ∀ c ∈ C,
          (D.filter fun x ↦ G.Adj c x).card ≤ A.card := by
        intro c hcC
        have hcX : c ∈ X := hAsub (hCsubA hcC)
        have hsubset : D.filter (fun x ↦ G.Adj c x) ⊆ neighborsWithin G X c := by
          intro x hx
          exact Finset.mem_filter.mpr
            ⟨hDsub (Finset.mem_filter.mp hx).1, (Finset.mem_filter.mp hx).2⟩
        calc
          (D.filter fun x ↦ G.Adj c x).card ≤ (neighborsWithin G X c).card :=
            Finset.card_le_card hsubset
          _ ≤ (neighborsWithin G X v).card := hvmax c hcX
          _ = A.card := rfl
      have hUcard : U.card = 1 + A.card + X'.card := by
        have hvnotUnion : v ∉ A ∪ X' := by simp [hvnotA, hvnotX']
        calc
          U.card = (A ∪ X').card + 1 := by
            simpa [U, hvnotUnion] using Finset.card_insert_of_not_mem hvnotUnion
          _ = (A.card + X'.card) + 1 := by
            rw [Finset.card_union_of_disjoint hAX']
          _ = 1 + A.card + X'.card := by omega
      have hDcard : X.card = 1 + A.card + D.card + X'.card := by
        have hpart := Finset.card_sdiff_add_card_eq_card hUsub
        change D.card + U.card = X.card at hpart
        omega
      let hub : Fin (P.s + 1) → V := Fin.cons v P.hub
      let Afun : Fin (P.s + 1) → Finset V := Fin.cons A P.A
      let Cfun : Fin (P.s + 1) → Finset V := Fin.cons C P.C
      let Dfun : Fin (P.s + 1) → Finset V := Fin.cons D P.D
      refine ⟨{
        s := P.s + 1
        hub := hub
        A := Afun
        C := Cfun
        D := Dfun
        hub_mem := ?_
        A_subset := ?_
        A_subset_neighbors := ?_
        C_subset_A := ?_
        D_subset := ?_
        hub_injective := ?_
        hubs_stable := ?_
        C_disjoint := ?_
        C_stable := ?_
        hub_adj_C := ?_
        hub_not_mem_D := ?_
        hub_nonadj_D := ?_
        C_D_disjoint := ?_
        D_covered := ?_
        C_degree_D := ?_
        A_power_bound := ?_
        card_partition := ?_ }⟩
      · intro i
        refine Fin.cases ?_ (fun j ↦ ?_) i
        · simpa [hub] using hvX
        · exact hX'sub (by simpa [hub] using P.hub_mem j)
      · intro i
        refine Fin.cases ?_ (fun j ↦ ?_) i
        · exact hAsub
        · exact (P.A_subset j).trans hX'sub
      · intro i
        cases i using Fin.cases with
        | zero =>
            intro x hx
            simpa [Afun, A, hub] using hx
        | succ j =>
            intro x hx
            have hx' := P.A_subset_neighbors j hx
            exact Finset.mem_filter.mpr
              ⟨hX'sub (Finset.mem_filter.mp hx').1,
                (Finset.mem_filter.mp hx').2⟩
      · intro i
        refine Fin.cases ?_ (fun j ↦ ?_) i
        · exact hCsubA
        · exact P.C_subset_A j
      · intro i
        refine Fin.cases ?_ (fun j ↦ ?_) i
        · exact hDsub
        · exact (P.D_subset j).trans hX'sub
      · intro i j heq
        cases i using Fin.cases with
        | zero =>
            cases j using Fin.cases with
            | zero => rfl
            | succ j =>
                exfalso
                have hvj : v = P.hub j := by simpa [hub] using heq
                exact hvnotX' (hvj ▸ P.hub_mem j)
        | succ i =>
            cases j using Fin.cases with
            | zero =>
                exfalso
                have hiv : P.hub i = v := by simpa [hub] using heq
                exact hvnotX' (hiv ▸ P.hub_mem i)
            | succ j =>
                exact congrArg Fin.succ (P.hub_injective (by simpa [hub] using heq))
      · intro i j hij
        cases i using Fin.cases with
        | zero =>
            cases j using Fin.cases with
            | zero => exact (hij rfl).elim
            | succ j =>
                simpa [hub] using (Finset.mem_filter.mp (P.hub_mem j)).2.2.1
        | succ i =>
            cases j using Fin.cases with
            | zero =>
                simpa [hub, G.adj_comm] using
                  (Finset.mem_filter.mp (P.hub_mem i)).2.2.1
            | succ j =>
                exact P.hubs_stable (fun h ↦ hij (congrArg Fin.succ h))
      · intro i j hij
        cases i using Fin.cases with
        | zero =>
            cases j using Fin.cases with
            | zero => exact (hij rfl).elim
            | succ j =>
                simpa [Cfun] using
                  hAX'.mono hCsubA (P.C_subset_A j |>.trans (P.A_subset j))
        | succ i =>
            cases j using Fin.cases with
            | zero =>
                simpa [Cfun] using
                  (hAX'.mono hCsubA (P.C_subset_A i |>.trans (P.A_subset i))).symm
            | succ j =>
                exact P.C_disjoint (fun h ↦ hij (congrArg Fin.succ h))
      · intro i j x y hx hy hxy
        cases i using Fin.cases with
        | zero =>
            cases j using Fin.cases with
            | zero =>
                exact hCindep (by simpa [Cfun] using hx)
                  (by simpa [Cfun] using hy) hxy
            | succ j =>
                have hy' : y ∈ P.C j := by simpa [Cfun] using hy
                have hx' : x ∈ C := by simpa [Cfun] using hx
                exact (Finset.mem_filter.mp
                  ((P.C_subset_A j |>.trans (P.A_subset j)) hy')).2.2.2 x hx'
        | succ i =>
            cases j using Fin.cases with
            | zero =>
                have hx' : x ∈ P.C i := by simpa [Cfun] using hx
                have hy' : y ∈ C := by simpa [Cfun] using hy
                simpa [G.adj_comm] using
                  (Finset.mem_filter.mp
                    ((P.C_subset_A i |>.trans (P.A_subset i)) hx')).2.2.2 y hy'
            | succ j =>
                exact P.C_stable (by simpa [Cfun] using hx)
                  (by simpa [Cfun] using hy) hxy
      · intro i x hx
        cases i using Fin.cases with
        | zero => exact (Finset.mem_filter.mp (hCsubA (by simpa [Cfun] using hx))).2
        | succ j => exact P.hub_adj_C j x (by simpa [Cfun] using hx)
      · intro i
        cases i using Fin.cases with
        | zero => exact fun hx ↦ hDnotv hx rfl
        | succ j => exact P.hub_not_mem_D j
      · intro i x hx
        cases i using Fin.cases with
        | zero => exact hDnonadj (by simpa [Dfun] using hx)
        | succ j => exact P.hub_nonadj_D j x (by simpa [Dfun] using hx)
      · intro i
        refine Fin.cases ?_ (fun j ↦ ?_) i
        · exact hCD
        · exact P.C_D_disjoint j
      · intro i x hx
        cases i using Fin.cases with
        | zero => exact hDcovered (by simpa [Dfun] using hx)
        | succ j => exact P.D_covered j x (by simpa [Dfun] using hx)
      · intro i c hc
        cases i using Fin.cases with
        | zero =>
            simpa [Cfun, Dfun, Afun] using hCdegree c (by simpa [Cfun] using hc)
        | succ j =>
            simpa [Cfun, Dfun, Afun] using
              P.C_degree_D j c (by simpa [Cfun] using hc)
      · intro i
        refine Fin.cases ?_ (fun j ↦ ?_) i
        · exact hApower
        · exact P.A_power_bound j
      · rw [hDcard, P.card_partition]
        simp [Afun, Dfun, Fin.sum_univ_succ]
        omega

/-- The hubs form a stable set, so there are at most `α(G)` layers. -/
lemma CriticalPartition.s_le_indepNum {q : ℕ} {X : Finset V}
    (P : CriticalPartition G q X) : P.s ≤ G.indepNum := by
  classical
  let H : Finset V := Finset.univ.map ⟨P.hub, P.hub_injective⟩
  have hH : G.IsIndepSet (H : Set V) := by
    intro x hx y hy hxy
    change x ∈ H at hx
    change y ∈ H at hy
    obtain ⟨i, -, rfl⟩ := Finset.mem_map.mp hx
    obtain ⟨j, -, rfl⟩ := Finset.mem_map.mp hy
    exact P.hubs_stable (fun h ↦ hxy (congrArg P.hub h))
  calc
    P.s = H.card := by simp [H]
    _ ≤ G.indepNum := hH.card_le_indepNum

/-- The stable sets chosen in all layers have total size at most `α(G)`. -/
lemma CriticalPartition.sum_C_le_indepNum {q : ℕ} {X : Finset V}
    (P : CriticalPartition G q X) :
    ∑ i : Fin P.s, (P.C i).card ≤ G.indepNum := by
  classical
  let U : Finset V := Finset.univ.biUnion P.C
  have hpair : Set.PairwiseDisjoint
      (↑(Finset.univ : Finset (Fin P.s)) : Set (Fin P.s)) P.C := by
    intro i _ j _ hij
    exact P.C_disjoint hij
  have hU : G.IsIndepSet (U : Set V) := by
    intro x hx y hy hxy
    change x ∈ U at hx
    change y ∈ U at hy
    obtain ⟨i, -, hxi⟩ := Finset.mem_biUnion.mp hx
    obtain ⟨j, -, hyj⟩ := Finset.mem_biUnion.mp hy
    exact P.C_stable hxi hyj hxy
  calc
    ∑ i : Fin P.s, (P.C i).card = U.card := by
      symm
      simpa [U] using Finset.card_biUnion hpair
    _ ≤ G.indepNum := hU.card_le_indepNum

/-- Taking `q`th roots in the critical bounds and summing over the layers. -/
lemma CriticalPartition.sum_A_rpow_le_kappa {q : ℕ} {X : Finset V}
    (hq : q ≠ 0) (P : CriticalPartition G q X) :
    ∑ i : Fin P.s, ((P.A i).card : ℝ) ^ ((q : ℝ)⁻¹) ≤ (kappa G : ℝ) := by
  have hone (i : Fin P.s) :
      ((P.A i).card : ℝ) ^ ((q : ℝ)⁻¹) ≤
        (G.cliqueNum : ℝ) * (P.C i).card := by
    have hcast : ((P.A i).card : ℝ) ≤
        (((G.cliqueNum * (P.C i).card) ^ q : ℕ) : ℝ) := by
      exact_mod_cast P.A_power_bound i
    calc
      ((P.A i).card : ℝ) ^ ((q : ℝ)⁻¹) ≤
          ((((G.cliqueNum * (P.C i).card) ^ q : ℕ) : ℝ)) ^ ((q : ℝ)⁻¹) :=
        Real.rpow_le_rpow (by positivity) hcast (by positivity)
      _ = ((G.cliqueNum * (P.C i).card : ℕ) : ℝ) := by
        rw [Nat.cast_pow, Real.pow_rpow_inv_natCast (by positivity) hq]
      _ = (G.cliqueNum : ℝ) * (P.C i).card := by norm_cast
  calc
    ∑ i : Fin P.s, ((P.A i).card : ℝ) ^ ((q : ℝ)⁻¹) ≤
        ∑ i : Fin P.s, (G.cliqueNum : ℝ) * (P.C i).card :=
      Finset.sum_le_sum fun i _ ↦ hone i
    _ = (G.cliqueNum : ℝ) * ∑ i : Fin P.s, ((P.C i).card : ℝ) := by
      rw [Finset.mul_sum]
    _ = (G.cliqueNum : ℝ) * (∑ i : Fin P.s, (P.C i).card : ℕ) := by
      norm_cast
    _ ≤ (G.cliqueNum : ℝ) * G.indepNum := by
      gcongr
      exact_mod_cast P.sum_C_le_indepNum G
    _ = (kappa G : ℝ) := by norm_cast

/-- The integral ceiling used as `Γ` in the bipartite lemma. -/
def gammaParameter (E x : ℕ) : ℕ :=
  (E * x) ⌈/⌉ keyCombConstant

lemma keyCombConstant_pos : 0 < keyCombConstant := by
  norm_num [keyCombConstant]

lemma gammaParameter_pos {E x : ℕ} (hE : 0 < E) (hx : 0 < x) :
    0 < gammaParameter E x := by
  have hK := keyCombConstant_pos
  have hle : E * x ≤ keyCombConstant * gammaParameter E x := by
    unfold gammaParameter
    exact (ceilDiv_le_iff_le_mul hK).mp le_rfl
  by_contra h
  have : gammaParameter E x = 0 := Nat.eq_zero_of_not_pos h
  rw [this] at hle
  have hzero : E * x = 0 := by simpa using hle
  exact (Nat.mul_pos hE hx).ne' hzero

lemma le_mul_gammaParameter (E x : ℕ) :
    E * x ≤ keyCombConstant * gammaParameter E x := by
  have hK := keyCombConstant_pos
  unfold gammaParameter
  exact (ceilDiv_le_iff_le_mul hK).mp le_rfl

lemma mul_gammaParameter_le_two_mul {E x : ℕ}
    (hK_E : keyCombConstant ≤ E) (hx : 0 < x) :
    keyCombConstant * gammaParameter E x ≤ 2 * E * x := by
  have hK := keyCombConstant_pos
  have hKa : keyCombConstant ≤ E * x := by
    exact hK_E.trans (Nat.le_mul_of_pos_right E hx)
  have hceil : gammaParameter E x ≤ E * x / keyCombConstant + 1 := by
    unfold gammaParameter
    rw [Nat.ceilDiv_eq_add_pred_div]
    calc
      (E * x + keyCombConstant - 1) / keyCombConstant ≤
          (E * x + keyCombConstant) / keyCombConstant :=
        Nat.div_le_div_right (Nat.sub_le _ _)
      _ = E * x / keyCombConstant + 1 := by
        simpa [add_comm] using Nat.add_mul_div_left (E * x) 1 hK
  calc
    keyCombConstant * gammaParameter E x ≤
        keyCombConstant * (E * x / keyCombConstant + 1) :=
      Nat.mul_le_mul_left _ hceil
    _ = keyCombConstant * (E * x / keyCombConstant) + keyCombConstant := by ring
    _ ≤ E * x + keyCombConstant :=
      Nat.add_le_add_right (Nat.mul_div_le _ _) _
    _ ≤ 2 * E * x := by
      calc
        E * x + keyCombConstant ≤ E * x + E * x :=
          Nat.add_le_add_left hKa _
        _ = 2 * E * x := by ring

/-- A comb returned in one layer, equipped with that layer's stable teeth and hub. -/
def CriticalPartition.stableHubCombOfBetween {q : ℕ} {X : Finset V}
    (P : CriticalPartition G q X) (i : Fin P.s) {t : ℕ}
    (Cmb : CombBetween G (P.C i) (P.D i) t) : StableHubComb G t where
  tooth := Cmb.tooth
  block := Cmb.block
  hub := P.hub i
  tooth_injective := Cmb.tooth_injective
  blocks_disjoint := Cmb.blocks_disjoint
  tooth_not_mem j k hx :=
    Finset.disjoint_left.mp (P.C_D_disjoint i) (Cmb.tooth_mem j)
      (Cmb.block_subset k hx)
  hub_not_mem j hx := P.hub_not_mem_D i (Cmb.block_subset j hx)
  tooth_adj_block := Cmb.tooth_adj_block
  tooth_nonadj_other := Cmb.tooth_nonadj_other
  teeth_stable hij := P.C_stable (Cmb.tooth_mem _) (Cmb.tooth_mem _)
    (Cmb.tooth_injective.ne hij)
  hub_adj_tooth j := P.hub_adj_C i _ (Cmb.tooth_mem j)
  hub_nonadj_block j x hx := P.hub_nonadj_D i x (Cmb.block_subset j hx)

/-- Disjoint comb blocks imply the required lower bound on the number of teeth. -/
lemma teeth_large_of_blocks {q : ℕ} {X : Finset V}
    (P : CriticalPartition G q X) (i : Fin P.s) {E t : ℕ}
    (hxpos : 0 < X.card) (ht : 0 < t)
    (Cmb : CombBetween G (P.C i) (P.D i) t)
    (hblocks : ∀ j : Fin t,
      gammaParameter E X.card ≤ t ^ 2 * (Cmb.block j).card) :
    E ≤ keyCombConstant * t := by
  have hblocksum : ∑ j : Fin t, (Cmb.block j).card ≤ X.card := by
    let U : Finset V := Finset.univ.biUnion Cmb.block
    have hpair : Set.PairwiseDisjoint
        (↑(Finset.univ : Finset (Fin t)) : Set (Fin t)) Cmb.block := by
      intro a _ b _ hab
      exact Cmb.blocks_disjoint hab
    have hUsub : U ⊆ X := by
      intro x hx
      obtain ⟨j, -, hxj⟩ := Finset.mem_biUnion.mp hx
      exact P.D_subset i (Cmb.block_subset j hxj)
    calc
      ∑ j : Fin t, (Cmb.block j).card = U.card := by
        symm
        simpa [U] using Finset.card_biUnion hpair
      _ ≤ X.card := Finset.card_le_card hUsub
  have hsum : t * gammaParameter E X.card ≤
      t ^ 2 * ∑ j : Fin t, (Cmb.block j).card := by
    calc
      t * gammaParameter E X.card =
          ∑ _j : Fin t, gammaParameter E X.card := by simp
      _ ≤ ∑ j : Fin t, t ^ 2 * (Cmb.block j).card :=
        Finset.sum_le_sum fun j _ ↦ hblocks j
      _ = t ^ 2 * ∑ j : Fin t, (Cmb.block j).card := by
        rw [Finset.mul_sum]
  have hmain : t * (E * X.card) ≤ t ^ 2 * (keyCombConstant * X.card) := by
    calc
      t * (E * X.card) ≤
          t * (keyCombConstant * gammaParameter E X.card) :=
        Nat.mul_le_mul_left t (le_mul_gammaParameter E X.card)
      _ = keyCombConstant *
          (t * gammaParameter E X.card) := by ring
      _ ≤ keyCombConstant *
          (t ^ 2 * ∑ j : Fin t, (Cmb.block j).card) :=
        Nat.mul_le_mul_left keyCombConstant hsum
      _ ≤ keyCombConstant * (t ^ 2 * X.card) :=
        Nat.mul_le_mul_left keyCombConstant
          (Nat.mul_le_mul_left (t ^ 2) hblocksum)
      _ = t ^ 2 * (keyCombConstant * X.card) := by ring
  have hcancelX : t * E ≤ t ^ 2 * keyCombConstant := by
    apply Nat.le_of_mul_le_mul_right (c := X.card) (hc := hxpos)
    simpa [mul_assoc, mul_left_comm, mul_comm] using hmain
  apply Nat.le_of_mul_le_mul_left (c := t) (hc := ht)
  simpa [pow_two, mul_assoc, mul_left_comm, mul_comm] using hcancelX

/-- Normalize the critical layer bounds by the size of `X`. -/
lemma CriticalPartition.sum_normalized_A_rpow_le {q D : ℕ} {X : Finset V}
    (hq : 0 < q) (P : CriticalPartition G q X)
    (hcritical : IsQCritical q G) (hX : 0 < X.card)
    (hdense : Fintype.card V ≤ D * X.card) :
    ∑ i : Fin P.s,
        (((P.A i).card : ℝ) / X.card) ^ ((q : ℝ)⁻¹) ≤
      (D : ℝ) ^ ((q : ℝ)⁻¹) := by
  have hsum : ∑ i : Fin P.s, ((P.A i).card : ℝ) ^ ((q : ℝ)⁻¹) ≤
      (kappa G : ℝ) := P.sum_A_rpow_le_kappa G hq.ne'
  have hXrpos : 0 < (X.card : ℝ) ^ ((q : ℝ)⁻¹) :=
    Real.rpow_pos_of_pos (by positivity) _
  have hnormalized :
      ∑ i : Fin P.s,
          (((P.A i).card : ℝ) / X.card) ^ ((q : ℝ)⁻¹) =
        (∑ i : Fin P.s, ((P.A i).card : ℝ) ^ ((q : ℝ)⁻¹)) /
          (X.card : ℝ) ^ ((q : ℝ)⁻¹) := by
    simp_rw [Real.div_rpow (Nat.cast_nonneg _) (Nat.cast_nonneg _)]
    simpa using (Finset.sum_div
      (s := (Finset.univ : Finset (Fin P.s)))
      (f := fun i ↦ ((P.A i).card : ℝ) ^ ((q : ℝ)⁻¹))
      (a := (X.card : ℝ) ^ ((q : ℝ)⁻¹))).symm
  rw [hnormalized]
  apply (div_le_iff₀ hXrpos).mpr
  calc
    ∑ i : Fin P.s, ((P.A i).card : ℝ) ^ ((q : ℝ)⁻¹) ≤
        (kappa G : ℝ) := hsum
    _ ≤ (Fintype.card V : ℝ) ^ ((q : ℝ)⁻¹) := by
      have hpow : ((kappa G : ℝ) ^ q) < Fintype.card V := by
        exact_mod_cast hcritical.1
      calc
        (kappa G : ℝ) = ((kappa G : ℝ) ^ q) ^ ((q : ℝ)⁻¹) := by
          rw [Real.pow_rpow_inv_natCast (by positivity) hq.ne']
        _ ≤ (Fintype.card V : ℝ) ^ ((q : ℝ)⁻¹) :=
          Real.rpow_le_rpow (by positivity) hpow.le (by positivity)
    _ ≤ ((D * X.card : ℕ) : ℝ) ^ ((q : ℝ)⁻¹) :=
      Real.rpow_le_rpow (by positivity) (by exact_mod_cast hdense) (by positivity)
    _ = (D : ℝ) ^ ((q : ℝ)⁻¹) *
        (X.card : ℝ) ^ ((q : ℝ)⁻¹) := by
      rw [Nat.cast_mul, Real.mul_rpow (by positivity) (by positivity)]

/-- Elementary interpolation between the `1/q` moment and a larger moment. -/
lemma sum_rpow_le_of_le {ι : Type*} [Fintype ι]
    (f : ι → ℝ) {q : ℕ} (hq : 2 ≤ q) {M B : ℝ}
    (hM : 0 < M) (hf0 : ∀ i, 0 ≤ f i) (hfM : ∀ i, f i ≤ M)
    (hsum : ∑ i, f i ^ ((q : ℝ)⁻¹) ≤ B)
    {r : ℝ} (hr : (q : ℝ)⁻¹ ≤ r) :
    ∑ i, f i ^ r ≤ M ^ (r - (q : ℝ)⁻¹) * B := by
  have hexp : 0 ≤ r - (q : ℝ)⁻¹ := sub_nonneg.mpr hr
  have hqinvpos : 0 < (q : ℝ)⁻¹ := by positivity
  have hrpos : 0 < r := hqinvpos.trans_le hr
  calc
    ∑ i, f i ^ r = ∑ i, f i ^ ((q : ℝ)⁻¹) *
        f i ^ (r - (q : ℝ)⁻¹) := by
      apply Finset.sum_congr rfl
      intro i _
      by_cases hfi : f i = 0
      · rw [hfi, Real.zero_rpow hrpos.ne', Real.zero_rpow hqinvpos.ne']
        simp
      · rw [← Real.rpow_add (lt_of_le_of_ne (hf0 i) (Ne.symm hfi))]
        congr 1
        ring
    _ ≤ ∑ i, f i ^ ((q : ℝ)⁻¹) * M ^ (r - (q : ℝ)⁻¹) := by
      apply Finset.sum_le_sum
      intro i _
      exact mul_le_mul_of_nonneg_left
        (Real.rpow_le_rpow (hf0 i) (hfM i) hexp)
        (Real.rpow_nonneg (hf0 i) _)
    _ = M ^ (r - (q : ℝ)⁻¹) * ∑ i, f i ^ ((q : ℝ)⁻¹) := by
      rw [Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro i _
      ring
    _ ≤ M ^ (r - (q : ℝ)⁻¹) * B := by
      gcongr

/-- A power-of-two bound for the root that occurs in Section 3. -/
lemma product_root_le_two {q E D : ℕ} (hq : 0 < q)
    (hED : E * D ≤ 2 ^ q) :
    (((E : ℝ) * D) ^ (q : ℝ)⁻¹ ≤ 2) := by
  have hcast : (E : ℝ) * D ≤ (2 : ℝ) ^ q := by
    exact_mod_cast hED
  calc
    ((E : ℝ) * D) ^ (q : ℝ)⁻¹ ≤
        ((2 : ℝ) ^ q) ^ (q : ℝ)⁻¹ :=
      Real.rpow_le_rpow (by positivity) hcast (by positivity)
    _ = 2 := Real.pow_rpow_inv_natCast (by positivity) hq.ne'

/-- Algebraic cancellation in the estimate for the `A_i` layers. -/
lemma inv_rpow_factor_one {q : ℕ} {E D : ℝ}
    (hE : 0 < E) (hD : 0 < D) :
    E⁻¹ ^ (1 - (q : ℝ)⁻¹) * D ^ (q : ℝ)⁻¹ =
      (E * D) ^ (q : ℝ)⁻¹ / E := by
  rw [Real.inv_rpow hE.le, ← Real.rpow_neg hE.le]
  rw [show -(1 - (q : ℝ)⁻¹) = (q : ℝ)⁻¹ - 1 by ring]
  rw [Real.rpow_sub hE, Real.mul_rpow hE.le hD.le, Real.rpow_one]
  ring

/-- Algebraic cancellation in the square-root estimate for the `D_i` layers. -/
lemma sqrt_inv_rpow_factor {q : ℕ} {E D K : ℝ}
    (hE : 0 < E) (hD : 0 < D) (hK : 0 < K) :
    √(2 * E / K) *
        (E⁻¹ ^ ((1 / 2 : ℝ) - (q : ℝ)⁻¹) * D ^ (q : ℝ)⁻¹) =
      √(2 / K) * (E * D) ^ (q : ℝ)⁻¹ := by
  simp_rw [Real.sqrt_eq_rpow]
  rw [Real.div_rpow (by positivity : 0 ≤ (2 : ℝ) * E) hK.le]
  rw [Real.mul_rpow (by positivity : 0 ≤ (2 : ℝ)) hE.le]
  rw [Real.inv_rpow hE.le, ← Real.rpow_neg hE.le]
  rw [show -((1 / 2 : ℝ) - (q : ℝ)⁻¹) =
      (q : ℝ)⁻¹ - (1 / 2 : ℝ) by ring]
  rw [Real.mul_rpow hE.le hD.le]
  rw [Real.div_rpow (by positivity : 0 ≤ (2 : ℝ)) hK.le]
  have hcombine : E ^ (1 / 2 : ℝ) *
      E ^ ((q : ℝ)⁻¹ - (1 / 2 : ℝ)) = E ^ (q : ℝ)⁻¹ := by
    rw [← Real.rpow_add hE]
    congr 1
    ring
  calc
    (2 ^ (1 / 2 : ℝ) * E ^ (1 / 2 : ℝ) / K ^ (1 / 2 : ℝ)) *
          (E ^ ((q : ℝ)⁻¹ - (1 / 2 : ℝ)) * D ^ (q : ℝ)⁻¹) =
        (2 ^ (1 / 2 : ℝ) / K ^ (1 / 2 : ℝ)) *
          ((E ^ (1 / 2 : ℝ) * E ^ ((q : ℝ)⁻¹ - (1 / 2 : ℝ))) *
            D ^ (q : ℝ)⁻¹) := by ring
    _ = (2 ^ (1 / 2 : ℝ) / K ^ (1 / 2 : ℝ)) *
          (E ^ (q : ℝ)⁻¹ * D ^ (q : ℝ)⁻¹) := by rw [hcombine]

/-- The cleared-square alternative, normalized by `|X|`. -/
lemma normalized_small_side {d gamma a E X K : ℕ}
    (hX : 0 < X) (hK : 0 < K)
    (hsmall : d ^ 2 ≤ 128 ^ 2 * gamma * a)
    (hgamma : K * gamma ≤ 2 * E * X) :
    (d : ℝ) / X ≤
      128 * √((2 * (E : ℝ) / K) * ((a : ℝ) / X)) := by
  have hcombined : K * d ^ 2 ≤ 128 ^ 2 * (2 * E * X) * a := by
    calc
      K * d ^ 2 ≤ K * (128 ^ 2 * gamma * a) := Nat.mul_le_mul_left K hsmall
      _ = 128 ^ 2 * (K * gamma) * a := by ring
      _ ≤ 128 ^ 2 * (2 * E * X) * a := by gcongr
  have hcombinedR : (K : ℝ) * (d : ℝ) ^ 2 ≤
      128 ^ 2 * (2 * (E : ℝ) * X) * a := by
    exact_mod_cast hcombined
  have hz : 0 ≤ (2 * (E : ℝ) / K) * ((a : ℝ) / X) := by positivity
  have hsq : ((d : ℝ) / X) ^ 2 ≤
      128 ^ 2 * ((2 * (E : ℝ) / K) * ((a : ℝ) / X)) := by
    field_simp
    nlinarith
  have hsqrt := Real.sq_sqrt hz
  have hleft : 0 ≤ (d : ℝ) / X := by positivity
  have hright : 0 ≤
      128 * √((2 * (E : ℝ) / K) * ((a : ℝ) / X)) := by positivity
  rw [← sq_le_sq₀ hleft hright]
  nlinarith

/-- A critical finite graph with positive exponent has `κ(G) ≥ 2`. -/
lemma two_le_kappa_of_critical {q : ℕ} (hq : 0 < q)
    (hcritical : IsQCritical q G) : 2 ≤ kappa G := by
  have hVpos : 0 < Fintype.card V := Nat.zero_lt_of_lt hcritical.1
  let v : V := Classical.choice (Fintype.card_pos_iff.mp hVpos)
  have hclique : 1 ≤ G.cliqueNum := by
    have hs : G.IsClique ({v} : Finset V) := by simp
    simpa using hs.card_le_cliqueNum
  have hindep : 1 ≤ G.indepNum := by
    have hs : G.IsIndepSet ({v} : Finset V) := by simp
    simpa using hs.card_le_indepNum
  have hkappa : 1 ≤ kappa G := by
    simpa [kappa] using Nat.mul_le_mul hclique hindep
  have hVtwo : 1 < Fintype.card V := by
    have hpow : 1 ≤ kappa G ^ q := Nat.one_le_pow q _ hkappa
    exact lt_of_le_of_lt hpow hcritical.1
  obtain ⟨a, b, hab⟩ := Fintype.one_lt_card_iff.mp hVtwo
  by_cases hadj : G.Adj a b
  · have hpair : G.IsClique ({a, b} : Finset V) := by
      simpa [SimpleGraph.isClique_pair, hab] using hadj
    have htwo : 2 ≤ G.cliqueNum := by
      simpa [Finset.card_pair hab] using hpair.card_le_cliqueNum
    simpa [kappa] using Nat.mul_le_mul htwo hindep
  · have hpair : G.IsIndepSet ({a, b} : Finset V) := by
      intro x hx y hy hxy hxyadj
      simp only [Finset.coe_insert, Finset.coe_singleton, Set.mem_insert_iff,
        Set.mem_singleton_iff] at hx hy
      rcases hx with rfl | rfl <;> rcases hy with rfl | rfl
      · exact hxy rfl
      · exact hadj hxyadj
      · exact hadj (G.adj_comm _ _ |>.mp hxyadj)
      · exact hxy rfl
    have htwo : 2 ≤ G.indepNum := by
      simpa [Finset.card_pair hab] using hpair.card_le_indepNum
    simpa [kappa] using Nat.mul_le_mul hclique htwo

/-- The stable hubs occupy less than one eighth of `X` for the chosen exponent. -/
lemma CriticalPartition.eight_mul_s_lt {q D : ℕ} {X : Finset V}
    (hq : 1 ≤ q) (P : CriticalPartition G q X)
    (hcritical : IsQCritical q G) (hD : 0 < D)
    (hdense : Fintype.card V ≤ D * X.card)
    (hpow : 16 * D ≤ 2 ^ q) : 8 * P.s < X.card := by
  have hkappa : 2 ≤ kappa G := two_le_kappa_of_critical G (by omega) hcritical
  have hclique : 1 ≤ G.cliqueNum := by
    rw [kappa] at hkappa
    by_contra h
    have : G.cliqueNum = 0 := by omega
    simp [this] at hkappa
  have hsK : P.s ≤ kappa G := by
    calc
      P.s ≤ G.indepNum := P.s_le_indepNum G
      _ = 1 * G.indepNum := by simp
      _ ≤ G.cliqueNum * G.indepNum := Nat.mul_le_mul_right _ hclique
      _ = kappa G := rfl
  have hqsplit : q - 1 + 1 = q := by omega
  have hpowK : kappa G * 2 ^ (q - 1) ≤ kappa G ^ q := by
    calc
      kappa G * 2 ^ (q - 1) ≤ kappa G * kappa G ^ (q - 1) := by
        exact Nat.mul_le_mul_left _ (Nat.pow_le_pow_left hkappa (q - 1))
      _ = kappa G ^ ((q - 1) + 1) := by rw [pow_succ']
      _ = kappa G ^ q := by rw [hqsplit]
  have hhalf : 8 * D ≤ 2 ^ (q - 1) := by
    have hrewrite : 2 ^ q = 2 * 2 ^ (q - 1) := by
      conv_lhs => rw [← hqsplit]
      rw [pow_succ']
    rw [hrewrite] at hpow
    omega
  have hmul : D * (8 * P.s) < D * X.card := by
    calc
      D * (8 * P.s) = P.s * (8 * D) := by ring
      _ ≤ P.s * 2 ^ (q - 1) := Nat.mul_le_mul_left P.s hhalf
      _ ≤ kappa G * 2 ^ (q - 1) := Nat.mul_le_mul_right _ hsK
      _ ≤ kappa G ^ q := hpowK
      _ < Fintype.card V := hcritical.1
      _ ≤ D * X.card := hdense
  exact Nat.lt_of_mul_lt_mul_left hmul

end KeyComb

open KeyComb

/--
---
conclusion: Lax54.KeyCombLemma.key_comb_lemma
assumptions:
  - Lax54.BipartiteCombLemma.bipartite_comb_lemma
---
Proof of Lemma 3.1. Decompose the prescribed vertex set into the critical
layers used in the paper and apply the $d=1/2$ bipartite comb lemma to each
layer. If no layer yields a comb, normalized estimates for the hubs, their
neighborhoods, and the covered residual sets contradict the partition
identity.
-/
theorem key_comb_lemma :
    ∀ E D Q : ℕ, keySparsityThreshold ≤ E → 0 < D →
      ∃ q : ℕ, 3 ≤ q ∧ Q ≤ q ∧
        ∀ {V : Type u} [Fintype V] [DecidableEq V]
          (G : SimpleGraph V) [DecidableRel G.Adj] (X : Finset V),
          IsQCritical q G →
          Fintype.card V ≤ D * X.card →
          (∀ x : {v : V // v ∈ X},
            E * (G.induce (X : Set V)).degree x < X.card) →
          ∃ (t : ℕ) (C : StableHubComb G t),
            E ≤ keyCombConstant * t ∧
              ∀ i : Fin t,
                E * X.card ≤ keyCombConstant * t ^ 2 * (C.block i).card := by
  intro E D Q hEthresh hD
  let N := max (E * D) (16 * D)
  obtain ⟨q₀, hq₀⟩ :=
    pow_unbounded_of_one_lt N (by norm_num : (1 : ℕ) < 2)
  let q := max (max 3 Q) q₀
  have hq₀q : q₀ ≤ q := le_max_right _ _
  have hNpow : N ≤ 2 ^ q := by
    exact hq₀.le.trans (Nat.pow_le_pow_right (by omega) hq₀q)
  have hEDpow : E * D ≤ 2 ^ q := (le_max_left _ _).trans hNpow
  have hDpow : 16 * D ≤ 2 ^ q := (le_max_right _ _).trans hNpow
  have hq3 : 3 ≤ q := le_max_left 3 Q |>.trans (le_max_left _ _)
  have hQq : Q ≤ q := le_max_right 3 Q |>.trans (le_max_left _ _)
  refine ⟨q, hq3, hQq, ?_⟩
  intro V _ _ G _ X hcritical hdense hdegree
  have hX : 0 < X.card := by
    have hV : 0 < Fintype.card V := Nat.zero_lt_of_lt hcritical.1
    by_contra hn
    have hx0 : X.card = 0 := Nat.eq_zero_of_not_pos hn
    rw [hx0] at hdense
    simp at hdense
    omega
  let P : CriticalPartition G q X :=
    Classical.choice (exists_criticalPartition G q hcritical X)
  have hGamma : 0 < gammaParameter E X.card := by
    apply gammaParameter_pos
    · have : 0 < keySparsityThreshold := by
        norm_num [keySparsityThreshold, keyCombConstant]
      omega
    · exact hX
  by_cases hcomb : ∃ i : Fin P.s, ∃ (t : ℕ)
      (Cmb : CombBetween G (P.C i) (P.D i) t),
      0 < t ∧ ∀ j : Fin t,
        gammaParameter E X.card ≤ t ^ 2 * (Cmb.block j).card
  · obtain ⟨i, t, Cmb, ht, hblocks⟩ := hcomb
    let C : StableHubComb G t := P.stableHubCombOfBetween G i Cmb
    refine ⟨t, C, teeth_large_of_blocks G P i hX ht Cmb hblocks, ?_⟩
    intro j
    calc
      E * X.card ≤ keyCombConstant * gammaParameter E X.card :=
        le_mul_gammaParameter E X.card
      _ ≤ keyCombConstant * (t ^ 2 * (Cmb.block j).card) :=
        Nat.mul_le_mul_left _ (hblocks j)
      _ = keyCombConstant * t ^ 2 * (C.block j).card := by
        simp [C, CriticalPartition.stableHubCombOfBetween]
        ring
  have hsmall : ∀ i : Fin P.s,
      (P.D i).card ^ 2 ≤
        128 ^ 2 * gammaParameter E X.card * (P.A i).card := by
    intro i
    rcases Lax54.BipartiteCombLemma.bipartite_comb_lemma G (P.C i) (P.D i)
        (gammaParameter E X.card) (P.A i).card
        (P.C_D_disjoint i) hGamma (P.D_covered i) (P.C_degree_D i) with
      h | h
    · exact (hcomb ⟨i, h⟩).elim
    · exact h
  have hE : 0 < E := by
    have : 0 < keySparsityThreshold := by
      norm_num [keySparsityThreshold, keyCombConstant]
    omega
  have hKleE : keyCombConstant ≤ E := by
    exact (by norm_num [keySparsityThreshold, keyCombConstant] :
      keyCombConstant ≤ keySparsityThreshold) |>.trans hEthresh
  have hE16 : 16 ≤ E := by
    exact (by norm_num [keySparsityThreshold, keyCombConstant] :
      16 ≤ keySparsityThreshold) |>.trans hEthresh
  let f : Fin P.s → ℝ := fun i ↦ ((P.A i).card : ℝ) / X.card
  have hf0 : ∀ i, 0 ≤ f i := by
    intro i
    dsimp [f]
    positivity
  have hfM : ∀ i, f i ≤ (E : ℝ)⁻¹ := by
    intro i
    have hAcard : (P.A i).card ≤
        (neighborsWithin G X (P.hub i)).card :=
      Finset.card_le_card (P.A_subset_neighbors i)
    have hhubDegree := hdegree ⟨P.hub i, P.hub_mem i⟩
    rw [← neighborsWithin_card_eq_degree G X (P.hub_mem i)] at hhubDegree
    have hmul : E * (P.A i).card < X.card :=
      lt_of_le_of_lt (Nat.mul_le_mul_left E hAcard) hhubDegree
    have hmulR : (E : ℝ) * (P.A i).card < X.card := by
      exact_mod_cast hmul
    have hratio : ((P.A i).card : ℝ) / X.card < 1 / (E : ℝ) := by
      apply (div_lt_div_iff₀ (by positivity : (0 : ℝ) < X.card)
        (by positivity : (0 : ℝ) < E)).mpr
      nlinarith
    simpa [f, one_div] using hratio.le
  have hmoment : ∑ i : Fin P.s, f i ^ (q : ℝ)⁻¹ ≤
      (D : ℝ) ^ (q : ℝ)⁻¹ := by
    simpa [f] using P.sum_normalized_A_rpow_le G (by omega : 0 < q)
      hcritical hX hdense
  have hqinv_one : (q : ℝ)⁻¹ ≤ 1 := by
    rw [inv_le_one₀ (by positivity : (0 : ℝ) < q)]
    exact_mod_cast (show 1 ≤ q by omega)
  have hAsumRaw : ∑ i : Fin P.s, f i ≤
      (E : ℝ)⁻¹ ^ (1 - (q : ℝ)⁻¹) *
        (D : ℝ) ^ (q : ℝ)⁻¹ := by
    simpa using sum_rpow_le_of_le f (show 2 ≤ q by omega)
      (by positivity : (0 : ℝ) < (E : ℝ)⁻¹) hf0 hfM hmoment hqinv_one
  have hroot : (((E : ℝ) * D) ^ (q : ℝ)⁻¹ ≤ 2) :=
    product_root_le_two (by omega) hEDpow
  have hAsum : ∑ i : Fin P.s, f i ≤ (1 / 8 : ℝ) := by
    calc
      ∑ i : Fin P.s, f i ≤
          (E : ℝ)⁻¹ ^ (1 - (q : ℝ)⁻¹) *
            (D : ℝ) ^ (q : ℝ)⁻¹ := hAsumRaw
      _ = ((E : ℝ) * D) ^ (q : ℝ)⁻¹ / E :=
        inv_rpow_factor_one (by positivity) (by positivity)
      _ ≤ 2 / (E : ℝ) := div_le_div_of_nonneg_right hroot (by positivity)
      _ ≤ 1 / 8 := by
        apply (div_le_iff₀ (by positivity : (0 : ℝ) < E)).mpr
        have hE16R : (16 : ℝ) ≤ E := by exact_mod_cast hE16
        nlinarith
  have hqinv_half : (q : ℝ)⁻¹ ≤ (1 / 2 : ℝ) := by
    simpa [one_div] using one_div_le_one_div_of_le
      (by norm_num : (0 : ℝ) < 2) (by exact_mod_cast (show 2 ≤ q by omega))
  have hgammaUpper : keyCombConstant * gammaParameter E X.card ≤
      2 * E * X.card := mul_gammaParameter_le_two_mul hKleE hX
  have hDpoint : ∀ i : Fin P.s,
      ((P.D i).card : ℝ) / X.card ≤
        128 * √(2 * (E : ℝ) / keyCombConstant) *
          f i ^ (1 / 2 : ℝ) := by
    intro i
    calc
      ((P.D i).card : ℝ) / X.card ≤
          128 * √((2 * (E : ℝ) / keyCombConstant) *
            (((P.A i).card : ℝ) / X.card)) :=
        normalized_small_side hX keyCombConstant_pos (hsmall i) hgammaUpper
      _ = 128 * √(2 * (E : ℝ) / keyCombConstant) *
          f i ^ (1 / 2 : ℝ) := by
        rw [Real.sqrt_mul (by positivity :
          (0 : ℝ) ≤ 2 * (E : ℝ) / keyCombConstant)]
        simp_rw [Real.sqrt_eq_rpow]
        dsimp [f]
        ring
  have hsqrtRaw : ∑ i : Fin P.s, f i ^ (1 / 2 : ℝ) ≤
      (E : ℝ)⁻¹ ^ ((1 / 2 : ℝ) - (q : ℝ)⁻¹) *
        (D : ℝ) ^ (q : ℝ)⁻¹ := by
    exact sum_rpow_le_of_le f (show 2 ≤ q by omega)
      (by positivity : (0 : ℝ) < (E : ℝ)⁻¹) hf0 hfM hmoment hqinv_half
  have hsqrtK : √(2 / (keyCombConstant : ℝ)) ≤ (1 / 512 : ℝ) := by
    rw [Real.sqrt_le_iff]
    constructor
    · norm_num
    · norm_num [keyCombConstant]
  have hDsum : ∑ i : Fin P.s, ((P.D i).card : ℝ) / X.card ≤
      (1 / 2 : ℝ) := by
    calc
      ∑ i : Fin P.s, ((P.D i).card : ℝ) / X.card ≤
          ∑ i : Fin P.s,
            128 * √(2 * (E : ℝ) / keyCombConstant) *
              f i ^ (1 / 2 : ℝ) :=
        Finset.sum_le_sum fun i _ ↦ hDpoint i
      _ = 128 * √(2 * (E : ℝ) / keyCombConstant) *
          ∑ i : Fin P.s, f i ^ (1 / 2 : ℝ) := by
        rw [Finset.mul_sum]
      _ ≤ 128 * √(2 * (E : ℝ) / keyCombConstant) *
          ((E : ℝ)⁻¹ ^ ((1 / 2 : ℝ) - (q : ℝ)⁻¹) *
            (D : ℝ) ^ (q : ℝ)⁻¹) := by
        gcongr
      _ = 128 * (√(2 / (keyCombConstant : ℝ)) *
          ((E : ℝ) * D) ^ (q : ℝ)⁻¹) := by
        rw [mul_assoc]
        rw [sqrt_inv_rpow_factor (by positivity) (by positivity)
          (by exact_mod_cast keyCombConstant_pos)]
      _ ≤ 128 * ((1 / 512 : ℝ) * 2) := by
        gcongr
      _ = 1 / 2 := by norm_num
  have hsNat : 8 * P.s < X.card :=
    P.eight_mul_s_lt G (show 1 ≤ q by omega) hcritical hD hdense hDpow
  have hs : (P.s : ℝ) / X.card ≤ (1 / 8 : ℝ) := by
    have hsR : 8 * (P.s : ℝ) < X.card := by exact_mod_cast hsNat
    apply le_of_lt
    apply (div_lt_iff₀ (by positivity : (0 : ℝ) < X.card)).mpr
    nlinarith
  have hAsum' : ∑ i : Fin P.s, ((P.A i).card : ℝ) / X.card ≤
      (1 / 8 : ℝ) := by
    simpa [f] using hAsum
  have hpartR : (X.card : ℝ) = (P.s : ℝ) +
      ∑ i : Fin P.s, (((P.A i).card : ℝ) + (P.D i).card) := by
    exact_mod_cast P.card_partition
  rw [Finset.sum_add_distrib] at hpartR
  have hidentity : (P.s : ℝ) / X.card +
      ∑ i : Fin P.s, ((P.A i).card : ℝ) / X.card +
      ∑ i : Fin P.s, ((P.D i).card : ℝ) / X.card = 1 := by
    rw [← Finset.sum_div, ← Finset.sum_div]
    field_simp
    linarith
  exfalso
  nlinarith

end Lax54Proofs
