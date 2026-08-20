import Lax54.RodlTheorem
import Mathlib.Combinatorics.Pigeonhole
import Mathlib.Combinatorics.SimpleGraph.Extremal.Turan
import Mathlib.Combinatorics.SimpleGraph.Regularity.Lemma
import Mathlib.Tactic

/-!
# Rödl's theorem

This file proves the sparse-or-dense induced-subgraph theorem quoted as
Theorem 4.1 in the paper. Apply Szemerédi's regularity lemma, use Turán's
theorem to select classes whose pairs are all regular, and apply finite Ramsey
theory to the three-coloring determined by low, high, and intermediate pair
density. The low- and high-density cases give a sparse induced subgraph in the
graph or its complement; the intermediate case gives an induced copy of the
forbidden graph by a greedy embedding argument.
-/

open Finset Fintype
open scoped SimpleGraph

namespace Lax54Proofs.RodlTheorem

open Lax54.GraphDefinitions

universe u v

section FiniteRamsey

/-- An explicit bound for the finite focusing argument. -/
def focusBound (q : ℕ) : ℕ → ℕ
  | 0 => 0
  | n + 1 => 1 + q * focusBound q n

@[simp] lemma focusBound_zero (q : ℕ) : focusBound q 0 = 0 := rfl

@[simp] lemma focusBound_succ (q n : ℕ) :
    focusBound q (n + 1) = 1 + q * focusBound q n := rfl

lemma focusBound_pos {q n : ℕ} (hn : 0 < n) : 0 < focusBound q n := by
  obtain ⟨n, rfl⟩ := Nat.exists_eq_succ_of_ne_zero hn.ne'
  simp [focusBound]

lemma le_focusBound {q n : ℕ} (hq : 0 < q) : n ≤ focusBound q n := by
  induction n with
  | zero => simp
  | succ n ih =>
      rw [focusBound_succ]
      calc
        n + 1 ≤ focusBound q n + 1 := Nat.add_le_add_right ih 1
        _ ≤ q * focusBound q n + 1 :=
          Nat.add_le_add_right (Nat.le_mul_of_pos_left _ hq) 1
        _ = 1 + q * focusBound q n := by omega

/--
The finite focusing construction. It produces an ordered tuple such that
all edges from an earlier vertex to later vertices have one colour depending
only on the earlier vertex.
-/
lemma exists_focused_tuple
    {A : Type*} [DecidableEq A] {q n : ℕ} (hq : 0 < q)
    (c : A → A → Fin q) (S : Finset A)
    (hS : focusBound q n ≤ S.card) :
    ∃ f : Fin n → A, Function.Injective f ∧
      (∀ i, f i ∈ S) ∧
      ∃ d : Fin n → Fin q, ∀ i j : Fin n, i < j → c (f i) (f j) = d i := by
  induction n generalizing S with
  | zero =>
      refine ⟨Fin.elim0, fun i => Fin.elim0 i, fun i => Fin.elim0 i,
        Fin.elim0, fun i => Fin.elim0 i⟩
  | succ n ih =>
      have hSne : S.Nonempty := by
        rw [nonempty_iff_ne_empty]
        intro hzero
        rw [hzero, Finset.card_empty] at hS
        simpa [focusBound] using hS
      let a := hSne.choose
      let T := S.erase a
      have haS : a ∈ S := hSne.choose_spec
      have hTcard : q * focusBound q n ≤ T.card := by
        rw [card_erase_of_mem haS]
        change 1 + q * focusBound q n ≤ S.card at hS
        omega
      letI : Nonempty (Fin q) := Fintype.card_pos_iff.mp (by simpa using hq)
      have hmaps : ∀ x ∈ T, c a x ∈ (Finset.univ : Finset (Fin q)) := by simp
      obtain ⟨colour, -, hcolour⟩ :=
        Finset.exists_le_card_fiber_of_mul_le_card_of_maps_to hmaps
          (Finset.univ_nonempty) (by simpa using hTcard)
      let U := {x ∈ T | c a x = colour}
      have hU : focusBound q n ≤ U.card := by simpa [U] using hcolour
      obtain ⟨g, hg_inj, hgU, e, he⟩ := ih U hU
      let f : Fin (n + 1) → A := Fin.cons a g
      let d : Fin (n + 1) → Fin q := Fin.cons colour e
      refine ⟨f, ?_, ?_, d, ?_⟩
      · rw [Fin.cons_injective_iff]
        refine ⟨?_, hg_inj⟩
        rintro ⟨i, hi⟩
        have hgiU := hgU i
        have hgiT : g i ∈ T := (mem_filter.1 hgiU).1
        exact (mem_erase.1 hgiT).1 hi
      · intro i
        refine Fin.cases haS (fun j => ?_) i
        exact (mem_erase.1 (mem_filter.1 (hgU j)).1).2
      · intro i j hij
        by_cases hi0 : i = 0
        · subst i
          have hj0 : j ≠ 0 := ne_of_gt hij
          obtain ⟨j', rfl⟩ := Fin.eq_succ_of_ne_zero hj0
          simpa [f, d] using (mem_filter.1 (hgU j')).2
        · obtain ⟨i', rfl⟩ := Fin.eq_succ_of_ne_zero hi0
          have hj0 : j ≠ 0 := by
            intro hj
            subst j
            exact (Fin.not_lt_zero _ hij)
          obtain ⟨j', rfl⟩ := Fin.eq_succ_of_ne_zero hj0
          have hij' : i' < j' := Fin.succ_lt_succ_iff.mp hij
          simpa [f, d] using he i' j' hij'

/-- A multicolor Ramsey bound obtained from `focusBound`. -/
def ramseyBound (q r : ℕ) : ℕ := focusBound q (q * (r - 1) + 1)

/-- Finite Ramsey extraction for a symmetric colouring of unordered pairs. -/
lemma exists_monochromatic_tuple
    {A : Type*} [DecidableEq A] {q r : ℕ} (hq : 0 < q) (hr : 0 < r)
    (c : A → A → Fin q) (S : Finset A)
    (hsymm : ∀ a b, c a b = c b a)
    (hS : ramseyBound q r ≤ S.card) :
    ∃ f : Fin r → A, Function.Injective f ∧ (∀ i, f i ∈ S) ∧
      ∃ colour : Fin q, ∀ i j : Fin r, i ≠ j → c (f i) (f j) = colour := by
  let m := q * (r - 1) + 1
  obtain ⟨f, hf_inj, hfS, d, hd⟩ :=
    exists_focused_tuple hq c S (n := m) (by simpa [ramseyBound, m] using hS)
  have hpigeon : q * (r - 1) < Fintype.card (Fin m) := by simp [m]
  obtain ⟨colour, hcolour⟩ :=
    Fintype.exists_lt_card_fiber_of_mul_lt_card (f := d) (n := r - 1) (by simpa using hpigeon)
  let I : Finset (Fin m) := Finset.univ.filter fun i => d i = colour
  have hIcard : r ≤ I.card := by
    have : r - 1 < I.card := by simpa [I] using hcolour
    omega
  obtain ⟨J, hJI, hJcard⟩ := Finset.exists_subset_card_eq hIcard
  let e : Fin r → Fin m := fun i => J.orderIsoOfFin hJcard i
  have he_inj : Function.Injective e := by
    intro i j hij
    apply (J.orderIsoOfFin hJcard).injective
    exact Subtype.ext hij
  -- Record explicitly the membership supplied by `orderIsoOfFin`.
  have heJ' (i : Fin r) : (e i : Fin m) ∈ J := (J.orderIsoOfFin hJcard i).property
  refine ⟨fun i => f (e i), hf_inj.comp he_inj, fun i => hfS (e i), colour, ?_⟩
  intro i j hij
  have hdi : d (e i) = colour := (mem_filter.1 (hJI (heJ' i))).2
  have hdj : d (e j) = colour := (mem_filter.1 (hJI (heJ' j))).2
  rcases lt_or_gt_of_ne (he_inj.ne hij) with hij' | hji'
  · exact (hd (e i) (e j) hij').trans hdi
  · have hback := hd (e j) (e i) hji'
    change c (f (e i)) (f (e j)) = colour
    rw [hsymm]
    exact hback.trans hdj

end FiniteRamsey

section UniformPairExtraction

variable {A : Type*} [Fintype A] [DecidableEq A]
  (G : SimpleGraph A) [DecidableRel G.Adj]

/-- The graph whose vertices are classes of `P` and whose edges are its non-uniform pairs. -/
def nonUniformGraph (P : Finpartition (Finset.univ : Finset A)) (η : ℝ) :
    SimpleGraph {U // U ∈ P.parts} where
  Adj U V := U ≠ V ∧ ¬ G.IsUniform η U.1 V.1
  symm := by
    rintro U V ⟨hUV, hirr⟩
    refine ⟨hUV.symm, ?_⟩
    intro hreg
    exact hirr hreg.symm
  loopless := ⟨fun U h => h.1 rfl⟩

noncomputable instance nonUniformGraph.instDecidableRel
    (P : Finpartition (Finset.univ : Finset A)) (η : ℝ) :
    DecidableRel (nonUniformGraph G P η).Adj := Classical.decRel _

/-- Ordered nonuniform pairs are precisely the ordered adjacent pairs of `nonUniformGraph`. -/
lemma two_mul_card_nonUniformGraph_edges
    (P : Finpartition (Finset.univ : Finset A)) (η : ℝ) :
    2 * (nonUniformGraph G P η).edgeFinset.card = (P.nonUniforms G η).card := by
  classical
  let B := nonUniformGraph G P η
  let Q : Finset ({U // U ∈ P.parts} × {U // U ∈ P.parts}) :=
    Finset.univ.filter fun p => B.Adj p.1 p.2
  rw [B.two_mul_card_edgeFinset]
  let e :
      (↑Q) ≃
      {p : Finset A × Finset A // p ∈ P.nonUniforms G η} :=
    { toFun := fun p => ⟨(p.1.1.1, p.1.2.1), by
          have hp := (Finset.mem_filter.1 p.2).2
          simpa [B, nonUniformGraph] using
            (show p.1.1.1 ≠ p.1.2.1 ∧ ¬G.IsUniform η p.1.1.1 p.1.2.1 from
              ⟨fun h => hp.1 (Subtype.ext h), hp.2⟩) ⟩
      invFun := fun p =>
        ⟨(⟨p.1.1, (Finpartition.mk_mem_nonUniforms P G).mp p.2 |>.1⟩,
          ⟨p.1.2, (Finpartition.mk_mem_nonUniforms P G).mp p.2 |>.2.1⟩), by
            rw [Finset.mem_filter]
            refine ⟨Finset.mem_univ _, ?_⟩
            have hp := (Finpartition.mk_mem_nonUniforms P G).mp p.2
            exact ⟨fun h => hp.2.2.1 (congrArg Subtype.val h), hp.2.2.2⟩ ⟩
      left_inv := by intro p; apply Subtype.ext; rfl
      right_inv := by intro p; apply Subtype.ext; rfl }
  calc
    #((Finset.univ : Finset ({U // U ∈ P.parts} × {U // U ∈ P.parts})).filter
        fun p => B.Adj p.1 p.2) = Q.card := by rfl
    _ = Fintype.card (↑Q) := (Fintype.card_coe Q).symm
    _ = Fintype.card (↑(P.nonUniforms G η)) := Fintype.card_congr e
    _ = #(P.nonUniforms G η) := Fintype.card_coe _

lemma card_edges_add_compl
    {B : Type*} [Fintype B] [DecidableEq B] (J : SimpleGraph B)
    [DecidableRel J.Adj] :
    J.edgeFinset.card + Jᶜ.edgeFinset.card = (Fintype.card B).choose 2 := by
  classical
  have hc : Jᶜ.edgeFinset = (⊤ : SimpleGraph B).edgeFinset \ J.edgeFinset := by
    ext e
    induction e using Sym2.inductionOn with
    | _ x y => simp [SimpleGraph.compl_adj]
  have hsub : J.edgeFinset ⊆ (⊤ : SimpleGraph B).edgeFinset :=
    SimpleGraph.edgeFinset_mono le_top
  rw [hc, Finset.card_sdiff_of_subset hsub,
    Nat.add_sub_of_le (Finset.card_le_card hsub),
    SimpleGraph.card_edgeFinset_top_eq_card_choose_two]

/-- A partition with few non-uniform pairs contains many mutually uniform classes. -/
lemma exists_pairwise_uniform_parts
    (P : Finpartition (Finset.univ : Finset A)) (η : ℝ) (N : ℕ)
    (hN : 2 ≤ N) (hNP : N ≤ P.parts.card)
    (hsmall : ((N - 1 : ℕ) : ℝ) ^ 2 * η < 1)
    (hP : P.IsUniform G η) :
    ∃ f : Fin N → Finset A, Function.Injective f ∧
      (∀ i, f i ∈ P.parts) ∧
      ∀ i j : Fin N, i ≠ j → G.IsUniform η (f i) (f j) := by
  classical
  let B := nonUniformGraph G P η
  have hcardB : Fintype.card {U // U ∈ P.parts} = P.parts.card := by simp
  by_contra! hcontra
  have hfree : B.IndepSetFree N := by
    intro T hT
    let eT : Fin N → T := fun i => T.equivFin.symm (Fin.cast hT.card_eq.symm i)
    let e : Fin N → {U // U ∈ P.parts} := fun i => (eT i).1
    have heTinj : Function.Injective eT :=
      T.equivFin.symm.injective.comp (Fin.cast_injective hT.card_eq.symm)
    have heinj : Function.Injective e := by
      intro i j hij
      apply heTinj
      exact Subtype.ext hij
    have hf_uniform : ∀ i j : Fin N, i ≠ j → G.IsUniform η (e i).1 (e j).1 := by
      intro i j hij
      have hnonadj := hT.isIndepSet (eT i).property (eT j).property (heinj.ne hij)
      have hnot : ¬ B.Adj (e i) (e j) := by simpa [e] using hnonadj
      by_contra hunif
      exact hnot ⟨heinj.ne hij, hunif⟩
    obtain ⟨i, j, hij, hn⟩ := hcontra (fun i => (e i).1)
      (fun i j h => heinj (Subtype.ext h)) (fun i => (e i).2)
    exact hn (hf_uniform i j hij)
  have hcf : Bᶜ.CliqueFree ((N - 1) + 1) := by
    simpa [Nat.sub_add_cancel (by omega : 1 ≤ N)] using hfree
  let k := P.parts.card
  have hkN : N ≤ k := hNP
  have hkpos : 0 < k := lt_of_lt_of_le (by omega : 0 < N) hkN
  have hedge_turan :
      Bᶜ.edgeFinset.card ≤
        (SimpleGraph.turanGraph k (N - 1)).edgeFinset.card := by
    simpa [k, hcardB, SimpleGraph.card_edgeFinset_turanGraph] using
      (hcf.card_edgeFinset_le (r := N - 1))
  have hcomp :
      2 * (N - 1) * Bᶜ.edgeFinset.card ≤ (N - 2) * k ^ 2 := by
    calc
      2 * (N - 1) * Bᶜ.edgeFinset.card ≤
          2 * (N - 1) * (SimpleGraph.turanGraph k (N - 1)).edgeFinset.card := by
            gcongr
      _ ≤ ((N - 1) - 1) * k ^ 2 :=
        SimpleGraph.mul_card_edgeFinset_turanGraph_le
      _ = (N - 2) * k ^ 2 := by rw [show (N - 1) - 1 = N - 2 by omega]
  have htotal : B.edgeFinset.card + Bᶜ.edgeFinset.card = k.choose 2 := by
    simpa [k, hcardB] using card_edges_add_compl B
  have hirr : ((2 * B.edgeFinset.card : ℕ) : ℝ) ≤
      ((k * (k - 1) : ℕ) : ℝ) * η := by
    rw [two_mul_card_nonUniformGraph_edges G P η]
    simpa [Finpartition.IsUniform, k] using hP
  have hkprodpos : (0 : ℝ) < ((k * (k - 1) : ℕ) : ℝ) := by
    norm_cast
    exact Nat.mul_pos hkpos (Nat.sub_pos_iff_lt.mpr (lt_of_lt_of_le (by omega) hkN))
  have hupper :
      (((N - 1) ^ 2 * (2 * B.edgeFinset.card) : ℕ) : ℝ) <
        ((k * (k - 1) : ℕ) : ℝ) := by
    calc
      (((N - 1) ^ 2 * (2 * B.edgeFinset.card) : ℕ) : ℝ) =
          (((N - 1 : ℕ) : ℝ) ^ 2) * ((2 * B.edgeFinset.card : ℕ) : ℝ) := by norm_num
      _ ≤ (((N - 1 : ℕ) : ℝ) ^ 2) *
          (((k * (k - 1) : ℕ) : ℝ) * η) := by gcongr
      _ = ((k * (k - 1) : ℕ) : ℝ) *
          ((((N - 1 : ℕ) : ℝ) ^ 2) * η) := by ring
      _ < ((k * (k - 1) : ℕ) : ℝ) * 1 :=
        mul_lt_mul_of_pos_left hsmall hkprodpos
      _ = ((k * (k - 1) : ℕ) : ℝ) := mul_one _
  have htotal' :
      2 * B.edgeFinset.card + 2 * Bᶜ.edgeFinset.card = k * (k - 1) := by
    calc
      2 * B.edgeFinset.card + 2 * Bᶜ.edgeFinset.card =
          2 * (B.edgeFinset.card + Bᶜ.edgeFinset.card) := by omega
      _ = 2 * k.choose 2 := by rw [htotal]
      _ = k * (k - 1) := by
        rw [Nat.choose_two_right, Nat.mul_div_cancel' (Nat.even_mul_pred_self k).two_dvd]
  have hcompR :
      (2 : ℝ) * ((N - 1 : ℕ) : ℝ) * Bᶜ.edgeFinset.card ≤
        ((N - 2 : ℕ) : ℝ) * (k : ℝ) ^ 2 := by
    exact_mod_cast hcomp
  rw [Nat.cast_sub (by omega : 1 ≤ N), Nat.cast_sub (by omega : 2 ≤ N)] at hcompR
  have htotalR :
      (2 : ℝ) * B.edgeFinset.card + 2 * Bᶜ.edgeFinset.card =
        (k : ℝ) * ((k - 1 : ℕ) : ℝ) := by
    exact_mod_cast htotal'
  rw [Nat.cast_sub (by omega : 1 ≤ k)] at htotalR
  have hkNR : (N : ℝ) ≤ k := by exact_mod_cast hkN
  have hN2R : (2 : ℝ) ≤ N := by exact_mod_cast hN
  have hlowerR :
      (k : ℝ) * ((k : ℝ) - N + 1) ≤
        ((N : ℝ) - 1) * (2 * B.edgeFinset.card) := by
    have hscaled := congrArg (fun x : ℝ => ((N : ℝ) - 1) * x) htotalR
    ring_nf at hscaled hcompR ⊢
    nlinarith
  have hfactor :
      (0 : ℝ) ≤ (k : ℝ) * ((N : ℝ) - 2) * ((k : ℝ) - N) := by
    positivity
  have halgebraR :
      (k : ℝ) * ((k : ℝ) - 1) ≤
        ((N : ℝ) - 1) * ((k : ℝ) * ((k : ℝ) - N + 1)) := by
    nlinarith
  have hlowerR' :
      (k : ℝ) * ((k : ℝ) - 1) ≤
        ((N : ℝ) - 1) ^ 2 * (2 * B.edgeFinset.card) := by
    calc
      (k : ℝ) * ((k : ℝ) - 1) ≤
          ((N : ℝ) - 1) * ((k : ℝ) * ((k : ℝ) - N + 1)) := halgebraR
      _ ≤ ((N : ℝ) - 1) * (((N : ℝ) - 1) * (2 * B.edgeFinset.card)) := by
        gcongr
        nlinarith
      _ = ((N : ℝ) - 1) ^ 2 * (2 * B.edgeFinset.card) := by ring
  have hupperR :
      (((N - 1 : ℕ) : ℝ)) ^ 2 * (2 * B.edgeFinset.card) <
        (k : ℝ) * ((k - 1 : ℕ) : ℝ) := by
    exact_mod_cast hupper
  rw [Nat.cast_sub (by omega : 1 ≤ N), Nat.cast_sub (by omega : 1 ≤ k)] at hupperR
  norm_num at hupperR
  exact (not_lt_of_ge hlowerR') hupperR

end UniformPairExtraction

section TypicalVertices

variable {A : Type*} [Fintype A] [DecidableEq A]
  (G : SimpleGraph A) [DecidableRel G.Adj]

/-- Uniformity is preserved by complementation on disjoint vertex sets. -/
lemma isUniform_compl_of_disjoint {s t : Finset A} {η : ℝ}
    (hs : s.Nonempty) (ht : t.Nonempty) (hst : Disjoint s t)
    (hu : G.IsUniform η s t) : Gᶜ.IsUniform η s t := by
  intro s' hs's t' ht't hs' ht'
  have hη : 0 < η := hu.pos
  have hs'ne : s'.Nonempty := by
    rw [Finset.nonempty_iff_ne_empty]
    intro hzero
    rw [hzero, Finset.card_empty, Nat.cast_zero] at hs'
    have : (0 : ℝ) < (s.card : ℝ) * η := mul_pos (by exact_mod_cast hs.card_pos) hη
    linarith
  have ht'ne : t'.Nonempty := by
    rw [Finset.nonempty_iff_ne_empty]
    intro hzero
    rw [hzero, Finset.card_empty, Nat.cast_zero] at ht'
    have : (0 : ℝ) < (t.card : ℝ) * η := mul_pos (by exact_mod_cast ht.card_pos) hη
    linarith
  have hst' : Disjoint s' t' := hst.mono hs's ht't
  have hmain := hu hs's ht't hs' ht'
  have hsum := G.edgeDensity_add_edgeDensity_compl hs'ne ht'ne hst'
  have hsum0 := G.edgeDensity_add_edgeDensity_compl hs ht hst
  have hsumR : (G.edgeDensity s' t' : ℝ) + Gᶜ.edgeDensity s' t' = 1 := by
    exact_mod_cast hsum
  have hsum0R : (G.edgeDensity s t : ℝ) + Gᶜ.edgeDensity s t = 1 := by
    exact_mod_cast hsum0
  have hc : (Gᶜ.edgeDensity s' t' : ℝ) = 1 - G.edgeDensity s' t' := by linarith
  have hc0 : (Gᶜ.edgeDensity s t : ℝ) = 1 - G.edgeDensity s t := by linarith
  rw [hc, hc0, show 1 - (G.edgeDensity s' t' : ℝ) -
      (1 - G.edgeDensity s t) = -(G.edgeDensity s' t' - G.edgeDensity s t) by ring,
    abs_neg]
  exact hmain

/-- Vertices whose degree into `t` is lower than regularity predicts. -/
noncomputable def badVertices (η : ℝ) (s t : Finset A) : Finset A :=
  {x ∈ s | #{y ∈ t | G.Adj x y} < (G.edgeDensity s t - η) * #t}

private lemma card_interedges_badVertices_le {s t : Finset A} {η : ℝ} :
    #(Rel.interedges G.Adj (badVertices G η s t) t) ≤
      #(badVertices G η s t) * #t * (G.edgeDensity s t - η) := by
  classical
  refine (Nat.cast_le.2 <| (card_le_card <| subset_of_eq (Rel.interedges_eq_biUnion _)).trans
    card_biUnion_le).trans ?_
  simp_rw [Nat.cast_sum, card_map, ← nsmul_eq_mul, smul_mul_assoc, mul_comm (#t : ℝ)]
  exact sum_le_card_nsmul _ _ _ fun x hx ↦ (mem_filter.1 hx).2.le

private lemma edgeDensity_badVertices_le {s t : Finset A} {η : ℝ}
    (hη : 0 ≤ η) (hd : 2 * η ≤ G.edgeDensity s t) :
    G.edgeDensity (badVertices G η s t) t ≤ G.edgeDensity s t - η := by
  rw [SimpleGraph.edgeDensity_def]
  push_cast
  refine div_le_of_le_mul₀ (by positivity) (sub_nonneg_of_le <| by linarith) ?_
  rw [mul_comm]
  exact card_interedges_badVertices_le G

/-- In a regular pair, at most an `η`-fraction of the first class is atypical. -/
lemma card_badVertices_le {s t : Finset A} {η : ℝ}
    (hd : 2 * η ≤ G.edgeDensity s t) (hu : G.IsUniform η s t) :
    ((badVertices G η s t).card : ℝ) ≤ s.card * η := by
  have hηone : η ≤ 1 := (le_mul_of_one_le_left hu.pos.le (by simp)).trans
    (hd.trans <| mod_cast G.edgeDensity_le_one s t)
  by_contra! h
  have hdiff :
      |(G.edgeDensity (badVertices G η s t) t - G.edgeDensity s t : ℝ)| < η :=
    hu (filter_subset _ _) Subset.rfl h.le
      (mul_le_of_le_one_right (Nat.cast_nonneg _) hηone)
  rw [abs_sub_lt_iff] at hdiff
  linarith [edgeDensity_badVertices_le G hu.pos.le hd]

/-- A vertex outside `badVertices` satisfies the corresponding degree lower bound. -/
lemma card_neighbors_ge_of_not_bad {s t : Finset A} {η : ℝ} {x : A}
    (hx : x ∈ s) (hxbad : x ∉ badVertices G η s t) :
    (G.edgeDensity s t - η) * t.card ≤ ({y ∈ t | G.Adj x y}.card : ℝ) := by
  simpa [badVertices, hx, not_lt] using hxbad

/--
Vertices of `s` that have fewer neighbors in a prescribed large subset
`t' ⊆ t` than the density of the original pair `(s,t)` predicts.
-/
noncomputable def relativeBadVertices (η : ℝ) (s t t' : Finset A) : Finset A :=
  {x ∈ s | #{y ∈ t' | G.Adj x y} < (G.edgeDensity s t - η) * #t'}

private lemma card_interedges_relativeBadVertices_le
    {s t t' : Finset A} {η : ℝ} :
    #(Rel.interedges G.Adj (relativeBadVertices G η s t t') t') ≤
      #(relativeBadVertices G η s t t') * #t' * (G.edgeDensity s t - η) := by
  classical
  refine (Nat.cast_le.2 <| (card_le_card <| subset_of_eq (Rel.interedges_eq_biUnion _)).trans
    card_biUnion_le).trans ?_
  simp_rw [Nat.cast_sum, card_map, ← nsmul_eq_mul, smul_mul_assoc, mul_comm (#t' : ℝ)]
  exact sum_le_card_nsmul _ _ _ fun x hx ↦ (mem_filter.1 hx).2.le

/-- The relative bad set still has size at most an `η`-fraction of `s`. -/
lemma card_relativeBadVertices_le
    {s t t' : Finset A} {η : ℝ}
    (ht'sub : t' ⊆ t) (ht'card : (t.card : ℝ) * η ≤ t'.card)
    (hd : η ≤ G.edgeDensity s t) (hu : G.IsUniform η s t) :
    ((relativeBadVertices G η s t t').card : ℝ) ≤ s.card * η := by
  by_contra! hbad
  have hdiff :
      |(G.edgeDensity (relativeBadVertices G η s t t') t' - G.edgeDensity s t : ℝ)| < η :=
    hu (filter_subset _ _) ht'sub hbad.le ht'card
  have hdensity :
      G.edgeDensity (relativeBadVertices G η s t t') t' ≤ G.edgeDensity s t - η := by
    rw [SimpleGraph.edgeDensity_def]
    push_cast
    refine div_le_of_le_mul₀ (by positivity) (sub_nonneg.mpr hd) ?_
    rw [mul_comm]
    exact card_interedges_relativeBadVertices_le G
  rw [abs_sub_lt_iff] at hdiff
  linarith

/-- Outside the relative bad set, the predicted degree lower bound holds. -/
lemma card_neighbors_ge_of_not_relativeBad
    {s t t' : Finset A} {η : ℝ} {x : A}
    (hx : x ∈ s) (hxbad : x ∉ relativeBadVertices G η s t t') :
    (G.edgeDensity s t - η) * t'.card ≤
      ({y ∈ t' | G.Adj x y}.card : ℝ) := by
  simpa [relativeBadVertices, hx, not_lt] using hxbad

end TypicalVertices

section InducedEmbedding

variable {I A : Type*} [DecidableEq I] [Fintype A] [DecidableEq A]
  (H : SimpleGraph I) [DecidableRel H.Adj]
  (G : SimpleGraph A) [DecidableRel G.Adj]

/-- Use adjacency in `G` for an edge of `H`, and adjacency in `Gᶜ` for a nonedge. -/
def targetGraph (i j : I) : SimpleGraph A := if H.Adj i j then G else Gᶜ

noncomputable instance targetGraph.instDecidableRel (i j : I) :
    DecidableRel (targetGraph H G i j).Adj := Classical.decRel _

/--
Greedy embedding with shrinking candidate sets. `d` records how many
vertices have already been embedded, so candidates have retained a
`q^d`-fraction of their original class.
-/
lemma inducedEmbeddingAux
    (U : I → Finset A) (η ρ q : ℝ) (N d n : ℕ)
    (hU_nonempty : ∀ i, (U i).Nonempty)
    (huniform : ∀ i j, i ≠ j →
      (targetGraph H G i j).IsUniform η (U i) (U j))
    (hdense : ∀ i j, i ≠ j →
      ρ ≤ (targetGraph H G i j).edgeDensity (U i) (U j))
    (hη : 0 ≤ η) (hq : 0 < q) (hq1 : q ≤ 1) (hqρ : q + η ≤ ρ)
    (hglobal : (N : ℝ) * η < q ^ N) (hdn : d + n = N)
    (idx : Fin n → I) (hidx : Function.Injective idx)
    (S : Fin n → Finset A)
    (hSU : ∀ i, S i ⊆ U (idx i))
    (hScard : ∀ i, q ^ d * (U (idx i)).card ≤ (S i).card) :
    ∃ f : Fin n → A, (∀ i, f i ∈ S i) ∧
      ∀ i j : Fin n, i < j → (targetGraph H G (idx i) (idx j)).Adj (f i) (f j) := by
  classical
  induction n generalizing d with
  | zero =>
      refine ⟨Fin.elim0, fun i => Fin.elim0 i, fun i => Fin.elim0 i⟩
  | succ n ih =>
      let i₀ : I := idx 0
      let U₀ : Finset A := U i₀
      let S₀ : Finset A := S 0
      let idx' : Fin n → I := fun j => idx j.succ
      have hidx' : Function.Injective idx' := hidx.comp (Fin.succ_injective n)
      have hi₀j (j : Fin n) : i₀ ≠ idx' j := by
        intro h
        exact Fin.succ_ne_zero j (hidx h).symm
      let K (j : Fin n) : SimpleGraph A := targetGraph H G i₀ (idx' j)
      let bad (j : Fin n) : Finset A :=
        relativeBadVertices (K j) η U₀ (U (idx' j)) (S j.succ)
      have hdle : d ≤ N := by omega
      have hpow : q ^ N ≤ q ^ d := pow_right_anti₀ hq.le hq1 hdle
      have hNpos : 0 < N := by omega
      have hηN : η ≤ (N : ℝ) * η := by
        nlinarith [show (1 : ℝ) ≤ N by exact_mod_cast hNpos]
      have hηpow : η < q ^ d := hηN.trans_lt (hglobal.trans_le hpow)
      have htailLarge (j : Fin n) :
          ((U (idx' j)).card : ℝ) * η ≤ (S j.succ).card := by
        calc
          ((U (idx' j)).card : ℝ) * η ≤
              q ^ d * (U (idx' j)).card := by
                nlinarith [mul_nonneg (show (0 : ℝ) ≤ (U (idx' j)).card by positivity)
                  hη]
          _ ≤ (S j.succ).card := hScard j.succ
      have hbad (j : Fin n) : ((bad j).card : ℝ) ≤ U₀.card * η := by
        have hηdens : η ≤ (K j).edgeDensity U₀ (U (idx' j)) := by
          have := hdense i₀ (idx' j) (hi₀j j)
          dsimp [K]
          linarith
        exact card_relativeBadVertices_le (K j) (hSU j.succ) (htailLarge j)
          hηdens (huniform i₀ (idx' j) (hi₀j j))
      let badUnion : Finset A := Finset.univ.biUnion bad
      have hbadUnion : (badUnion.card : ℝ) ≤ (n : ℝ) * (U₀.card * η) := by
        calc
          (badUnion.card : ℝ) ≤ ∑ j : Fin n, ((bad j).card : ℝ) := by
            exact_mod_cast Finset.card_biUnion_le
          _ ≤ ∑ _j : Fin n, (U₀.card : ℝ) * η := by
            exact Finset.sum_le_sum fun j _ => hbad j
          _ = (n : ℝ) * (U₀.card * η) := by simp
      have hnN : (n : ℝ) ≤ N := by exact_mod_cast (by omega : n ≤ N)
      have hnηpow : (n : ℝ) * η < q ^ d := by
        calc
          (n : ℝ) * η ≤ N * η := by gcongr
          _ < q ^ N := hglobal
          _ ≤ q ^ d := hpow
      have hU₀pos : (0 : ℝ) < U₀.card := by
        exact_mod_cast (hU_nonempty i₀).card_pos
      have hbad_lt_S : badUnion.card < S₀.card := by
        have hreal : (badUnion.card : ℝ) < S₀.card := calc
          (badUnion.card : ℝ) ≤ (n : ℝ) * (U₀.card * η) := hbadUnion
          _ = ((n : ℝ) * η) * U₀.card := by ring
          _ < q ^ d * U₀.card := mul_lt_mul_of_pos_right hnηpow hU₀pos
          _ ≤ S₀.card := hScard 0
        exact_mod_cast hreal
      have hnotSub : ¬ S₀ ⊆ badUnion := fun hsub =>
        (not_lt_of_ge (Finset.card_le_card hsub)) hbad_lt_S
      obtain ⟨x, hxS₀, hxgood⟩ := Set.not_subset.mp hnotSub
      have hxU₀ : x ∈ U₀ := hSU 0 hxS₀
      have hxnotbad (j : Fin n) : x ∉ bad j := by
        intro hx
        exact hxgood (Finset.mem_biUnion.mpr ⟨j, Finset.mem_univ _, hx⟩)
      let S' (j : Fin n) : Finset A := {y ∈ S j.succ | (K j).Adj x y}
      have hS'U (j : Fin n) : S' j ⊆ U (idx' j) :=
        fun y hy => hSU j.succ (Finset.mem_filter.1 hy).1
      have hS'card (j : Fin n) :
          q ^ (d + 1) * (U (idx' j)).card ≤ (S' j).card := by
        have hdegree := card_neighbors_ge_of_not_relativeBad (K j) hxU₀ (hxnotbad j)
        have hqden : q ≤ (K j).edgeDensity U₀ (U (idx' j)) - η := by
          have := hdense i₀ (idx' j) (hi₀j j)
          dsimp [K]
          linarith
        calc
          q ^ (d + 1) * (U (idx' j)).card =
              q * (q ^ d * (U (idx' j)).card) := by rw [pow_succ]; ring
          _ ≤ q * (S j.succ).card := by gcongr; exact hScard j.succ
          _ ≤ ((K j).edgeDensity U₀ (U (idx' j)) - η) * (S j.succ).card := by
            gcongr
          _ ≤ (S' j).card := by simpa [S'] using hdegree
      have hdn' : (d + 1) + n = N := by omega
      obtain ⟨f', hf'S, hf'adj⟩ := ih (d + 1) hdn' idx' hidx' S' hS'U hS'card
      let f : Fin (n + 1) → A := Fin.cons x f'
      refine ⟨f, ?_, ?_⟩
      · intro i
        refine Fin.cases hxS₀ (fun j => ?_) i
        exact (Finset.mem_filter.1 (hf'S j)).1
      · intro i j hij
        by_cases hi0 : i = 0
        · subst i
          have hj0 : j ≠ 0 := ne_of_gt hij
          obtain ⟨j', rfl⟩ := Fin.eq_succ_of_ne_zero hj0
          simpa [f, K, i₀, idx'] using (Finset.mem_filter.1 (hf'S j')).2
        · obtain ⟨i', rfl⟩ := Fin.eq_succ_of_ne_zero hi0
          have hj0 : j ≠ 0 := by
            intro hj
            subst j
            exact Fin.not_lt_zero _ hij
          obtain ⟨j', rfl⟩ := Fin.eq_succ_of_ne_zero hj0
          have hij' : i' < j' := Fin.succ_lt_succ_iff.mp hij
          simpa [f, idx'] using hf'adj i' j' hij'

/-- Adjacency in `targetGraph` records exactly the adjacency pattern of `H`. -/
lemma targetGraph_adj_agrees {i j : I} {x y : A}
    (h : (targetGraph H G i j).Adj x y) : G.Adj x y ↔ H.Adj i j := by
  by_cases hij : H.Adj i j
  · simpa [targetGraph, hij] using h
  · have h' : Gᶜ.Adj x y := by simpa [targetGraph, hij] using h
    exact ⟨fun hxy => (h'.2 hxy).elim, fun hH => (hij hH).elim⟩

/-- An induced embedding lemma for mutually regular, intermediate-density classes. -/
lemma induced_copy_of_uniform_middle
    [Fintype I]
    (U : I → Finset A) (η ρ q : ℝ)
    (hU_nonempty : ∀ i, (U i).Nonempty)
    (hU_disjoint : ∀ {i j}, i ≠ j → Disjoint (U i) (U j))
    (huniform : ∀ i j, i ≠ j → G.IsUniform η (U i) (U j))
    (hlow : ∀ i j, i ≠ j → ρ ≤ G.edgeDensity (U i) (U j))
    (hhigh : ∀ i j, i ≠ j → G.edgeDensity (U i) (U j) ≤ 1 - ρ)
    (hη : 0 ≤ η) (hq : 0 < q) (hq1 : q ≤ 1) (hqρ : q + η ≤ ρ)
    (hglobal : (Fintype.card I : ℝ) * η < q ^ Fintype.card I) :
    H ⊴ G := by
  classical
  let N := Fintype.card I
  let idx : Fin N → I := (Fintype.equivFin I).symm
  have hidx : Function.Injective idx := (Fintype.equivFin I).symm.injective
  have htarget_uniform : ∀ i j, i ≠ j →
      (targetGraph H G i j).IsUniform η (U i) (U j) := by
    intro i j hij
    by_cases hHij : H.Adj i j
    · simpa [targetGraph, hHij] using huniform i j hij
    · simpa [targetGraph, hHij] using
        isUniform_compl_of_disjoint G (hU_nonempty i) (hU_nonempty j)
          (hU_disjoint hij) (huniform i j hij)
  have htarget_dense : ∀ i j, i ≠ j →
      ρ ≤ (targetGraph H G i j).edgeDensity (U i) (U j) := by
    intro i j hij
    by_cases hHij : H.Adj i j
    · simpa [targetGraph, hHij] using hlow i j hij
    · have hsum := G.edgeDensity_add_edgeDensity_compl
          (hU_nonempty i) (hU_nonempty j) (hU_disjoint hij)
      have hsumR : (G.edgeDensity (U i) (U j) : ℝ) +
          Gᶜ.edgeDensity (U i) (U j) = 1 := by exact_mod_cast hsum
      have : ρ ≤ (Gᶜ.edgeDensity (U i) (U j) : ℝ) := by
        linarith [hhigh i j hij]
      simpa [targetGraph, hHij] using this
  obtain ⟨f, hfU, hfadj⟩ := inducedEmbeddingAux H G U η ρ q N 0 N
    hU_nonempty htarget_uniform htarget_dense hη hq hq1 hqρ
    (by simpa [N] using hglobal) (by simp) idx hidx (fun i => U (idx i))
    (fun _ => Subset.rfl) (by simp)
  let φ : I → A := fun i => f (Fintype.equivFin I i)
  have hφmem (i : I) : φ i ∈ U i := by
    simpa [φ, idx] using hfU (Fintype.equivFin I i)
  have hφinj : Function.Injective φ := by
    intro i j hij
    by_contra hne
    have hd := Finset.disjoint_left.mp (hU_disjoint hne)
    exact hd (hφmem i) (by simpa [hij] using hφmem j)
  refine ⟨{
    toFun := φ
    inj' := hφinj
    map_rel_iff' := ?_
  }⟩
  intro i j
  by_cases hij : i = j
  · subst j
    simp
  have heij : Fintype.equivFin I i ≠ Fintype.equivFin I j :=
    (Fintype.equivFin I).injective.ne hij
  rcases lt_or_gt_of_ne heij with hlt | hgt
  · have ht := hfadj (Fintype.equivFin I i) (Fintype.equivFin I j) hlt
    simpa [φ, idx] using targetGraph_adj_agrees H G ht
  · have ht := hfadj (Fintype.equivFin I j) (Fintype.equivFin I i) hgt
    simpa [φ, idx, H.adj_comm, G.adj_comm] using targetGraph_adj_agrees H G ht

end InducedEmbedding

section SparseUnion

variable {A : Type*} [Fintype A] [DecidableEq A]
  (G : SimpleGraph A) [DecidableRel G.Adj]

/-- Ordered edges in a set are the ordered adjacent pairs of the corresponding induced graph. -/
lemma two_mul_card_edge_induce_eq_interedges (X : Finset A) :
    2 * (G.induce (X : Set A)).edgeFinset.card = (G.interedges X X).card := by
  classical
  let J := G.induce (X : Set A)
  let Q : Finset ({x // x ∈ X} × {x // x ∈ X}) :=
    Finset.univ.filter fun p => J.Adj p.1 p.2
  rw [J.two_mul_card_edgeFinset]
  let e : (↑Q) ≃ (↑(G.interedges X X)) :=
    { toFun := fun p => ⟨(p.1.1.1, p.1.2.1), by
          have hp := (Finset.mem_filter.1 p.2).2
          simpa [J, SimpleGraph.mem_interedges_iff] using
            (show p.1.1.1 ∈ X ∧ p.1.2.1 ∈ X ∧ G.Adj p.1.1.1 p.1.2.1 from
              ⟨p.1.1.2, p.1.2.2, hp⟩) ⟩
      invFun := fun p => ⟨(⟨p.1.1, ((G.mem_interedges_iff).mp p.2).1⟩,
          ⟨p.1.2, ((G.mem_interedges_iff).mp p.2).2.1⟩), by
            rw [Finset.mem_filter]
            exact ⟨Finset.mem_univ _, ((G.mem_interedges_iff).mp p.2).2.2⟩ ⟩
      left_inv := by intro p; apply Subtype.ext; rfl
      right_inv := by intro p; apply Subtype.ext; rfl }
  calc
    #((Finset.univ : Finset ({x // x ∈ X} × {x // x ∈ X})).filter
        fun p => J.Adj p.1 p.2) = Q.card := by rfl
    _ = Fintype.card (↑Q) := (Fintype.card_coe Q).symm
    _ = Fintype.card (↑(G.interedges X X)) := Fintype.card_congr e
    _ = (G.interedges X X).card := Fintype.card_coe _

/-- A union of many equal, mutually sparse blocks is itself sparse. -/
lemma sparse_equal_block_union
    {r m : ℕ} (U : Fin r → Finset A) (θ : ℝ)
    (hm : 0 < m) (hθ : 0 ≤ θ)
    (hcard : ∀ i, (U i).card = m)
    (hdis : ∀ {i j}, i ≠ j → Disjoint (U i) (U j))
    (hsparse : ∀ i j, i ≠ j → (G.edgeDensity (U i) (U j) : ℝ) < θ) :
    let X := Finset.univ.biUnion U
    ((2 * (G.induce (X : Set A)).edgeFinset.card : ℕ) : ℝ) ≤
      (r : ℝ) * m ^ 2 + θ * r ^ 2 * m ^ 2 := by
  classical
  dsimp
  let pairs : Finset (Fin r × Fin r) := Finset.univ ×ˢ Finset.univ
  let diag : Finset (Fin r × Fin r) := pairs.filter fun ij => ij.1 = ij.2
  let off : Finset (Fin r × Fin r) := pairs.filter fun ij => ij.1 ≠ ij.2
  have hdecomp : pairs = diag ∪ off := by
    ext ij
    simp [pairs, diag, off, Classical.em]
  have hdo : Disjoint diag off := by
    rw [Finset.disjoint_left]
    intro ij hd ho
    exact (Finset.mem_filter.1 ho).2 (Finset.mem_filter.1 hd).2
  have hdiagcard : diag.card = r := by
    let emb : Fin r ↪ Fin r × Fin r :=
      ⟨fun i => (i, i), fun i j h => congrArg Prod.fst h⟩
    have heq : diag = Finset.univ.map emb := by
      ext ij
      constructor
      · intro hij
        have heqij : ij.1 = ij.2 := (Finset.mem_filter.1 hij).2
        rw [Finset.mem_map]
        exact ⟨ij.1, Finset.mem_univ _, by ext <;> simp [emb, heqij]⟩
      · intro hij
        rw [Finset.mem_map] at hij
        obtain ⟨i, -, rfl⟩ := hij
        simp [diag, pairs, emb]
    rw [heq, Finset.card_map, Finset.card_univ, Fintype.card_fin]
  have hoffcard : off.card ≤ r ^ 2 := by
    calc
      off.card ≤ pairs.card := Finset.card_le_card (filter_subset _ _)
      _ = r ^ 2 := by simp [pairs, pow_two]
  have hinterdiag (ij : Fin r × Fin r) (hij : ij ∈ diag) :
      ((G.interedges (U ij.1) (U ij.2)).card : ℝ) ≤ m ^ 2 := by
    have := G.card_interedges_le_mul (U ij.1) (U ij.2)
    rw [hcard ij.1, hcard ij.2] at this
    norm_cast
    simpa [pow_two] using this
  have hinteroff (ij : Fin r × Fin r) (hij : ij ∈ off) :
      ((G.interedges (U ij.1) (U ij.2)).card : ℝ) ≤ θ * m ^ 2 := by
    have hne : ij.1 ≠ ij.2 := (Finset.mem_filter.1 hij).2
    have hdens := hsparse ij.1 ij.2 hne
    rw [SimpleGraph.edgeDensity_def, hcard ij.1, hcard ij.2] at hdens
    push_cast at hdens
    have hmR : (0 : ℝ) < (m : ℝ) * m := mul_pos (by exact_mod_cast hm) (by exact_mod_cast hm)
    have := (div_lt_iff₀ hmR).mp hdens
    nlinarith
  have hsumdiag :
      (∑ ij ∈ diag, ((G.interedges (U ij.1) (U ij.2)).card : ℝ)) ≤ r * m ^ 2 := by
    calc
      _ ≤ diag.card * (m : ℝ) ^ 2 :=
        by simpa [nsmul_eq_mul] using Finset.sum_le_card_nsmul _ _ _ hinterdiag
      _ = r * (m : ℝ) ^ 2 := by rw [hdiagcard]
  have hsumoff :
      (∑ ij ∈ off, ((G.interedges (U ij.1) (U ij.2)).card : ℝ)) ≤
        θ * r ^ 2 * m ^ 2 := by
    calc
      _ ≤ off.card * (θ * (m : ℝ) ^ 2) :=
        by simpa [nsmul_eq_mul] using Finset.sum_le_card_nsmul _ _ _ hinteroff
      _ ≤ (r : ℝ) ^ 2 * (θ * (m : ℝ) ^ 2) := by
        gcongr
        exact_mod_cast hoffcard
      _ = θ * (r : ℝ) ^ 2 * (m : ℝ) ^ 2 := by ring
  rw [two_mul_card_edge_induce_eq_interedges]
  have hinter := G.interedges_biUnion (Finset.univ : Finset (Fin r))
    (Finset.univ : Finset (Fin r)) U U
  rw [hinter]
  calc
    (((pairs.biUnion fun ij => G.interedges (U ij.1) (U ij.2)).card : ℕ) : ℝ) ≤
        ∑ ij ∈ pairs, ((G.interedges (U ij.1) (U ij.2)).card : ℝ) := by
          exact_mod_cast Finset.card_biUnion_le
    _ = (∑ ij ∈ diag, ((G.interedges (U ij.1) (U ij.2)).card : ℝ)) +
        ∑ ij ∈ off, ((G.interedges (U ij.1) (U ij.2)).card : ℝ) := by
          rw [hdecomp, Finset.sum_union hdo]
    _ ≤ (r : ℝ) * m ^ 2 + θ * r ^ 2 * m ^ 2 := add_le_add hsumdiag hsumoff

/-- A bounded-block version of `sparse_equal_block_union`. -/
lemma sparse_bounded_block_union
    {r b : ℕ} (U : Fin r → Finset A) (θ : ℝ)
    (hθ : 0 ≤ θ)
    (hne : ∀ i, (U i).Nonempty)
    (hcard : ∀ i, (U i).card ≤ b)
    (hsparse : ∀ i j, i ≠ j → (G.edgeDensity (U i) (U j) : ℝ) < θ) :
    let X := Finset.univ.biUnion U
    ((2 * (G.induce (X : Set A)).edgeFinset.card : ℕ) : ℝ) ≤
      (r : ℝ) * b ^ 2 + θ * r ^ 2 * b ^ 2 := by
  classical
  dsimp
  let pairs : Finset (Fin r × Fin r) := Finset.univ ×ˢ Finset.univ
  let diag : Finset (Fin r × Fin r) := pairs.filter fun ij => ij.1 = ij.2
  let off : Finset (Fin r × Fin r) := pairs.filter fun ij => ij.1 ≠ ij.2
  have hdecomp : pairs = diag ∪ off := by
    ext ij
    simp [pairs, diag, off, Classical.em]
  have hdo : Disjoint diag off := by
    rw [Finset.disjoint_left]
    intro ij hd ho
    exact (Finset.mem_filter.1 ho).2 (Finset.mem_filter.1 hd).2
  have hdiagcard : diag.card = r := by
    let emb : Fin r ↪ Fin r × Fin r :=
      ⟨fun i => (i, i), fun i j h => congrArg Prod.fst h⟩
    have heq : diag = Finset.univ.map emb := by
      ext ij
      constructor
      · intro hij
        have heqij : ij.1 = ij.2 := (Finset.mem_filter.1 hij).2
        rw [Finset.mem_map]
        exact ⟨ij.1, Finset.mem_univ _, by ext <;> simp [emb, heqij]⟩
      · intro hij
        rw [Finset.mem_map] at hij
        obtain ⟨i, -, rfl⟩ := hij
        simp [diag, pairs, emb]
    rw [heq, Finset.card_map, Finset.card_univ, Fintype.card_fin]
  have hoffcard : off.card ≤ r ^ 2 := by
    calc
      off.card ≤ pairs.card := Finset.card_le_card (filter_subset _ _)
      _ = r ^ 2 := by simp [pairs, pow_two]
  have hinterdiag (ij : Fin r × Fin r) (hij : ij ∈ diag) :
      ((G.interedges (U ij.1) (U ij.2)).card : ℝ) ≤ b ^ 2 := by
    calc
      ((G.interedges (U ij.1) (U ij.2)).card : ℝ) ≤
          ((U ij.1).card * (U ij.2).card : ℕ) := by
            exact_mod_cast G.card_interedges_le_mul (U ij.1) (U ij.2)
      _ ≤ (b : ℝ) ^ 2 := by
        exact_mod_cast (show (U ij.1).card * (U ij.2).card ≤ b ^ 2 by
          simpa [pow_two] using Nat.mul_le_mul (hcard ij.1) (hcard ij.2))
  have hinteroff (ij : Fin r × Fin r) (hij : ij ∈ off) :
      ((G.interedges (U ij.1) (U ij.2)).card : ℝ) ≤ θ * b ^ 2 := by
    have hneij : ij.1 ≠ ij.2 := (Finset.mem_filter.1 hij).2
    have hdens := hsparse ij.1 ij.2 hneij
    rw [SimpleGraph.edgeDensity_def] at hdens
    push_cast at hdens
    have hden : (0 : ℝ) < (U ij.1).card * (U ij.2).card := by
      exact mul_pos (by exact_mod_cast (hne ij.1).card_pos)
        (by exact_mod_cast (hne ij.2).card_pos)
    have hraw := (div_lt_iff₀ hden).mp hdens
    calc
      ((G.interedges (U ij.1) (U ij.2)).card : ℝ) ≤
          θ * ((U ij.1).card * (U ij.2).card) := hraw.le
      _ ≤ θ * (b : ℝ) ^ 2 := by
        gcongr
        exact_mod_cast (show (U ij.1).card * (U ij.2).card ≤ b ^ 2 by
          simpa [pow_two] using Nat.mul_le_mul (hcard ij.1) (hcard ij.2))
  have hsumdiag :
      (∑ ij ∈ diag, ((G.interedges (U ij.1) (U ij.2)).card : ℝ)) ≤ r * b ^ 2 := by
    calc
      _ ≤ diag.card * (b : ℝ) ^ 2 :=
        by simpa [nsmul_eq_mul] using Finset.sum_le_card_nsmul _ _ _ hinterdiag
      _ = r * (b : ℝ) ^ 2 := by rw [hdiagcard]
  have hsumoff :
      (∑ ij ∈ off, ((G.interedges (U ij.1) (U ij.2)).card : ℝ)) ≤
        θ * r ^ 2 * b ^ 2 := by
    calc
      _ ≤ off.card * (θ * (b : ℝ) ^ 2) :=
        by simpa [nsmul_eq_mul] using Finset.sum_le_card_nsmul _ _ _ hinteroff
      _ ≤ (r : ℝ) ^ 2 * (θ * (b : ℝ) ^ 2) := by
        gcongr
        exact_mod_cast hoffcard
      _ = θ * (r : ℝ) ^ 2 * (b : ℝ) ^ 2 := by ring
  rw [two_mul_card_edge_induce_eq_interedges]
  have hinter := G.interedges_biUnion (Finset.univ : Finset (Fin r))
    (Finset.univ : Finset (Fin r)) U U
  rw [hinter]
  calc
    (((pairs.biUnion fun ij => G.interedges (U ij.1) (U ij.2)).card : ℕ) : ℝ) ≤
        ∑ ij ∈ pairs, ((G.interedges (U ij.1) (U ij.2)).card : ℝ) := by
          exact_mod_cast Finset.card_biUnion_le
    _ = (∑ ij ∈ diag, ((G.interedges (U ij.1) (U ij.2)).card : ℝ)) +
        ∑ ij ∈ off, ((G.interedges (U ij.1) (U ij.2)).card : ℝ) := by
          rw [hdecomp, Finset.sum_union hdo]
    _ ≤ (r : ℝ) * b ^ 2 + θ * r ^ 2 * b ^ 2 := add_le_add hsumdiag hsumoff

end SparseUnion

section NumericalChoice

/-- A positive regularity scale satisfying both extraction and embedding requirements. -/
lemma exists_small_regularity_scale (q : ℝ) (N h : ℕ) (hq : 0 < q) :
    ∃ η : ℝ, 0 < η ∧ η < q ∧
      ((N - 1 : ℕ) : ℝ) ^ 2 * η < 1 ∧
      (h : ℝ) * η < q ^ h := by
  let a : ℝ := q
  let b : ℝ := 1 / ((((N - 1 : ℕ) : ℝ) ^ 2) + 1)
  let c : ℝ := q ^ h / ((h : ℝ) + 1)
  let t := min a (min b c)
  have ha : 0 < a := hq
  have hb : 0 < b := by positivity
  have hc : 0 < c := by positivity
  have ht : 0 < t := by simp [t, ha, hb, hc]
  refine ⟨t / 2, by positivity, ?_, ?_, ?_⟩
  · have hta : t ≤ a := min_le_left _ _
    have hta' : t ≤ q := by simpa [a] using hta
    linarith
  · have htb : t ≤ b := (min_le_right a _).trans (min_le_left b c)
    have hden : 0 < ((((N - 1 : ℕ) : ℝ) ^ 2) + 1) := by positivity
    have hmul : ((((N - 1 : ℕ) : ℝ) ^ 2) + 1) * (t / 2) < 1 := by
      have hlt : t / 2 < b := by linarith
      have hlt' : t / 2 < 1 / ((((N - 1 : ℕ) : ℝ) ^ 2) + 1) := by
        simpa [b] using hlt
      rw [lt_div_iff₀ hden] at hlt'
      nlinarith
    nlinarith [sq_nonneg (((N - 1 : ℕ) : ℝ))]
  · have htc : t ≤ c := (min_le_right a _).trans (min_le_right b c)
    have hhden : (0 : ℝ) < (h : ℝ) + 1 := by positivity
    have hmul : ((h : ℝ) + 1) * (t / 2) < q ^ h := by
      have hlt : t / 2 < c := by linarith
      have hlt' : t / 2 < q ^ h / ((h : ℝ) + 1) := by simpa [c] using hlt
      rw [lt_div_iff₀ hhden] at hlt'
      nlinarith
    nlinarith

/-- The numerical estimate used for a sparse union of regularity classes. -/
lemma sparse_numerical_bound {E r m x e : ℕ}
    (hE : 0 < E) (hr : 128 * E ≤ r) (hm : 0 < m) (hx : r * m ≤ x)
    (he : (e : ℝ) ≤
      (r : ℝ) * ((m + 1 : ℕ) : ℝ) ^ 2 +
        (1 / (1024 * (E : ℝ))) * (r : ℝ) ^ 2 * ((m + 1 : ℕ) : ℝ) ^ 2) :
    E * e ≤ x * (x - 1) := by
  have hER : (0 : ℝ) < E := by exact_mod_cast hE
  have hEone : (1 : ℝ) ≤ E := by exact_mod_cast hE
  have hrR : (128 : ℝ) * E ≤ r := by exact_mod_cast hr
  have hmR : (1 : ℝ) ≤ m := by exact_mod_cast hm
  have hxR : (r : ℝ) * m ≤ x := by exact_mod_cast hx
  have hr128 : (128 : ℝ) ≤ r := by nlinarith
  have hx128 : (128 : ℝ) ≤ x := by
    have hrm : (r : ℝ) ≤ r * m := by nlinarith
    linarith
  have hb : (((m + 1 : ℕ) : ℝ)) ≤ 2 * (m : ℝ) := by
    push_cast
    linarith
  have hb2 : (((m + 1 : ℕ) : ℝ)) ^ 2 ≤ 4 * (m : ℝ) ^ 2 := by
    nlinarith [sq_nonneg (((m + 1 : ℕ) : ℝ)), sq_nonneg (m : ℝ)]
  have hEr : (E : ℝ) * r ≤ (r : ℝ) ^ 2 / 128 := by
    have hrnonneg : (0 : ℝ) ≤ r := by positivity
    nlinarith [mul_nonneg hrnonneg (sub_nonneg.mpr hrR)]
  have hEt : (E : ℝ) * (1 / (1024 * (E : ℝ))) = 1 / 1024 := by
    field_simp
  have he' : (E : ℝ) * e ≤ (9 / 256 : ℝ) * ((r : ℝ) * m) ^ 2 := by
    calc
      (E : ℝ) * e ≤ (E : ℝ) *
          ((r : ℝ) * ((m + 1 : ℕ) : ℝ) ^ 2 +
            (1 / (1024 * (E : ℝ))) * (r : ℝ) ^ 2 *
              ((m + 1 : ℕ) : ℝ) ^ 2) := by gcongr
      _ = ((E : ℝ) * r +
          ((E : ℝ) * (1 / (1024 * (E : ℝ)))) * (r : ℝ) ^ 2) *
          ((m + 1 : ℕ) : ℝ) ^ 2 := by ring
      _ = ((E : ℝ) * r + (1 / 1024 : ℝ) * (r : ℝ) ^ 2) *
          ((m + 1 : ℕ) : ℝ) ^ 2 := by rw [hEt]
      _ ≤ (((r : ℝ) ^ 2 / 128) + (1 / 1024 : ℝ) * (r : ℝ) ^ 2) *
          ((m + 1 : ℕ) : ℝ) ^ 2 := by gcongr
      _ = (9 / 1024 : ℝ) * (r : ℝ) ^ 2 *
          ((m + 1 : ℕ) : ℝ) ^ 2 := by ring
      _ ≤ (9 / 1024 : ℝ) * (r : ℝ) ^ 2 * (4 * (m : ℝ) ^ 2) := by
        gcongr
      _ = (9 / 256 : ℝ) * ((r : ℝ) * m) ^ 2 := by ring
  have hxx : (9 / 256 : ℝ) * ((r : ℝ) * m) ^ 2 ≤
      (9 / 256 : ℝ) * (x : ℝ) ^ 2 := by
    gcongr
  have hxone : 1 ≤ x := by exact_mod_cast (show (1 : ℝ) ≤ x by linarith)
  have hfinalR : (E : ℝ) * e ≤ (x : ℝ) * ((x : ℝ) - 1) := by
    nlinarith [he'.trans hxx, sq_nonneg (x : ℝ)]
  have hcast : ((E * e : ℕ) : ℝ) ≤ ((x * (x - 1) : ℕ) : ℝ) := by
    push_cast [Nat.cast_sub hxone]
    exact hfinalR
  exact_mod_cast hcast

end NumericalChoice

section RodlTheorem

/-- Taking an induced subgraph commutes with complementation. -/
lemma compl_induce_eq_induce_compl
    {A : Type*} (G : SimpleGraph A) (S : Set A) :
    (G.induce S)ᶜ = Gᶜ.induce S := by
  ext x y
  simp [SimpleGraph.compl_adj, Subtype.ext_iff]

/-- The selected pairwise-disjoint blocks contribute the sum of their cardinalities. -/
lemma card_biUnion_eq_sum_of_pairwise_disjoint
    {A : Type*} [DecidableEq A] {r : ℕ} (U : Fin r → Finset A)
    (hdis : ∀ {i j}, i ≠ j → Disjoint (U i) (U j)) :
    (Finset.univ.biUnion U).card = ∑ i : Fin r, (U i).card := by
  classical
  apply Finset.card_biUnion
  intro i hi j hj hij
  exact hdis hij

/--
---
conclusion: Lax54.RodlTheorem.rodl_theorem
---
Proof of Rödl's theorem. Regularity and Turán's theorem produce a large family
of pairwise regular classes. A three-color Ramsey argument yields either a
sparse union in the graph, a sparse union in its complement, or sufficiently
many intermediate-density pairs to embed an induced copy of the forbidden
graph.
-/
theorem rodl_theorem :
    ∀ {W : Type u} [Fintype W] (H : SimpleGraph W) (E : ℕ),
      0 < E → ∃ D : ℕ, 0 < D ∧
        ∀ {V : Type v} [Fintype V] [DecidableEq V] (G : SimpleGraph V)
          [DecidableRel G.Adj],
          ¬ H ⊴ G →
            ∃ X : Finset V, Fintype.card V ≤ D * X.card ∧
              HasSparseSide (G.induce (X : Set V)) E := by
  classical
  intro W _ H E hE
  let h := Fintype.card W
  let r := max (128 * E) h
  have hrE : 128 * E ≤ r := le_max_left _ _
  have hhr : h ≤ r := le_max_right _ _
  have hrpos : 0 < r := by
    have : 0 < 128 * E := Nat.mul_pos (by norm_num) hE
    exact this.trans_le hrE
  let N := ramseyBound 3 r
  have hrN : r ≤ N := by
    have hrm : r ≤ 3 * (r - 1) + 1 := by omega
    exact hrm.trans (by
      simpa [N, ramseyBound] using
        (le_focusBound (q := 3) (n := 3 * (r - 1) + 1) (by norm_num)))
  have hNtwo : 2 ≤ N := by omega
  let β : ℝ := 1 / (1024 * (E : ℝ))
  let q : ℝ := β / 2
  have hβ : 0 < β := by dsimp [β]; positivity
  have hq : 0 < q := by dsimp [q]; positivity
  obtain ⟨η, hη, hηq, hηextract, hηembed⟩ :=
    exists_small_regularity_scale q N h hq
  let M := SzemerediRegularity.bound η N
  have hMpos : 0 < M := by
    simpa [M] using SzemerediRegularity.bound_pos η N
  have hNM : N ≤ M := by
    simpa [M] using SzemerediRegularity.le_bound η N
  refine ⟨2 * M, by positivity, ?_⟩
  intro V _ _ G _ hfree
  by_cases hnlarge : N ≤ Fintype.card V
  · obtain ⟨P, hPeq, hNP, hPM, hPunif⟩ :=
      szemeredi_regularity G hη hnlarge
    obtain ⟨classes, hclasses_inj, hclasses_mem, hclasses_uniform⟩ :=
      exists_pairwise_uniform_parts G P η N hNtwo hNP hηextract hPunif
    let edgeColour : Fin N → Fin N → Fin 3 := fun i j =>
      if G.edgeDensity (classes i) (classes j) < β then ⟨0, by omega⟩
      else if Gᶜ.edgeDensity (classes i) (classes j) < β then ⟨1, by omega⟩
      else ⟨2, by omega⟩
    have hcolour_symm : ∀ i j, edgeColour i j = edgeColour j i := by
      intro i j
      simp only [edgeColour]
      rw [G.edgeDensity_comm (classes i) (classes j),
        Gᶜ.edgeDensity_comm (classes i) (classes j)]
    obtain ⟨sel, hsel_inj, -, colour, hmono⟩ :=
      exists_monochromatic_tuple (q := 3) (r := r) (by norm_num) hrpos
        edgeColour Finset.univ hcolour_symm (by simp [N])
    let U : Fin r → Finset V := fun i => classes (sel i)
    have hUmem (i : Fin r) : U i ∈ P.parts := hclasses_mem (sel i)
    have hUne (i : Fin r) : (U i).Nonempty := P.nonempty_of_mem_parts (hUmem i)
    have hUinj : Function.Injective U := hclasses_inj.comp hsel_inj
    have hUdis : ∀ {i j : Fin r}, i ≠ j → Disjoint (U i) (U j) := by
      intro i j hij
      exact P.disjoint (hUmem i) (hUmem j) (hUinj.ne hij)
    have hUuniform : ∀ i j : Fin r, i ≠ j → G.IsUniform η (U i) (U j) := by
      intro i j hij
      exact hclasses_uniform (sel i) (sel j) (hsel_inj.ne hij)
    let m := Fintype.card V / P.parts.card
    have hkpos : 0 < P.parts.card := lt_of_lt_of_le (by omega : 0 < N) hNP
    have hkV : P.parts.card ≤ Fintype.card V := by
      simpa using P.card_parts_le_card
    have hmpos : 0 < m := by
      exact Nat.div_pos hkV hkpos
    have hUlower (i : Fin r) : m ≤ (U i).card := by
      simpa [m] using hPeq.average_le_card_part (hUmem i)
    have hUupper (i : Fin r) : (U i).card ≤ m + 1 := by
      simpa [m] using hPeq.card_part_le_average_add_one (hUmem i)
    let X : Finset V := Finset.univ.biUnion U
    have hXcard : X.card = ∑ i : Fin r, (U i).card := by
      simpa [X] using card_biUnion_eq_sum_of_pairwise_disjoint U hUdis
    have hXlower : r * m ≤ X.card := by
      rw [hXcard]
      calc
        r * m = ∑ _i : Fin r, m := by simp
        _ ≤ ∑ i : Fin r, (U i).card := Finset.sum_le_sum fun i _ => hUlower i
    have hmX : m ≤ X.card := by
      have hrone : 1 ≤ r := hrpos
      exact (Nat.le_mul_of_pos_left m hrpos).trans hXlower
    have hn_partition : Fintype.card V < P.parts.card * (m + 1) := by
      simpa [m, Nat.mul_comm] using
        (Nat.lt_mul_of_div_lt (Nat.lt_succ_self (Fintype.card V / P.parts.card)) hkpos)
    have hn_two : Fintype.card V ≤ 2 * P.parts.card * m := by
      have hmone : m + 1 ≤ 2 * m := by omega
      calc
        Fintype.card V ≤ P.parts.card * (m + 1) := hn_partition.le
        _ ≤ P.parts.card * (2 * m) := Nat.mul_le_mul_left _ hmone
        _ = 2 * P.parts.card * m := by ring
    have hsize : Fintype.card V ≤ (2 * M) * X.card := by
      calc
        Fintype.card V ≤ 2 * P.parts.card * m := hn_two
        _ ≤ 2 * M * X.card := by gcongr
        _ = (2 * M) * X.card := rfl
    have hβ1 : β ≤ 1 := by
      dsimp [β]
      have hER : (1 : ℝ) ≤ E := by exact_mod_cast hE
      have : (1 : ℝ) ≤ 1024 * E := by nlinarith
      exact (div_le_one (by positivity)).2 this
    fin_cases colour
    · have hsparse : ∀ i j : Fin r, i ≠ j →
          (G.edgeDensity (U i) (U j) : ℝ) < β := by
        intro i j hij
        have hc := hmono i j hij
        by_contra hg
        by_cases hgc : (Gᶜ.edgeDensity (U i) (U j) : ℝ) < β
        · simp [edgeColour, U, hg, hgc] at hc
        · simp [edgeColour, U, hg, hgc] at hc
      have hedge := sparse_bounded_block_union G U β hβ.le hUne hUupper hsparse
      refine ⟨X, hsize, Or.inl ?_⟩
      have hnum := sparse_numerical_bound hE hrE hmpos hXlower (e :=
        2 * (G.induce (X : Set V)).edgeFinset.card) (by
          simpa [X, β] using hedge)
      simpa [HasSparseSide, Nat.mul_assoc] using hnum
    · have hsparse : ∀ i j : Fin r, i ≠ j →
          (Gᶜ.edgeDensity (U i) (U j) : ℝ) < β := by
        intro i j hij
        have hc := hmono i j hij
        by_contra hgc
        by_cases hg : (G.edgeDensity (U i) (U j) : ℝ) < β
        · simp [edgeColour, U, hg] at hc
        · simp [edgeColour, U, hg, hgc] at hc
      have hedge := sparse_bounded_block_union Gᶜ U β hβ.le hUne hUupper hsparse
      refine ⟨X, hsize, Or.inr ?_⟩
      have hnum := sparse_numerical_bound hE hrE hmpos hXlower (e :=
        2 * (Gᶜ.induce (X : Set V)).edgeFinset.card) (by
          simpa [X, β] using hedge)
      have hedgeeq : ((G.induce (X : Set V))ᶜ).edgeFinset =
          (Gᶜ.induce (X : Set V)).edgeFinset := by
        ext e
        simp only [SimpleGraph.mem_edgeFinset]
        rw [compl_induce_eq_induce_compl]
      rw [hedgeeq]
      simpa [HasSparseSide, Nat.mul_assoc] using hnum
    · have hmiddle : ∀ i j : Fin r, i ≠ j →
          β ≤ G.edgeDensity (U i) (U j) ∧
            β ≤ Gᶜ.edgeDensity (U i) (U j) := by
        intro i j hij
        have hc := hmono i j hij
        constructor
        · apply le_of_not_gt
          intro hg
          simp [edgeColour, U, hg] at hc
        · apply le_of_not_gt
          intro hgc
          by_cases hg : (G.edgeDensity (U i) (U j) : ℝ) < β
          · simp [edgeColour, U, hg] at hc
          · simp [edgeColour, U, hg, hgc] at hc
      let eW : W → Fin h := Fintype.equivFin W
      let embedIndex : W → Fin r := fun w => Fin.castLE hhr (eW w)
      let UH : W → Finset V := fun w => U (embedIndex w)
      have hembedIndex : Function.Injective embedIndex :=
        (Fin.castLE_injective hhr).comp (Fintype.equivFin W).injective
      have hUHne (w : W) : (UH w).Nonempty := hUne (embedIndex w)
      have hUHdis : ∀ {i j : W}, i ≠ j → Disjoint (UH i) (UH j) := by
        intro i j hij
        exact hUdis (hembedIndex.ne hij)
      have hUHunif : ∀ i j : W, i ≠ j → G.IsUniform η (UH i) (UH j) := by
        intro i j hij
        exact hUuniform (embedIndex i) (embedIndex j) (hembedIndex.ne hij)
      have hUHlow : ∀ i j : W, i ≠ j → β ≤ G.edgeDensity (UH i) (UH j) := by
        intro i j hij
        exact (hmiddle (embedIndex i) (embedIndex j) (hembedIndex.ne hij)).1
      have hUHhigh : ∀ i j : W, i ≠ j →
          G.edgeDensity (UH i) (UH j) ≤ 1 - β := by
        intro i j hij
        have hc := (hmiddle (embedIndex i) (embedIndex j) (hembedIndex.ne hij)).2
        have hsum := G.edgeDensity_add_edgeDensity_compl
          (hUHne i) (hUHne j) (hUHdis hij)
        have hsumR : (G.edgeDensity (UH i) (UH j) : ℝ) +
            Gᶜ.edgeDensity (UH i) (UH j) = 1 := by exact_mod_cast hsum
        linarith
      have hq1 : q ≤ 1 := by dsimp [q]; linarith
      have hqβ : q + η ≤ β := by
        dsimp [q] at hηq ⊢
        linarith
      have hinduced : H ⊴ G := induced_copy_of_uniform_middle H G UH η β q
        hUHne hUHdis hUHunif hUHlow hUHhigh hη.le hq hq1 hqβ
        (by simpa [h] using hηembed)
      exact (hfree hinduced).elim
  · have hnsmall : Fintype.card V < N := Nat.lt_of_not_ge hnlarge
    by_cases hVzero : Fintype.card V = 0
    · refine ⟨∅, by simp [hVzero], ?_⟩
      left
      have hbot : G.induce (((∅ : Finset V) : Set V)) = ⊥ := by
        ext x y
        have hxfalse : False := by simpa using x.property
        exact hxfalse.elim
      have hedgeempty : (G.induce (((∅ : Finset V) : Set V))).edgeFinset = ∅ :=
        SimpleGraph.edgeFinset_eq_empty.mpr hbot
      rw [hedgeempty]
      simp
    · have hVpos : 0 < Fintype.card V := Nat.pos_of_ne_zero hVzero
      let v : V := (Fintype.card_pos_iff.mp hVpos).some
      refine ⟨{v}, ?_, ?_⟩
      · simp only [Finset.card_singleton, mul_one]
        exact hnsmall.le.trans (hNM.trans (Nat.le_mul_of_pos_left M (by norm_num)))
      · left
        have hbot : G.induce ((({v} : Finset V) : Set V)) = ⊥ := by
          ext ⟨x, hx⟩ ⟨y, hy⟩
          simp only [SimpleGraph.bot_adj, iff_false]
          intro hxy
          have hxv : x = v := by simpa using hx
          have hyv : y = v := by simpa using hy
          subst x
          subst y
          exact G.loopless.irrefl _ hxy
        have hedgeempty : (G.induce ((({v} : Finset V) : Set V))).edgeFinset = ∅ :=
          SimpleGraph.edgeFinset_eq_empty.mpr hbot
        rw [hedgeempty]
        simp

end RodlTheorem

end Lax54Proofs.RodlTheorem
