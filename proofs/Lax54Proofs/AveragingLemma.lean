import Lax54.AveragingLemma
import Mathlib.Combinatorics.SimpleGraph.Density
import Mathlib.Combinatorics.SimpleGraph.DegreeSum
import Mathlib.Data.Finset.Powerset
import Mathlib.Tactic

namespace Lax54Proofs

open Finset
open scoped BigOperators

universe u

/-- Ordered edges of an induced graph are the ordered edges of the ambient
graph with both endpoints in the inducing set. -/
theorem twice_card_edges_induce_eq_card_interedges
    {V : Type u} [Fintype V] [DecidableEq V] (G : SimpleGraph V)
    [DecidableRel G.Adj] (Y : Finset V) :
    2 * (G.induce (Y : Set V)).edgeFinset.card = (G.interedges Y Y).card := by
  rw [SimpleGraph.two_mul_card_edgeFinset]
  refine Finset.card_bij
    (fun p (_ : p ∈ (Finset.univ.filter fun (x, y) ↦
      (G.induce (Y : Set V)).Adj x y)) ↦ (p.1.1, p.2.1)) ?_ ?_ ?_
  · intro p hp
    simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hp
    rw [SimpleGraph.mem_interedges_iff]
    exact ⟨p.1.2, p.2.2, hp⟩
  · intro a ha b hb hab
    apply Prod.ext
    · exact Subtype.ext (congrArg Prod.fst hab)
    · exact Subtype.ext (congrArg Prod.snd hab)
  · intro p hp
    rw [SimpleGraph.mem_interedges_iff] at hp
    have hpm := hp
    let x : {v : V // v ∈ Y} := ⟨p.1, hpm.1⟩
    let y : {v : V // v ∈ Y} := ⟨p.2, hpm.2.1⟩
    refine ⟨(x, y), ?_, rfl⟩
    simpa [x, y] using hpm.2.2

/-- Double-count ordered edges over all `k`-subsets. Every ordered edge is
contained in exactly `choose (n-2) (k-2)` such subsets. -/
theorem sum_card_interedges_powersetCard
    {V : Type u} [Fintype V] [DecidableEq V] (G : SimpleGraph V)
    [DecidableRel G.Adj] (Z : Finset V) (k : ℕ) (hk : 2 ≤ k) :
    ∑ Y ∈ Z.powersetCard k, (G.interedges Y Y).card =
      (G.interedges Z Z).card * Nat.choose (Z.card - 2) (k - 2) := by
  classical
  let Ω := Z.powersetCard k
  let D := G.interedges Z Z
  calc
    ∑ Y ∈ Ω, (G.interedges Y Y).card =
        ∑ Y ∈ Ω, ∑ e ∈ D, if ({e.1, e.2} : Finset V) ⊆ Y then 1 else 0 := by
      apply Finset.sum_congr rfl
      intro Y hY
      have hYZ : Y ⊆ Z := (Finset.mem_powersetCard.mp hY).1
      rw [← Finset.card_filter]
      congr 1
      ext e
      rw [Finset.mem_filter, SimpleGraph.mem_interedges_iff]
      constructor
      · rintro ⟨he₁, he₂, hadj⟩
        refine ⟨?_, ?_⟩
        · rw [SimpleGraph.mem_interedges_iff]
          exact ⟨hYZ he₁, hYZ he₂, hadj⟩
        · intro x hx
          simp only [Finset.mem_insert, Finset.mem_singleton] at hx
          rcases hx with rfl | rfl
          · exact he₁
          · exact he₂
      · rintro ⟨heD, hpair⟩
        rw [SimpleGraph.mem_interedges_iff] at heD
        exact ⟨hpair (by simp), hpair (by simp), heD.2.2⟩
    _ = ∑ e ∈ D, ∑ Y ∈ Ω,
          if ({e.1, e.2} : Finset V) ⊆ Y then 1 else 0 := by
      rw [Finset.sum_comm]
    _ = ∑ _e ∈ D, Nat.choose (Z.card - 2) (k - 2) := by
      apply Finset.sum_congr rfl
      intro e he
      rw [← Finset.card_filter]
      have hedata : e.1 ∈ Z ∧ e.2 ∈ Z ∧ G.Adj e.1 e.2 := by
        rw [SimpleGraph.mem_interedges_iff] at he
        exact he
      have hadj : G.Adj e.1 e.2 := hedata.2.2
      have hpair : ({e.1, e.2} : Finset V).card = 2 := by
        simp [G.ne_of_adj hadj]
      rw [Finset.card_filter_powersetCard_subset
        ({e.1, e.2} : Finset V) Z k
          (by
            intro x hx
            simp only [Finset.mem_insert, Finset.mem_singleton] at hx
            rcases hx with rfl | rfl
            · exact hedata.1
            · exact hedata.2.1)
          (by omega)]
      simp [hpair]
    _ = (G.interedges Z Z).card * Nat.choose (Z.card - 2) (k - 2) := by
      simp [D]

/-- The binomial identity obtained by marking an ordered pair in a
`k`-subset. -/
theorem choose_mul_falling_two
    (n k : ℕ) (hk : 2 ≤ k) :
    Nat.choose n k * k * (k - 1) =
      n * (n - 1) * Nat.choose (n - 2) (k - 2) := by
  have hchoose := Nat.choose_mul (n := n) (k := k) (s := 2) hk
  rw [Nat.choose_two_right, Nat.choose_two_right] at hchoose
  have hk_even : 2 ∣ k * (k - 1) := (Nat.even_mul_pred_self k).two_dvd
  have hn_even : 2 ∣ n * (n - 1) := (Nat.even_mul_pred_self n).two_dvd
  have hk_cancel : k * (k - 1) / 2 * 2 = k * (k - 1) :=
    Nat.div_mul_cancel hk_even
  have hn_cancel : n * (n - 1) / 2 * 2 = n * (n - 1) :=
    Nat.div_mul_cancel hn_even
  calc
    Nat.choose n k * k * (k - 1) =
        Nat.choose n k * (k * (k - 1)) := by ring
    _ = Nat.choose n k * ((k * (k - 1) / 2) * 2) := by
      rw [hk_cancel]
    _ = (Nat.choose n k * (k * (k - 1) / 2)) * 2 := by ring
    _ = ((n * (n - 1) / 2) * Nat.choose (n - 2) (k - 2)) * 2 := by
      rw [hchoose]
    _ = ((n * (n - 1) / 2) * 2) * Nat.choose (n - 2) (k - 2) := by ring
    _ = n * (n - 1) * Nat.choose (n - 2) (k - 2) := by rw [hn_cancel]

/-- Averaging over all `k`-subsets produces one whose ordered-edge density is
no larger than that of the ambient graph. -/
theorem exists_sparse_powersetCard
    {V : Type u} [Fintype V] [DecidableEq V] (G : SimpleGraph V)
    [DecidableRel G.Adj] (Z : Finset V) (E k : ℕ) (hk : 2 ≤ k)
    (hkn : k ≤ Z.card)
    (hsparse : E * 2 * (G.induce (Z : Set V)).edgeFinset.card ≤
      Z.card * (Z.card - 1)) :
    ∃ Y ∈ Z.powersetCard k,
      E * (G.interedges Y Y).card ≤ k * (k - 1) := by
  classical
  let Ω := Z.powersetCard k
  have hΩ : Ω.Nonempty := by
    rw [Finset.nonempty_iff_ne_empty, ne_eq, Finset.powersetCard_eq_empty]
    omega
  have hinteredges_univ :
      (G.interedges Z Z).card =
        2 * (G.induce (Z : Set V)).edgeFinset.card :=
    (twice_card_edges_induce_eq_card_interedges G Z).symm
  have htotal :
      ∑ Y ∈ Ω, E * (G.interedges Y Y).card ≤
        ∑ _Y ∈ Ω, k * (k - 1) := by
    rw [← Finset.mul_sum, sum_card_interedges_powersetCard G Z k hk,
      hinteredges_univ]
    simp only [Finset.sum_const, nsmul_eq_mul]
    rw [show Ω.card = Nat.choose Z.card k by simp [Ω]]
    calc
      E * (2 * (G.induce (Z : Set V)).edgeFinset.card *
          Nat.choose (Z.card - 2) (k - 2)) =
          (E * 2 * (G.induce (Z : Set V)).edgeFinset.card) *
            Nat.choose (Z.card - 2) (k - 2) := by ring
      _ ≤ (Z.card * (Z.card - 1)) *
            Nat.choose (Z.card - 2) (k - 2) :=
        Nat.mul_le_mul_right _ hsparse
      _ = Nat.choose Z.card k * (k * (k - 1)) := by
        rw [← choose_mul_falling_two Z.card k hk]
        ring
  obtain ⟨Y, hYΩ, hY⟩ := Finset.exists_le_of_sum_le hΩ htotal
  exact ⟨Y, hYΩ, hY⟩

/--
An elementary averaging principle: if each of `N` values were at least `b`,
their sum would be at least `N*b`. Thus a strict upper bound on the sum gives
a value below `b`.
-/
theorem exists_lt_of_sum_lt_card_mul
    {I : Type u} [Fintype I] (f : I → ℕ) (b : ℕ)
    (h : ∑ i, f i < Fintype.card I * b) : ∃ i, f i < b := by
  by_contra hn
  push Not at hn
  have := Finset.sum_le_sum fun i (_ : i ∈ (Finset.univ : Finset I)) ↦ hn i
  have : Fintype.card I * b ≤ ∑ i, f i := by
    simpa using this
  omega

/-- If at most `m-1` vertices are bad in a `2m-1` set, at least `m` are good. -/
theorem card_filter_ge_of_bad_lt
    {V : Type u} [DecidableEq V] (Y : Finset V) (bad : V → Prop)
    [DecidablePred bad] (m : ℕ) (hY : Y.card = 2 * m - 1)
    (hbad : (Y.filter bad).card < m) :
    m ≤ (Y.filter fun x ↦ ¬ bad x).card := by
  have hpartition := Finset.card_filter_add_card_filter_not (s := Y) bad
  omega

/--
The second half of the paper's proof of Lemma 4.2: from a `2m-1` vertex set
with fewer than `m` high-degree vertices, choose `m` low-degree vertices.
-/
theorem choose_low_degree_subset
    {V : Type u} [Fintype V] [DecidableEq V] (G : SimpleGraph V)
    [DecidableRel G.Adj] (Y : Finset V) (E m b : ℕ)
    (hY : Y.card = 2 * m - 1)
    (hbad : (Y.attach.filter fun y ↦
      b < E * (G.induce (Y : Set V)).degree y).card < m) :
    ∃ X : Finset V, X ⊆ Y ∧ X.card = m ∧
      ∀ x : {v : V // v ∈ X}, E * (G.induce (X : Set V)).degree x ≤ b := by
  classical
  let bad : V → Prop := fun y ↦
    ∃ hy : y ∈ Y, b < E * (G.induce (Y : Set V)).degree ⟨y, hy⟩
  let good := Y.filter fun y ↦ ¬ bad y
  have hgood : m ≤ good.card := by
    apply card_filter_ge_of_bad_lt Y bad m hY
    let source := Y.attach.filter fun y ↦
      b < E * (G.induce (Y : Set V)).degree y
    have hcardeq : source.card = (Y.filter bad).card := by
      refine Finset.card_bij (fun y (_ : y ∈ source) ↦ y.1) ?_ ?_ ?_
      · intro y hy
        have hydata := Finset.mem_filter.mp hy
        rw [Finset.mem_filter]
        exact ⟨y.2, ⟨y.2, hydata.2⟩⟩
      · intro y₁ hy₁ y₂ hy₂ heq
        exact Subtype.ext heq
      · intro y hy
        have hydata := Finset.mem_filter.mp hy
        have hyY : y ∈ Y := hydata.1
        have hybad : bad y := hydata.2
        change ∃ hy' : y ∈ Y,
          b < E * (G.induce (Y : Set V)).degree ⟨y, hy'⟩ at hybad
        obtain ⟨hy', hineq⟩ := hybad
        let y' : {v : V // v ∈ Y} := ⟨y, hyY⟩
        refine ⟨y', ?_, rfl⟩
        rw [Finset.mem_filter]
        exact ⟨Finset.mem_attach _ _, by simpa [y'] using hineq⟩
    rw [← hcardeq]
    exact hbad
  obtain ⟨X, hXY, hXcard⟩ := Finset.exists_subset_card_eq hgood
  have hXY' : X ⊆ Y := hXY.trans (Finset.filter_subset _ _)
  refine ⟨X, hXY', hXcard, ?_⟩
  intro x
  have hxgood : x.1 ∈ good := hXY x.2
  have hxY : x.1 ∈ Y := (Finset.mem_filter.mp hxgood).1
  have hlowY : E * (G.induce (Y : Set V)).degree ⟨x.1, hxY⟩ ≤ b := by
    have := (Finset.mem_filter.mp hxgood).2
    simp only [bad, not_exists] at this
    exact le_of_not_gt (this hxY)
  have hdeg : (G.induce (X : Set V)).degree x ≤
      (G.induce (Y : Set V)).degree ⟨x.1, hxY⟩ := by
    rw [← SimpleGraph.card_neighborFinset_eq_degree,
      ← SimpleGraph.card_neighborFinset_eq_degree]
    rw [← Finset.card_map (f := Function.Embedding.subtype (fun v ↦ v ∈ X)),
      ← Finset.card_map (f := Function.Embedding.subtype (fun v ↦ v ∈ Y))]
    apply Finset.card_le_card
    intro z hz
    obtain ⟨w, hw, rfl⟩ := Finset.mem_map.mp hz
    let wY : {v : V // v ∈ Y} := ⟨w.1, hXY' w.2⟩
    refine Finset.mem_map.mpr ⟨wY, ?_, rfl⟩
    rw [SimpleGraph.mem_neighborFinset] at hw ⊢
    exact hw
  exact (Nat.mul_le_mul_left E hdeg).trans hlowY

/-- In the sampled `2m-1` set, fewer than `m` vertices can exceed the
degree threshold `4(m-1)/E`. -/
theorem card_high_degree_lt
    {V : Type u} [Fintype V] [DecidableEq V] (G : SimpleGraph V)
    [DecidableRel G.Adj] (Y : Finset V) (E m : ℕ) (hm : 2 ≤ m)
    (hY : Y.card = 2 * m - 1)
    (havg : E * (G.interedges Y Y).card ≤
      (2 * m - 1) * (2 * m - 1 - 1)) :
    (Y.attach.filter fun y ↦
      4 * (m - 1) < E * (G.induce (Y : Set V)).degree y).card < m := by
  classical
  let H := G.induce (Y : Set V)
  let bad := Y.attach.filter fun y ↦ 4 * (m - 1) < E * H.degree y
  have hsum_eq :
      ∑ y ∈ Y.attach, E * H.degree y = E * (G.interedges Y Y).card := by
    calc
      ∑ y ∈ Y.attach, E * H.degree y = E * ∑ y ∈ Y.attach, H.degree y := by
        rw [Finset.mul_sum]
      _ = E * ∑ y : {v : V // v ∈ Y}, H.degree y := by
        rw [Finset.attach_eq_univ]
      _ = E * (2 * H.edgeFinset.card) := by
        rw [SimpleGraph.sum_degrees_eq_twice_card_edges]
      _ = E * (G.interedges Y Y).card := by
        rw [twice_card_edges_induce_eq_card_interedges]
  have hbad_each : ∀ y ∈ bad,
      4 * (m - 1) + 1 ≤ E * H.degree y := by
    intro y hy
    have := (Finset.mem_filter.mp hy).2
    omega
  have hbad_lower : bad.card * (4 * (m - 1) + 1) ≤
      ∑ y ∈ Y.attach, E * H.degree y := by
    calc
      bad.card * (4 * (m - 1) + 1) =
          ∑ _y ∈ bad, (4 * (m - 1) + 1) := by simp
      _ ≤ ∑ y ∈ bad, E * H.degree y :=
        Finset.sum_le_sum hbad_each
      _ ≤ ∑ y ∈ Y.attach, E * H.degree y :=
        Finset.sum_le_sum_of_subset (Finset.filter_subset _ _)
  change bad.card < m
  by_contra hnot
  have hmbad : m ≤ bad.card := by omega
  have hlower : m * (4 * (m - 1) + 1) ≤
      ∑ y ∈ Y.attach, E * H.degree y :=
    (Nat.mul_le_mul_right _ hmbad).trans hbad_lower
  have hupper : ∑ y ∈ Y.attach, E * H.degree y ≤
      (2 * m - 1) * (2 * m - 1 - 1) := by
    rw [hsum_eq]
    exact havg
  obtain ⟨r, rfl⟩ : ∃ r, m = r + 2 := by
    use m - 2
    omega
  have h₁ : r + 2 - 1 = r + 1 := by omega
  have h₂ : 2 * (r + 2) - 1 = 2 * r + 3 := by omega
  rw [h₁] at hlower
  rw [h₂] at hupper
  have h₃ : 2 * r + 3 - 1 = 2 * r + 2 := by omega
  rw [h₃] at hupper
  have hgap :
      (r + 2) * (4 * (r + 1) + 1) =
        (2 * r + 3) * (2 * r + 2) + (3 * r + 4) := by ring
  omega

/--
---
conclusion: Lax54.AveragingLemma.sparse_graph_thinning
---
Proof of Lemma 4.2. Average the ordered edge count over all
$(2m-1)$-element subsets, select a subset no denser than the ambient graph,
and retain $m$ vertices whose degrees do not exceed the stated bound.
-/
theorem sparse_graph_thinning :
    ∀ {V : Type u} [Fintype V] [DecidableEq V] (G : SimpleGraph V)
      [DecidableRel G.Adj] (Z : Finset V) (E m : ℕ),
      0 < E → 2 * m ≤ Z.card + 1 →
      E * 2 * (G.induce (Z : Set V)).edgeFinset.card ≤
        Z.card * (Z.card - 1) →
      ∃ X : Finset V, X ⊆ Z ∧ X.card = m ∧
        ∀ x : {v : V // v ∈ X},
          E * (G.induce (X : Set V)).degree x ≤ 4 * (m - 1) := by
  intro V _ _ G _ Z E m hE hsize hsparse
  classical
  rcases m with _ | _ | m
  · refine ⟨∅, by simp, by simp, ?_⟩
    intro x
    exact (Finset.notMem_empty x.1 x.2).elim
  · have hcard : 0 < Z.card := by omega
    obtain ⟨v, hv⟩ := Finset.card_pos.mp hcard
    refine ⟨{v}, by simpa, by simp, ?_⟩
    intro x
    have hdeg :
        (G.induce (({v} : Finset V) : Set V)).degree x < 1 := by
      simpa only [Fintype.card_coe, Finset.card_singleton] using
        (G.induce (({v} : Finset V) : Set V)).degree_lt_card_verts x
    have hdeg0 :
        (G.induce (({v} : Finset V) : Set V)).degree x = 0 := by omega
    rw [hdeg0]
    simp
  · let M := m + 2
    let k := 2 * M - 1
    have hM : 2 ≤ M := by omega
    have hk : 2 ≤ k := by
      dsimp [k, M]
      omega
    have hkn : k ≤ Z.card := by
      dsimp [k, M]
      omega
    obtain ⟨Y, hYmem, havg⟩ :=
      exists_sparse_powersetCard G Z E k hk hkn hsparse
    have hYcard : Y.card = 2 * M - 1 := by
      exact (Finset.mem_powersetCard.mp hYmem).2
    have hbad := card_high_degree_lt G Y E M hM hYcard (by simpa [k] using havg)
    obtain ⟨X, _hXY, hXcard, hdegree⟩ :=
      choose_low_degree_subset G Y E M (4 * (M - 1)) hYcard hbad
    refine ⟨X, _hXY.trans (Finset.mem_powersetCard.mp hYmem).1,
      by simpa [M] using hXcard, ?_⟩
    intro x
    simpa [M] using hdegree x

end Lax54Proofs
