import Lax54.CriticalCombInput
import Lax54.ErdosHajnalC5
import Lax54Proofs.CombC5
import Lax54Proofs.CriticalCombInput
import Lax54Proofs.KappaBlocks
import Mathlib.Tactic

namespace Lax54Proofs

open Finset
open scoped BigOperators SimpleGraph
open Lax54.GraphDefinitions

universe u

/-- Induced subgraphs of induced-`C₅`-free graphs are induced-`C₅`-free. -/
theorem IsC5Free.induce_finset
    {V : Type u} {G : SimpleGraph V} (hfree : IsC5Free G) (S : Finset V) :
    IsC5Free (G.induce (S : Set V)) := by
  intro hC5
  apply hfree
  exact hC5.trans ⟨SimpleGraph.Embedding.induce (G := G) (S : Set V)⟩

/-- `κ(G)` is at most the square of the largest homogeneous-set size. -/
theorem kappa_le_homogeneousNumber_sq
    {V : Type u} (G : SimpleGraph V) :
    kappa G ≤ homogeneousNumber G ^ 2 := by
  unfold kappa homogeneousNumber
  calc
    G.cliqueNum * G.indepNum ≤
        max G.cliqueNum G.indepNum * max G.cliqueNum G.indepNum :=
      Nat.mul_le_mul (le_max_left _ _) (le_max_right _ _)
    _ = max G.cliqueNum G.indepNum ^ 2 := by simp [pow_two]

/--
The critical-comb conclusion is incompatible with `q`-criticality in an
induced-`C₅`-free graph. This is the final contradiction in Theorem 4.4,
expressed without real roots.
-/
theorem not_isQCritical_of_critical_comb
    (q A : ℕ) (hq : 3 ≤ q) (hA : A ≤ 2 ^ (q - 2))
    {V : Type u} [Fintype V] [DecidableEq V] (G : SimpleGraph V)
    (hfree : IsC5Free G)
    (hcomb : ∃ (t : ℕ) (C : StableHubComb G t),
      2 ≤ t ∧
        ∀ i : Fin t, Fintype.card V ≤ A * t ^ 2 * (C.block i).card) :
    ¬ IsQCritical q G := by
  classical
  intro hcritical
  obtain ⟨t, C, ht, hlarge⟩ := hcomb
  have htpos : 0 < t := by omega
  have hanti : ∀ {i j : Fin t}, i ≠ j →
      ∀ x ∈ C.block i, ∀ y ∈ C.block j, ¬ G.Adj x y :=
    Lax54Proofs.StableHubComb.blocks_anticomplete_of_c5Free C hfree
  have hsum :
      ∑ i : Fin t, kappa (G.induce (C.block i : Set V)) ≤ kappa G :=
    sum_kappa_induce_le C.block C.blocks_disjoint hanti
  let k : Fin t → ℕ := fun i ↦ kappa (G.induce (C.block i : Set V))
  have huniv : (Finset.univ : Finset (Fin t)).Nonempty :=
    ⟨⟨0, htpos⟩, Finset.mem_univ _⟩
  obtain ⟨i₀, -, hi₀⟩ :=
    Finset.exists_min_image (Finset.univ : Finset (Fin t)) k huniv
  let r : ℕ := k i₀
  have hr_le (i : Fin t) : r ≤ k i := hi₀ i (Finset.mem_univ i)
  have htr_le_sum : t * r ≤ ∑ i : Fin t, k i := by
    calc
      t * r = ∑ _i : Fin t, r := by simp
      _ ≤ ∑ i : Fin t, k i :=
        Finset.sum_le_sum fun i _ ↦ hr_le i
  have htr_le_kappa : t * r ≤ kappa G := by
    exact htr_le_sum.trans (by simpa [k] using hsum)
  have hblock_proper : (C.block i₀).card < Fintype.card V := by
    rw [← Finset.card_univ]
    apply Finset.card_lt_card
    refine Finset.ssubset_iff_subset_ne.mpr ⟨Finset.subset_univ _, ?_⟩
    intro heq
    have : C.tooth i₀ ∈ C.block i₀ := by
      rw [heq]
      exact Finset.mem_univ _
    exact C.tooth_not_mem i₀ i₀ this
  have hblock_critical : (C.block i₀).card ≤ r ^ q := by
    simpa [r, k] using hcritical.2 (C.block i₀) hblock_proper
  have hn_le : Fintype.card V ≤ A * t ^ 2 * r ^ q :=
    (hlarge i₀).trans (Nat.mul_le_mul_left (A * t ^ 2) hblock_critical)
  have hA_le_t : A ≤ t ^ (q - 2) :=
    hA.trans (Nat.pow_le_pow_left ht (q - 2))
  have hcoeff : A * t ^ 2 * r ^ q ≤ t ^ (q - 2) * t ^ 2 * r ^ q := by
    exact Nat.mul_le_mul_right (r ^ q)
      (Nat.mul_le_mul_right (t ^ 2) hA_le_t)
  have hpower_eq : t ^ (q - 2) * t ^ 2 * r ^ q = (t * r) ^ q := by
    calc
      t ^ (q - 2) * t ^ 2 * r ^ q = t ^ q * r ^ q := by
        rw [← pow_add, Nat.sub_add_cancel (by omega)]
      _ = (t * r) ^ q := (Nat.mul_pow t r q).symm
  have hpow_le : (t * r) ^ q ≤ kappa G ^ q :=
    Nat.pow_le_pow_left htr_le_kappa q
  have : Fintype.card V < Fintype.card V :=
    hn_le.trans_lt <| hcoeff.trans_lt <| hpower_eq.le.trans_lt <|
      hpow_le.trans_lt hcritical.1
  exact this.false

/--
Strong induction on the number of vertices. A noncritical counterexample has
a smaller induced counterexample; a critical counterexample is excluded by
the comb argument.
-/
theorem kappa_pow_bound_of_critical_comb
    (q A : ℕ) (hq : 3 ≤ q) (hA : A ≤ 2 ^ (q - 2))
    (hcomb : ∀ {V : Type u} [Fintype V] [DecidableEq V]
      (G : SimpleGraph V), IsC5Free G → IsQCritical q G →
        (∃ (t : ℕ) (C : StableHubComb G t),
            2 ≤ t ∧
              ∀ i : Fin t, Fintype.card V ≤ A * t ^ 2 * (C.block i).card) ∨
        (∃ (t : ℕ) (C : StableHubComb Gᶜ t),
            2 ≤ t ∧
              ∀ i : Fin t, Fintype.card V ≤ A * t ^ 2 * (C.block i).card)) :
    ∀ {V : Type u} [Fintype V] (G : SimpleGraph V),
      IsC5Free G → Fintype.card V ≤ kappa G ^ q := by
  classical
  let P : ℕ → Prop := fun n ↦
    ∀ (V : Type u) [Fintype V] (G : SimpleGraph V),
      Fintype.card V = n → IsC5Free G → Fintype.card V ≤ kappa G ^ q
  have hP : ∀ n : ℕ, P n := by
    intro n
    induction n using Nat.strong_induction_on with
    | h n ih =>
        intro V _ G hcard hfree
        by_contra hbound
        have hbad : kappa G ^ q < Fintype.card V := Nat.lt_of_not_ge hbound
        have hproper : ∀ S : Finset V, S.card < Fintype.card V →
            S.card ≤ kappa (G.induce (S : Set V)) ^ q := by
          intro S hS
          have hSn : S.card < n := by simpa [hcard] using hS
          have hsub := ih S.card hSn
          simpa only [Fintype.card_coe] using
            hsub {x : V // x ∈ S} (G.induce (S : Set V))
              (by simp) (Lax54Proofs.IsC5Free.induce_finset hfree S)
        have hcrit : IsQCritical q G := ⟨hbad, hproper⟩
        rcases hcomb G hfree hcrit with hdirect | hcompl
        · exact (not_isQCritical_of_critical_comb q A hq hA G hfree hdirect) hcrit
        · exact (not_isQCritical_of_critical_comb q A hq hA Gᶜ
            (Lax54Proofs.IsC5Free.compl hfree) hcompl)
            (Lax54Proofs.IsQCritical.compl hcrit)
  intro V _ G hfree
  exact hP (Fintype.card V) V G rfl hfree

/--
---
conclusion: Lax54.ErdosHajnalC5.erdos_hajnal_C5
---
Proof of Theorem 4.4. Strong induction reduces the result to a critical
counterexample. The critical-comb statement and the induced-$C_5$ obstruction
between distinct blocks exclude that case. Finally,
$\kappa(G)=\alpha(G)\omega(G)\leq h(G)^2$ gives the asserted exponent.
-/
theorem erdos_hajnal_C5 :
    ∃ q : ℕ, 0 < q ∧
      ∀ {V : Type u} [Fintype V] (G : SimpleGraph V),
        IsC5Free G → Fintype.card V ≤ homogeneousNumber G ^ q := by
  obtain ⟨q, A, hq, hA, hcomb⟩ :=
    Lax54Proofs.CriticalCombInput.exists_critical_comb_parameters
  refine ⟨2 * q, by omega, ?_⟩
  intro V _ G hfree
  have hkappa : Fintype.card V ≤ kappa G ^ q :=
    kappa_pow_bound_of_critical_comb q A hq hA hcomb G hfree
  calc
    Fintype.card V ≤ kappa G ^ q := hkappa
    _ ≤ (homogeneousNumber G ^ 2) ^ q :=
      Nat.pow_le_pow_left (kappa_le_homogeneousNumber_sq G) q
    _ = homogeneousNumber G ^ (2 * q) := by rw [pow_mul]

end Lax54Proofs
