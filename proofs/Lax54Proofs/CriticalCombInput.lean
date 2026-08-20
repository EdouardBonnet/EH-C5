import Lax54.CriticalCombInput
import Lax54.KeyCombLemma
import Lax54.MaximumDegreeReduction
import Lax54Proofs.GraphComplements
import Mathlib.Tactic

namespace Lax54Proofs

open Finset
open scoped SimpleGraph
open Lax54.GraphDefinitions
open Lax54.KeyCombLemma

universe u

namespace CriticalCombInput

/-- The block-size normalization used when applying Lemma 3.1 in Section 4. -/
lemma package_key_comb {V : Type u} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) {D : ℕ} [DecidableRel G.Adj]
    (X : Finset V) (hdense : Fintype.card V ≤ D * X.card)
    {t : ℕ} (C : StableHubComb G t)
    (hteeth : keySparsityThreshold ≤ keyCombConstant * t)
    (hblocks : ∀ i : Fin t,
      keySparsityThreshold * X.card ≤
        keyCombConstant * t ^ 2 * (C.block i).card) :
    2 ≤ t ∧
      ∀ i : Fin t, Fintype.card V ≤ D * t ^ 2 * (C.block i).card := by
  have hK : 0 < keyCombConstant := by
    norm_num [keyCombConstant]
  have ht : 2 ≤ t := by
    have hmul : keyCombConstant * 2 ≤ keyCombConstant * t := by
      simpa [keySparsityThreshold, mul_comm] using hteeth
    exact Nat.le_of_mul_le_mul_left hmul hK
  refine ⟨ht, ?_⟩
  intro i
  have hmul : keyCombConstant * (2 * X.card) ≤
      keyCombConstant * (t ^ 2 * (C.block i).card) := by
    simpa [keySparsityThreshold, mul_assoc, mul_left_comm, mul_comm] using hblocks i
  have htwoX : 2 * X.card ≤ t ^ 2 * (C.block i).card :=
    Nat.le_of_mul_le_mul_left hmul hK
  have hXblock : X.card ≤ t ^ 2 * (C.block i).card := by omega
  calc
    Fintype.card V ≤ D * X.card := hdense
    _ ≤ D * (t ^ 2 * (C.block i).card) := Nat.mul_le_mul_left D hXblock
    _ = D * t ^ 2 * (C.block i).card := by ring

/--
---
conclusion: Lax54.CriticalCombInput.exists_critical_comb_parameters
assumptions:
  - Lax54.KeyCombLemma.key_comb_lemma
  - Lax54.MaximumDegreeReduction.maximum_degree_reduction
---
Choose the critical exponent large enough to absorb the linear-size constant
from Lemma 4.3. Apply the maximum-degree reduction and then Lemma 3.1 in the
sparse orientation. Complement invariance gives the second alternative.
-/
theorem exists_critical_comb_parameters :
    ∃ q A : ℕ, 3 ≤ q ∧ A ≤ 2 ^ (q - 2) ∧
      ∀ {V : Type u} [Fintype V] [DecidableEq V] (G : SimpleGraph V),
        IsC5Free G → IsQCritical q G →
          (∃ (t : ℕ) (C : StableHubComb G t),
              2 ≤ t ∧
                ∀ i : Fin t, Fintype.card V ≤ A * t ^ 2 * (C.block i).card) ∨
          (∃ (t : ℕ) (C : StableHubComb Gᶜ t),
              2 ≤ t ∧
                ∀ i : Fin t, Fintype.card V ≤ A * t ^ 2 * (C.block i).card) := by
  let E := keySparsityThreshold
  have hE : 0 < E := by
    norm_num [E, keySparsityThreshold, keyCombConstant]
  obtain ⟨D, hD, hmax⟩ :=
    Lax54.MaximumDegreeReduction.maximum_degree_reduction C5 E hE
  obtain ⟨Q, hQ⟩ :=
    pow_unbounded_of_one_lt (4 * D) (by norm_num : (1 : ℕ) < 2)
  obtain ⟨q, hq3, hQq, hkey⟩ :=
    Lax54.KeyCombLemma.key_comb_lemma E D Q (by rfl) hD
  have h4Dpow : 4 * D ≤ 2 ^ q := by
    exact hQ.le.trans (Nat.pow_le_pow_right (by omega) hQq)
  have hqsplit : q - 2 + 2 = q := by omega
  have hpowRewrite : 2 ^ q = 4 * 2 ^ (q - 2) := by
    conv_lhs => rw [← hqsplit]
    rw [pow_add]
    norm_num
    ring
  have hDpow : D ≤ 2 ^ (q - 2) := by
    rw [hpowRewrite] at h4Dpow
    exact Nat.le_of_mul_le_mul_left h4Dpow (by omega)
  refine ⟨q, D, hq3, hDpow, ?_⟩
  intro V _ _ G hfree hcritical
  letI : DecidableRel G.Adj := Classical.decRel G.Adj
  obtain ⟨X, hdense, hside⟩ := hmax G hfree
  rcases hside with hlow | hlow
  · obtain ⟨t, C, hteeth, hblocks⟩ := hkey G X hcritical hdense hlow
    exact Or.inl ⟨t, C,
      package_key_comb G X hdense C hteeth hblocks⟩
  · obtain ⟨t, C, hteeth, hblocks⟩ :=
      hkey Gᶜ X (Lax54Proofs.IsQCritical.compl hcritical) hdense hlow
    exact Or.inr ⟨t, C,
      package_key_comb Gᶜ X hdense C hteeth hblocks⟩

end CriticalCombInput

end Lax54Proofs
