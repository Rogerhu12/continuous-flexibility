import ContinuousFlexibility.Analysis.N07aMaterialPullbackJets
import ContinuousFlexibility.Analysis.CylinderMixedJets

/-!
# Material radius pullback on an actual open domain

The finite chain rule uses only the physical jets at the actual image point.
The constants are selected before the open set, function and evaluation point.
-/

noncomputable section

namespace ContinuousFlexibility.Analysis

open Set
open scoped ContDiff BigOperators
open ContinuousFlexibility.Statements

theorem n04_materialRadiusPullback_mixedDerivative
    {D : ReferenceData} {T : MaterialData} (hT : IsMaterialData D T)
    {U : Set PolarPoint} (hU : IsOpen U) {f : PolarPoint → ℝ}
    (hf : ContDiffOn ℝ ∞ f U) (a b : ℕ) {p : PolarPoint}
    (hp : (T.radius p.1, p.2) ∈ U) :
    mixedDerivative a b (fun q => f (T.radius q.1, q.2)) p =
      ∑ c : OrderedFinpartition a,
        mixedDerivative c.length b f (T.radius p.1, p.2) *
          n07aRadiusJetCoefficient T c p.1 := by
  have hradius : ContDiff ℝ ∞ T.radius := hT.2.2.2.2.2.2.1
  let g : ℝ → ℝ := fun r => iteratedDeriv b (fun θ => f (r, θ)) p.2
  have hg : ContDiffAt ℝ ∞ g (T.radius p.1) := by
    have hs : ContDiffAt ℝ ∞ (fun r : ℝ => (r, p.2)) (T.radius p.1) :=
      contDiffAt_id.prodMk contDiffAt_const
    simpa only [g, Function.comp_def, mixedDerivative, iteratedDeriv_zero, id_eq] using
      ((contDiffOn_mixedDerivative hU hf 0 b).contDiffAt
        (hU.mem_nhds hp)).comp (T.radius p.1) hs
  have h := iteratedDeriv_comp_eq_sum_orderedFinpartition hg hradius.contDiffAt
    (show (a : ℕ∞ω) ≤ ∞ by simp)
  simpa only [mixedDerivative, Function.comp_def, g, n07aRadiusJetCoefficient] using h

theorem n04_materialRadiusPullback_mixedDerivative_bound
    {D : ReferenceData} {T : MaterialData} (hT : IsMaterialData D T) (a : ℕ) :
    ∃ K : ℝ, 0 ≤ K ∧ ∀ (U : Set PolarPoint), IsOpen U →
      ∀ (f : PolarPoint → ℝ), ContDiffOn ℝ ∞ f U →
      ∀ (b : ℕ) (p : PolarPoint), (T.radius p.1, p.2) ∈ U →
      ∀ W : ℝ, 0 ≤ W →
      (∀ j : ℕ, j ≤ a → |mixedDerivative j b f (T.radius p.1, p.2)| ≤ W) →
      |mixedDerivative a b (fun q => f (T.radius q.1, q.2)) p| ≤ K * W := by
  choose B hB hBb using fun c : OrderedFinpartition a =>
    n07aRadiusJetCoefficient_bounded hT c
  refine ⟨∑ c, B c, Finset.sum_nonneg (fun c _ => hB c), ?_⟩
  intro U hU f hf b p hp W hW hb
  rw [n04_materialRadiusPullback_mixedDerivative hT hU hf a b hp, Finset.sum_mul]
  apply (Finset.abs_sum_le_sum_abs _ _).trans
  apply Finset.sum_le_sum
  intro c _
  rw [abs_mul]
  exact (mul_le_mul (hb c.length c.length_le) (hBb c p.1)
    (abs_nonneg _) hW).trans_eq (mul_comm W (B c))

theorem n04_materialRadiusPullback_iteratedFDeriv_bound
    {D : ReferenceData} {T : MaterialData} (hT : IsMaterialData D T) (N : ℕ) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ (U : Set PolarPoint), IsOpen U →
      ∀ (f : PolarPoint → ℝ), ContDiffOn ℝ ∞ f U →
      ∀ (p : PolarPoint), (T.radius p.1, p.2) ∈ U →
      ∀ W : ℝ, 0 ≤ W →
      (∀ a b : ℕ, a + b ≤ N → |mixedDerivative a b f (T.radius p.1, p.2)| ≤ W) →
      ∀ k : ℕ, k ≤ N →
        ‖iteratedFDeriv ℝ k (fun q => f (T.radius q.1, q.2)) p‖ ≤ C * W := by
  choose K hK hKb using fun a : ℕ =>
    n04_materialRadiusPullback_mixedDerivative_bound hT a
  let A : ℝ := ∑ a ∈ Finset.range (N + 1), K a
  have hA : 0 ≤ A := Finset.sum_nonneg (fun a _ => hK a)
  refine ⟨(2 : ℝ) ^ N * A, mul_nonneg (by positivity) hA, ?_⟩
  intro U hU f hf p hp W hW hb k hk
  let Φ : PolarPoint → PolarPoint := fun q => (T.radius q.1, q.2)
  have hradius : ContDiff ℝ ∞ T.radius := hT.2.2.2.2.2.2.1
  have hΦ : ContDiff ℝ ∞ Φ := (hradius.comp contDiff_fst).prodMk contDiff_snd
  have hV : IsOpen (Φ ⁻¹' U) := hU.preimage hΦ.continuous
  have hfΦ : ContDiffOn ℝ ∞ (fun q => f (T.radius q.1, q.2)) (Φ ⁻¹' U) :=
    hf.comp hΦ.contDiffOn (fun _ h => h)
  have hpV : p ∈ Φ ⁻¹' U := hp
  have hm : ∀ a b : ℕ, a + b = k →
      ‖mixedDerivative a b (fun q => f (T.radius q.1, q.2)) p‖ ≤ A * W := by
    intro a b hab
    have ha : a ≤ N := by omega
    have hKa : K a ≤ A :=
      Finset.single_le_sum (fun j _ => hK j) (Finset.mem_range.mpr (by omega))
    rw [Real.norm_eq_abs]
    exact (hKb a U hU f hf b p hp W hW
      (fun j hj => hb j b (by omega))).trans (mul_le_mul_of_nonneg_right hKa hW)
  calc
    ‖iteratedFDeriv ℝ k (fun q => f (T.radius q.1, q.2)) p‖
        ≤ (2 : ℝ) ^ k * (A * W) :=
      norm_iteratedFDeriv_le_of_mixedDerivative hV hfΦ k hpV (mul_nonneg hA hW) hm
    _ ≤ (2 : ℝ) ^ N * (A * W) :=
      mul_le_mul_of_nonneg_right (pow_le_pow_right₀ (by norm_num : (1 : ℝ) ≤ 2) hk)
        (mul_nonneg hA hW)
    _ = ((2 : ℝ) ^ N * A) * W := (mul_assoc _ _ _).symm

end ContinuousFlexibility.Analysis
