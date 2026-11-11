import ContinuousFlexibility.Radial.InnerBorderTransport
import ContinuousFlexibility.Radial.InnerWeightL2
import Mathlib.Analysis.Normed.Operator.Prod

/-!
# Actual weights on the Hilbert space with one scalar

A real field multiplier acts on the physical L² coordinate and fixes the
single central scalar. This is the weight used in Hilbert adjoints.
In particular an output coefficient loss bounded by one remains a
contraction on the full bordered source space.
-/

noncomputable section

namespace ContinuousFlexibility.Radial

open MeasureTheory
open scoped InnerProductSpace

variable {α : Type*} [MeasurableSpace α] (μ : Measure α)

theorem innerBorderL2_inner_coordinates (F H : InnerBorderL2 μ) :
    ⟪F, H⟫_ℝ = ⟪F.fst, H.fst⟫_ℝ + F.snd * H.snd := by
  rw [WithLp.prod_inner_apply]
  simp only [WithLp.ofLp_fst, WithLp.ofLp_snd, RCLike.inner_apply, conj_trivial]
  ring

theorem innerBorderL2_norm_sq_coordinates (F : InnerBorderL2 μ) :
    ‖F‖ ^ 2 = ‖F.fst‖ ^ 2 + F.snd ^ 2 := by
  rw [← real_inner_self_eq_norm_sq, innerBorderL2_inner_coordinates,
    real_inner_self_eq_norm_sq]
  ring

def innerBorderFieldMap (A : Lp ℝ 2 μ →L[ℝ] Lp ℝ 2 μ) :
    InnerBorderL2 μ →L[ℝ] InnerBorderL2 μ :=
  ((innerBorderMaxEquiv μ).symm : (Lp ℝ 2 μ × ℝ) →L[ℝ] InnerBorderL2 μ) ∘L
    A.prodMap (ContinuousLinearMap.id ℝ ℝ) ∘L
    (innerBorderMaxEquiv μ : InnerBorderL2 μ →L[ℝ] (Lp ℝ 2 μ × ℝ))

theorem innerBorderFieldMap_apply (A : Lp ℝ 2 μ →L[ℝ] Lp ℝ 2 μ)
    (F : InnerBorderL2 μ) :
    innerBorderFieldMap μ A F = WithLp.toLp 2 (A F.fst, F.snd) := rfl

theorem innerBorderFieldMap_fst (A : Lp ℝ 2 μ →L[ℝ] Lp ℝ 2 μ) (F : InnerBorderL2 μ) :
    (innerBorderFieldMap μ A F).fst = A F.fst := rfl

theorem innerBorderFieldMap_snd (A : Lp ℝ 2 μ →L[ℝ] Lp ℝ 2 μ) (F : InnerBorderL2 μ) :
    (innerBorderFieldMap μ A F).snd = F.snd := rfl

theorem innerBorderFieldMap_comp (A B : Lp ℝ 2 μ →L[ℝ] Lp ℝ 2 μ) :
    innerBorderFieldMap μ (A ∘L B) = innerBorderFieldMap μ A ∘L innerBorderFieldMap μ B := by
  apply ContinuousLinearMap.ext
  intro F
  rfl

theorem innerBorderFieldMap_selfAdjoint (A : Lp ℝ 2 μ →L[ℝ] Lp ℝ 2 μ)
    (hA : IsSelfAdjoint A) : IsSelfAdjoint (innerBorderFieldMap μ A) := by
  apply ContinuousLinearMap.isSelfAdjoint_iff_isSymmetric.mpr
  intro F H
  simp only [innerBorderL2_inner_coordinates]
  change ⟪A F.fst, H.fst⟫_ℝ + F.snd * H.snd =
    ⟪F.fst, A H.fst⟫_ℝ + F.snd * H.snd
  have hfield : ⟪A F.fst, H.fst⟫_ℝ = ⟪F.fst, A H.fst⟫_ℝ :=
    hA.isSymmetric F.fst H.fst
  exact congrArg (fun z : ℝ => z + F.snd * H.snd) hfield

/-- The exact Hilbert estimate, without a norm-equivalence factor. -/
theorem norm_innerBorderFieldMap_le (A : Lp ℝ 2 μ →L[ℝ] Lp ℝ 2 μ)
    {K : ℝ} (hK : 1 ≤ K) (hA : ‖A‖ ≤ K) :
    ‖innerBorderFieldMap μ A‖ ≤ K := by
  have hK0 : 0 ≤ K := zero_le_one.trans hK
  apply ContinuousLinearMap.opNorm_le_bound _ hK0
  intro F
  have hfield : ‖A F.fst‖ ≤ K * ‖F.fst‖ :=
    (A.le_opNorm _).trans (mul_le_mul_of_nonneg_right hA (norm_nonneg _))
  have hfieldsq := (sq_le_sq₀ (norm_nonneg (A F.fst))
    (mul_nonneg hK0 (norm_nonneg F.fst))).mpr hfield
  have hKsq : 1 ≤ K ^ 2 := by nlinarith only [hK]
  have hscalar : F.snd ^ 2 ≤ K ^ 2 * F.snd ^ 2 := by
    simpa only [one_mul] using mul_le_mul_of_nonneg_right hKsq (sq_nonneg F.snd)
  apply (sq_le_sq₀ (norm_nonneg _) (mul_nonneg hK0 (norm_nonneg F))).mp
  rw [innerBorderFieldMap_apply, innerBorderL2_norm_sq, mul_pow,
    innerBorderL2_norm_sq_coordinates]
  nlinarith only [hfieldsq, hscalar]

def innerBorderWeightEquiv (W : Lp ℝ 2 μ ≃L[ℝ] Lp ℝ 2 μ) :
    InnerBorderL2 μ ≃L[ℝ] InnerBorderL2 μ :=
  (innerBorderMaxEquiv μ).trans
    ((W.prodCongr (ContinuousLinearEquiv.refl ℝ ℝ)).trans (innerBorderMaxEquiv μ).symm)

theorem innerBorderWeightEquiv_apply (W : Lp ℝ 2 μ ≃L[ℝ] Lp ℝ 2 μ)
    (F : InnerBorderL2 μ) :
    innerBorderWeightEquiv μ W F = WithLp.toLp 2 (W F.fst, F.snd) := rfl

theorem innerBorderWeightEquiv_symm_apply (W : Lp ℝ 2 μ ≃L[ℝ] Lp ℝ 2 μ)
    (F : InnerBorderL2 μ) :
    (innerBorderWeightEquiv μ W).symm F = WithLp.toLp 2 (W.symm F.fst, F.snd) := rfl

theorem innerBorderWeightEquiv_toCLM (W : Lp ℝ 2 μ ≃L[ℝ] Lp ℝ 2 μ) :
    (innerBorderWeightEquiv μ W : InnerBorderL2 μ →L[ℝ] InnerBorderL2 μ) =
      innerBorderFieldMap μ (W : Lp ℝ 2 μ →L[ℝ] Lp ℝ 2 μ) := by
  apply ContinuousLinearMap.ext
  intro F
  rfl

theorem innerBorderWeightEquiv_symm_toCLM (W : Lp ℝ 2 μ ≃L[ℝ] Lp ℝ 2 μ) :
    ((innerBorderWeightEquiv μ W).symm : InnerBorderL2 μ →L[ℝ] InnerBorderL2 μ) =
      innerBorderFieldMap μ (W.symm : Lp ℝ 2 μ →L[ℝ] Lp ℝ 2 μ) := by
  apply ContinuousLinearMap.ext
  intro F
  rfl

theorem innerBorderWeightEquiv_selfAdjoint (W : Lp ℝ 2 μ ≃L[ℝ] Lp ℝ 2 μ)
    (hW : IsSelfAdjoint (W : Lp ℝ 2 μ →L[ℝ] Lp ℝ 2 μ)) :
    IsSelfAdjoint (innerBorderWeightEquiv μ W : InnerBorderL2 μ →L[ℝ] InnerBorderL2 μ) := by
  rw [innerBorderWeightEquiv_toCLM]
  exact innerBorderFieldMap_selfAdjoint μ _ hW

end ContinuousFlexibility.Radial
