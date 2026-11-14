module

public import ContinuousFlexibility.Radial.InnerSupportedWeights
public import Mathlib.Analysis.Normed.Lp.ProdLp

/-!
# Scalar sign on the same supported physical Hilbert space

The change between the two border-column conventions fixes the physical
field and negates its one scalar coordinate. It is an involutive linear
isometry of the existing supported source, including its scalar-zero
constraint in unbordered modes. Actual field weights commute with this
map, so conjugating the same inverse preserves every weighted norm.
-/

@[expose] public section

noncomputable section

namespace ContinuousFlexibility.Radial

open Set MeasureTheory
open scoped InnerProductSpace

variable {α : Type*} [MeasurableSpace α] (μ : Measure α)
  (s : Set α) (hs : MeasurableSet s) (bordered : Bool)

/-- Scalar sign on the existing Hilbert product, with the field fixed. -/
def innerBorderScalarSign : InnerBorderL2 μ ≃ₗᵢ[ℝ] InnerBorderL2 μ :=
  LinearIsometryEquiv.withLpProdCongr 2
    (LinearIsometryEquiv.refl ℝ (Lp ℝ 2 μ))
    (LinearIsometryEquiv.neg ℝ)

@[simp] theorem innerBorderScalarSign_apply (F : InnerBorderL2 μ) :
    innerBorderScalarSign μ F = WithLp.toLp 2 (F.fst, -F.snd) := by
  simp only [innerBorderScalarSign, LinearIsometryEquiv.withLpProdCongr_apply,
    LinearIsometryEquiv.coe_refl, LinearIsometryEquiv.coe_neg, id_eq]

theorem innerBorderScalarSign_involutive :
    Function.Involutive (innerBorderScalarSign μ) := by
  intro F
  apply WithLp.ofLp_injective 2
  apply Prod.ext
  · simp only [WithLp.ofLp_fst, innerBorderScalarSign_apply, WithLp.toLp_fst]
  · simp only [WithLp.ofLp_snd, innerBorderScalarSign_apply,
      WithLp.toLp_snd, neg_neg]

local notation "S" => innerSupportedAdmissibleSource μ s bordered
local notation "HSrc" => ↥S

theorem innerSupportedScalarSign_mem (F : HSrc) :
    innerBorderScalarSign μ F.val ∈ innerSupportedAdmissibleSource μ s bordered := by
  have hF := (mem_innerSupportedAdmissibleSource μ s bordered F.val).mp F.property
  apply (mem_innerSupportedAdmissibleSource μ s bordered _).mpr
  rw [innerBorderScalarSign_apply, WithLp.toLp_fst, WithLp.toLp_snd]
  refine ⟨?_, hF.2⟩
  rcases hF.1 with hborder | hzero
  · exact Or.inl hborder
  · exact Or.inr (by rw [hzero, neg_zero])

/-- The convention change acts on the same supported admissible source.
No measurability assumption on the support is needed for this map. -/
def innerSupportedScalarSign : HSrc ≃ₗᵢ[ℝ] HSrc where
  toFun F := ⟨innerBorderScalarSign μ F.val,
    innerSupportedScalarSign_mem μ s bordered F⟩
  invFun F := ⟨innerBorderScalarSign μ F.val,
    innerSupportedScalarSign_mem μ s bordered F⟩
  left_inv F := by
    apply Subtype.ext
    exact innerBorderScalarSign_involutive μ F.val
  right_inv F := by
    apply Subtype.ext
    exact innerBorderScalarSign_involutive μ F.val
  map_add' F K := by
    apply Subtype.ext
    exact map_add (innerBorderScalarSign μ) F.val K.val
  map_smul' c F := by
    apply Subtype.ext
    exact map_smul (innerBorderScalarSign μ) c F.val
  norm_map' F := (innerBorderScalarSign μ).norm_map F.val

@[simp] theorem innerSupportedScalarSign_apply_val (F : HSrc) :
    (innerSupportedScalarSign μ s bordered F).val =
      WithLp.toLp 2 (F.val.fst, -F.val.snd) :=
  innerBorderScalarSign_apply μ F.val

@[simp] theorem innerSupportedScalarSign_fst (F : HSrc) :
    (innerSupportedScalarSign μ s bordered F).val.fst = F.val.fst := by
  rw [innerSupportedScalarSign_apply_val, WithLp.toLp_fst]

@[simp] theorem innerSupportedScalarSign_snd (F : HSrc) :
    (innerSupportedScalarSign μ s bordered F).val.snd = -F.val.snd := by
  rw [innerSupportedScalarSign_apply_val, WithLp.toLp_snd]

theorem innerSupportedScalarSign_involutive :
    Function.Involutive (innerSupportedScalarSign μ s bordered) := by
  intro F
  apply Subtype.ext
  exact innerBorderScalarSign_involutive μ F.val

@[simp] theorem innerSupportedScalarSign_norm (F : HSrc) :
    ‖innerSupportedScalarSign μ s bordered F‖ = ‖F‖ :=
  (innerSupportedScalarSign μ s bordered).norm_map F

theorem innerSupportedScalarSign_inner (F K : HSrc) :
    ⟪innerSupportedScalarSign μ s bordered F, K⟫_ℝ =
      ⟪F, innerSupportedScalarSign μ s bordered K⟫_ℝ := by
  have h :
      ⟪innerSupportedScalarSign μ s bordered F,
        innerSupportedScalarSign μ s bordered
          (innerSupportedScalarSign μ s bordered K)⟫_ℝ =
        ⟪F, innerSupportedScalarSign μ s bordered K⟫_ℝ :=
    (innerSupportedScalarSign μ s bordered).toLinearIsometry.inner_map_map F
      (innerSupportedScalarSign μ s bordered K)
  rwa [innerSupportedScalarSign_involutive μ s bordered K] at h

theorem innerSupportedScalarSign_selfAdjoint :
    IsSelfAdjoint (innerSupportedScalarSign μ s bordered : HSrc →L[ℝ] HSrc) := by
  apply ContinuousLinearMap.isSelfAdjoint_iff_isSymmetric.mpr
  intro F K
  exact innerSupportedScalarSign_inner μ s bordered F K

local notation "J" => (innerSupportedScalarSign μ s bordered : HSrc →L[ℝ] HSrc)

/-- This covers every supported scalar-identity field operator, before
specializing to the actual measurable multipliers. -/
theorem innerSupportedScalarSign_commute_fieldMap
    (A : Lp ℝ 2 μ →L[ℝ] Lp ℝ 2 μ) (B : HSrc →L[ℝ] HSrc)
    (hB : ∀ F, (B F).val = innerBorderFieldMap μ A F.val) :
    J ∘L B = B ∘L J := by
  apply ContinuousLinearMap.ext
  intro F
  apply Subtype.ext
  simp only [ContinuousLinearMap.comp_apply, LinearIsometryEquiv.coe_coe'',
    innerSupportedScalarSign_apply_val, hB, innerBorderFieldMap_apply,
    WithLp.toLp_fst, WithLp.toLp_snd]

theorem innerSupportedScalarSign_commute_multiplier
    (W : α → ℝ) (hW : Measurable W) (C : ℝ) (hWC : ∀ x, |W x| ≤ C) :
    J ∘L innerSupportedWeightMultiplier μ s hs bordered W hW C hWC =
      innerSupportedWeightMultiplier μ s hs bordered W hW C hWC ∘L J :=
  innerSupportedScalarSign_commute_fieldMap μ s bordered
    (innerWeightMultiplier μ W hW C hWC)
    (innerSupportedWeightMultiplier μ s hs bordered W hW C hWC)
    (innerSupportedWeightMultiplier_apply μ s hs bordered W hW C hWC)

section WeightEquivalence

variable (W : α → ℝ) (hW : Measurable W) (hpos : ∀ x, 0 < W x)
  (C Cinv : ℝ) (hWC : ∀ x, |W x| ≤ C) (hWinv : ∀ x, |(W x)⁻¹| ≤ Cinv)

theorem innerSupportedScalarSign_commute_equiv :
    J ∘L (innerSupportedWeightEquiv μ s hs bordered W hW hpos C Cinv hWC hWinv :
        HSrc →L[ℝ] HSrc) =
      (innerSupportedWeightEquiv μ s hs bordered W hW hpos C Cinv hWC hWinv :
        HSrc →L[ℝ] HSrc) ∘L J := by
  simpa only [innerSupportedWeightEquiv_toCLM] using
    innerSupportedScalarSign_commute_multiplier μ s hs bordered W hW C hWC

theorem innerSupportedScalarSign_commute_equiv_symm :
    J ∘L ((innerSupportedWeightEquiv μ s hs bordered W hW hpos C Cinv hWC hWinv).symm :
        HSrc →L[ℝ] HSrc) =
      ((innerSupportedWeightEquiv μ s hs bordered W hW hpos C Cinv hWC hWinv).symm :
        HSrc →L[ℝ] HSrc) ∘L J := by
  simpa only [innerSupportedWeightEquiv_symm_toCLM] using
    innerSupportedScalarSign_commute_multiplier μ s hs bordered
      (fun x => (W x)⁻¹) hW.inv Cinv hWinv

end WeightEquivalence

section OperatorNorm

variable {B : Type*} [NormedAddCommGroup B] [NormedSpace ℝ B]

/-- Left composition preserves the norm for arbitrary boundary/source
spaces, in particular for the same physical Poisson operator. -/
theorem innerSupportedScalarSign_comp_norm (T : B →L[ℝ] HSrc) :
    ‖J ∘L T‖ = ‖T‖ := by
  have hnorm (x : B) : ‖(J ∘L T) x‖ = ‖T x‖ :=
    (innerSupportedScalarSign μ s bordered).norm_map (T x)
  apply le_antisymm
  · apply ContinuousLinearMap.opNorm_le_bound _ (norm_nonneg T)
    intro x
    rw [hnorm]
    exact T.le_opNorm x
  · apply ContinuousLinearMap.opNorm_le_bound _ (norm_nonneg (J ∘L T))
    intro x
    rw [← hnorm]
    exact (J ∘L T).le_opNorm x

theorem innerSupportedScalarSign_norm_comp (T : HSrc →L[ℝ] B) :
    ‖T ∘L J‖ = ‖T‖ := by
  apply le_antisymm
  · apply ContinuousLinearMap.opNorm_le_bound _ (norm_nonneg T)
    intro x
    have h := T.le_opNorm (innerSupportedScalarSign μ s bordered x)
    simpa only [ContinuousLinearMap.comp_apply, LinearIsometryEquiv.coe_coe'',
      innerSupportedScalarSign_norm] using h
  · apply ContinuousLinearMap.opNorm_le_bound _ (norm_nonneg (T ∘L J))
    intro x
    have h := (T ∘L J).le_opNorm (innerSupportedScalarSign μ s bordered x)
    simpa only [ContinuousLinearMap.comp_apply, LinearIsometryEquiv.coe_coe'',
      innerSupportedScalarSign_involutive μ s bordered x,
      innerSupportedScalarSign_norm] using h

theorem innerSupportedScalarSign_weighted_comp_norm
    (T : B →L[ℝ] HSrc) (W : HSrc →L[ℝ] HSrc)
    (hW : J ∘L W = W ∘L J) :
    ‖W ∘L J ∘L T‖ = ‖W ∘L T‖ := by
  have hWT : W ∘L J ∘L T = J ∘L (W ∘L T) := by
    apply ContinuousLinearMap.ext
    intro x
    simpa only [ContinuousLinearMap.comp_apply] using
      congrArg (fun A : HSrc →L[ℝ] HSrc => A (T x)) hW.symm
  rw [hWT, innerSupportedScalarSign_comp_norm]

end OperatorNorm

theorem innerSupportedScalarSign_conjugate_norm (A : HSrc →L[ℝ] HSrc) :
    ‖J ∘L A ∘L J‖ = ‖A‖ := by
  rw [innerSupportedScalarSign_comp_norm, innerSupportedScalarSign_norm_comp]

/-- Actual weights and coefficient losses keep their norms after the
same scalar-sign conjugation. The two exterior operators may differ. -/
theorem innerSupportedScalarSign_weighted_conjugate_norm
    (A W V : HSrc →L[ℝ] HSrc)
    (hW : J ∘L W = W ∘L J) (hV : J ∘L V = V ∘L J) :
    ‖W ∘L (J ∘L A ∘L J) ∘L V‖ = ‖W ∘L A ∘L V‖ := by
  have hWF (x : HSrc) : W (J x) = J (W x) := by
    simpa only [ContinuousLinearMap.comp_apply] using
      congrArg (fun B : HSrc →L[ℝ] HSrc => B x) hW.symm
  have hVF (x : HSrc) : J (V x) = V (J x) := by
    simpa only [ContinuousLinearMap.comp_apply] using
      congrArg (fun B : HSrc →L[ℝ] HSrc => B x) hV
  have hWV : W ∘L (J ∘L A ∘L J) ∘L V = J ∘L (W ∘L A ∘L V) ∘L J := by
    apply ContinuousLinearMap.ext
    intro x
    simp only [ContinuousLinearMap.comp_apply]
    rw [hWF, hVF]
  rw [hWV, innerSupportedScalarSign_conjugate_norm]

end ContinuousFlexibility.Radial
