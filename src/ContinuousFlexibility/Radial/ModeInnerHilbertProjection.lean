import ContinuousFlexibility.Radial.ModeRegionSources
import Mathlib.Analysis.InnerProductSpace.ProdL2
import Mathlib.Topology.Algebra.Module.ClosedSubmodule

/-!
# Actual supported source projection for the inner inverse

The field is restricted by its measurable indicator in the existing radial
measure. The scalar is retained precisely in a bordered mode. These operations
form a contraction in the Hilbert product. A closed source subspace is supplied
only through its actual coordinate membership criterion; no equation, inverse
or estimate is included in this criterion.

An operator on that same subspace extends by the proved projection and inclusion.
Passing to the frozen ordinary product costs at most the fixed factor sqrt 2.
-/

noncomputable section

namespace ContinuousFlexibility.Radial

open Set Filter MeasureTheory
open scoped InnerProductSpace
open ContinuousFlexibility.Statements

abbrev ModeHilbertPair (D : ReferenceData) : Type := WithLp 2 (RadialModePair D)

theorem modeRegionProjection_apply (D : ReferenceData) (J : Set ℝ)
    (hJ : MeasurableSet J) (f : RadialModeL2 D) :
    modeRegionProjection D J hJ f = modeRegionVector D J hJ f := by
  simp only [modeRegionProjection, LinearMap.mkContinuous_apply, LinearMap.coe_mk,
    AddHom.coe_mk]

theorem modeRegionVector_eq_self_iff (D : ReferenceData) (J : Set ℝ)
    (hJ : MeasurableSet J) (f : RadialModeL2 D) :
    modeRegionVector D J hJ f = f ↔
      ∀ᵐ r ∂radialHilbertMeasure D, r ∉ J → f r = 0 := by
  constructor
  · intro h
    have ha := modeRegionVector_coe D J hJ f
    rw [h] at ha
    filter_upwards [ha] with r hr hn
    exact hr.trans (indicator_of_notMem hn _)
  · intro h
    apply Lp.ext
    filter_upwards [modeRegionVector_coe D J hJ f, h] with r hr hz
    rw [hr]
    by_cases hj : r ∈ J
    · exact indicator_of_mem hj _
    · rw [indicator_of_notMem hj, hz hj]

theorem modeRegionVector_congr_set_ae (D : ReferenceData) {J K : Set ℝ}
    (hJ : MeasurableSet J) (hK : MeasurableSet K)
    (hJK : ∀ᵐ r ∂radialHilbertMeasure D, r ∈ J ↔ r ∈ K)
    (f : RadialModeL2 D) :
    modeRegionVector D J hJ f = modeRegionVector D K hK f := by
  apply Lp.ext
  filter_upwards [modeRegionVector_coe D J hJ f,
    modeRegionVector_coe D K hK f, hJK] with r hr hs he
  rw [hr, hs]
  by_cases hj : r ∈ J
  · rw [indicator_of_mem hj, indicator_of_mem (he.mp hj)]
  · rw [indicator_of_notMem hj, indicator_of_notMem (fun hk => hj (he.mpr hk))]

/-- Finite internal cuts do not change the actual source projection. -/
theorem modeRegionVector_congr_off_finset {D : ReferenceData}
    (hD : IsAccumulatingProfile D) {J K : Set ℝ}
    (hJ : MeasurableSet J) (hK : MeasurableSet K) (s : Finset ℝ)
    (hJK : ∀ r, r ∉ s → (r ∈ J ↔ r ∈ K)) (f : RadialModeL2 D) :
    modeRegionVector D J hJ f = modeRegionVector D K hK f := by
  classical
  apply modeRegionVector_congr_set_ae D hJ hK _ f
  have hpoints : ∀ᵐ r ∂radialHilbertMeasure D, ∀ c : s, r ≠ (c : ℝ) :=
    ae_all_iff.mpr (fun c => matching_ae_ne hD c)
  filter_upwards [hpoints] with r hr
  exact hJK r (fun hs => hr ⟨r, hs⟩ rfl)

/-- The indicator projection and scalar admissibility in the genuine
Hilbert product, with the scalar coordinate unchanged in bordered modes. -/
def modeSupportedHilbertProjection (D : ReferenceData) (J : Set ℝ)
    (hJ : MeasurableSet J) (bordered : Bool) :
    ModeHilbertPair D →L[ℝ] ModeHilbertPair D :=
  ((WithLp.prodContinuousLinearEquiv 2 ℝ (RadialModeL2 D) ℝ).symm :
      RadialModePair D →L[ℝ] ModeHilbertPair D).comp
    (((modeRegionProjection D J hJ).comp (WithLp.fstL 2 ℝ (RadialModeL2 D) ℝ)).prod
      (if bordered then WithLp.sndL 2 ℝ (RadialModeL2 D) ℝ else 0))

theorem modeSupportedHilbertProjection_apply (D : ReferenceData) (J : Set ℝ)
    (hJ : MeasurableSet J) (bordered : Bool) (F : ModeHilbertPair D) :
    modeSupportedHilbertProjection D J hJ bordered F =
      WithLp.toLp 2 (modeRegionVector D J hJ F.fst, if bordered then F.snd else 0) := by
  cases bordered <;>
    simp only [modeSupportedHilbertProjection, Bool.false_eq_true, eq_self_iff_true,
      ite_false, ite_true,
      ContinuousLinearMap.comp_apply, ContinuousLinearMap.prod_apply,
      ContinuousLinearEquiv.coe_coe, WithLp.prodContinuousLinearEquiv_symm_apply,
      WithLp.fstL_apply, WithLp.sndL_apply, ContinuousLinearMap.zero_apply,
      modeRegionProjection_apply]

theorem modeSupportedHilbertProjection_idempotent (D : ReferenceData) (J : Set ℝ)
    (hJ : MeasurableSet J) (bordered : Bool) (F : ModeHilbertPair D) :
    modeSupportedHilbertProjection D J hJ bordered
        (modeSupportedHilbertProjection D J hJ bordered F) =
      modeSupportedHilbertProjection D J hJ bordered F := by
  cases bordered <;>
    simp only [modeSupportedHilbertProjection_apply, WithLp.toLp_fst, WithLp.toLp_snd,
      Bool.false_eq_true, eq_self_iff_true, ite_false, ite_true, modeRegionVector_idempotent]

theorem modeSupportedHilbertProjection_norm_le (D : ReferenceData) (J : Set ℝ)
    (hJ : MeasurableSet J) (bordered : Bool) (F : ModeHilbertPair D) :
    ‖modeSupportedHilbertProjection D J hJ bordered F‖ ≤ ‖F‖ := by
  have hf := modeRegionVector_norm_le D J hJ F.fst
  have hs : ‖(if bordered then F.snd else 0 : ℝ)‖ ≤ ‖F.snd‖ := by
    cases bordered <;> simp only [Bool.false_eq_true, eq_self_iff_true, ite_false, ite_true, norm_zero,
      norm_nonneg, le_refl]
  apply (sq_le_sq₀ (norm_nonneg _) (norm_nonneg _)).mp
  simp only [modeSupportedHilbertProjection_apply, WithLp.prod_norm_sq_eq_of_L2,
    WithLp.toLp_fst, WithLp.toLp_snd]
  exact add_le_add ((sq_le_sq₀ (norm_nonneg _) (norm_nonneg _)).mpr hf)
    ((sq_le_sq₀ (norm_nonneg _) (norm_nonneg _)).mpr hs)

theorem modeSupportedHilbertProjection_fixed_iff (D : ReferenceData) (J : Set ℝ)
    (hJ : MeasurableSet J) (bordered : Bool) (F : ModeHilbertPair D) :
    modeSupportedHilbertProjection D J hJ bordered F = F ↔
      (bordered = true ∨ F.snd = 0) ∧ modeRegionVector D J hJ F.fst = F.fst := by
  constructor
  · intro h
    have hf := congrArg WithLp.fst h
    have hs := congrArg WithLp.snd h
    simp only [modeSupportedHilbertProjection_apply, WithLp.toLp_fst] at hf
    simp only [modeSupportedHilbertProjection_apply, WithLp.toLp_snd] at hs
    refine ⟨?_, hf⟩
    cases bordered
    · exact Or.inr (by simpa only [Bool.false_eq_true, ite_false] using hs.symm)
    · exact Or.inl rfl
  · rintro ⟨hs, hf⟩
    apply WithLp.ofLp_injective 2
    simp only [modeSupportedHilbertProjection_apply, WithLp.ofLp_toLp]
    apply Prod.ext
    · simpa only [WithLp.ofLp_fst] using hf
    · simp only [WithLp.ofLp_snd]
      cases bordered
      · have hz : F.snd = 0 := by simpa only [Bool.false_eq_true, false_or] using hs
        simp only [Bool.false_eq_true, ite_false, hz]
      · simp only [eq_self_iff_true, ite_true]

section ActualSource

variable (D : ReferenceData) (J : Set ℝ) (hJ : MeasurableSet J) (bordered : Bool)
  (K : ClosedSubmodule ℝ (ModeHilbertPair D))
  (hK : ∀ F, F ∈ K ↔
    (bordered = true ∨ F.snd = 0) ∧ modeRegionVector D J hJ F.fst = F.fst)

/-- Restriction into the same supplied physical source subspace. -/
def modeSupportedHilbertRestrict : ModeHilbertPair D →L[ℝ] K :=
  (modeSupportedHilbertProjection D J hJ bordered).codRestrict K.toSubmodule (fun F => by
    apply (hK _).mpr
    exact (modeSupportedHilbertProjection_fixed_iff D J hJ bordered _).mp
      (modeSupportedHilbertProjection_idempotent D J hJ bordered F))

theorem modeSupportedHilbertRestrict_coe (F : ModeHilbertPair D) :
    (modeSupportedHilbertRestrict D J hJ bordered K hK F : ModeHilbertPair D) =
      modeSupportedHilbertProjection D J hJ bordered F := by
  exact ContinuousLinearMap.coe_codRestrict_apply _ _ _ _

theorem modeSupportedHilbertRestrict_norm_le (F : ModeHilbertPair D) :
    ‖modeSupportedHilbertRestrict D J hJ bordered K hK F‖ ≤ ‖F‖ := by
  rw [← ClosedSubmodule.norm_coe, modeSupportedHilbertRestrict_coe]
  exact modeSupportedHilbertProjection_norm_le D J hJ bordered F

theorem modeSupportedHilbertRestrict_inclusion (F : K) :
    modeSupportedHilbertRestrict D J hJ bordered K hK (F : ModeHilbertPair D) = F := by
  apply Subtype.ext
  rw [modeSupportedHilbertRestrict_coe]
  exact (modeSupportedHilbertProjection_fixed_iff D J hJ bordered _).mpr
    ((hK _).mp F.property)

theorem modeSupportedHilbert_member_supported (F : K) :
    ∀ᵐ r ∂radialHilbertMeasure D, r ∉ J → F.val.fst r = 0 :=
  (modeRegionVector_eq_self_iff D J hJ F.val.fst).mp ((hK _).mp F.property).2

theorem modeSupportedHilbert_member_scalar (hb : bordered = false) (F : K) :
    F.val.snd = 0 := by
  have h := ((hK _).mp F.property).1
  simpa only [hb, Bool.false_eq_true, false_or] using h

/-- Extend the actual subspace operator by restriction and isometric inclusion. -/
def modeSupportedHilbertExtension (G : K →L[ℝ] K) :
    ModeHilbertPair D →L[ℝ] ModeHilbertPair D :=
  K.toSubmodule.subtypeL.comp
    (G.comp (modeSupportedHilbertRestrict D J hJ bordered K hK))

theorem modeSupportedHilbertExtension_apply (G : K →L[ℝ] K) (F : ModeHilbertPair D) :
    modeSupportedHilbertExtension D J hJ bordered K hK G F =
      (G (modeSupportedHilbertRestrict D J hJ bordered K hK F) : ModeHilbertPair D) := by
  simp only [modeSupportedHilbertExtension, ContinuousLinearMap.comp_apply,
    Submodule.subtypeL_apply]

theorem modeSupportedHilbertExtension_norm_le (G : K →L[ℝ] K) :
    ‖modeSupportedHilbertExtension D J hJ bordered K hK G‖ ≤ ‖G‖ := by
  apply ContinuousLinearMap.opNorm_le_bound _ (norm_nonneg G)
  intro F
  rw [modeSupportedHilbertExtension_apply, ClosedSubmodule.norm_coe]
  exact (G.le_opNorm _).trans (mul_le_mul_of_nonneg_left
    (modeSupportedHilbertRestrict_norm_le D J hJ bordered K hK F) (norm_nonneg G))

/-- The fixed statement-layer coordinates of the same actual operator. -/
def modeSupportedPairOperator (G : K →L[ℝ] K) : RadialModePair D →L[ℝ] RadialModePair D :=
  (WithLp.prodContinuousLinearEquiv 2 ℝ (RadialModeL2 D) ℝ :
      ModeHilbertPair D →L[ℝ] RadialModePair D).comp
    ((modeSupportedHilbertExtension D J hJ bordered K hK G).comp
      ((WithLp.prodContinuousLinearEquiv 2 ℝ (RadialModeL2 D) ℝ).symm :
        RadialModePair D →L[ℝ] ModeHilbertPair D))

theorem modeSupportedPairOperator_apply (G : K →L[ℝ] K) (F : RadialModePair D) :
    modeSupportedPairOperator D J hJ bordered K hK G F =
      WithLp.ofLp (G (modeSupportedHilbertRestrict D J hJ bordered K hK
        (WithLp.toLp 2 F)) : ModeHilbertPair D) := by
  simp only [modeSupportedPairOperator, ContinuousLinearMap.comp_apply,
    ContinuousLinearEquiv.coe_coe, WithLp.prodContinuousLinearEquiv_apply,
    WithLp.prodContinuousLinearEquiv_symm_apply, modeSupportedHilbertExtension_apply]

theorem modeSupportedPairOperator_inclusion (G : K →L[ℝ] K) (F : K) :
    modeSupportedPairOperator D J hJ bordered K hK G (WithLp.ofLp F.val) =
      WithLp.ofLp (G F).val := by
  rw [modeSupportedPairOperator_apply, WithLp.toLp_ofLp,
    modeSupportedHilbertRestrict_inclusion]

theorem modeSupportedPairOperator_supported (G : K →L[ℝ] K) (F : RadialModePair D) :
    ∀ᵐ r ∂radialHilbertMeasure D,
      r ∉ J → (modeSupportedPairOperator D J hJ bordered K hK G F).1 r = 0 := by
  have h := modeSupportedHilbert_member_supported D J hJ bordered K hK
    (G (modeSupportedHilbertRestrict D J hJ bordered K hK (WithLp.toLp 2 F)))
  simpa only [modeSupportedPairOperator_apply, WithLp.ofLp_fst] using h

theorem modeSupportedPairOperator_scalar (hb : bordered = false)
    (G : K →L[ℝ] K) (F : RadialModePair D) :
    (modeSupportedPairOperator D J hJ bordered K hK G F).2 = 0 := by
  have h := modeSupportedHilbert_member_scalar D J hJ bordered K hK hb
    (G (modeSupportedHilbertRestrict D J hJ bordered K hK (WithLp.toLp 2 F)))
  simpa only [modeSupportedPairOperator_apply, WithLp.ofLp_snd] using h

end ActualSource

theorem modeHilbertPair_ofLp_norm_le {D : ReferenceData} (F : ModeHilbertPair D) :
    ‖WithLp.ofLp F‖ ≤ ‖F‖ := by
  rw [Prod.norm_def, WithLp.ofLp_fst, WithLp.ofLp_snd]
  exact max_le (WithLp.norm_fst_le F) (WithLp.norm_snd_le F)

theorem modeHilbertPair_toLp_norm_le {D : ReferenceData} (F : RadialModePair D) :
    ‖(WithLp.toLp 2 F : ModeHilbertPair D)‖ ≤ Real.sqrt 2 * ‖F‖ := by
  have hf : ‖F.1‖ ≤ ‖F‖ := by rw [Prod.norm_def]; exact le_max_left _ _
  have hs : ‖F.2‖ ≤ ‖F‖ := by rw [Prod.norm_def]; exact le_max_right _ _
  apply (sq_le_sq₀ (norm_nonneg _)
    (mul_nonneg (Real.sqrt_nonneg 2) (norm_nonneg F))).mp
  simp only [WithLp.prod_norm_sq_eq_of_L2, WithLp.toLp_fst, WithLp.toLp_snd, mul_pow,
    Real.sq_sqrt (by norm_num : (0 : ℝ) ≤ 2)]
  calc
    ‖F.1‖ ^ 2 + ‖F.2‖ ^ 2 ≤ ‖F‖ ^ 2 + ‖F‖ ^ 2 :=
      add_le_add ((sq_le_sq₀ (norm_nonneg _) (norm_nonneg _)).mpr hf)
        ((sq_le_sq₀ (norm_nonneg _) (norm_nonneg _)).mpr hs)
    _ = 2 * ‖F‖ ^ 2 := by ring

theorem modeSupportedPairOperator_norm_le (D : ReferenceData) (J : Set ℝ)
    (hJ : MeasurableSet J) (bordered : Bool) (K : ClosedSubmodule ℝ (ModeHilbertPair D))
    (hK : ∀ F, F ∈ K ↔
      (bordered = true ∨ F.snd = 0) ∧ modeRegionVector D J hJ F.fst = F.fst)
    (G : K →L[ℝ] K) :
    ‖modeSupportedPairOperator D J hJ bordered K hK G‖ ≤ Real.sqrt 2 * ‖G‖ := by
  apply ContinuousLinearMap.opNorm_le_bound _
    (mul_nonneg (Real.sqrt_nonneg 2) (norm_nonneg G))
  intro F
  rw [modeSupportedPairOperator_apply]
  calc
    _ ≤ ‖(G (modeSupportedHilbertRestrict D J hJ bordered K hK
        (WithLp.toLp 2 F)) : ModeHilbertPair D)‖ := modeHilbertPair_ofLp_norm_le _
    _ = ‖G (modeSupportedHilbertRestrict D J hJ bordered K hK (WithLp.toLp 2 F))‖ :=
      ClosedSubmodule.norm_coe _
    _ ≤ ‖G‖ * ‖modeSupportedHilbertRestrict D J hJ bordered K hK (WithLp.toLp 2 F)‖ :=
      G.le_opNorm _
    _ ≤ ‖G‖ * ‖(WithLp.toLp 2 F : ModeHilbertPair D)‖ :=
      mul_le_mul_of_nonneg_left
        (modeSupportedHilbertRestrict_norm_le D J hJ bordered K hK _) (norm_nonneg G)
    _ ≤ ‖G‖ * (Real.sqrt 2 * ‖F‖) :=
      mul_le_mul_of_nonneg_left (modeHilbertPair_toLp_norm_le F) (norm_nonneg G)
    _ = (Real.sqrt 2 * ‖G‖) * ‖F‖ := by ring

/-- The frozen inner source still retains its scalar; the Hilbert projection
then enforces the mode's admissibility without changing the operator. -/
theorem modeSupportedPairOperator_innerSource (D : ReferenceData) (l h : ℝ)
    (bordered : Bool) (K : ClosedSubmodule ℝ (ModeHilbertPair D))
    (hK : ∀ F, F ∈ K ↔ (bordered = true ∨ F.snd = 0) ∧
      modeRegionVector D (Ioo l h) measurableSet_Ioo F.fst = F.fst)
    (G : K →L[ℝ] K) (F : RadialModePair D) :
    modeSupportedPairOperator D (Ioo l h) measurableSet_Ioo bordered K hK G
        (modeInnerSource D l h F) =
      modeSupportedPairOperator D (Ioo l h) measurableSet_Ioo bordered K hK G F := by
  have he : modeSupportedHilbertRestrict D (Ioo l h) measurableSet_Ioo bordered K hK
      (WithLp.toLp 2 (modeInnerSource D l h F)) =
      modeSupportedHilbertRestrict D (Ioo l h) measurableSet_Ioo bordered K hK
        (WithLp.toLp 2 F) := by
    apply Subtype.ext
    simp only [modeSupportedHilbertRestrict_coe, modeSupportedHilbertProjection_apply,
      WithLp.toLp_fst, WithLp.toLp_snd, modeInnerSource, modeRegionVector_idempotent]
  rw [modeSupportedPairOperator_apply, modeSupportedPairOperator_apply, he]

end ContinuousFlexibility.Radial
