module

public import ContinuousFlexibility.Analysis.N05ReferenceResidual
public import ContinuousFlexibility.Analysis.SpacesCompactHeights
public import Mathlib.Analysis.Calculus.FDeriv.Congr

/-!
# Actual compact tests for the reference correction

Every smooth even periodic field with compact radial support belongs to the
physical height model.  The reference operator identity therefore applies to
these concrete fields.  Locality is proved for the actual Frechet divergence,
without imposing unrecorded regularity on the corrected coefficients.
-/

@[expose] public section

noncomputable section

namespace ContinuousFlexibility.Statements

open Set Filter MeasureTheory
open scoped Topology ContDiff

set_option backward.isDefEq.respectTransparency false

/-- Compact radial support remains bounded under the material coordinate,
also for tests that depend on the angular variable. -/
theorem n05_materialPullback_isCylinderTest
    {D : ReferenceData} {T : MaterialData} (hT : IsMaterialData D T)
    {f : PolarPoint → ℝ} (hf : ContDiff ℝ ∞ f)
    (hperiodic : Function.Periodic f (0, Real.pi))
    (hsupport : HasCompactRadialSupport D f) (γ : ℝ) :
    IsCylinderTest (materialPullback T γ f) := by
  obtain ⟨K, hK, hKD, hzero⟩ := hsupport
  have hρ : ContinuousOn T.rho K := (hT.1 T.rho (by simp)).continuousOn.mono hKD
  obtain ⟨B, hB⟩ := hK.exists_bound_of_continuousOn hρ
  have hinv := hT.2.2.2.2.2.2.2.1
  refine ⟨contDiff_materialPullback hT hf.contDiffOn, ?_,
    max B 0 + 1, by positivity, ?_⟩
  · intro p
    change T.H (T.radius (p.1 + 0)) ^ (-γ) *
      f (T.radius (p.1 + 0), p.2 + Real.pi) =
        T.H (T.radius p.1) ^ (-γ) * f (T.radius p.1, p.2)
    rw [add_zero]
    congr 1
    simpa only [Prod.mk_add_mk, add_zero] using
      hperiodic (T.radius p.1, p.2)
  · intro p hp
    have hout : T.radius p.1 ∉ K := by
      intro hr
      have hb := hB (T.radius p.1) hr
      rw [(hinv p.1).2, Real.norm_eq_abs] at hb
      have hmax : B ≤ max B 0 := le_max_left _ _
      linarith
    simp only [materialPullback, hzero _ hout, mul_zero]

/-- Concrete compact even periodic tests lie in every physical height class. -/
theorem n05_heightMember_of_compact_radial_support
    {D : ReferenceData} {T : MaterialData} (hT : IsMaterialData D T)
    {f : PolarPoint → ℝ} (hf : ContDiff ℝ ∞ f)
    (heven : ∀ r θ, f (r, -θ) = f (r, θ))
    (hperiodic : Function.Periodic f (0, Real.pi))
    (hsupport : HasCompactRadialSupport D f) (γ : ℝ) :
    HeightMember D T γ f := by
  have htest := n05_materialPullback_isCylinderTest hT hf hperiodic hsupport γ
  refine ⟨hf.contDiffOn, heven, hperiodic, ?_, ?_⟩
  · obtain ⟨K, _, hKD, hzero⟩ := hsupport
    intro p hp
    exact hzero p.1 (fun hKp => hp ⟨hKD hKp, mem_univ _⟩) p.2
  · intro a b c
    exact (spaces_cylinderTest_weight hT (htest.mixedDerivative a b) c).memLp

/-- Realization is supplied by the exact physical model's decoder. -/
theorem n05_exists_heightPair_of_compact_test
    {D : ReferenceData} {T : MaterialData} {S : PhysicalSpacesData}
    (hT : IsMaterialData D T) (hS : IsPhysicalSpaces D T S)
    {f : PolarPoint → ℝ} (hf : ContDiff ℝ ∞ f)
    (heven : ∀ r θ, f (r, -θ) = f (r, θ))
    (hperiodic : Function.Periodic f (0, Real.pi))
    (hsupport : HasCompactRadialSupport D f) :
    ∃ η : HeightPair S, heightPairField S η = f := by
  have hm := n05_heightMember_of_compact_radial_support hT hf heven hperiodic
    hsupport (3 / 4 : ℝ)
  obtain ⟨u, hu⟩ := (hS.1 (3 / 4 : ℝ)).2.2.2.2.1 f hm
  refine ⟨(u, 0), ?_⟩
  funext p
  simp only [heightPairField, hu, zero_mul, add_zero]

/-- The actual divergence depends only on the germ of the test function.
No differentiability assumption on the coefficient fields is needed. -/
theorem n05_divergenceOperator_congr
    (L : SymmetricCoefficients) {f g : PolarPoint → ℝ} {p : PolarPoint}
    (hfg : f =ᶠ[𝓝 p] g) :
    divergenceOperator L f p = divergenceOperator L g p := by
  have hpartial : ∀ᶠ q in 𝓝 p,
      radialPartial f q = radialPartial g q ∧
        angularPartial f q = angularPartial g q := by
    filter_upwards [hfg.fderiv (𝕜 := ℝ)] with q hq
    constructor <;> simp only [radialPartial, angularPartial, hq]
  have hN : (fun q => L.a q * radialPartial f q + L.b q * angularPartial f q) =ᶠ[𝓝 p]
      (fun q => L.a q * radialPartial g q + L.b q * angularPartial g q) := by
    filter_upwards [hpartial] with q hq
    rw [hq.1, hq.2]
  have hT : (fun q => L.b q * radialPartial f q + L.c q * angularPartial f q) =ᶠ[𝓝 p]
      (fun q => L.b q * radialPartial g q + L.c q * angularPartial g q) := by
    filter_upwards [hpartial] with q hq
    rw [hq.1, hq.2]
  exact congrArg₂ (fun a b : ℝ => a + b)
    (congrArg (fun A : PolarPoint →L[ℝ] ℝ => A (1, 0))
      (hN.fderiv_eq (𝕜 := ℝ)))
    (congrArg (fun A : PolarPoint →L[ℝ] ℝ => A (0, 1))
      (hT.fderiv_eq (𝕜 := ℝ)))

/-- A realized local test may be used in the reference operator identity. -/
theorem n05_reference_correctionOperator_eq_germ
    {D : ReferenceData} {T : MaterialData} {S : PhysicalSpacesData}
    {C : NonlinearGeometryData S} {R : ReturnEquationData S}
    {L : ReturnCorrectionData S} {base loss : ℕ} {ε : ℝ}
    (h : NonlinearPropertiesThrough03 D T S C R L base loss ε)
    {f : PolarPoint → ℝ} {p : PolarPoint} (hp : p ∈ annularOpen D)
    (η : HeightPair S) (hη : heightPairField S η =ᶠ[𝓝 p] f) :
    divergenceOperator (originalCoefficients D S C (C.referenceState, 0)) f p =
      divergenceOperator (L.coefficients (C.referenceState, 0)) f p := by
  calc
    _ = divergenceOperator (originalCoefficients D S C (C.referenceState, 0))
        (heightPairField S η) p := n05_divergenceOperator_congr _ hη.symm
    _ = divergenceOperator (L.coefficients (C.referenceState, 0))
        (heightPairField S η) p := n05_reference_correctionOperator_eq h η hp
    _ = _ := n05_divergenceOperator_congr _ hη

/-- The reference equality holds for all actual compact even periodic tests. -/
theorem n05_reference_correctionOperator_eq_compact_test
    {D : ReferenceData} {T : MaterialData} {S : PhysicalSpacesData}
    {C : NonlinearGeometryData S} {R : ReturnEquationData S}
    {L : ReturnCorrectionData S} {base loss : ℕ} {ε : ℝ}
    (hT : IsMaterialData D T) (hS : IsPhysicalSpaces D T S)
    (h : NonlinearPropertiesThrough03 D T S C R L base loss ε)
    {f : PolarPoint → ℝ} (hf : ContDiff ℝ ∞ f)
    (heven : ∀ r θ, f (r, -θ) = f (r, θ))
    (hperiodic : Function.Periodic f (0, Real.pi))
    (hsupport : HasCompactRadialSupport D f)
    {p : PolarPoint} (hp : p ∈ annularOpen D) :
    divergenceOperator (originalCoefficients D S C (C.referenceState, 0)) f p =
      divergenceOperator (L.coefficients (C.referenceState, 0)) f p := by
  obtain ⟨η, hη⟩ := n05_exists_heightPair_of_compact_test hT hS hf heven hperiodic hsupport
  apply n05_reference_correctionOperator_eq_germ h hp η
  exact Filter.Eventually.of_forall (congrFun hη)

end ContinuousFlexibility.Statements

