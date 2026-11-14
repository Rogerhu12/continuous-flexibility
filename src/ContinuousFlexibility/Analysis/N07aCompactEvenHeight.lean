module

public import ContinuousFlexibility.Analysis.SpacesCompactHeights
public import ContinuousFlexibility.Scalar.WeightedDecodeLift
public import ContinuousFlexibility.Statements.Nonlinear

/-!
# Genuine compact even tests in the physical height space

An actual smooth periodic field with compact radial support has every
weighted material jet in L². Its evenness then places it in the frozen
height decoder, so N03 may be applied to this actual test field.
-/

@[expose] public section

noncomputable section

namespace ContinuousFlexibility.Analysis

open Set Filter MeasureTheory ContinuousFlexibility.Statements
open scoped ContDiff

theorem n07a_compact_physical_pullback_test {D : ReferenceData} {T : MaterialData}
    (hT : IsMaterialData D T) {φ : PolarPoint → ℝ} (hφ : ContDiff ℝ ∞ φ)
    (hπ : Function.Periodic φ (0, Real.pi))
    (hsupp : HasCompactRadialSupport D φ) (γ : ℝ) :
    IsCylinderTest (materialPullback T γ φ) := by
  obtain ⟨A, hAc, hAU, hzero⟩ := hsupp
  have hρ : ContinuousOn T.rho A := (hT.1 T.rho (by simp)).continuousOn.mono hAU
  obtain ⟨B, hB⟩ := hAc.exists_bound_of_continuousOn hρ
  have hinv := hT.2.2.2.2.2.2.2.1
  refine ⟨contDiff_materialPullback hT hφ.contDiffOn, ?_, max B 0 + 1,
    by positivity, ?_⟩
  · intro p
    change T.H (T.radius (p.1 + 0)) ^ (-γ) * φ (T.radius (p.1 + 0), p.2 + Real.pi) =
      T.H (T.radius p.1) ^ (-γ) * φ (T.radius p.1, p.2)
    simp only [add_zero]
    apply congrArg (T.H (T.radius p.1) ^ (-γ) * ·)
    simpa only [Prod.mk_add_mk, add_zero] using hπ (T.radius p.1, p.2)
  · intro p hp
    have hout : T.radius p.1 ∉ A := by
      intro hr
      have hb := hB (T.radius p.1) hr
      rw [(hinv p.1).2, Real.norm_eq_abs] at hb
      have hmax : B ≤ max B 0 := le_max_left _ _
      linarith
    simp only [materialPullback, hzero _ hout, mul_zero]

theorem n07a_compact_even_heightMember {D : ReferenceData} {T : MaterialData}
    (hT : IsMaterialData D T) {φ : PolarPoint → ℝ} (hφ : ContDiff ℝ ∞ φ)
    (heven : ∀ r θ, φ (r, -θ) = φ (r, θ))
    (hπ : Function.Periodic φ (0, Real.pi))
    (hsupp : HasCompactRadialSupport D φ) (γ : ℝ) :
    HeightMember D T γ φ := by
  have htest := n07a_compact_physical_pullback_test hT hφ hπ hsupp γ
  refine ⟨hφ.contDiffOn, heven, hπ, ?_, ?_⟩
  · obtain ⟨A, _, hAU, hzero⟩ := hsupp
    intro p hp
    exact hzero p.1 (fun h => hp ⟨hAU h, mem_univ _⟩) p.2
  · intro a b c
    exact (spaces_cylinderTest_weight hT (htest.mixedDerivative a b) c).memLp

theorem n07a_compact_even_heightPair {D : ReferenceData} {T : MaterialData}
    {S : PhysicalSpacesData} (hS : IsPhysicalSpaces D T S) (hT : IsMaterialData D T)
    {φ : PolarPoint → ℝ} (hφ : ContDiff ℝ ∞ φ)
    (heven : ∀ r θ, φ (r, -θ) = φ (r, θ))
    (hπ : Function.Periodic φ (0, Real.pi))
    (hsupp : HasCompactRadialSupport D φ) :
    ∃ η : HeightPair S, heightPairField S η = φ := by
  let hmem := n07a_compact_even_heightMember hT hφ heven hπ hsupp (3 / 4 : ℝ)
  let η := SobolevModelData.liftHeight (hS.1 (3 / 4 : ℝ)) φ hmem
  have hη := SobolevModelData.decode_liftHeight (hS.1 (3 / 4 : ℝ)) φ hmem
  refine ⟨(η, 0), ?_⟩
  funext p
  simp only [heightPairField, zero_mul, add_zero]
  exact congrFun hη p

end ContinuousFlexibility.Analysis
