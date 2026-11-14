module

public import ContinuousFlexibility.Analysis.SpacesCompactHeights
public import ContinuousFlexibility.Statements.Nonlinear

/-!
# Actual compact radial tests in the height space

A smooth, angularly periodic physical function with compact radial
support has a genuine cylinder-test material pullback. Evenness then
places it in every weighted height class. The existing Sobolev-model
surjectivity supplies an actual height element and a HeightPair with
zero endpoint constant; no local test-operator assumption is used.
-/

@[expose] public section

noncomputable section

namespace ContinuousFlexibility.Analysis

open Set Filter MeasureTheory
open ContinuousFlexibility.Statements
open scoped Topology ContDiff

set_option backward.isDefEq.respectTransparency false

/-- Compact radial support, rather than compact support on the lifted
cylinder, makes every material derivative a genuine cylinder test. -/
theorem materialPullback_isCylinderTest_of_compactRadialSupport
    {D : ReferenceData} {T : MaterialData} (hT : IsMaterialData D T)
    {f : PolarPoint → ℝ} (hf : ContDiffOn ℝ ∞ f (annularOpen D))
    (hperiod : Function.Periodic f (0, Real.pi))
    (hsupport : HasCompactRadialSupport D f) (γ : ℝ) :
    IsCylinderTest (materialPullback T γ f) := by
  obtain ⟨K, hK, hKD, hzero⟩ := hsupport
  have hρ : ContinuousOn T.rho K := (hT.1 T.rho (by simp)).continuousOn.mono hKD
  obtain ⟨B, hB⟩ := hK.exists_bound_of_continuousOn hρ
  have hinv := hT.2.2.2.2.2.2.2.1
  refine ⟨contDiff_materialPullback hT hf, ?_, max B 0 + 1, by positivity, ?_⟩
  · rintro ⟨r, θ⟩
    simpa only [Prod.mk_add_mk, add_zero] using
      materialPullback_angular_periodic (T := T) (γ := γ) hperiod r θ
  · intro p hp
    have hout : T.radius p.1 ∉ K := by
      intro hr
      have hb := hB (T.radius p.1) hr
      rw [(hinv p.1).2, Real.norm_eq_abs] at hb
      have hmax : B ≤ max B 0 := le_max_left _ _
      linarith
    change T.H (T.radius p.1) ^ (-γ) * f (T.radius p.1, p.2) = 0
    rw [hzero _ hout p.2, mul_zero]

/-- Actual even periodic compact radial tests belong to every weighted
height class, including all of its weighted material derivatives. -/
theorem heightMember_of_compact_even_periodic
    {D : ReferenceData} {T : MaterialData} (hT : IsMaterialData D T)
    {f : PolarPoint → ℝ} (hf : ContDiffOn ℝ ∞ f (annularOpen D))
    (heven : ∀ r θ, f (r, -θ) = f (r, θ))
    (hperiod : Function.Periodic f (0, Real.pi))
    (hsupport : HasCompactRadialSupport D f) (γ : ℝ) :
    HeightMember D T γ f := by
  have htest := materialPullback_isCylinderTest_of_compactRadialSupport
    hT hf hperiod hsupport γ
  obtain ⟨K, hK, hKD, hzero⟩ := hsupport
  refine ⟨hf, heven, hperiod, ?_, ?_⟩
  · intro p hp
    apply hzero p.1
    intro hKp
    exact hp ⟨hKD hKp, mem_univ _⟩
  · intro a b c
    exact (spaces_cylinderTest_weight hT (htest.mixedDerivative a b) c).memLp

/-- The decoded test is represented by a true height element. The
endpoint constant vanishes, so its HeightPair field is exactly the test
on the entire physical plane. -/
theorem exists_heightPair_of_compact_even_periodic
    {D : ReferenceData} {T : MaterialData} {S : PhysicalSpacesData}
    (hT : IsMaterialData D T) (hS : IsPhysicalSpaces D T S)
    {f : PolarPoint → ℝ} (hf : ContDiffOn ℝ ∞ f (annularOpen D))
    (heven : ∀ r θ, f (r, -θ) = f (r, θ))
    (hperiod : Function.Periodic f (0, Real.pi))
    (hsupport : HasCompactRadialSupport D f) :
    ∃ η : HeightPair S, η.2 = 0 ∧ heightPairField S η = f := by
  have hmem : HeightMember D T (3 / 4 : ℝ) f :=
    heightMember_of_compact_even_periodic hT hf heven hperiod hsupport _
  obtain ⟨u, hu⟩ := (hS.1 (3 / 4 : ℝ)).2.2.2.2.1 f hmem
  refine ⟨(u, 0), rfl, ?_⟩
  funext p
  simpa only [heightPairField, zero_mul, add_zero] using congrFun hu p

end ContinuousFlexibility.Analysis
