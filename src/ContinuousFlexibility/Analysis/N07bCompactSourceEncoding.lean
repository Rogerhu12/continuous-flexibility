module

public import ContinuousFlexibility.Analysis.SpacesCompactHeights
public import ContinuousFlexibility.Scalar.WeightedDecodeLift

/-!
# Encoding actual compact physical sources

A globally smooth, periodic, even physical field with compact radial support
belongs to every height class. The genuine material coordinate makes its
support bounded on the cylinder, so each weighted jet is an actual cylinder
test. The existing Sobolev decoder then lifts a compatible field to the
physical source kernel, with exact equality of its grading and physical norm.

This construction uses neither a canonical chart nor a volume-space bound.
-/

@[expose] public section

noncomputable section

namespace ContinuousFlexibility.Analysis

open Set Filter MeasureTheory
open ContinuousFlexibility.Statements
open scoped ContDiff Topology

set_option backward.isDefEq.respectTransparency false

/-- Compact radial support is bounded in the actual material coordinate,
also for a field with angular dependence. -/
theorem n07b_compact_pullback_isCylinderTest
    {D : ReferenceData} {T : MaterialData} (hT : IsMaterialData D T)
    {f : PolarPoint → ℝ} (hf : ContDiff ℝ ∞ f)
    (hp : Function.Periodic f (0, Real.pi))
    (hs : HasCompactRadialSupport D f) (γ : ℝ) :
    IsCylinderTest (materialPullback T γ f) := by
  obtain ⟨K, hK, hKD, hzero⟩ := hs
  have hρ : ContinuousOn T.rho K :=
    (hT.1 T.rho (by simp)).continuousOn.mono hKD
  obtain ⟨B, hB⟩ := hK.exists_bound_of_continuousOn hρ
  have hinv := hT.2.2.2.2.2.2.2.1
  refine ⟨contDiff_materialPullback hT hf.contDiffOn, ?_,
    max B 0 + 1, by positivity, ?_⟩
  · intro p
    change T.H (T.radius (p.1 + 0)) ^ (-γ) *
      f (T.radius (p.1 + 0), p.2 + Real.pi) =
        T.H (T.radius p.1) ^ (-γ) * f (T.radius p.1, p.2)
    rw [add_zero]
    have h := hp (T.radius p.1, p.2)
    change f (T.radius p.1 + 0, p.2 + Real.pi) = f (T.radius p.1, p.2) at h
    rw [add_zero] at h
    rw [h]
  · intro p hp
    have hout : T.radius p.1 ∉ K := by
      intro hr
      have hb := hB (T.radius p.1) hr
      rw [(hinv p.1).2, Real.norm_eq_abs] at hb
      have hmax : B ≤ max B 0 := le_max_left _ _
      linarith
    simp only [materialPullback, hzero _ hout, mul_zero]

/-- Compact support supplies all actual weighted jets, at every exponent. -/
theorem n07b_heightMember_of_compact_support
    {D : ReferenceData} {T : MaterialData} (hT : IsMaterialData D T)
    {f : PolarPoint → ℝ} (hf : ContDiff ℝ ∞ f)
    (hp : Function.Periodic f (0, Real.pi))
    (he : ∀ r θ, f (r, -θ) = f (r, θ))
    (hs : HasCompactRadialSupport D f) (γ : ℝ) :
    HeightMember D T γ f := by
  have htest := n07b_compact_pullback_isCylinderTest hT hf hp hs γ
  obtain ⟨K, hK, hKD, hzero⟩ := hs
  refine ⟨hf.contDiffOn, he, hp, ?_, ?_⟩
  · intro p hp
    exact hzero p.1 (fun hr => hp ⟨hKD hr, mem_univ _⟩) p.2
  · intro a b c
    exact (spaces_cylinderTest_weight hT (htest.mixedDerivative a b) c).memLp

/-- The existing decoder lift belongs to the actual compatibility kernel. -/
def n07bSourceOfHeightMember
    {D : ReferenceData} {T : MaterialData} {S : PhysicalSpacesData}
    (hS : IsPhysicalSpaces D T S) (f : PolarPoint → ℝ)
    (hf : HeightMember D T (3 / 4 : ℝ) f)
    (hQ : physicalSourceIntegral D f = 0) : S.Source :=
  ⟨SobolevModelData.liftHeight (hS.1 (3 / 4 : ℝ)) f hf, by
    change S.Q (SobolevModelData.liftHeight (hS.1 (3 / 4 : ℝ)) f hf) = 0
    rw [hS.2.2.2.2.2.2.2.1, SobolevModelData.decode_liftHeight, hQ]⟩

theorem n07bSourceOfHeightMember_decode
    {D : ReferenceData} {T : MaterialData} {S : PhysicalSpacesData}
    (hS : IsPhysicalSpaces D T S) (f : PolarPoint → ℝ)
    (hf : HeightMember D T (3 / 4 : ℝ) f)
    (hQ : physicalSourceIntegral D f = 0) :
    (S.height (3 / 4 : ℝ)).decode (n07bSourceOfHeightMember hS f hf hQ).val = f :=
  SobolevModelData.decode_liftHeight (hS.1 (3 / 4 : ℝ)) f hf

theorem n07bSourceOfHeightMember_grading
    {D : ReferenceData} {T : MaterialData} {S : PhysicalSpacesData}
    (hS : IsPhysicalSpaces D T S) (f : PolarPoint → ℝ)
    (hf : HeightMember D T (3 / 4 : ℝ) f)
    (hQ : physicalSourceIntegral D f = 0) (s : ℕ) :
    S.sourceGrading s (n07bSourceOfHeightMember hS f hf hQ) =
      physicalNorm T (3 / 4 : ℝ) s f := by
  rw [PhysicalSpacesData.sourceGrading, Seminorm.comp_apply, Submodule.subtype_apply,
    sobolevGrading_eq_physicalNorm (hS.1 (3 / 4 : ℝ)),
    n07bSourceOfHeightMember_decode]

/-- A compact compatible physical field has an exact source-space encoding.
No membership or norm of the desired source is assumed. -/
theorem n07b_exists_source_of_compact_support
    {D : ReferenceData} {T : MaterialData} {S : PhysicalSpacesData}
    (hT : IsMaterialData D T) (hS : IsPhysicalSpaces D T S)
    {f : PolarPoint → ℝ} (hf : ContDiff ℝ ∞ f)
    (hp : Function.Periodic f (0, Real.pi))
    (he : ∀ r θ, f (r, -θ) = f (r, θ))
    (hs : HasCompactRadialSupport D f)
    (hQ : physicalSourceIntegral D f = 0) :
    ∃ F : S.Source, (S.height (3 / 4 : ℝ)).decode F.val = f ∧
      ∀ s, S.sourceGrading s F = physicalNorm T (3 / 4 : ℝ) s f := by
  have hm := n07b_heightMember_of_compact_support hT hf hp he hs (3 / 4 : ℝ)
  exact ⟨n07bSourceOfHeightMember hS f hm hQ,
    n07bSourceOfHeightMember_decode hS f hm hQ,
    n07bSourceOfHeightMember_grading hS f hm hQ⟩

end ContinuousFlexibility.Analysis
