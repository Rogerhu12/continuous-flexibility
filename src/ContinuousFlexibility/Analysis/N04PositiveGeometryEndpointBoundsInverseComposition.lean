module

public import ContinuousFlexibility.Analysis.N04PositiveGeometryEndpointBoundsCalculus
public import ContinuousFlexibility.Analysis.CircleTravelUniformJets

/-!
# Actual inverse composition preserves a common low parameter order

The original positive inverse operator is restricted to the open
half-lower-bound domain containing the given endpoint family. Its
fixed-base estimate and the genuine ordered-partition chain rule then
give the estimate for the composed family.
-/

@[expose] public section

noncomputable section

namespace ContinuousFlexibility.Analysis

open Set ContinuousFlexibility.Statements

theorem n04PositiveGeometry_endpointBounds_inverseCompose
    {D : ReferenceData} {T : MaterialData} {γ : ℝ} {M : CircleModelData}
    (hM : IsCircleModel T γ M) (hT : IsMaterialData D T)
    (hD : IsAccumulatingProfile D) (hγ : 0 < γ) (hi : HasInterpolation M.grading)
    {E : Type*} [TopologicalSpace E] [AddCommGroup E] [Module ℝ E]
    [IsTopologicalAddGroup E] [ContinuousSMul ℝ E]
    {p : ℕ → Seminorm ℝ E} (hp : Monotone p)
    (hI : HasInterpolation (pairGrading realGrading p))
    {U : Set E} {f g : E → M.Space}
    {J : SmoothDirections U f} {K : SmoothDirections U g}
    (hJ : N04EndpointFixedBaseBounds p M.grading J)
    (hK : N04EndpointFixedBaseBounds p M.grading K)
    (travel : ℕ → ℝ) {a : ℝ} (ha : 0 < a)
    (hlower : ∀ x ∈ U, ∀ m θ, a ≤ 1 + deriv (M.decode (f x) m) θ)
    (Jout : SmoothDirections U
      (fun x => circlePositiveInverseComposeLinear hM hT hD hγ travel (f x) (g x))) :
    N04EndpointFixedBaseBounds p M.grading Jout := by
  let V := circleUniformInverseDomain M a ×ˢ (univ : Set M.Space)
  have hV : IsOpen V := (circleUniformInverseDomain_isOpen M a).prod isOpen_univ
  have hsub : V ⊆ circlePositiveLiftDomain M ×ˢ univ :=
    fun _ hx => ⟨circleUniformInverseDomain_subset_positive ha hx.1, hx.2⟩
  let JF := (exists_circleChartComposition_uniform_oneHigh
    hM hT hD hγ hi (fun _ => 0)).choose
  let JP0 := (smoothTameOn_circlePositiveInverseComposeLinear
    hM hT hD hγ hi (fun _ => 0)).choose
  let JP := (smoothTameOn_circlePositiveInverseComposeLinear
    hM hT hD hγ hi travel).choose
  let Q := smoothDirectionsRestrict JP hV hsub
  have hQ : N04EndpointFixedBaseBounds
      (pairGrading M.grading M.grading) M.grading Q := by
    refine (circlePositiveInverseComposeLinear_fixedBase_oneHigh
      hD hT hγ hM hi JF JP0 (a / 2) (half_pos ha)).elim ?_
    intro B hB
    refine ⟨B, fun n => ?_⟩
    refine (hB n).elim ?_
    intro ell hell
    refine ⟨ell, fun R _ s => ?_⟩
    refine (hell (max 1 R) (le_max_left _ _) s).elim ?_
    intro C hC
    refine ⟨C, hC.1, fun x hx hxR v => ?_⟩
    have hxlower : ∀ m θ,
        a / 2 ≤ deriv (circleAffineLift travel (M.decode x.1) 1 m) θ := by
      intro m θ
      simpa only [circleAffineLift_deriv hM] using (interior_subset hx.1 m θ)
    exact hC.2 travel JP x hxlower (hxR.trans (le_max_right _ _)) v
  have hmap : MapsTo (fun x => (f x, g x)) U V := by
    intro x hx
    exact ⟨mem_circleUniformInverseDomain hM hT hD hγ ha (f x) (hlower x hx), mem_univ _⟩
  have hcomp := (hJ.prod hp hK).compCircle hp hI hM hQ hmap
  exact hcomp.of_unique Jout

end ContinuousFlexibility.Analysis
