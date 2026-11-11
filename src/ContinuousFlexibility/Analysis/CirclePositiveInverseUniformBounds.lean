import ContinuousFlexibility.Analysis.CircleInverseUniformGrowth
import ContinuousFlexibility.Analysis.CircleCompositionUniformBounds
import ContinuousFlexibility.Analysis.TameInverseUniformBounds
import ContinuousFlexibility.Analysis.CirclePositiveInverseSmoothTame

/-!
# Uniform one-high bounds for the canonical positive inverse

The canonical inverse has a genuine tower on the full positive-lift
domain. At points with any specified common positive lower derivative
bound, all of its parameter jets satisfy uniform bounded-low-seminorm
estimates. A single open set with half the lower bound contains all
such points. The proof estimates the actual finite inverse expressions
on that set and identifies their jets by uniqueness.
-/

noncomputable section

namespace ContinuousFlexibility.Statements

open Set ContinuousFlexibility.Analysis

local instance circlePositiveInverseUniformBoundsPairSMul (S : CircleModelData) :
    SMul ℝ (S.Space × S.Space) := Prod.instSMul

variable {D : ReferenceData} {T : MaterialData} {γ : ℝ} {S : CircleModelData}

theorem circlePositiveInverseComposeLinear_uniform_oneHigh
    (hS : IsCircleModel T γ S) (hT : IsMaterialData D T)
    (hD : IsAccumulatingProfile D) (hγ : 0 < γ)
    (hinterp : HasInterpolation S.grading) (travel : ℕ → ℝ)
    (JP : SmoothDirections (circlePositiveLiftDomain S ×ˢ univ)
      (fun x : S.Space × S.Space =>
        circlePositiveInverseComposeLinear hS hT hD hγ travel x.1 x.2))
    (a : ℝ) (ha : 0 < a) :
    ∀ n, ∃ base loss : ℕ, ∀ K : ℝ, 0 ≤ K → ∀ s : ℕ, ∃ C : ℝ, 0 ≤ C ∧
      ∀ x : S.Space × S.Space,
        (∀ m θ, a ≤ deriv (circleAffineLift travel (S.decode x.1) 1 m) θ) →
        pairGrading S.grading S.grading base x ≤ K → ∀ v : Fin n → S.Space × S.Space,
          S.grading s (JP.D n x v) ≤
            C * tameJetSize (pairGrading S.grading S.grading) n s loss base x v := by
  let U : Set S.Space := interior {e : S.Space |
    ∀ m θ, a / 2 ≤ deriv (circleAffineLift travel (S.decode e) 1 m) θ}
  have hU : IsOpen U := isOpen_interior
  have ha' : 0 < a / 2 := half_pos ha
  have hlower (e : S.Space) (he : e ∈ U) (m : ℕ) (θ : ℝ) :
      a / 2 ≤ deriv (circleAffineLift travel (S.decode e) 1 m) θ :=
    interior_subset he m θ
  have hsub : U ⊆ circlePositiveLiftDomain S := by
    intro e he
    exact (circlePositiveLiftDomain_iff hS travel e).mpr
      (fun m θ => ha'.trans_le (hlower e he m θ))
  let L : S.Space → S.Space →L[ℝ] S.Space :=
    circleShiftedChartComposeContinuousLinear hS hT hD hγ travel
  let hforward := exists_circleChartComposition_uniform_oneHigh hS hT hD hγ hinterp travel
  let J₀ : SmoothDirections univ (fun x : S.Space × S.Space => L x.1 x.2) := hforward.choose
  let J : SmoothDirections (U ×ˢ univ) (fun x : S.Space × S.Space => L x.1 x.2) :=
    J₀.restrict (hU.prod isOpen_univ) (subset_univ _)
  have hJbound (n : ℕ) :
      HasUniformLowGrowth (jetGrading (pairGrading S.grading S.grading) n) S.grading
        (fun z => J.D n z.1 z.2) := by
    apply (uniformLowGrowth_circleChartCompositionJetValue hS hT hD hγ hinterp travel n).congr
    intro z
    apply hS.2.2.2.2.2.1
    exact (hforward.choose_spec.1 n z.1 z.2).trans
      (circleChartCompositionJetValue_decode hS hT hD hγ travel n z.1 z.2).symm
  let V : S.Space → S.Space →ₗ[ℝ] S.Space :=
    circleInverseComposeLinear hS hT hD hγ travel (a / 2) ha'
  have heq (e : S.Space) (he : e ∈ U) :
      circlePositiveInverseComposeLinear hS hT hD hγ travel e = V e :=
    circlePositiveInverseComposeLinear_eq_fixed hS hT hD hγ travel (a / 2) ha' e
      (hlower e he)
  have hV : ContinuousOn (fun x : S.Space × S.Space => V x.1 x.2) (U ×ˢ univ) := by
    apply (JP.continuousOn.mono (fun x hx => ⟨hsub hx.1, hx.2⟩)).congr
    intro x hx
    exact (congrArg (fun M : S.Space →ₗ[ℝ] S.Space => M x.2) (heq x.1 hx.1)).symm
  let VC : S.Space → S.Space →L[ℝ] S.Space := inverseFamilyContinuousLinearMap V hV
  have hVC (e : S.Space) (he : e ∈ U) (u : S.Space) : VC e u = V e u :=
    inverseFamilyContinuousLinearMap_apply V hV he u
  have hVCcont : ContinuousOn (fun x : S.Space × S.Space => VC x.1 x.2) (U ×ˢ univ) :=
    continuousOn_inverseFamilyContinuousLinearMap V hV
  have hleft (e : S.Space) (he : e ∈ U) (u : S.Space) : VC e (L e u) = u :=
    (hVC e he (L e u)).trans
      (circleInverseComposeLinear_left_inverse hS hT hD hγ travel (a / 2) ha' e u
        (hlower e he))
  have hright (e : S.Space) (he : e ∈ U) (u : S.Space) : L e (VC e u) = u :=
    (congrArg (L e) (hVC e he u)).trans
      (circleInverseComposeLinear_right_inverse hS hT hD hγ travel (a / 2) ha' e u
        (hlower e he))
  have hVCbound : HasUniformLowGrowth (pairGrading S.grading S.grading) S.grading
      (fun x : S.Space × S.Space => VC x.1 x.2) :=
    inverseFamilyContinuousLinearMap_uniformLowGrowth V hV
      (uniformLowGrowth_circleInverseComposeLinear hS hT hD hγ hinterp travel (a / 2) ha')
  let JV := inverseFamilySmoothDirections J hU VC hleft hright hVCcont
  have hvalue (x : S.Space × S.Space) (hx : x ∈ U ×ˢ univ) :
      VC x.1 x.2 = circlePositiveInverseComposeLinear hS hT hD hγ travel x.1 x.2 :=
    (hVC x.1 hx.1 x.2).trans
      (congrArg (fun M : S.Space →ₗ[ℝ] S.Space => M x.2) (heq x.1 hx.1)).symm
  let Jactual := JV.congr hvalue
  have hm := gradedSeminorm_monotone (fun j => S.level j) S.bond
  have hb := inverseFamilySmoothDirections_uniform_oneHigh hm hm hm
    J hU VC hleft hright hVCcont hVCbound hJbound
  intro n
  let hn := hb n
  let base : ℕ := hn.choose
  let loss : ℕ := hn.choose_spec.choose
  have hbound := hn.choose_spec.choose_spec
  refine ⟨base, loss, fun K hK s => ?_⟩
  let hC := hbound K hK s
  refine ⟨hC.choose, hC.choose_spec.1, fun x hpos hx v => ?_⟩
  have hxU : x ∈ U ×ˢ univ :=
    ⟨circleAffineLift_mem_interior_half_lower hS hT hD hγ travel a ha x.1 hpos, mem_univ _⟩
  have hjet : JP.D n x = Jactual.D n x :=
    (JP.restrict (hU.prod isOpen_univ) (fun z hz => ⟨hsub hz.1, hz.2⟩)).unique
      Jactual n x hxU
  have hjetValue : JP.D n x v = JV.D n x v := congrArg (fun A => A v) hjet
  exact hjetValue.symm ▸ hC.choose_spec.2 x hxU hx v

/-- One canonical tower works for every specified common positive
derivative bound. Each bound then supplies constants before any point,
direction, or external selector is chosen. -/
theorem exists_circlePositiveInverseComposeLinear_uniform_oneHigh
    (hS : IsCircleModel T γ S) (hT : IsMaterialData D T)
    (hD : IsAccumulatingProfile D) (hγ : 0 < γ)
    (hinterp : HasInterpolation S.grading) (travel : ℕ → ℝ) :
    ∃ J : SmoothDirections (circlePositiveLiftDomain S ×ˢ univ)
      (fun x : S.Space × S.Space =>
        circlePositiveInverseComposeLinear hS hT hD hγ travel x.1 x.2),
      ∀ a : ℝ, 0 < a → ∀ n, ∃ base loss : ℕ,
        ∀ K : ℝ, 0 ≤ K → ∀ s : ℕ, ∃ C : ℝ, 0 ≤ C ∧
          ∀ x : S.Space × S.Space,
            (∀ m θ, a ≤ deriv (circleAffineLift travel (S.decode x.1) 1 m) θ) →
            pairGrading S.grading S.grading base x ≤ K → ∀ v : Fin n → S.Space × S.Space,
              S.grading s (J.D n x v) ≤
                C * tameJetSize (pairGrading S.grading S.grading) n s loss base x v := by
  let h := smoothTameOn_circlePositiveInverseComposeLinear hS hT hD hγ hinterp travel
  refine ⟨h.choose, fun a ha => ?_⟩
  exact circlePositiveInverseComposeLinear_uniform_oneHigh hS hT hD hγ hinterp travel h.choose a ha

end ContinuousFlexibility.Statements
