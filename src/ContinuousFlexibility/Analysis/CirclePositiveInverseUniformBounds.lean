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

/-- Keep the inverse construction and jet uniqueness over an abstract space.
The concrete circle model is used only when supplying these hypotheses. -/
private theorem inverse_family_actual_uniform_oneHigh
    {E : Type*} [TopologicalSpace E] [AddCommGroup E] [Module ℝ E]
    [IsTopologicalAddGroup E] [ContinuousSMul ℝ E] [T2Space E]
    (p : ℕ → Seminorm ℝ E) (hp : Monotone p)
    {U W : Set E} (hU : IsOpen U) (hUW : U ⊆ W)
    (L : E → E →L[ℝ] E)
    (J₀ : SmoothDirections univ (fun x : E × E => L x.1 x.2))
    (hJ₀ : ∀ n, HasUniformLowGrowth (jetGrading (pairGrading p p) n) p
      (fun z => J₀.D n z.1 z.2))
    (V : E → E →ₗ[ℝ] E)
    (hVbound : HasUniformLowGrowth (pairGrading p p) p
      (fun x : E × E => V x.1 x.2))
    (hleft : ∀ e ∈ U, ∀ u, V e (L e u) = u)
    (hright : ∀ e ∈ U, ∀ u, L e (V e u) = u)
    (P : E → E →ₗ[ℝ] E)
    (JP : SmoothDirections (W ×ˢ univ) (fun x : E × E => P x.1 x.2))
    (hPV : ∀ e ∈ U, P e = V e)
    (A : E → Prop) (hAU : ∀ e, A e → e ∈ U) :
    ∀ n, ∃ base loss : ℕ, ∀ K : ℝ, 0 ≤ K → ∀ s : ℕ, ∃ C : ℝ, 0 ≤ C ∧
      ∀ x : E × E, A x.1 →
        pairGrading p p base x ≤ K → ∀ v : Fin n → E × E,
          p s (JP.D n x v) ≤ C * tameJetSize (pairGrading p p) n s loss base x v := by
  let J : SmoothDirections (U ×ˢ univ) (fun x : E × E => L x.1 x.2) :=
    J₀.restrict (hU.prod isOpen_univ) (subset_univ _)
  have hJbound (n : ℕ) :
      HasUniformLowGrowth (jetGrading (pairGrading p p) n) p
        (fun z => J.D n z.1 z.2) := hJ₀ n
  have hV : ContinuousOn (fun x : E × E => V x.1 x.2) (U ×ˢ univ) := by
    apply (JP.continuousOn.mono (fun x hx => ⟨hUW hx.1, hx.2⟩)).congr
    intro x hx
    exact (congrArg (fun M : E →ₗ[ℝ] E => M x.2) (hPV x.1 hx.1)).symm
  let VC : E → E →L[ℝ] E := inverseFamilyContinuousLinearMap V hV
  have hVC (e : E) (he : e ∈ U) (u : E) : VC e u = V e u :=
    inverseFamilyContinuousLinearMap_apply V hV he u
  have hVCcont : ContinuousOn (fun x : E × E => VC x.1 x.2) (U ×ˢ univ) :=
    continuousOn_inverseFamilyContinuousLinearMap V hV
  have hleftC (e : E) (he : e ∈ U) (u : E) : VC e (L e u) = u :=
    (hVC e he (L e u)).trans (hleft e he u)
  have hrightC (e : E) (he : e ∈ U) (u : E) : L e (VC e u) = u :=
    (congrArg (L e) (hVC e he u)).trans (hright e he u)
  have hVCbound : HasUniformLowGrowth (pairGrading p p) p
      (fun x : E × E => VC x.1 x.2) :=
    inverseFamilyContinuousLinearMap_uniformLowGrowth V hV hVbound
  let JV : SmoothDirections (U ×ˢ univ) (fun x : E × E => VC x.1 x.2) :=
    inverseFamilySmoothDirections J hU VC hleftC hrightC hVCcont
  have hvalue (x : E × E) (hx : x ∈ U ×ˢ univ) : VC x.1 x.2 = P x.1 x.2 :=
    (hVC x.1 hx.1 x.2).trans
      (congrArg (fun M : E →ₗ[ℝ] E => M x.2) (hPV x.1 hx.1)).symm
  let Jactual : SmoothDirections (U ×ˢ univ) (fun x : E × E => P x.1 x.2) :=
    JV.congrOn (fun x hx => hvalue x hx)
  have hb := inverseFamilySmoothDirections_uniform_oneHigh hp hp hp
    J hU VC hleftC hrightC hVCcont hVCbound hJbound
  intro n
  let hn := hb n
  let base : ℕ := hn.choose
  let loss : ℕ := hn.choose_spec.choose
  have hbound := hn.choose_spec.choose_spec
  refine ⟨base, loss, fun K hK s => ?_⟩
  let hC := hbound K hK s
  refine ⟨hC.choose, hC.choose_spec.1, fun x hA hx v => ?_⟩
  have hxU : x ∈ U ×ˢ univ := ⟨hAU x.1 hA, mem_univ _⟩
  have hjet : JP.D n x = JV.D n x :=
    (JP.restrict (hU.prod isOpen_univ) (fun z hz => ⟨hUW hz.1, hz.2⟩)).unique
      Jactual n x hxU
  have hmeasure : p s (JP.D n x v) = p s (JV.D n x v) :=
    congrArg (fun M : (E × E) [×n]→L[ℝ] E => p s (M v)) hjet
  exact hmeasure.le.trans (hC.choose_spec.2 x hxU hx v)

private theorem circlePositiveInverse_forward_uniform_growth
    (hS : IsCircleModel T γ S) (hT : IsMaterialData D T)
    (hD : IsAccumulatingProfile D) (hγ : 0 < γ)
    (hinterp : HasInterpolation S.grading) (travel : ℕ → ℝ) :
    ∃ J : SmoothDirections univ
      (fun x : S.Space × S.Space =>
        circleShiftedChartComposeContinuousLinear hS hT hD hγ travel x.1 x.2),
      ∀ n, HasUniformLowGrowth (jetGrading (pairGrading S.grading S.grading) n) S.grading
        (fun z => J.D n z.1 z.2) := by
  let hforward := exists_circleChartComposition_uniform_oneHigh
    (D := D) (T := T) (γ := γ) (S := S) hS hT hD hγ hinterp travel
  refine ⟨hforward.choose, fun n => ?_⟩
  exact (uniformLowGrowth_circleChartCompositionJetValue
    (D := D) (T := T) (γ := γ) (S := S) hS hT hD hγ hinterp travel n).congr
    (fun z : (S.Space × S.Space) × (Fin n → S.Space × S.Space) =>
      hS.2.2.2.2.2.1 ((hforward.choose_spec.1 n z.1 z.2).trans
        (circleChartCompositionJetValue_decode
          (D := D) (T := T) (γ := γ) (S := S) hS hT hD hγ travel n z.1 z.2).symm))

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
  let hforward := circlePositiveInverse_forward_uniform_growth
    (D := D) (T := T) (γ := γ) (S := S) hS hT hD hγ hinterp travel
  exact inverse_family_actual_uniform_oneHigh (E := S.Space) S.grading
    (gradedSeminorm_monotone (fun j => S.level j) S.bond) hU hsub
    (circleShiftedChartComposeContinuousLinear hS hT hD hγ travel)
    hforward.choose hforward.choose_spec
    (circleInverseComposeLinear hS hT hD hγ travel (a / 2) ha')
    (uniformLowGrowth_circleInverseComposeLinear
      (D := D) (T := T) (γ := γ) (S := S) hS hT hD hγ hinterp travel (a / 2) ha')
    (fun e he u => circleInverseComposeLinear_left_inverse
      hS hT hD hγ travel (a / 2) ha' e u (hlower e he))
    (fun e he u => circleInverseComposeLinear_right_inverse
      hS hT hD hγ travel (a / 2) ha' e u (hlower e he))
    (circlePositiveInverseComposeLinear hS hT hD hγ travel) JP
    (fun e he => circlePositiveInverseComposeLinear_eq_fixed
      hS hT hD hγ travel (a / 2) ha' e (hlower e he))
    (fun e => ∀ m θ, a ≤ deriv (circleAffineLift travel (S.decode e) 1 m) θ)
    (fun e he => circleAffineLift_mem_interior_half_lower hS hT hD hγ travel a ha e he)

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
