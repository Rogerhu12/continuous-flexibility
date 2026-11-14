module

public import ContinuousFlexibility.Analysis.CircleCompositionSmoothTame
public import ContinuousFlexibility.Analysis.CircleInverseFamilyTame
public import ContinuousFlexibility.Analysis.TameInverseInitialContinuity
public import ContinuousFlexibility.Analysis.TameInverseTheorem
public import ContinuousFlexibility.Analysis.NonlinearNeighborhoodRestriction

/-!
# Smooth tame composition with the actual inverse circle lift

The inverse operator is the composition operator of `Function.invFun`.
Its true two-sided inverse identities, fixed-loss estimates, and the
resolvent identity give the hypotheses of the genuine inverse-family
theorem. The low seminorm order is chosen before the positive derivative
bound, the size of the local box, and the output order.
-/

@[expose] public section

noncomputable section

namespace ContinuousFlexibility.Analysis

open Set ContinuousFlexibility.Statements

theorem smoothTameOn_inverseFamily_of_linearFamilyTame
    {X Y Z : Type*}
    [TopologicalSpace X] [AddCommGroup X] [Module ℝ X]
    [IsTopologicalAddGroup X] [ContinuousSMul ℝ X]
    [TopologicalSpace Y] [AddCommGroup Y] [Module ℝ Y]
    [IsTopologicalAddGroup Y] [ContinuousSMul ℝ Y] [T2Space Y]
    [TopologicalSpace Z] [AddCommGroup Z] [Module ℝ Z]
    [IsTopologicalAddGroup Z] [ContinuousSMul ℝ Z] [T2Space Z]
    {p : ℕ → Seminorm ℝ X} {q : ℕ → Seminorm ℝ Y} {r : ℕ → Seminorm ℝ Z}
    (hp : Monotone p) (hq : Monotone q) (hr : Monotone r)
    (htp : WithSeminorms p) (htq : WithSeminorms q) (htr : WithSeminorms r)
    {U : Set X} (hU : IsOpen U)
    (L : X → Y →L[ℝ] Z) (V : X → Z →ₗ[ℝ] Y)
    (hL : SmoothTameOn (pairGrading p q) r (U ×ˢ univ)
      (fun z : X × Y => L z.1 z.2))
    (hleft : ∀ x ∈ U, ∀ y, V x (L x y) = y)
    (hright : ∀ x ∈ U, ∀ y, L x (V x y) = y)
    (hVTame : LinearFamilyTame p q r U V) :
    SmoothTameOn (pairGrading p r) q (U ×ˢ univ)
      (fun z : X × Z => V z.1 z.2) := by
  have hV : ContinuousOn (fun z : X × Z => V z.1 z.2) (U ×ˢ univ) :=
    continuousOn_inverseFamily_of_linearFamilyTame htp htq htr hq
      (fun x => (L x).toLinearMap) V hL.choose.continuousOn hleft hright hVTame
  exact smoothTameOn_inverseFamily hp hq hr htp htq htr hU L V
    hL hleft hright hV hVTame

end ContinuousFlexibility.Analysis

namespace ContinuousFlexibility.Statements

open Set ContinuousFlexibility.Analysis

local instance circleInverseSmoothTamePairSMul (S : CircleModelData) :
    SMul ℝ (S.Space × S.Space) := Prod.instSMul

variable {D : ReferenceData} {T : MaterialData} {γ : ℝ} {S : CircleModelData}

theorem smoothTameOn_circleInverseComposeLinear_of_low_bound
    (hS : IsCircleModel T γ S) (hT : IsMaterialData D T)
    (hD : IsAccumulatingProfile D) (hγ : 0 < γ)
    (hinterp : HasInterpolation S.grading)
    (base loss : ℕ) (hbase : loss + 2 ≤ base)
    (hselected : ∀ b c : ℕ, base < b → b + loss < c →
      ∃ C : ℝ, 0 ≤ C ∧ ∀ x,
        S.grading b x ≤ C * (S.grading base x) ^ (((c : ℝ) - b - loss) / (c - base)) *
          (S.grading c x) ^ (((b : ℝ) - base + loss) / (c - base)))
    (travel : ℕ → ℝ) (a : ℝ) (ha : 0 < a)
    (U : Set S.Space) (hU : IsOpen U) (K : ℝ) (hK : 0 ≤ K)
    (hUlow : ∀ e ∈ U, S.grading base e ≤ K)
    (hUpos : ∀ e ∈ U, ∀ m θ,
      a ≤ deriv (circleAffineLift travel (S.decode e) 1 m) θ) :
    SmoothTameOn (pairGrading S.grading S.grading) S.grading (U ×ˢ univ)
      (fun z : S.Space × S.Space =>
        circleInverseComposeLinear hS hT hD hγ travel a ha z.1 z.2) := by
  have hp : Monotone S.grading :=
    gradedSeminorm_monotone (fun j => S.level j) S.bond
  have ht : WithSeminorms S.grading :=
    withSeminorms_graded (fun j => S.level j) S.bond
  have hL : SmoothTameOn (pairGrading S.grading S.grading) S.grading (U ×ˢ univ)
      (fun z : S.Space × S.Space =>
        circleShiftedChartComposeContinuousLinear hS hT hD hγ travel z.1 z.2) :=
    smoothTameOn_restrict_open
      (smoothTameOn_circleChartComposition hS hT hD hγ hinterp travel)
      (hU.prod isOpen_univ) (subset_univ _)
  have hV : LinearFamilyTame S.grading S.grading S.grading U
      (circleInverseComposeLinear hS hT hD hγ travel a ha) :=
    circleInverseComposeLinear_linearFamilyTame hS hT hD hγ base loss hbase hselected
      travel a ha U K hK hUlow hUpos
  exact smoothTameOn_inverseFamily_of_linearFamilyTame hp hp hp ht ht ht hU
    (circleShiftedChartComposeContinuousLinear hS hT hD hγ travel)
    (circleInverseComposeLinear hS hT hD hγ travel a ha) hL
    (fun e he u => circleInverseComposeLinear_left_inverse hS hT hD hγ
      travel a ha e u (hUpos e he))
    (fun e he u => circleInverseComposeLinear_right_inverse hS hT hD hγ
      travel a ha e u (hUpos e he)) hV

/-- Inverse composition on an arbitrary open low-seminorm box with a
uniform positive chart derivative. The low order is independent of
the box, its size, the derivative lower bound, and the output order. -/
theorem smoothTameOn_circleInverseComposeLinear
    (hS : IsCircleModel T γ S) (hT : IsMaterialData D T)
    (hD : IsAccumulatingProfile D) (hγ : 0 < γ)
    (hinterp : HasInterpolation S.grading) (travel : ℕ → ℝ)
    (requestedBase : ℕ) :
    ∃ base : ℕ, requestedBase ≤ base ∧
      ∀ K : ℝ, 0 ≤ K → ∀ a : ℝ, ∀ ha : 0 < a,
      ∀ U : Set S.Space, IsOpen U →
      (∀ e ∈ U, S.grading base e ≤ K) →
      (∀ e ∈ U, ∀ m θ, a ≤ deriv (circleAffineLift travel (S.decode e) 1 m) θ) →
      SmoothTameOn (pairGrading S.grading S.grading) S.grading (U ×ˢ univ)
        (fun z : S.Space × S.Space =>
          circleInverseComposeLinear hS hT hD hγ travel a ha z.1 z.2) := by
  let initialBase : ℕ := hinterp.choose
  let loss : ℕ := hinterp.choose_spec.choose
  have hi := hinterp.choose_spec.choose_spec
  let base : ℕ := max requestedBase (max initialBase (loss + 2))
  have hib : initialBase ≤ base := (le_max_left _ _).trans (le_max_right _ _)
  have hlb : loss + 2 ≤ base := (le_max_right _ _).trans (le_max_right _ _)
  refine ⟨base, le_max_left _ _, ?_⟩
  intro K hK a ha U hU hUlow hUpos
  exact smoothTameOn_circleInverseComposeLinear_of_low_bound hS hT hD hγ hinterp
    base loss hlb (fun b c hb hc => hi base b c hib hb hc)
    travel a ha U hU K hK hUlow hUpos

end ContinuousFlexibility.Statements
