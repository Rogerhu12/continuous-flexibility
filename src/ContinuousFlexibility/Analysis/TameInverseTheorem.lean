import ContinuousFlexibility.Analysis.TameInverseBounds
import ContinuousFlexibility.Analysis.TameJetLocalBounds

/-!
# Hamilton's smooth tame inverse-family theorem

The proof constructs all genuine derivatives by finite inverse expressions,
proves local tame growth of each expression, and then normalizes its
multilinear increments.  The initial inverse is assumed only continuous
and tame, as in the frozen statement.
-/

noncomputable section

namespace ContinuousFlexibility.Analysis

open Set Filter
open scoped Topology BigOperators
open ContinuousFlexibility.Statements

set_option backward.isDefEq.respectTransparency false

section GeneralInverse

variable {X Y Z : Type*}
  [TopologicalSpace X] [AddCommGroup X] [Module ℝ X]
  [IsTopologicalAddGroup X] [ContinuousSMul ℝ X]
  [TopologicalSpace Y] [AddCommGroup Y] [Module ℝ Y]
  [IsTopologicalAddGroup Y] [ContinuousSMul ℝ Y] [T2Space Y]
  [TopologicalSpace Z] [AddCommGroup Z] [Module ℝ Z]
  [IsTopologicalAddGroup Z] [ContinuousSMul ℝ Z] [T2Space Z]

/-- A continuous tame inverse family of a smooth tame linear family is
smooth tame, for the actual topologies and the exact homogeneous bounds. -/
theorem smoothTameOn_inverseFamily
    {p : ℕ → Seminorm ℝ X} {q : ℕ → Seminorm ℝ Y} {r : ℕ → Seminorm ℝ Z}
    (hp : Monotone p) (hq : Monotone q) (hr : Monotone r)
    (htp : WithSeminorms p) (htq : WithSeminorms q) (htr : WithSeminorms r)
    {U : Set X} (hU : IsOpen U)
    (L : X → Y →L[ℝ] Z) (V : X → Z →ₗ[ℝ] Y)
    (hL : SmoothTameOn (pairGrading p q) r (U ×ˢ univ) (fun z : X × Y => L z.1 z.2))
    (hleft : ∀ x ∈ U, ∀ y, V x (L x y) = y)
    (hright : ∀ x ∈ U, ∀ y, L x (V x y) = y)
    (hV : ContinuousOn (fun z : X × Z => V z.1 z.2) (U ×ˢ univ))
    (hVTame : LinearFamilyTame p q r U V) :
    SmoothTameOn (pairGrading p r) q (U ×ˢ univ) (fun z : X × Z => V z.1 z.2) := by
  obtain ⟨J, hJ⟩ := hL
  let VC : X → Z →L[ℝ] Y := inverseFamilyContinuousLinearMap V hV
  have hVC (x : X) (hx : x ∈ U) (y : Z) : VC x y = V x y :=
    inverseFamilyContinuousLinearMap_apply V hV hx y
  have hVCcont : ContinuousOn (fun z : X × Z => VC z.1 z.2) (U ×ˢ univ) :=
    continuousOn_inverseFamilyContinuousLinearMap V hV
  have hleftC : ∀ x ∈ U, ∀ y, VC x (L x y) = y := by
    intro x hx y
    rw [hVC x hx]
    exact hleft x hx y
  have hrightC : ∀ x ∈ U, ∀ y, L x (VC x y) = y := by
    intro x hx y
    rw [hVC x hx]
    exact hright x hx y
  have hVlocal : LocallyTameOn (pairGrading p r) q (U ×ˢ univ)
      (fun z : X × Z => VC z.1 z.2) :=
    (locallyTameOn_inverse_of_linearFamilyTame htr hV hVTame).congr
      (fun z hz => hVC z.1 hz.1 z.2)
  have hJlocal (k : ℕ) : LocallyTameOn
      (pairGrading (pairGrading p q) (tupleGrading (fun _ : Fin k => pairGrading p q)))
      r ((U ×ˢ univ) ×ˢ univ) (fun z => J.D k z.1 z.2) :=
    locallyTameOn_jetEvaluation (withSeminorms_pairGrading htp htq) J hJ k
  let JV := inverseFamilySmoothDirections J hU VC hleftC hrightC hVCcont
  have hJVlocal (k : ℕ) : LocallyTameOn (jetGrading (pairGrading p r) k) q
      ((U ×ˢ univ) ×ˢ univ) (fun z => JV.D k z.1 z.2) := by
    have he := (inverseExpressionJet (X := X) (Y := Y) (Z := Z) k).locallyTameOn_eval
      hp hq hr (tupleGrading_monotone _ (fun _ => pairGrading_monotone hp hr))
      (inverseExpressionJet_zeroLoss p q r k) J VC hVlocal hJlocal
    apply (inverseLocallyTame_fst he).congr
    intro z hz
    exact inverseFamilySmoothDirections_apply J hU VC hleftC hrightC hVCcont k hz.1.1 z.2
  have hsmooth := smoothTameOn_of_locallyTameOn_jets (pairGrading_monotone hp hr)
    (withSeminorms_pairGrading htp htr) JV hJVlocal
  exact smoothTameOn_congr hsmooth (fun z hz => hVC z.1 hz.1 z.2)

end GeneralInverse

/-- Hamilton's inverse-family theorem on the project's concrete Banach
projective limits.  No smoothing or inverse theorem is assumed. -/
theorem h02Statement : H02Statement := by
  intro E F G _ _ _ _ _ _ _ _ _ e f g
  intro U hU L V hL hleft hright hV hVTame
  exact smoothTameOn_inverseFamily
    (gradedSeminorm_monotone E e) (gradedSeminorm_monotone F f) (gradedSeminorm_monotone G g)
    (withSeminorms_graded E e) (withSeminorms_graded F f) (withSeminorms_graded G g)
    hU L V hL hleft hright hV hVTame

end ContinuousFlexibility.Analysis
