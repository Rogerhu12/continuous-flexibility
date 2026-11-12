import ContinuousFlexibility.Analysis.N08ExtendedControlResidual
import ContinuousFlexibility.Analysis.N08ControlColumnSmooth

/-!
# The genuine smoothing control column of the scalar residual

The column is extracted from the actual extended residual, with one state
ball and one loss for every output order. Exact affine-line agreement turns
its weak-control derivative into the original scalar residual's derivative
in every physical circle direction.
-/

noncomputable section

namespace ContinuousFlexibility.Statements

open Set ContinuousFlexibility.Analysis

set_option backward.isDefEq.respectTransparency false

private theorem n08_lineDerivative_of_equal_rays
    {E B Y : Type*} [AddCommGroup E] [Module ℝ E]
    [AddCommGroup B] [Module ℝ B]
    [TopologicalSpace Y] [AddCommGroup Y] [Module ℝ Y]
    {f : E → Y} {g : B → Y} {x v : E} {b : B} {df : Y}
    (heq : ∀ t : ℝ, g (t • b) = f (x + t • v))
    (hg : HasProjectiveLineDerivAt g df 0 b) : HasProjectiveLineDerivAt f df x v := by
  simpa only [HasProjectiveLineDerivAt, zero_add, heq] using hg

private theorem n08_with_controlColumn
    {X B Y : Type*}
    [TopologicalSpace X] [AddCommGroup X] [Module ℝ X]
    [IsTopologicalAddGroup X] [ContinuousSMul ℝ X]
    [NormedAddCommGroup B] [NormedSpace ℝ B]
    [TopologicalSpace Y] [AddCommGroup Y] [Module ℝ Y]
    [IsTopologicalAddGroup Y] [ContinuousSMul ℝ Y] [T2Space Y]
    {p : ℕ → Seminorm ℝ X} {q : ℕ → Seminorm ℝ Y} {x0 : X} {F : X × B → Y}
    (hp : Monotone p) (hq : Monotone q) (htp : WithSeminorms p)
    (hF : UniformTameGerm (pairGrading p (fun _ => normSeminorm ℝ B)) q (x0, 0) F)
    {P : Prop}
    (hP : ∀ base loss : ℕ, ∀ ε : ℝ, 0 < ε → ∀ H : X → B →L[ℝ] Y,
      (∀ x, p base (x - x0) < ε → ∀ b : B,
        HasProjectiveLineDerivAt (fun a : B => F (x, a)) (H x b) 0 b) →
      SmoothTameOn (pairGrading p (fun _ => normSeminorm ℝ B)) q
        ({x | p base (x - x0) < ε} ×ˢ univ) (fun z : X × B => H z.1 z.2) →
      (∀ s : ℕ, ∃ K : ℝ, 0 ≤ K ∧ ∀ x, p base (x - x0) < ε → ∀ b : B,
        q s (H x b) ≤ K * (1 + p (s + loss) (x - x0)) * ‖b‖) → P) : P := by
  obtain ⟨base, loss, ε, hε, H, hderiv, hsmooth, hbound⟩ :=
    n08ControlColumn_of_uniformTameGerm hp hq htp hF
  exact hP base loss ε hε H hderiv hsmooth hbound

theorem n08_sourceGrading_monotone (S : PhysicalSpacesData) :
    Monotone S.sourceGrading := by
  intro i j hij f
  exact gradedSeminorm_monotone (fun n => (S.height (3 / 4 : ℝ)).level n)
    (S.height (3 / 4 : ℝ)).bond hij f.val

variable {D : ReferenceData} {T : MaterialData} {S : PhysicalSpacesData}
  {C : NonlinearGeometryData S} {base loss : ℕ} {ε : ℝ}

theorem n08ExtendedControlResidual_hasLineDerivAt
    (hT : IsMaterialData D T) (hS : IsPhysicalSpaces D T S)
    (hN : N01Properties D T S C base loss ε)
    (z : AnnularState S × ℝ) (u : CircleSpace S) (df : S.Source)
    (hd : HasProjectiveLineDerivAt
      (fun b : ControlBanach => n08ExtendedControlResidual hT hS hN (z, b))
      df 0 (n08ControlRestriction S u)) :
    HasProjectiveLineDerivAt (fun x => n08ActualScalarResidual hT hS hN (x, z.2))
      df z.1 (0, (0, (u, 0))) :=
  n08_lineDerivative_of_equal_rays
    (fun t => n08ExtendedControlResidual_controlLine hT hS hN z u t) hd

/-- The column, its actual derivative identity, and all smoothing bounds
are obtained together on one common neighborhood of the reference state. -/
theorem n08ActualControlColumn_exists
    (hT : IsMaterialData D T) (hS : IsPhysicalSpaces D T S)
    (hN : N01Properties D T S C base loss ε) :
    ∃ columnBase columnLoss : ℕ, ∃ δ : ℝ, 0 < δ ∧
      ∃ H : AnnularState S × ℝ → ControlBanach →L[ℝ] S.Source,
        (∀ z, n08StateParameterGrading S columnBase (z - (C.referenceState, 0)) < δ →
          ∀ u : CircleSpace S,
          HasProjectiveLineDerivAt
            (fun x => n08ActualScalarResidual hT hS hN (x, z.2))
            (H z (n08ControlRestriction S u)) z.1 (0, (0, (u, 0)))) ∧
        SmoothTameOn (n08ExtendedControlGrading S) S.sourceGrading
          ({z | n08StateParameterGrading S columnBase (z - (C.referenceState, 0)) < δ}
            ×ˢ univ) (fun z : (AnnularState S × ℝ) × ControlBanach => H z.1 z.2) ∧
        (∀ s : ℕ, ∃ K : ℝ, 0 ≤ K ∧ ∀ z,
          n08StateParameterGrading S columnBase (z - (C.referenceState, 0)) < δ →
          ∀ b : ControlBanach,
          S.sourceGrading s (H z b) ≤
            K * (1 + n08StateParameterGrading S (s + columnLoss)
              (z - (C.referenceState, 0))) * ‖b‖) := by
  refine n08_with_controlColumn
      (X := AnnularState S × ℝ) (B := ControlBanach) (Y := S.Source)
      (p := n08StateParameterGrading S) (q := S.sourceGrading)
      (x0 := (C.referenceState, 0)) (F := n08ExtendedControlResidual hT hS hN)
      (n08StateParameterGrading_monotone S)
      (n08_sourceGrading_monotone S) (n08StateParameterGrading_topology S)
      (n08ExtendedControlResidual_uniformTameGerm hT hS hN) ?_
  intro columnBase columnLoss δ hδ H hderiv hsmooth hbound
  refine ⟨columnBase, columnLoss, δ, hδ, H, ?_, hsmooth, hbound⟩
  intro z hz u
  exact n08ExtendedControlResidual_hasLineDerivAt hT hS hN z u
    (H z (n08ControlRestriction S u)) (hderiv z hz (n08ControlRestriction S u))

end ContinuousFlexibility.Statements
