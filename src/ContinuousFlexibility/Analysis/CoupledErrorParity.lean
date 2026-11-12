import ContinuousFlexibility.Statements.Nonlinear
import ContinuousFlexibility.Analysis.CircleReturnAlgebra
import ContinuousFlexibility.Analysis.SpacesCircleParity

/-!
# Parity of the independent circle correction error

For an even residual, its derivative is odd. The second term of the actual
circle error is therefore a product of two odd functions, while its first
term is an even part. The second independent argument need not itself be
odd. The original even projection gives a total continuous linear map into
the required subspace and preserves this actual error on the N02 domain.
-/

noncomputable section

namespace ContinuousFlexibility.Statements

open Set ContinuousFlexibility.Analysis
open scoped ContDiff

set_option backward.isDefEq.respectTransparency false

theorem coupled_evenPart_even (f : ℝ → ℝ) : Function.Even (evenPart f) := by
  intro θ
  exact circleReturnEven_even f θ

theorem coupled_oddPart_odd (f : ℝ → ℝ) : Function.Odd (oddPart f) := by
  intro θ
  exact circleReturnOdd_odd f θ

theorem coupled_deriv_odd_of_even {f : ℝ → ℝ}
    (hf : Differentiable ℝ f) (he : Function.Even f) : Function.Odd (deriv f) := by
  intro θ
  have hm : HasDerivAt (fun t : ℝ => f (-t)) (-deriv f (-θ)) θ := by
    simpa only [Function.comp_def, neg_one_smul] using
      (hf (-θ)).hasDerivAt.scomp θ (hasDerivAt_neg' (x := θ))
  have hfun : (fun t : ℝ => f (-t)) = f := funext he
  rw [hfun] at hm
  have h := congrArg Neg.neg (hm.unique (hf θ).hasDerivAt)
  simpa only [neg_neg] using h

private theorem coupled_even_sub_odd_product (f g h : ℝ → ℝ)
    (hg : Function.Odd g) :
    Function.Even (fun θ => evenPart f θ - g θ * oddPart h θ) := by
  intro θ
  change evenPart f (-θ) - g (-θ) * oddPart h (-θ) =
    evenPart f θ - g θ * oddPart h θ
  rw [coupled_evenPart_even f θ, hg θ, coupled_oddPart_odd h θ, neg_mul_neg]

private theorem coupled_even_average (f : ℝ → ℝ) (θ : ℝ) :
    (f (-θ) + f (- -θ)) / 2 = (f θ + f (-θ)) / 2 := by
  rw [neg_neg, add_comm]

variable {D : ReferenceData} {T : MaterialData} {S : PhysicalSpacesData}
  {C : NonlinearGeometryData S} {R : ReturnEquationData S}

/-- Evenness of the independent residual is sufficient for the circle error.
The odd part appearing in the formula handles an arbitrary second argument. -/
theorem coupled_circleChartError_even
    (z : AnnularState S × ℝ) (r v : CircleSpace S) (m : ℕ)
    (hr : Function.Even ((S.circle (3 / 4 : ℝ)).decode r m))
    (hdr : Differentiable ℝ ((S.circle (3 / 4 : ℝ)).decode r m)) :
    Function.Even (circleChartError S C z r v m) := by
  exact coupled_even_sub_odd_product
    (fun t => (S.circle (3 / 4 : ℝ)).decode r m t *
      ∫ a in (0 : ℝ)..1, deriv ((S.circle (3 / 4 : ℝ)).decode v m)
        (t + C.travel m + a * returnResidualField S C z m t))
    (deriv ((S.circle (3 / 4 : ℝ)).decode r m))
    (fun t => (S.circle (3 / 4 : ℝ)).decode v m
      (t + C.travel m + returnResidualField S C z m t))
    (coupled_deriv_odd_of_even hdr hr)

/-- The actual N02 error belongs to the original even circle subspace. -/
theorem coupled_returnError_mem_even
    (hS : IsPhysicalSpaces D T S) {base : ℕ} {ε : ℝ}
    (h2 : N02Properties D T S C R base ε)
    {z : AnnularState S × ℝ} (hz : z ∈ stateNeighborhood S C base ε)
    (hs : stateSector S z.1) (r : CircleSpace S)
    (hr : r ∈ evenCircleSubmodule S) (v : CircleSpace S) :
    R.error z r v ∈ evenCircleSubmodule S := by
  intro m θ
  have hdr : Differentiable ℝ ((S.circle (3 / 4 : ℝ)).decode r m) :=
    (((hS.2.1 (3 / 4 : ℝ)).2.2.2.1 r).1 m).1.differentiable (by simp)
  exact (h2.2.2.2.2.1 z hz hs r v m (-θ)).trans
    ((coupled_circleChartError_even (S := S) (C := C) z r v m
      (fun t => hr m t) hdr θ).trans (h2.2.2.2.2.1 z hz hs r v m θ).symm)

theorem coupled_evenProjection_mem
    (hS : IsPhysicalSpaces D T S) (u : CircleSpace S) :
    circleModelEvenProjection (hS.2.1 (3 / 4 : ℝ)) u ∈ evenCircleSubmodule S := by
  intro m θ
  exact (circleModelEvenProjection_decode (hS.2.1 (3 / 4 : ℝ)) u m (-θ)).trans
    ((coupled_even_average ((S.circle (3 / 4 : ℝ)).decode u m) θ).trans
      (circleModelEvenProjection_decode (hS.2.1 (3 / 4 : ℝ)) u m θ).symm)

theorem coupled_evenProjection_eq_of_even
    (hS : IsPhysicalSpaces D T S) {u : CircleSpace S}
    (hu : u ∈ evenCircleSubmodule S) :
    circleModelEvenProjection (hS.2.1 (3 / 4 : ℝ)) u = u := by
  apply (hS.2.1 (3 / 4 : ℝ)).2.2.2.2.2.1
  funext m θ
  rw [circleModelEvenProjection_decode, hu m θ]
  ring

/-- The existing even projection, with its proved even-circle codomain. -/
def coupledEvenProjectionCLM (hS : IsPhysicalSpaces D T S) :
    CircleSpace S →L[ℝ] EvenCircle S :=
  (circleModelEvenProjection (hS.2.1 (3 / 4 : ℝ))).codRestrict
    (evenCircleSubmodule S) (coupled_evenProjection_mem hS)

theorem coupledEvenProjectionCLM_val (hS : IsPhysicalSpaces D T S)
    (u : CircleSpace S) :
    (coupledEvenProjectionCLM hS u).val =
      circleModelEvenProjection (hS.2.1 (3 / 4 : ℝ)) u := rfl

theorem coupledEvenProjectionCLM_coe (hS : IsPhysicalSpaces D T S)
    (u : EvenCircle S) : coupledEvenProjectionCLM hS u.val = u := by
  apply Subtype.ext
  rw [coupledEvenProjectionCLM_val]
  exact coupled_evenProjection_eq_of_even hS u.property

theorem coupledEvenProjectionCLM_isTame (hS : IsPhysicalSpaces D T S) :
    IsTameLinear (S.circle (3 / 4 : ℝ)).grading
      (evenCircleGradingAt S (3 / 4 : ℝ))
      (coupledEvenProjectionCLM hS).toLinearMap 0 0 :=
  circleModelEvenProjection_isTame (hS.2.1 (3 / 4 : ℝ))

/-- The total projection preserves the actual error on its geometric domain. -/
theorem coupled_projected_returnError_eq
    (hS : IsPhysicalSpaces D T S) {base : ℕ} {ε : ℝ}
    (h2 : N02Properties D T S C R base ε)
    {z : AnnularState S × ℝ} (hz : z ∈ stateNeighborhood S C base ε)
    (hs : stateSector S z.1) (r : EvenCircle S) (v : CircleSpace S) :
    (coupledEvenProjectionCLM hS (R.error z r.val v)).val = R.error z r.val v := by
  exact (coupledEvenProjectionCLM_val hS (R.error z r.val v)).trans
    (coupled_evenProjection_eq_of_even hS
      (coupled_returnError_mem_even (D := D) (T := T) (S := S) (C := C) (R := R)
        hS h2 hz hs r.val r.property v))

end ContinuousFlexibility.Statements
