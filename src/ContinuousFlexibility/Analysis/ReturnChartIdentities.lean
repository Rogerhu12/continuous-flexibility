import ContinuousFlexibility.Analysis.CircleReturnAlgebra
import ContinuousFlexibility.Statements.Nonlinear

/-!
# The actual return residual and the two charted returns

The algebraic part of section 7, `eq:full-height-one-chart` and
`eq:return-identity`.  The right chart is the odd part of the transported
left chart; its even part is read in the coordinates of the right chart.
The identities below use the actual inverse maps from the nonlinear data.
In particular, vanishing of the residual is equivalent to the two desired
return identities, not merely to an auxiliary Fourier equation.
-/

noncomputable section

namespace ContinuousFlexibility.Statements

theorem evenPart_eq_circleReturnEven (f : ℝ → ℝ) :
    evenPart f = Analysis.circleReturnEven f := rfl

theorem oddPart_eq_circleReturnOdd (f : ℝ → ℝ) :
    oddPart f = Analysis.circleReturnOdd f := rfl

theorem evenPart_add_oddPart (f : ℝ → ℝ) (θ : ℝ) :
    evenPart f θ + oddPart f θ = f θ :=
  Analysis.circleReturnEven_add_odd f θ

theorem oddPart_add_evenPart (f : ℝ → ℝ) (θ : ℝ) :
    oddPart f θ + evenPart f θ = f θ := by
  rw [add_comm]
  exact evenPart_add_oddPart f θ

theorem evenPart_neg_argument (f : ℝ → ℝ) (θ : ℝ) :
    evenPart f (-θ) = evenPart f θ :=
  Analysis.circleReturnEven_even f θ

theorem oddPart_neg_argument (f : ℝ → ℝ) (θ : ℝ) :
    oddPart f (-θ) = -oddPart f θ :=
  Analysis.circleReturnOdd_odd f θ

theorem evenPart_comp_odd (f h : ℝ → ℝ) (hh : ∀ θ, h (-θ) = -h θ) :
    evenPart (f ∘ h) = evenPart f ∘ h :=
  Analysis.circleReturnEven_comp_odd f h hh

theorem oddPart_comp_odd (f h : ℝ → ℝ) (hh : ∀ θ, h (-θ) = -h θ) :
    oddPart (f ∘ h) = oddPart f ∘ h :=
  Analysis.circleReturnOdd_comp_odd f h hh

/-- Both inverse identities are used: an arbitrary right inverse need not
inherit a symmetry without injectivity of the original map. -/
theorem returnChart_inverse_odd (h hInv : ℝ → ℝ)
    (hodd : ∀ θ, h (-θ) = -h θ)
    (hleft : ∀ θ, hInv (h θ) = θ) (hright : ∀ θ, h (hInv θ) = θ)
    (θ : ℝ) : hInv (-θ) = -hInv θ := by
  have hinj : Function.Injective h := Function.LeftInverse.injective hleft
  apply hinj
  rw [hright, hodd, hright]

theorem returnChart_inverse_add_period (h hInv : ℝ → ℝ) (period : ℝ)
    (hlift : ∀ θ, h (θ + period) = h θ + period)
    (hleft : ∀ θ, hInv (h θ) = θ) (hright : ∀ θ, h (hInv θ) = θ)
    (θ : ℝ) : hInv (θ + period) = hInv θ + period := by
  have hinj : Function.Injective h := Function.LeftInverse.injective hleft
  apply hinj
  rw [hright, hlift, hright]

/-- The odd part of a degree-one lift is again a degree-one lift. -/
theorem oddPart_add_period_of_lift (f : ℝ → ℝ) (period : ℝ)
    (hf : ∀ θ, f (θ + period) = f θ + period) (θ : ℝ) :
    oddPart f (θ + period) = oddPart f θ + period := by
  have hm := hf (-θ - period)
  have harg : -θ - period + period = -θ := by ring
  rw [harg] at hm
  have hminus : f (-θ - period) = f (-θ) - period := by linarith
  unfold oddPart
  rw [hf θ, show -(θ + period) = -θ - period by ring, hminus]
  ring

/-- The even part of a degree-one lift is periodic. -/
theorem evenPart_add_period_of_lift (f : ℝ → ℝ) (period : ℝ)
    (hf : ∀ θ, f (θ + period) = f θ + period) (θ : ℝ) :
    evenPart f (θ + period) = evenPart f θ := by
  have hm := hf (-θ - period)
  have harg : -θ - period + period = -θ := by ring
  rw [harg] at hm
  have hminus : f (-θ - period) = f (-θ) - period := by linarith
  unfold evenPart
  rw [hf θ, show -(θ + period) = -θ - period by ring, hminus]
  ring

variable (S : PhysicalSpacesData) (C : NonlinearGeometryData S)
  (z : AnnularState S × ℝ) (m : ℕ)

theorem rightChartCandidate_odd (θ : ℝ) :
    rightChartCandidate S C z m (-θ) = -rightChartCandidate S C z m θ :=
  oddPart_neg_argument _ θ

theorem rightChartInverse_odd
    (hleft : ∀ θ, C.rightChartInverse z m (rightChartCandidate S C z m θ) = θ)
    (hright : ∀ θ, rightChartCandidate S C z m (C.rightChartInverse z m θ) = θ)
    (θ : ℝ) : C.rightChartInverse z m (-θ) = -C.rightChartInverse z m θ :=
  returnChart_inverse_odd _ _ (rightChartCandidate_odd S C z m) hleft hright θ

theorem rightChartCandidate_add_period (period : ℝ)
    (hleft : ∀ θ, stateLeftChart S z.1 m (θ + period) = stateLeftChart S z.1 m θ + period)
    (hinv : ∀ θ, C.minusReturnInverse z m (θ + period) = C.minusReturnInverse z m θ + period)
    (θ : ℝ) : rightChartCandidate S C z m (θ + period) =
      rightChartCandidate S C z m θ + period := by
  apply oddPart_add_period_of_lift
  intro t
  rw [hinv, hleft]
  ring

theorem returnResidualField_even
    (hleft : ∀ θ, C.rightChartInverse z m (rightChartCandidate S C z m θ) = θ)
    (hright : ∀ θ, rightChartCandidate S C z m (C.rightChartInverse z m θ) = θ)
    (θ : ℝ) : returnResidualField S C z m (-θ) = returnResidualField S C z m θ := by
  unfold returnResidualField
  rw [rightChartInverse_odd S C z m hleft hright]
  exact evenPart_neg_argument _ _

theorem returnResidualField_add_period (period : ℝ)
    (hleft : ∀ θ, stateLeftChart S z.1 m (θ + period) = stateLeftChart S z.1 m θ + period)
    (hinv : ∀ θ, C.minusReturnInverse z m (θ + period) = C.minusReturnInverse z m θ + period)
    (hchartLeft : ∀ θ, C.rightChartInverse z m (rightChartCandidate S C z m θ) = θ)
    (hchartRight : ∀ θ, rightChartCandidate S C z m (C.rightChartInverse z m θ) = θ)
    (θ : ℝ) : returnResidualField S C z m (θ + period) = returnResidualField S C z m θ := by
  have hrightLift := rightChartCandidate_add_period S C z m period hleft hinv
  have hinverseLift := returnChart_inverse_add_period _ _ period hrightLift hchartLeft hchartRight
  unfold returnResidualField
  rw [hinverseLift]
  apply evenPart_add_period_of_lift
  intro t
  rw [hinv, hleft]
  ring

/-- The transported left chart is `(id + residual) ∘ rightChart`. -/
theorem returnChart_decomposition
    (hchartLeft : ∀ θ, C.rightChartInverse z m (rightChartCandidate S C z m θ) = θ)
    (θ : ℝ) :
    rightChartCandidate S C z m θ +
        returnResidualField S C z m (rightChartCandidate S C z m θ) =
      stateLeftChart S z.1 m (C.minusReturnInverse z m θ) - C.travel m := by
  unfold returnResidualField
  rw [hchartLeft]
  exact oddPart_add_evenPart _ θ

/-- The exact return identity before setting the residual to zero. -/
theorem returnResidualField_return_identity
    (hreturnLeft : ∀ θ, C.minusReturnInverse z m (C.minusFlow z m (C.right m) θ) = θ)
    (hchartLeft : ∀ θ, C.rightChartInverse z m (rightChartCandidate S C z m θ) = θ)
    (θ : ℝ) :
    rightChartCandidate S C z m (C.minusFlow z m (C.right m) θ) +
        returnResidualField S C z m
          (rightChartCandidate S C z m (C.minusFlow z m (C.right m) θ)) =
      stateLeftChart S z.1 m θ - C.travel m := by
  have h := returnChart_decomposition S C z m hchartLeft (C.minusFlow z m (C.right m) θ)
  rw [hreturnLeft] at h
  exact h

theorem returnResidualField_zero_iff_minus_return
    (hreturnLeft : ∀ θ, C.minusReturnInverse z m (C.minusFlow z m (C.right m) θ) = θ)
    (hreturnRight : ∀ θ, C.minusFlow z m (C.right m) (C.minusReturnInverse z m θ) = θ)
    (hchartLeft : ∀ θ, C.rightChartInverse z m (rightChartCandidate S C z m θ) = θ) :
    (∀ θ, returnResidualField S C z m θ = 0) ↔
      ∀ θ, rightChartCandidate S C z m (C.minusFlow z m (C.right m) θ) =
        stateLeftChart S z.1 m θ - C.travel m := by
  constructor
  · intro hzero θ
    have h := returnResidualField_return_identity S C z m hreturnLeft hchartLeft θ
    rw [hzero, add_zero] at h
    exact h
  · intro hreturn θ
    let t : ℝ := C.rightChartInverse z m θ
    have h := hreturn (C.minusReturnInverse z m t)
    rw [hreturnRight] at h
    have hdecomp := oddPart_add_evenPart
      (fun u => stateLeftChart S z.1 m (C.minusReturnInverse z m u) - C.travel m) t
    have hodd : oddPart
        (fun u => stateLeftChart S z.1 m (C.minusReturnInverse z m u) - C.travel m) t =
      stateLeftChart S z.1 m (C.minusReturnInverse z m t) - C.travel m := h
    change evenPart
      (fun u => stateLeftChart S z.1 m (C.minusReturnInverse z m u) - C.travel m) t = 0
    linarith only [hdecomp, hodd]

/-- Odd charts turn the minus return identity into the reflected plus identity. -/
theorem plus_return_of_minus_return
    (hleftOdd : ∀ θ, stateLeftChart S z.1 m (-θ) = -stateLeftChart S z.1 m θ)
    (hminus : ∀ θ, rightChartCandidate S C z m (C.minusFlow z m (C.right m) θ) =
      stateLeftChart S z.1 m θ - C.travel m) (θ : ℝ) :
    rightChartCandidate S C z m (-C.minusFlow z m (C.right m) (-θ)) =
      stateLeftChart S z.1 m θ + C.travel m := by
  rw [rightChartCandidate_odd, hminus, hleftOdd]
  ring

theorem returnResidualField_zero_iff_returns
    (hreturnLeft : ∀ θ, C.minusReturnInverse z m (C.minusFlow z m (C.right m) θ) = θ)
    (hreturnRight : ∀ θ, C.minusFlow z m (C.right m) (C.minusReturnInverse z m θ) = θ)
    (hchartLeft : ∀ θ, C.rightChartInverse z m (rightChartCandidate S C z m θ) = θ)
    (hleftOdd : ∀ θ, stateLeftChart S z.1 m (-θ) = -stateLeftChart S z.1 m θ) :
    (∀ θ, returnResidualField S C z m θ = 0) ↔
      ∀ θ, rightChartCandidate S C z m (C.minusFlow z m (C.right m) θ) =
        stateLeftChart S z.1 m θ - C.travel m ∧
      rightChartCandidate S C z m (-C.minusFlow z m (C.right m) (-θ)) =
        stateLeftChart S z.1 m θ + C.travel m := by
  rw [returnResidualField_zero_iff_minus_return S C z m hreturnLeft hreturnRight hchartLeft]
  constructor
  · intro hminus θ
    exact ⟨hminus θ, plus_return_of_minus_return S C z m hleftOdd hminus θ⟩
  · intro hreturns θ
    exact (hreturns θ).1

/-- Equality in the abstract circle space is detected by its actual decoded field. -/
theorem circle_eq_zero_iff_decoded_zero {T : MaterialData} (γ : ℝ)
    (hmodel : IsCircleModel T γ (S.circle γ)) (u : (S.circle γ).Space) :
    u = 0 ↔ ∀ m θ, (S.circle γ).decode u m θ = 0 := by
  constructor
  · intro hu
    subst u
    intro m θ
    exact congrFun (congrFun ((S.circle γ).decode.map_zero) m) θ
  · intro hu
    apply hmodel.2.2.2.2.2.1
    funext m θ
    rw [hu]
    exact (congrFun (congrFun ((S.circle γ).decode.map_zero) m) θ).symm

/-- The exact zero-residual clause of `N02Properties`, assuming only its
realization and the geometric inverse/chart identities supplied by N01. -/
theorem returnEquation_residual_zero_iff_returns {T : MaterialData}
    (hmodel : IsCircleModel T (3 / 4 : ℝ) (S.circle (3 / 4 : ℝ)))
    (R : ReturnEquationData S)
    (hdecode : ∀ m θ, (S.circle (3 / 4 : ℝ)).decode (R.residual z) m θ =
      returnResidualField S C z m θ)
    (hreturnLeft : ∀ m θ, C.minusReturnInverse z m (C.minusFlow z m (C.right m) θ) = θ)
    (hreturnRight : ∀ m θ, C.minusFlow z m (C.right m) (C.minusReturnInverse z m θ) = θ)
    (hchartLeft : ∀ m θ, C.rightChartInverse z m (rightChartCandidate S C z m θ) = θ)
    (hleftOdd : ∀ m θ, stateLeftChart S z.1 m (-θ) = -stateLeftChart S z.1 m θ) :
    R.residual z = 0 ↔ ∀ m θ,
      rightChartCandidate S C z m (C.minusFlow z m (C.right m) θ) =
        stateLeftChart S z.1 m θ - C.travel m ∧
      rightChartCandidate S C z m (-C.minusFlow z m (C.right m) (-θ)) =
        stateLeftChart S z.1 m θ + C.travel m := by
  rw [circle_eq_zero_iff_decoded_zero S (3 / 4 : ℝ) hmodel]
  simp_rw [hdecode]
  constructor
  · intro hzero m
    exact (returnResidualField_zero_iff_returns S C z m
      (hreturnLeft m) (hreturnRight m) (hchartLeft m) (hleftOdd m)).mp (hzero m)
  · intro hreturns m
    exact (returnResidualField_zero_iff_returns S C z m
      (hreturnLeft m) (hreturnRight m) (hchartLeft m) (hleftOdd m)).mpr (hreturns m)

/-- This is the zero-equation clause with the hypotheses of N01 itself,
so the algebraic bridge does not demand additional chart assumptions. -/
theorem N01Properties.residual_eq_zero_iff_returns {D : ReferenceData} {T : MaterialData}
    {base loss : ℕ} {ε : ℝ} (hN01 : N01Properties D T S C base loss ε)
    (hS : IsPhysicalSpaces D T S) (R : ReturnEquationData S)
    (hz : z ∈ stateNeighborhood S C base ε) (hsector : stateSector S z.1)
    (hdecode : ∀ m θ, (S.circle (3 / 4 : ℝ)).decode (R.residual z) m θ =
      returnResidualField S C z m θ) :
    R.residual z = 0 ↔ ∀ m θ,
      rightChartCandidate S C z m (C.minusFlow z m (C.right m) θ) =
        stateLeftChart S z.1 m θ - C.travel m ∧
      rightChartCandidate S C z m (-C.minusFlow z m (C.right m) (-θ)) =
        stateLeftChart S z.1 m θ + C.travel m := by
  rcases hN01 with ⟨_, _, _, _, _, _, _, hleft, hInv, _⟩
  have hI := hInv z hz hsector
  have hL := hleft z hz hsector
  exact returnEquation_residual_zero_iff_returns S C z (hS.2.1 _) R hdecode
    (fun m θ => (hI m θ).2.1) (fun m θ => (hI m θ).1)
    (fun m θ => (hI m θ).2.2.2) (fun m θ => (hL m θ).2.2.2)

end ContinuousFlexibility.Statements
