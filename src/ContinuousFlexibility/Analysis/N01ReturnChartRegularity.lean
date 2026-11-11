import ContinuousFlexibility.Analysis.ReturnChartDifferentiation

/-!
# Scalar return-chart regularity already implied by N01

The ordinary-flow hypothesis asserts a strictly positive angular derivative
on the closed component, including its right endpoint.  Consequently the
actual return and its specified inverse are differentiable without any
endpoint limiting argument.  These facts supply the scalar regularity
hypotheses needed to differentiate the actual chart residual.
-/

noncomputable section

namespace ContinuousFlexibility.Statements

open Set
open scoped ContDiff

set_option backward.isDefEq.respectTransparency false

variable (S : PhysicalSpacesData) (C : NonlinearGeometryData S)
  (z : AnnularState S × ℝ) (m : ℕ)

theorem stateLeftChart_contDiff {T : MaterialData}
    (hcircle : IsCircleModel T (3 / 4 : ℝ) (S.circle (3 / 4 : ℝ))) :
    ContDiff ℝ ∞ (stateLeftChart S z.1 m) := by
  have hdecode := ((hcircle.2.2.2.1 z.1.2.2.2).1 m).1
  simpa only [stateLeftChart] using contDiff_id.add hdecode

theorem N01Properties.minusFlow_differentiable {D : ReferenceData} {T : MaterialData}
    {base loss : ℕ} {ε r : ℝ} (hN01 : N01Properties D T S C base loss ε)
    (hz : z ∈ stateNeighborhood S C base ε) (hr : r ∈ Icc (C.left m) (C.right m)) :
    Differentiable ℝ (C.minusFlow z m r) := by
  rcases hN01 with ⟨_, _, _, _, _, _, hflow, _⟩
  intro θ
  exact differentiableAt_of_deriv_ne_zero (((hflow z hz m θ).2.2.2 r hr).1.ne')

theorem N01Properties.minusReturnInverse_differentiable {D : ReferenceData} {T : MaterialData}
    {base loss : ℕ} {ε : ℝ} (hN01 : N01Properties D T S C base loss ε)
    (hz : z ∈ stateNeighborhood S C base ε) (hsector : stateSector S z.1) :
    Differentiable ℝ (C.minusReturnInverse z m) := by
  rcases hN01 with ⟨_, _, _, hcontrol, _, _, hflow, _, hInv, _⟩
  have hI := hInv z hz hsector m
  have hpos (θ : ℝ) : 0 < deriv (C.minusFlow z m (C.right m)) θ :=
    ((hflow z hz m θ).2.2.2 (C.right m) ⟨(hcontrol.1 m).2.1.le, le_rfl⟩).1
  intro θ
  exact (returnChart_hasDerivAt_inverse _ _ hpos
    (fun t => (hI t).2.1) (fun t => (hI t).1) θ).differentiableAt

theorem N01Properties.transportedLeftChart_differentiable {D : ReferenceData} {T : MaterialData}
    {base loss : ℕ} {ε : ℝ} (hN01 : N01Properties D T S C base loss ε)
    (hz : z ∈ stateNeighborhood S C base ε) (hsector : stateSector S z.1) :
    Differentiable ℝ
      (fun t => stateLeftChart S z.1 m (C.minusReturnInverse z m t) - C.travel m) := by
  have hinv := N01Properties.minusReturnInverse_differentiable S C z m hN01 hz hsector
  rcases hN01 with ⟨_, _, _, _, _, _, _, hleft, _⟩
  have hleftDiff : Differentiable ℝ (stateLeftChart S z.1 m) := by
    intro θ
    have hpos : 0 < deriv (stateLeftChart S z.1 m) θ :=
      lt_of_lt_of_le (by norm_num : (0 : ℝ) < 1 / 2) (hleft z hz hsector m θ).1
    exact differentiableAt_of_deriv_ne_zero hpos.ne'
  simpa only [Function.comp_def] using (hleftDiff.comp hinv).sub_const (C.travel m)

theorem N01Properties.rightChart_differentiable {D : ReferenceData} {T : MaterialData}
    {base loss : ℕ} {ε : ℝ} (hN01 : N01Properties D T S C base loss ε)
    (hz : z ∈ stateNeighborhood S C base ε) (hsector : stateSector S z.1) :
    Differentiable ℝ (rightChartCandidate S C z m) := fun θ =>
  differentiableAt_of_deriv_ne_zero
    (N01Properties.rightChart_deriv_pos S C z m hN01 hz hsector θ).ne'

theorem N01Properties.rightChartInverse_differentiable {D : ReferenceData} {T : MaterialData}
    {base loss : ℕ} {ε : ℝ} (hN01 : N01Properties D T S C base loss ε)
    (hz : z ∈ stateNeighborhood S C base ε) (hsector : stateSector S z.1) :
    Differentiable ℝ (C.rightChartInverse z m) := by
  have hpos := N01Properties.rightChart_deriv_pos S C z m hN01 hz hsector
  rcases hN01 with ⟨_, _, _, _, _, _, _, _, hInv, _⟩
  have hI := hInv z hz hsector m
  intro θ
  exact (returnChart_hasDerivAt_inverse _ _ hpos
    (fun t => (hI t).2.2.2) (fun t => (hI t).2.2.1) θ).differentiableAt

theorem N01Properties.returnResidualField_differentiable {D : ReferenceData} {T : MaterialData}
    {base loss : ℕ} {ε : ℝ} (hN01 : N01Properties D T S C base loss ε)
    (hz : z ∈ stateNeighborhood S C base ε) (hsector : stateSector S z.1) :
    Differentiable ℝ (returnResidualField S C z m) := by
  let F : ℝ → ℝ := fun t =>
    stateLeftChart S z.1 m (C.minusReturnInverse z m t) - C.travel m
  have hF : Differentiable ℝ F :=
    N01Properties.transportedLeftChart_differentiable S C z m hN01 hz hsector
  have hEven : Differentiable ℝ (evenPart F) := by
    simpa only [evenPart, Function.comp_def, Pi.add_apply] using
      (hF.add (hF.comp differentiable_neg)).div_const (2 : ℝ)
  have hInv := N01Properties.rightChartInverse_differentiable S C z m hN01 hz hsector
  simpa only [returnResidualField, F, Function.comp_def] using hEven.comp hInv

end ContinuousFlexibility.Statements
