module

public import ContinuousFlexibility.Analysis.N01FlowAngularSmoothness

/-!
# Smoothness of the specified N01 return charts and residual

The actual closed-interval angular flow is smooth.  Its strictly positive
derivative and the specified inverse identities imply smoothness of the
actual inverse by induction on derivative order.  This propagates through
the odd right chart, its inverse, and the even return residual.
-/

@[expose] public section

noncomputable section

namespace ContinuousFlexibility.Statements

open Set Filter
open scoped ContDiff Topology

set_option backward.isDefEq.respectTransparency false

/-- Smoothness of a specified one-dimensional inverse follows from the
actual two inverse identities and a positive derivative. -/
theorem returnChart_inverse_contDiff (f g : ℝ → ℝ)
    (hf : ContDiff ℝ ∞ f) (hfpos : ∀ θ, 0 < deriv f θ)
    (hleft : ∀ θ, g (f θ) = θ) (hright : ∀ θ, f (g θ) = θ) :
    ContDiff ℝ ∞ g := by
  have hg (θ : ℝ) := returnChart_hasDerivAt_inverse f g hfpos hleft hright θ
  have hgdiff : Differentiable ℝ g := fun θ => (hg θ).differentiableAt
  have hdf : ContDiff ℝ ∞ (deriv f) := (contDiff_infty_iff_deriv.mp hf).2
  apply contDiff_infty.mpr
  intro n
  induction n with
  | zero => exact contDiff_zero.mpr hgdiff.continuous
  | succ n ih =>
    have hdfn : ContDiff ℝ (n : ℕ∞ω) (deriv f) := contDiff_infty.mp hdf n
    have hdinv := (hdfn.comp ih).inv (fun θ => (hfpos (g θ)).ne')
    have hdg : ContDiff ℝ (n : ℕ∞ω) (deriv g) := by
      apply contDiff_iff_contDiffAt.mpr
      intro θ
      exact hdinv.contDiffAt.congr_of_eventuallyEq
        (Eventually.of_forall fun t => by
          simpa only [Pi.inv_apply, Function.comp_apply] using (hg t).deriv)
    have h : ContDiff ℝ ((n : ℕ∞ω) + 1) g :=
      contDiff_succ_iff_deriv.mpr ⟨hgdiff, by simp, hdg⟩
    simpa only [Nat.cast_add, Nat.cast_one] using h

section ActualCharts

variable {D : ReferenceData} {T : MaterialData} {S : PhysicalSpacesData}
  {C : NonlinearGeometryData S} {base loss : ℕ} {ε : ℝ}
  (hN01 : N01Properties D T S C base loss ε)
  (hS : IsPhysicalSpaces D T S) (hT : IsMaterialData D T)
  {z : AnnularState S × ℝ} (hz : z ∈ stateNeighborhood S C base ε)
  (hsector : stateSector S z.1) (m : ℕ)

include hN01 hS hT hz hsector

theorem N01Properties.minusReturnInverse_contDiff :
    ContDiff ℝ ∞ (C.minusReturnInverse z m) := by
  have hcontrol : controlGeometryConditions D S C := hN01.2.2.2.1
  have hr : C.right m ∈ Icc (C.left m) (C.right m) :=
    ⟨(hcontrol.1 m).2.1.le, le_rfl⟩
  have hf := N01Properties.minusFlow_angular_contDiff hN01 hS hT hz hsector m hr
  rcases hN01 with ⟨_, _, _, _, _, _, hflow, _, hInv, _⟩
  exact returnChart_inverse_contDiff (C.minusFlow z m (C.right m))
    (C.minusReturnInverse z m) hf
    (fun θ => ((hflow z hz m θ).2.2.2 (C.right m) hr).1)
    (fun θ => (hInv z hz hsector m θ).2.1)
    (fun θ => (hInv z hz hsector m θ).1)

theorem N01Properties.transportedLeftChart_contDiff :
    ContDiff ℝ ∞
      (fun θ => stateLeftChart S z.1 m (C.minusReturnInverse z m θ) - C.travel m) := by
  have hl : ContDiff ℝ ∞ (stateLeftChart S z.1 m) :=
    stateLeftChart_contDiff S z m (hS.2.1 (3 / 4 : ℝ))
  have hi := N01Properties.minusReturnInverse_contDiff hN01 hS hT hz hsector m
  apply contDiff_iff_contDiffAt.mpr
  intro θ
  exact ((hl.comp hi).sub
    (contDiff_const : ContDiff ℝ ∞ (fun _ : ℝ => C.travel m))).contDiffAt.congr_of_eventuallyEq
    (Eventually.of_forall fun t => by simp only [Function.comp_def, Pi.sub_apply])

theorem N01Properties.rightChartCandidate_contDiff :
    ContDiff ℝ ∞ (rightChartCandidate S C z m) := by
  let F : ℝ → ℝ := fun θ =>
    stateLeftChart S z.1 m (C.minusReturnInverse z m θ) - C.travel m
  have hF : ContDiff ℝ ∞ F :=
    N01Properties.transportedLeftChart_contDiff hN01 hS hT hz hsector m
  apply contDiff_iff_contDiffAt.mpr
  intro θ
  exact ((hF.sub (hF.comp contDiff_neg)).div_const 2).contDiffAt.congr_of_eventuallyEq
    (Eventually.of_forall fun t => by
      simp only [rightChartCandidate, oddPart, F, Function.comp_def, Pi.sub_apply])

theorem N01Properties.rightChartInverse_contDiff :
    ContDiff ℝ ∞ (C.rightChartInverse z m) := by
  have hf := N01Properties.rightChartCandidate_contDiff hN01 hS hT hz hsector m
  have hpos := N01Properties.rightChart_deriv_pos S C z m hN01 hz hsector
  rcases hN01 with ⟨_, _, _, _, _, _, _, _, hInv, _⟩
  exact returnChart_inverse_contDiff (rightChartCandidate S C z m)
    (C.rightChartInverse z m) hf hpos
    (fun θ => (hInv z hz hsector m θ).2.2.2)
    (fun θ => (hInv z hz hsector m θ).2.2.1)

/-- The inverse coordinate appearing in the frozen correction factor is
the composition of the two actual N01 inverses. -/
theorem N01Properties.returnTransportInverse_contDiff :
    ContDiff ℝ ∞
      (fun θ => C.minusReturnInverse z m (C.rightChartInverse z m θ)) := by
  have hf := N01Properties.minusReturnInverse_contDiff hN01 hS hT hz hsector m
  have hg := N01Properties.rightChartInverse_contDiff hN01 hS hT hz hsector m
  apply contDiff_iff_contDiffAt.mpr
  intro θ
  exact (hf.comp hg).contDiffAt.congr_of_eventuallyEq
    (Eventually.of_forall fun t => by simp only [Function.comp_def])

theorem N01Properties.returnResidualField_contDiff :
    ContDiff ℝ ∞ (returnResidualField S C z m) := by
  let F : ℝ → ℝ := fun θ =>
    stateLeftChart S z.1 m (C.minusReturnInverse z m θ) - C.travel m
  have hF : ContDiff ℝ ∞ F :=
    N01Properties.transportedLeftChart_contDiff hN01 hS hT hz hsector m
  have hg := N01Properties.rightChartInverse_contDiff hN01 hS hT hz hsector m
  have hE : ContDiff ℝ ∞ (evenPart F) := by
    apply contDiff_iff_contDiffAt.mpr
    intro θ
    exact ((hF.add (hF.comp contDiff_neg)).div_const 2).contDiffAt.congr_of_eventuallyEq
      (Eventually.of_forall fun t => by simp only [evenPart, Function.comp_def, Pi.add_apply])
  apply contDiff_iff_contDiffAt.mpr
  intro θ
  exact (hE.comp hg).contDiffAt.congr_of_eventuallyEq
    (Eventually.of_forall fun t => by simp only [returnResidualField, F, Function.comp_def])

end ActualCharts

end ContinuousFlexibility.Statements
