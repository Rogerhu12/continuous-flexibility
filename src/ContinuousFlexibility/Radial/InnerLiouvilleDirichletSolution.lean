import ContinuousFlexibility.Radial.InnerLiouvilleFormTransport
import ContinuousFlexibility.Radial.InnerLiouvilleModelRealization

/-!
# The same localized Dirichlet inverse solves the physical weak problem

This theorem uses the original R09 localized inverse, transports its
actual L² source, and returns the physical domain, signed potential,
scalar row and every closed-domain weak test equation. The field and
scalar are exactly the previously defined physical continuous map.
-/

noncomputable section

namespace ContinuousFlexibility.Radial

open Real Set Filter MeasureTheory
open ContinuousFlexibility.Statements
open scoped Topology ContDiff InnerProductSpace

variable (D : ReferenceData) {B : BufferData} (hB : BufferHypotheses B)
  {C K : ℝ} (M : InnerBufferLocalizedData B C K)
  {R s : ℝ → ℝ} {lam : ℝ} (hlam : 0 < lam)
  (hR : ContDiff ℝ ∞ R) (hs : ContDiff ℝ ∞ s)
  (hp : ∀ x ∈ Icc B.l B.h, 0 < R x ∧ 0 < deriv R x ∧ 0 < s x)
  (hcore : Ioo (R B.l) (R B.h) ⊆ radialCore D)
  (hw : ∀ x ∈ Icc B.l B.h, D.w (R x) = lam * s x ^ 2 * deriv R x)
  (U : ℝ) (hU : 0 ≤ U)
  (hv : ∀ x ∈ Icc B.l B.h, |deriv R x / R x| ≤ U)
  (hDw : ContDiff ℝ ∞ D.w) (j : ℝ)
  (hcoeff : ∀ x ∈ Ioo B.l B.h,
    B.potential x = liouvilleV0 s x - j ^ 2 * liouvilleRho R s x)

include hDw hcoeff in
theorem innerLiouvilleLocalizedDirichlet_solution (F : RadialModeL2 D × ℝ)
    (hscalar : B.bordered = false → F.2 = 0) :
    let P := innerLiouvillePhysicalDirichlet D hB.1.le hlam hR hs hp hcore hw
      U hU hv M.dirichlet F
    ∃ grad potential : RadialModeL2 D,
      (P.1, grad) ∈ innerRadialH1Zero D (R B.l) (R B.h) ∧
      InnerRadialPotentialClass D j (R B.l) (R B.h) P.1 potential ∧
      (if B.bordered then
        ⟪innerLiouvilleColumnLift D hB.1.le hlam hR hs hp hcore hw B.border, P.1⟫_ℝ = F.2
       else P.2 = 0 ∧ F.2 = 0) ∧
      ∀ T ∈ innerRadialH1Zero D (R B.l) (R B.h),
        innerRadialWeakResidual D (P.1, grad) potential F.1
          (innerLiouvilleColumnLift D hB.1.le hlam hR hs hp hcore hw B.border) P.2 T = 0 := by
  have hV : Continuous B.potential := by
    rcases hB with ⟨_, _, _, _, hV, _⟩
    exact hV.continuous
  have hborder : (B.border : ℝ → ℝ) =ᵐ[volume.restrict ((Ioo B.l B.h)ᶜ)] (fun _ => 0) := by
    rcases hB with ⟨_, _, _, _, _, _, _, _, _, _, _, hb, _⟩
    exact hb
  have hpos := innerLiouville_radial_weight_pos_closed D hB.1.le hlam hR hp hw
  obtain ⟨d, q, hclosure, hform, hdomain, hrow⟩ :=
    innerLiouvilleLocalizedDirichlet_realization D hB M hlam hR hs hp hcore hw U hU hv
      hDw.continuous F hscalar
  rw [innerLiouvillePhysicalDirichlet_apply] at hdomain hrow
  dsimp only
  rw [innerLiouvillePhysicalDirichlet_apply]
  refine ⟨innerLiouvilleGradientLift D hB.1.le hlam hR hs hp hcore hw
      ((M.dirichlet
        (innerLiouvilleSource D hB.1.le hlam hR hs hp hcore hw U hU hv F.1, F.2)).1, d),
    innerRadialPotentialMultiplier D hDw j hpos
      (innerLiouvilleFieldLift D hB.1.le hlam hR hs hp hcore hw U hU hv
        (M.dirichlet
          (innerLiouvilleSource D hB.1.le hlam hR hs hp hcore hw U hU hv F.1, F.2)).1),
    hdomain, innerRadialPotentialMultiplier_class D hDw j hpos _, hrow, ?_⟩
  intro T hT
  exact innerLiouvilleWeakResidual_on_zeroDomain D hB.1 hlam hR hs hp hcore hw U hU hv
    hDw j hpos hV hcoeff F.1 _ hborder hclosure hform hT

end ContinuousFlexibility.Radial
