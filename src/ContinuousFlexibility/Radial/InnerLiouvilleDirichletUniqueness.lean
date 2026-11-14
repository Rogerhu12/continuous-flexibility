module

public import ContinuousFlexibility.Radial.InnerLiouvilleDirichletSolution
public import ContinuousFlexibility.Radial.InnerRadialLocalDuality

/-!
# Uniqueness for the actual transported local Dirichlet problem

The existence hypothesis in local duality is supplied by the same
localized R09 inverse and the proved Liouville weak-form transport.
No physical inverse, uniqueness or reverse-domain identification is
assumed.
-/

@[expose] public section

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

include M U hU hv hDw hcoeff in
theorem innerLiouvilleLocalizedDirichlet_kernel
    (q : InnerRadialH1Pair D) (v : RadialModeL2 D) (scalar : ℝ)
    (hq : q ∈ innerRadialH1Zero D (R B.l) (R B.h))
    (hpot : InnerRadialPotentialClass D j (R B.l) (R B.h) q.1 v)
    (hrow : if B.bordered then
      ⟪innerLiouvilleColumnLift D hB.1.le hlam hR hs hp hcore hw B.border, q.1⟫_ℝ = 0
      else scalar = 0)
    (hweak : ∀ T ∈ innerRadialH1Zero D (R B.l) (R B.h),
      innerRadialWeakResidual D q v 0
        (innerLiouvilleColumnLift D hB.1.le hlam hR hs hp hcore hw B.border) scalar T = 0) :
    q = 0 ∧ v = 0 ∧ scalar = 0 := by
  apply innerRadialLocalKernel_unique_of_solutions D j (R B.l) (R B.h) B.bordered
    (innerLiouvilleColumnLift D hB.1.le hlam hR hs hp hcore hw B.border) ?_
    q v scalar hq hpot hrow hweak
  intro F rowF hF
  obtain ⟨grad, potential, hdom, hpot', hrow', hweak'⟩ :=
    innerLiouvilleLocalizedDirichlet_solution D hB M hlam hR hs hp hcore hw U hU hv
      hDw j hcoeff (F, rowF) hF
  let P := innerLiouvillePhysicalDirichlet D hB.1.le hlam hR hs hp hcore hw U hU hv
    M.dirichlet (F, rowF)
  exact ⟨(P.1, grad), potential, P.2, hdom, hpot', hrow', hweak'⟩

end ContinuousFlexibility.Radial
