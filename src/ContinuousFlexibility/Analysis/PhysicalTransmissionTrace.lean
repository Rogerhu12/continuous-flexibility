module

public import ContinuousFlexibility.Analysis.MaterialCylinderPointwise

/-!
# Boundary jets of an equation on an open strip

Equality on an open set is inherited by every mixed coordinate derivative.
For globally smooth functions these derivatives are continuous, so the
equality extends to the closure. A single closed-strip formulation handles
both sides of a physical transmission interface.
-/

@[expose] public section

namespace ContinuousFlexibility.Statements

open Set Filter
open scoped ContDiff Topology

/-- The actual mixed slice derivatives depend only on the germ of the
function. No differentiability assumption is needed for this congruence. -/
theorem mixedDerivative_eqOn_of_isOpen {U : Set PolarPoint}
    {g h : PolarPoint → ℝ} (hU : IsOpen U) (he : EqOn g h U) (i j : ℕ) :
    EqOn (mixedDerivative i j g) (mixedDerivative i j h) U := by
  have hAngular : EqOn
      (fun p : PolarPoint => iteratedDeriv j (fun θ => g (p.1, θ)) p.2)
      (fun p : PolarPoint => iteratedDeriv j (fun θ => h (p.1, θ)) p.2) U := by
    intro p hp
    have hSlice : Continuous (fun θ : ℝ => (p.1, θ)) :=
      continuous_const.prodMk continuous_id
    have hNear : (fun θ => g (p.1, θ)) =ᶠ[𝓝 p.2] (fun θ => h (p.1, θ)) := by
      filter_upwards [hSlice.continuousAt.preimage_mem_nhds (hU.mem_nhds hp)] with θ hθ
      exact he hθ
    exact (hNear.iteratedDeriv j).eq_of_nhds
  intro p hp
  have hSlice : Continuous (fun r : ℝ => (r, p.2)) :=
    continuous_id.prodMk continuous_const
  have hNear :
      (fun r => iteratedDeriv j (fun θ => g (r, θ)) p.2) =ᶠ[𝓝 p.1]
      (fun r => iteratedDeriv j (fun θ => h (r, θ)) p.2) := by
    filter_upwards [hSlice.continuousAt.preimage_mem_nhds (hU.mem_nhds hp)] with r hr
    exact hAngular hr
  exact (hNear.iteratedDeriv i).eq_of_nhds

/-- A smooth equation valid on an open set holds to every mixed order on
its closure. In particular it supplies the equation jets at an interface. -/
theorem mixedDerivative_eqOn_closure {U : Set PolarPoint}
    {g h : PolarPoint → ℝ} (hU : IsOpen U)
    (hg : ContDiff ℝ ∞ g) (hh : ContDiff ℝ ∞ h)
    (he : EqOn g h U) (i j : ℕ) :
    EqOn (mixedDerivative i j g) (mixedDerivative i j h) (closure U) :=
  (mixedDerivative_eqOn_of_isOpen hU he i j).closure
    (contDiff_mixedDerivative hg i j).continuous
    (contDiff_mixedDerivative hh i j).continuous

/-- The same boundary-jet statement applies at either endpoint of a
nonempty radial strip; no separate left and right argument is required. -/
theorem mixedDerivative_eqOn_closed_strip {a b : ℝ} {g h : PolarPoint → ℝ}
    (hab : a < b) (hg : ContDiff ℝ ∞ g) (hh : ContDiff ℝ ∞ h)
    (he : EqOn g h (Ioo a b ×ˢ (univ : Set ℝ))) (i j : ℕ) :
    EqOn (mixedDerivative i j g) (mixedDerivative i j h)
      (Icc a b ×ˢ (univ : Set ℝ)) := by
  have hClosure : closure (Ioo a b ×ˢ (univ : Set ℝ)) =
      Icc a b ×ˢ (univ : Set ℝ) := by
    rw [closure_prod_eq, closure_Ioo hab.ne, closure_univ]
  rw [← hClosure]
  exact mixedDerivative_eqOn_closure (isOpen_Ioo.prod isOpen_univ) hg hh he i j

end ContinuousFlexibility.Statements
