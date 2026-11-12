import ContinuousFlexibility.Analysis.N04bLocalIntertwining
import ContinuousFlexibility.Blueprint.Statements
import Mathlib.Tactic.Linarith

/-!
# Actual physical operator action from the frozen canonical parts

Part A supplies the smooth chart, inverse chart and positive height.
Part B supplies the actual operator action on global smooth tests.
Localizing the inverse pullback gives the physical action on every global
smooth function without regularity assumptions on the stored coefficients.

One Bool case split handles both canonical signs. The potential acquires
the same sign when the canonical operator identity is solved for the
physical divergence operator.
-/

noncomputable section

namespace ContinuousFlexibility.Analysis

open ContinuousFlexibility.Statements ContinuousFlexibility.Blueprint
open Set
open scoped ContDiff

set_option backward.isDefEq.respectTransparency false

/-- The frozen Part A/B conditions determine the actual physical operator
action. No differentiability of either stored coefficient field is needed. -/
theorem n04b_physicalOperator_of_parts
    {D : ReferenceData} {S : PhysicalSpacesData} {C : NonlinearGeometryData S}
    {L : ReturnCorrectionData S} {K : CanonicalData S} {base : ℕ} {ε : ℝ}
    (hA : N04PartA D S C K base ε) (hB : N04PartB S C L K base ε)
    {z : AnnularState S × ℝ} (hz : z ∈ stateNeighborhood S C base ε)
    (hsector : stateSector S z.1) (m : ℕ)
    {u : PolarPoint → ℝ} (hu : ContDiff ℝ ∞ u) {x : PolarPoint}
    (hx : x ∈ physicalPieceOpen S K z m) :
    divergenceOperator (L.coefficients z) u x =
      |planeJacobian (K.chart z m) x| / K.height z m x *
        (divergenceOperator (K.coefficients z m)
          (canonicalHeight S K z m u) (K.chart z m x) +
        ((if K.positive m then -1 else (1 : ℝ)) *
          K.potential z m (K.chart z m x)) * (u x / K.height z m x)) := by
  have hcharts := hA.charts z hz hsector m
  have hU : IsOpen (physicalPieceOpen S K z m) :=
    (hA.domains z hz hsector m).1
  have hΩ : IsOpen (canonicalOpen S K m) :=
    isOpen_Ioo.prod isOpen_univ
  have hact : ∀ W : PolarPoint → ℝ, ContDiff ℝ ∞ W →
      K.height z m x *
          divergenceOperator (L.coefficients z)
            (fun y => K.height z m y * W (K.chart z m y)) x /
          |planeJacobian (K.chart z m) x| =
        divergenceOperator (K.coefficients z m) W (K.chart z m x) +
          ((if K.positive m then -1 else (1 : ℝ)) *
            K.potential z m (K.chart z m x)) * W (K.chart z m x) := by
    intro W hW
    have he := hB.2.2.1 z hz hsector m W hW
      (K.chart z m x) (hcharts.1 hx)
    dsimp only [canonicalOperator, canonicalSource] at he
    rw [hcharts.2.2.1 x hx] at he
    cases hsign : K.positive m <;> simp [hsign] at he ⊢ <;> linarith
  have hheight : canonicalHeight S K z m u =
      (fun p => u (K.inverseChart z m p) /
        K.height z m (K.inverseChart z m p)) := by
    funext p
    rfl
  rw [hheight]
  exact n04b_physicalOperator_of_intertwining
      (A := L.coefficients z) (B := K.coefficients z m)
      (F := K.chart z m) (G := K.inverseChart z m)
      (h := K.height z m) (u := u)
      (V := (if K.positive m then -1 else (1 : ℝ)) *
        K.potential z m (K.chart z m x))
      hU hΩ hx hcharts.1 hcharts.2.1 hcharts.2.2.1
      (hcharts.2.2.2.2.1.continuousOn.continuousAt (hU.mem_nhds hx))
      hcharts.2.2.2.2.2.1 hcharts.2.2.2.2.2.2.1
      (fun y hy => (hcharts.2.2.2.2.2.2.2 y hy).1) hu
      (hcharts.2.2.2.2.2.2.2 x hx).2.1 hact

end ContinuousFlexibility.Analysis
