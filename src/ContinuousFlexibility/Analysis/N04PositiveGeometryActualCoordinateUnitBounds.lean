import ContinuousFlexibility.Analysis.N04PositiveGeometryActualCoordinateDirections
import ContinuousFlexibility.Analysis.N04PositiveGeometryCoordinateNormalization

/-!
# Unit normalizations of the actual four coordinate components

These identities apply to arbitrary genuine towers of the displayed
fields. Thus restriction and the eventual whole-atlas identification do
not introduce an independent jet or an additional regularity premise.
-/

noncomputable section

namespace ContinuousFlexibility.Analysis

open Set ContinuousFlexibility.Statements CanonicalGeometry
open scoped ContDiff

theorem n04PositiveGeometry_controlledForwardCoordinate_word_bound
    {W : N04RealizationStart} {X : N04RealizationChoice W} {order : ℕ}
    (F : N04PositiveGeometryControlledFamily W X order)
    (Y : N04PositiveComponent W.D.a W.D.b (deriv W.D.w) → ℝ → ℝ)
    {base : ℕ} {ε : ℝ} (angle : Bool)
    (i : N04PositiveComponent W.D.a W.D.b (deriv W.D.w))
    (J : SmoothDirections (sectorNeighborhood W.S base ε ε ×ˢ univ)
      (fun z : (StateDirections W.S × ℝ) × PolarPoint =>
        n04PositiveGeometry_controlledReferenceComponent F Y false angle i
          (liftSectorParameter W.S W.C z.1) z.2))
    (Q : SmoothDirections (sectorNeighborhood W.S base ε ε ×ˢ unitStrip)
      (fun z : (StateDirections W.S × ℝ) × PolarPoint =>
        n04PositiveGeometry_controlledCoordinate F Y false angle i
          (liftSectorParameter W.S W.C z.1) z.2))
    {C : ℝ} (hC : 1 ≤ C) (hspan : |n04PositiveRight i - n04PositiveLeft i| ≤ C)
    (p q : Seminorm ℝ (StateDirections W.S × ℝ)) {R M : ℝ} (hR : 0 ≤ R)
    (n : ℕ) (w : StateAngleWord n) (hw : 0 < w.stateArity)
    (x : StateDirections W.S × ℝ) (hx : x ∈ sectorNeighborhood W.S base ε ε)
    (y : PolarPoint) (hy : y ∈ unitStrip)
    (hbound : ∀ u : Fin n → (StateDirections W.S × ℝ) × PolarPoint,
      (∀ j, p (u j).1 ≤ 1) → (∀ j, q (u j).1 ≤ R) → (∀ j, ‖(u j).2‖ ≤ 1) →
      (∀ j, w.isState j = false → (u j).1 = 0) →
      (∀ j, w.isState j = true → (u j).2 = 0) →
      ‖J.D n (x, (n04PositiveLeft i + (n04PositiveRight i - n04PositiveLeft i) * y.1, y.2)) u‖ ≤ M)
    (v : Fin n → (StateDirections W.S × ℝ) × PolarPoint)
    (hvL : ∀ j, p (v j).1 ≤ 1) (hvH : ∀ j, q (v j).1 ≤ R)
    (hvS : ∀ j, ‖(v j).2‖ ≤ 1)
    (hv0 : ∀ j, w.isState j = false → (v j).1 = 0)
    (hv1 : ∀ j, w.isState j = true → (v j).2 = 0) :
    |Q.D n (x, y) v| ≤ C ^ n * M := by
  have hU := sectorNeighborhood_isOpen W.S base ε ε
  cases angle with
  | false =>
      exact (Real.norm_eq_abs _).symm.trans_le
        (n04PositiveGeometry_unitPullback_word_bound hU J (n04PositiveLeft i)
          (n04PositiveRight i) hC hspan Q p q hR n w x hx y hy
          hbound v hvL hvH hvS hv0 hv1)
  | true =>
      let JP := n04PositiveGeometry_unitPullbackDirections J hU
        (n04PositiveLeft i) (n04PositiveRight i)
      have he := n04PositiveGeometry_unitAngleDefect_word_bound hU JP Q w hw hx hy v hv1
      exact (congrArg abs he).trans_le ((Real.norm_eq_abs _).symm.trans_le
        (n04PositiveGeometry_unitPullback_word_bound hU J (n04PositiveLeft i)
          (n04PositiveRight i) hC hspan JP p q hR n w x hx y hy
          hbound v hvL hvH hvS hv0 hv1))

theorem n04PositiveGeometry_controlledInverseCoordinate_parameter_identity
    {W : N04RealizationStart} {X : N04RealizationChoice W} {order : ℕ}
    (F : N04PositiveGeometryControlledFamily W X order)
    (Y : N04PositiveComponent W.D.a W.D.b (deriv W.D.w) → ℝ → ℝ)
    {base : ℕ} {ε : ℝ} (angle : Bool)
    (i : N04PositiveComponent W.D.a W.D.b (deriv W.D.w))
    (JF : SmoothDirections (sectorNeighborhood W.S base ε ε ×ˢ univ)
      (fun z : (StateDirections W.S × ℝ) × PolarPoint =>
        n04PositiveGeometry_controlledReferenceComponent F Y true angle i
          (liftSectorParameter W.S W.C z.1) z.2))
    (a b : ℕ) (q : PolarPoint)
    (J : SmoothDirections (sectorNeighborhood W.S base ε ε)
      (fun x => mixedDerivative a b (fun p => n04PositiveGeometry_controlledReferenceComponent
        F Y true angle i (liftSectorParameter W.S W.C x) p) q))
    (Q : SmoothDirections (sectorNeighborhood W.S base ε ε)
      (fun x => mixedDerivative a b (fun p => n04PositiveGeometry_controlledCoordinate
        F Y true angle i (liftSectorParameter W.S W.C x) p) q))
    {k : ℕ} (hk : 0 < k) {x : StateDirections W.S × ℝ}
    (hx : x ∈ sectorNeighborhood W.S base ε ε) (v : Fin k → (StateDirections W.S × ℝ)) :
    Q.D k x v = (if angle then 1 else (n04PositiveRight i - n04PositiveLeft i)⁻¹) * J.D k x v := by
  let f := fun x p => n04PositiveGeometry_controlledReferenceComponent F Y true angle i
    (liftSectorParameter W.S W.C x) p
  let g : PolarPoint → ℝ := fun p => if angle then p.2 else n04PositiveLeft i
  let c : ℝ := if angle then 1 else (n04PositiveRight i - n04PositiveLeft i)⁻¹
  have hg : ContDiffOn ℝ ∞ g univ := by
    cases angle
    · exact contDiffOn_const
    · exact contDiff_snd.contDiffOn
  let Q' : SmoothDirections (sectorNeighborhood W.S base ε ε)
      (fun x => mixedDerivative a b (fun p => c * (f x p - g p)) q) :=
    Q.congrOn (fun x _ => congrArg (fun h : PolarPoint → ℝ => mixedDerivative a b h q) (by
      funext p
      cases angle <;>
        simp only [n04PositiveGeometry_controlledCoordinate, f, g, c,
          Bool.false_eq_true, ite_false, ite_true, one_mul, div_eq_mul_inv] <;> ring))
  exact n04PositiveGeometry_positiveMixed_fixedAffine isOpen_univ
    (fun x hx => JF.spatial_value_contDiffOn isOpen_univ x hx) hg c a b (mem_univ q)
      J Q' hk hx v

end ContinuousFlexibility.Analysis
