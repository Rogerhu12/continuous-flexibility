import ContinuousFlexibility.Analysis.N04PositiveGeometryControlledHeight
import ContinuousFlexibility.Analysis.N04PositiveGeometryReferencePullbackCosts
import ContinuousFlexibility.Analysis.N04RealizationPositiveGaugeHeightBounds

/-!
# The chosen positive height at its actual inverse point

The inverse identity cancels the relative transports before estimating
the pulled height. The fixed reference height and inverse contribute
their already retained material costs. The remaining parameter jets
are those of the same stored Taylor height and its reciprocal.
-/

noncomputable section

namespace ContinuousFlexibility.Analysis

open Set ContinuousFlexibility.Statements
open scoped ContDiff BigOperators

variable {V : Type*} [TopologicalSpace V] [AddCommGroup V] [Module ℝ V]
  [IsTopologicalAddGroup V] [ContinuousSMul ℝ V]

private theorem referenceCost_raise {A B E : ℝ} (hAB : A ≤ B)
    (hB : 0 ≤ B) (hE : 1 ≤ E) : A * E ^ A ≤ B * E ^ B :=
  mul_le_mul hAB (Real.rpow_le_rpow_of_exponent_le hE hAB)
    (Real.rpow_nonneg (zero_le_one.trans hE) _) hB

/-- The literal fixed-gauge pulled height and its reciprocal have the
same finite normalized exponent as the original source-height prefix. -/
theorem n04PositiveGeometry_controlledPulledHeight_shifted_bound
    {W : N04RealizationStart} {X : N04RealizationChoice W} {n : ℕ}
    (G : N04PositiveGeometryControlledFamily W X n)
    (Y H₀ : N04PositiveComponent W.D.a W.D.b (deriv W.D.w) → ℝ → ℝ)
    (href : N04PositiveReferenceFamily (W.A X.e₀) X.src 4 Y H₀)
    (hmaterial : N04PositiveReferenceMaterialBounds W.T X.cell Y H₀)
    (k a b : ℕ) (RH A : ℝ) :
    ∃ B : ℝ, 1 ≤ B ∧
    ∀ (U : Set V), IsOpen U → ∀ state : V → AnnularState W.S × ℝ,
    (∀ x ∈ U, state x ∈ stateNeighborhood W.S W.C G.base G.ε) →
    (∀ x ∈ U, stateSector W.S (state x).1) →
    ∀ i : N04PositiveComponent W.D.a W.D.b (deriv W.D.w),
    ∀ JH : ∀ side, ∀ j : ℕ, j ≤ n → ∀ u θ,
      SmoothDirections U (fun x => iteratedDeriv u
        (radialBoundaryJet (n04PositiveSourceHeight (X.src i side)
          (W.A X.e₀) (state x)) (n04PositiveEndpoint i side) j) θ),
    ∀ x ∈ U, ∀ (P : V → Prop) (v : Fin k → V), (∀ t, P (v t)) →
    ∀ H R : ℝ, 0 ≤ H → H ≤ RH → 1 ≤ R → ∀ budget shift : ℕ,
    (∀ side, ∀ j : ℕ, ∀ hj : j ≤ n, ∀ e : ℕ, e ≤ k →
      ∀ u : ℕ, u ≤ a + b → ∀ θ, ∀ z : Fin e → V, (∀ t, P (z t)) →
      ‖(JH side j hj u θ).D e x z‖ ≤
        A * W.U.E0 (W.U.sample (X.cell i)) ^ A * parameterHeightWeight H e *
          R ^ (((u + shift * e : ℕ) : ℝ) / ((budget : ℝ) + 1))) →
    ∀ inv : Bool, ∀ q ∈ CanonicalGeometry.unitStrip,
    ∀ J : SmoothDirections U (fun y => mixedDerivative a b
      (fun p => if inv then
        (wholePositiveReferenceGaugeHeight (fun z => H₀ i z.1)
          (G.toN04PositiveGeometryControlData.σ (state y) i)
          (G.toN04PositiveGeometryControlData.Q (state y) i)
          (wholePositiveReferenceGaugeInverse
            (G.toN04PositiveGeometryControlData.τ (state y) i)
            (positiveReferenceCylinderInverse (Y i)) p))⁻¹
        else wholePositiveReferenceGaugeHeight (fun z => H₀ i z.1)
          (G.toN04PositiveGeometryControlData.σ (state y) i)
          (G.toN04PositiveGeometryControlData.Q (state y) i)
          (wholePositiveReferenceGaugeInverse
            (G.toN04PositiveGeometryControlData.τ (state y) i)
            (positiveReferenceCylinderInverse (Y i)) p)) q),
      ‖J.D k x v‖ ≤ B * W.U.E0 (W.U.sample (X.cell i)) ^ B *
        parameterHeightWeight H k *
          R ^ (((a + b + shift * k : ℕ) : ℝ) / ((budget : ℝ) + 1)) := by
  have hsmooth (i) := n04PositiveGeometry_reference_scalar_geometry (href i).1
  obtain ⟨Br, hBr, hr⟩ :=
    n04PositiveGeometry_reference_prefix_material_cost W.floor hmaterial (a + b)
  obtain ⟨Bc, hBc, hc⟩ := n04PositiveGeometry_reference_chain_mass_material_cost
    W.floor hmaterial (fun i => (hsmooth i).2.1) (a + b)
  obtain ⟨CQ, d, hCQ, hd, hbound⟩ :=
    n04Realization_positiveGaugeHeight_shifted_parameter_bound (X := V) n k a b RH
  let Ac := max 1 (max A (max Br Bc))
  have hAc : 0 ≤ Ac := zero_le_one.trans (le_max_left _ _)
  have hAAc : A ≤ Ac := (le_max_left _ _).trans (le_max_right _ _)
  have hBrAc : Br ≤ Ac :=
    (le_max_left _ _).trans ((le_max_right _ _).trans (le_max_right _ _))
  have hBcAc : Bc ≤ Ac :=
    (le_max_right _ _).trans ((le_max_right _ _).trans (le_max_right _ _))
  obtain ⟨B, hB, M, hM⟩ :=
    n04PositiveGeometry_controlled_height_material_envelope G Ac CQ d
  refine ⟨B, hB, ?_⟩
  intro U hU state hstate hsector i JH x hx P v hv H R hH hHR hR budget shift hraw inv q hq J
  let E := W.U.E0 (W.U.sample (X.cell i))
  have hE : 1 ≤ E := (W.floor _).trans (le_enlargedMaterialData_E0 W.T _)
  have hAto : A * E ^ A ≤ M i :=
    (referenceCost_raise hAAc hAc hE).trans (hM i).2.1
  have hRto : Br * E ^ Br ≤ M i :=
    (referenceCost_raise hBrAc hAc hE).trans (hM i).2.1
  have hCto : Bc * E ^ Bc ≤ M i :=
    (referenceCost_raise hBcAc hAc hE).trans (hM i).2.1
  have hroot (y : V) (hy : y ∈ U) (side : Bool) (θ : ℝ) :=
    (n04Coordinates_actualAtlas_positiveEndpoint_of_source
      W.hT W.hS W.through03 W.field X.e₀ (X.src i side)
      (stateNeighborhood_mono W.S W.C G.base_le G.radius_le (hstate y hy))
      (hsector y hy)).height_root θ
  have hinverse (side : Bool) (θ : ℝ) :
      (n04PositiveSourceHeight (X.src i side) (W.A X.e₀) (state x)
        (n04PositiveEndpoint i side, θ))⁻¹ ≤ M i :=
    ((G.endpoint_bounds (state x) (hstate x hx) (hsector x hx) i).height_inverse side θ).trans
      (hM i).2.2.1
  have hraw' (side : Bool) (j : ℕ) (hj : j ≤ n) (e : ℕ) (he : e ≤ k)
      (u : ℕ) (hu : u ≤ a + b) (θ : ℝ) (z : Fin e → V) (hz : ∀ t, P (z t)) :
      ‖(JH side j hj u θ).D e x z‖ ≤ M i * parameterHeightWeight H e *
        R ^ (((u + shift * e : ℕ) : ℝ) / ((budget : ℝ) + 1)) :=
    (hraw side j hj e he u hu θ z hz).trans
      (mul_le_mul_of_nonneg_right
        (mul_le_mul_of_nonneg_right hAto (parameterHeightWeight_nonneg hH e))
        (Real.rpow_nonneg (zero_le_one.trans hR) _))
  have hfixed (u w : ℕ) (huw : u + w ≤ a + b) :
      |mixedDerivative u w (fun p : PolarPoint => if inv then (H₀ i p.1)⁻¹ else H₀ i p.1)
        (Function.invFun (Y i) q.1, q.2)| ≤ M i := by
    have hu : u ≤ a + b := by omega
    cases inv <;>
      simp only [Bool.false_eq_true, ite_false, ite_true, mixedDerivative_radialFunction]
    · split_ifs with hw
      · exact ((hr i u hu _).2.2.1).trans hRto
      · simpa only [abs_zero] using (zero_le_one.trans (hM i).1)
    · split_ifs with hw
      · exact ((hr i u hu _).2.2.2).trans hRto
      · simpa only [abs_zero] using (zero_le_one.trans (hM i).1)
  have hchain : (∑ j : Fin (a + 1),
      |radialChainCoefficient (Function.invFun (Y i)) a j q.1|) ≤ M i :=
    (hc i a (Nat.le_add_right _ _) q.1).trans hCto
  have hsmall := n04PositiveGeometry_controlledHeight_log_smallness G i
  have hout := hbound U hU (n04PositiveLeft i) (n04PositiveRight i) (G.δ i)
    (G.width_pos i) (G.width_one i)
    (fun y side => n04PositiveSourceHeight (X.src i side) (W.A X.e₀) (state y))
    (fun y hy side θ => (hroot y hy side θ).1)
    (fun y hy side θ => (hroot y hy side θ).2) JH
    (Y i) (H₀ i) (hsmooth i).2.1 (hsmooth i).2.2.1 (hsmooth i).2.2.2
    (fun y => G.toN04PositiveGeometryControlData.τ (state y) i)
    (fun y => G.toN04PositiveGeometryControlData.σ (state y) i)
    (fun y hy => (G.matching (state y) (hstate y hy) (hsector y hy) i).geometry.left_inverse)
    x hx P v hv H (M i) R hH hHR (hM i).1 hR (hM i).2.2.2.1 budget shift
    hinverse hraw' (G.Clog * G.M i ^ (2 * n + 1)) hsmall.1
    (G.log_bound (state x) (hstate x hx) (hsector x hx) i) hsmall.2 inv q hq hfixed hchain J
  exact hout.trans (mul_le_mul_of_nonneg_right
    (mul_le_mul_of_nonneg_right (hM i).2.2.2.2 (parameterHeightWeight_nonneg hH k))
    (Real.rpow_nonneg (zero_le_one.trans hR) _))

end ContinuousFlexibility.Analysis
