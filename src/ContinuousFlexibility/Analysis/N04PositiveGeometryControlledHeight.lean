module

public import ContinuousFlexibility.Analysis.N04PositiveGeometryControlledFamilyMaterial
public import ContinuousFlexibility.Analysis.N04RealizationPositiveHeightTaylorJets
public import ContinuousFlexibility.Analysis.N04RealizationPositiveHeightOneHigh

/-!
# The actual chosen height: mixed towers and one high material bounds

The raw source-height towers are passed through the fixed logarithmic
Taylor interpolation and exponential. The width, low logarithmic margin
and numerical envelope come from the same controlled family. Both the
height and its reciprocal retain one parameter height factor.
-/

@[expose] public section

noncomputable section

namespace ContinuousFlexibility.Analysis

open Set ContinuousFlexibility.Statements
open scoped ContDiff

set_option backward.isDefEq.respectTransparency false

variable {V : Type*} [TopologicalSpace V] [AddCommGroup V] [Module ℝ V]
  [IsTopologicalAddGroup V] [ContinuousSMul ℝ V]

private theorem controlled_source_height_root
    {W : N04RealizationStart} {X : N04RealizationChoice W} {n : ℕ}
    (G : N04PositiveGeometryControlledFamily W X n)
    {z : AnnularState W.S × ℝ} (hz : z ∈ stateNeighborhood W.S W.C G.base G.ε)
    (hs : stateSector W.S z.1)
    (i : N04PositiveComponent W.D.a W.D.b (deriv W.D.w)) (side : Bool) (θ : ℝ) :
    ContDiffAt ℝ ∞ (n04PositiveSourceHeight (X.src i side) (W.A X.e₀) z)
      (n04PositiveEndpoint i side, θ) ∧
      0 < n04PositiveSourceHeight (X.src i side) (W.A X.e₀) z
        (n04PositiveEndpoint i side, θ) :=
  (n04Coordinates_actualAtlas_positiveEndpoint_of_source
    W.hT W.hS W.through03 W.field X.e₀ (X.src i side)
    (stateNeighborhood_mono W.S W.C G.base_le G.radius_le hz) hs).height_root θ

/-- The exact stored reciprocal formula pays for the low logarithmic
Taylor correction, for every state and every future output order. -/
theorem n04PositiveGeometry_controlledHeight_log_smallness
    {W : N04RealizationStart} {X : N04RealizationChoice W} {n : ℕ}
    (G : N04PositiveGeometryControlledFamily W X n)
    (i : N04PositiveComponent W.D.a W.D.b (deriv W.D.w)) :
    0 ≤ G.Clog * G.M i ^ (2 * n + 1) ∧
      ((n + 1 : ℕ) : ℝ) * (G.Clog * G.M i ^ (2 * n + 1)) * G.δ i ≤ 1 := by
  let ρ : ℝ := min ((n04PositiveRight i - n04PositiveLeft i) / 4)
    (min (G.buffer.centerLeft i - n04PositiveLeft i)
      (n04PositiveRight i - G.buffer.centerRight i))
  let Mlow : ℝ := G.Clog * G.M i ^ (2 * n + 1)
  have hρ : 0 < ρ := (G.width_pos i).trans_le (G.width_core i)
  have hMlow : 0 ≤ Mlow := mul_nonneg G.log_constant.le
    (pow_nonneg (zero_le_one.trans (G.input_one i)) _)
  have hwidth : G.δ i = oneSidedEndpointHeightWidth n ρ Mlow := by
    calc
      G.δ i = ((G.δ i)⁻¹)⁻¹ := (inv_inv _).symm
      _ = oneSidedEndpointHeightWidth n ρ Mlow :=
        congrArg (fun t : ℝ => t⁻¹) (G.width_inverse i)
  have hsmall := (oneSidedEndpointHeightWidth_margins n hρ hMlow).2.2.2.2
  rw [← hwidth] at hsmall
  exact ⟨hMlow, hsmall⟩

/-- This is a tower for the stored `Q` itself and its literal reciprocal.
Only the genuine original source-height axis towers are supplied. -/
def n04PositiveGeometry_controlledHeight_mixedJetRegularity
    {W : N04RealizationStart} {X : N04RealizationChoice W} {n : ℕ}
    (G : N04PositiveGeometryControlledFamily W X n)
    {U : Set V} (hU : IsOpen U) (state : V → AnnularState W.S × ℝ)
    (hstate : ∀ x ∈ U, state x ∈ stateNeighborhood W.S W.C G.base G.ε)
    (hsector : ∀ x ∈ U, stateSector W.S (state x).1)
    (i : N04PositiveComponent W.D.a W.D.b (deriv W.D.w))
    (JH : ∀ side, ∀ j : ℕ, j ≤ n → ∀ b θ,
      SmoothDirections U (fun x => iteratedDeriv b
        (radialBoundaryJet (n04PositiveSourceHeight (X.src i side)
          (W.A X.e₀) (state x)) (n04PositiveEndpoint i side) j) θ)) (inv : Bool) :
    MixedJetRegularity U univ (fun x q => if inv then
      (G.toN04PositiveGeometryControlData.Q (state x) i q)⁻¹
      else G.toN04PositiveGeometryControlData.Q (state x) i q) :=
  n04Realization_positiveHeightTaylor_mixedJetRegularity hU n
    (n04PositiveLeft i) (n04PositiveRight i) (G.δ i)
    (fun x side => n04PositiveSourceHeight (X.src i side) (W.A X.e₀) (state x))
    (fun x hx side θ => (controlled_source_height_root G (hstate x hx) (hsector x hx) i side θ).1)
    (fun x hx side θ => (controlled_source_height_root G (hstate x hx) (hsector x hx) i side θ).2)
    JH inv

/-- A common material envelope for the raw prefix, stored source values
and selected height collar, followed by any fixed polynomial cost. -/
theorem n04PositiveGeometry_controlled_height_material_envelope
    {W : N04RealizationStart} {X : N04RealizationChoice W} {n : ℕ}
    (G : N04PositiveGeometryControlledFamily W X n) (A CQ : ℝ) (d : ℕ) :
    ∃ B : ℝ, 1 ≤ B ∧
      ∃ M : N04PositiveComponent W.D.a W.D.b (deriv W.D.w) → ℝ, ∀ i,
      1 ≤ M i ∧ A * W.U.E0 (W.U.sample (X.cell i)) ^ A ≤ M i ∧
      G.M i ≤ M i ∧ (G.δ i)⁻¹ ≤ M i ∧
      CQ * M i ^ d ≤ B * W.U.E0 (W.U.sample (X.cell i)) ^ B := by
  obtain ⟨Cmat, hCmat, hmaterial⟩ := n04PositiveGeometry_controlledFamily_material_bounds G
  let C : ℝ := max 1 (max A Cmat)
  have hC : 1 ≤ C := le_max_left _ _
  have hAC : A ≤ C := (le_max_left _ _).trans (le_max_right _ _)
  have hCmatC : Cmat ≤ C := (le_max_right _ _).trans (le_max_right _ _)
  obtain ⟨B₀, hB₀, hpack⟩ := n04PositiveGeometry_polynomial_sample_pack CQ C d
  let B : ℝ := max 1 B₀
  have hB : 1 ≤ B := le_max_left _ _
  have hB₀B : B₀ ≤ B := le_max_right _ _
  refine ⟨B, hB, (fun i => C * W.U.E0 (W.U.sample (X.cell i)) ^ C), ?_⟩
  intro i
  let E : ℝ := W.U.E0 (W.U.sample (X.cell i))
  have hE : 1 ≤ E := (W.floor _).trans (le_enlargedMaterialData_E0 W.T _)
  have hraw : A * E ^ A ≤ C * E ^ C := mul_le_mul hAC
    (Real.rpow_le_rpow_of_exponent_le hE hAC)
    (Real.rpow_nonneg (zero_le_one.trans hE) _) (zero_le_one.trans hC)
  have hmaterial' : Cmat * E ^ Cmat ≤ C * E ^ C := mul_le_mul hCmatC
    (Real.rpow_le_rpow_of_exponent_le hE hCmatC)
    (Real.rpow_nonneg (zero_le_one.trans hE) _) (zero_le_one.trans hC)
  exact ⟨one_le_mul_of_one_le_of_one_le hC
      (Real.one_le_rpow hE (zero_le_one.trans hC)),
    hraw, (hmaterial.input i).trans hmaterial',
    (le_abs_self _).trans ((hmaterial.height_width i).trans hmaterial'),
    (hpack E hE).trans (mul_le_mul hB₀B (Real.rpow_le_rpow_of_exponent_le hE hB₀B)
      (Real.rpow_nonneg (zero_le_one.trans hE) _) (zero_le_one.trans hB))⟩

/-- The finite raw normalized prefix passes to the same stored height
and reciprocal with a polynomial sample cost. No normalization of the
parameter directions has yet been imposed. -/
theorem n04PositiveGeometry_controlledHeight_shifted_bound
    {W : N04RealizationStart} {X : N04RealizationChoice W} {n : ℕ}
    (G : N04PositiveGeometryControlledFamily W X n)
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
    ∀ inv : Bool, ∀ q : PolarPoint, ∀ J : SmoothDirections U
      (fun y => mixedDerivative a b (fun z => if inv then
        (G.toN04PositiveGeometryControlData.Q (state y) i z)⁻¹
        else G.toN04PositiveGeometryControlData.Q (state y) i z) q),
    ‖J.D k x v‖ ≤ B * W.U.E0 (W.U.sample (X.cell i)) ^ B *
      parameterHeightWeight H k *
        R ^ (((a + b + shift * k : ℕ) : ℝ) / ((budget : ℝ) + 1)) := by
  obtain ⟨CQ, d, hCQ, hd, hbound⟩ :=
    n04Realization_positiveHeightTaylor_shifted_parameter_bound (X := V) n k a b RH
  obtain ⟨B, hB, M, hM⟩ := n04PositiveGeometry_controlled_height_material_envelope G A CQ d
  refine ⟨B, hB, ?_⟩
  intro U hU state hstate hsector i JH x hx P v hv H R hH hHR hR budget shift hraw inv q J
  have hroot (y : V) (hy : y ∈ U) (side : Bool) (θ : ℝ) :=
    controlled_source_height_root G (hstate y hy) (hsector y hy) i side θ
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
        (mul_le_mul_of_nonneg_right (hM i).2.1 (parameterHeightWeight_nonneg hH e))
        (Real.rpow_nonneg (zero_le_one.trans hR) _))
  have hsmall := n04PositiveGeometry_controlledHeight_log_smallness G i
  have hout := hbound U hU (n04PositiveLeft i) (n04PositiveRight i) (G.δ i)
    (G.width_pos i) (G.width_one i)
    (fun y side => n04PositiveSourceHeight (X.src i side) (W.A X.e₀) (state y))
    (fun y hy side θ => (hroot y hy side θ).1)
    (fun y hy side θ => (hroot y hy side θ).2)
    JH x hx P v hv H (M i) R hH hHR (hM i).1 hR (hM i).2.2.2.1
    budget shift hinverse hraw' (G.Clog * G.M i ^ (2 * n + 1)) hsmall.1
    (G.log_bound (state x) (hstate x hx) (hsector x hx) i) hsmall.2 inv q J
  exact hout.trans (mul_le_mul_of_nonneg_right
    (mul_le_mul_of_nonneg_right (hM i).2.2.2.2 (parameterHeightWeight_nonneg hH k))
    (Real.rpow_nonneg (zero_le_one.trans hR) _))

/-- A normalized raw source prefix gives one high seminorm for every
positive parameter derivative of both actual height choices. The output
material coefficient is selected before the component and the state. -/
theorem n04PositiveGeometry_controlledHeight_positive_oneHigh
    {W : N04RealizationStart} {X : N04RealizationChoice W} {n : ℕ}
    (G : N04PositiveGeometryControlledFamily W X n)
    (K s shift : ℕ) (RH A : ℝ) (hA : 1 ≤ A) :
    ∃ B : ℝ, 1 ≤ B ∧
    ∀ (p : ℕ → Seminorm ℝ V) (center : V) (base high : ℕ),
    ∀ (U : Set V), IsOpen U → ∀ state : V → AnnularState W.S × ℝ,
    (∀ x ∈ U, state x ∈ stateNeighborhood W.S W.C G.base G.ε) →
    (∀ x ∈ U, stateSector W.S (state x).1) →
    ∀ i : N04PositiveComponent W.D.a W.D.b (deriv W.D.w),
    ∀ JH : ∀ side, ∀ j : ℕ, j ≤ n → ∀ b θ,
      SmoothDirections U (fun x => iteratedDeriv b
        (radialBoundaryJet (n04PositiveSourceHeight (X.src i side)
          (W.A X.e₀) (state x)) (n04PositiveEndpoint i side) j) θ),
    ∀ H : ℝ, 0 ≤ H → H ≤ RH →
    ∀ x ∈ U, p base (x - center) ≤ 1 →
    (∀ side, ∀ j : ℕ, ∀ hj : j ≤ n, ∀ e : ℕ, e ≤ K →
      ∀ u : ℕ, u ≤ s → ∀ θ, ∀ z : Fin e → V,
      (∀ t, p base (z t) ≤ 1) →
      ∀ R : ℝ, 1 ≤ R → p high (x - center) ≤ R → (∀ t, p high (z t) ≤ R) →
      ‖(JH side j hj u θ).D e x z‖ ≤
        A * W.U.E0 (W.U.sample (X.cell i)) ^ A * parameterHeightWeight H e *
          R ^ (((u + shift * e : ℕ) : ℝ) / (((s + shift * K : ℕ) : ℝ) + 1))) →
    ∀ k : ℕ, k ≤ K → 0 < k → ∀ a b : ℕ, a + b ≤ s →
    ∀ inv : Bool, ∀ q : PolarPoint, ∀ J : SmoothDirections U
      (fun y => mixedDerivative a b (fun z => if inv then
        (G.toN04PositiveGeometryControlData.Q (state y) i z)⁻¹
        else G.toN04PositiveGeometryControlData.Q (state y) i z) q),
    ∀ v : Fin k → V, ‖J.D k x v‖ ≤
      B * W.U.E0 (W.U.sample (X.cell i)) ^ B * H *
        oneHighVariationWeight p base high (x - center) v := by
  obtain ⟨CQ, d, hCQ, hd, hbound⟩ :=
    n04Realization_positiveHeightTaylor_positive_oneHigh (X := V) n K s shift RH
  obtain ⟨B, hB, M, hM⟩ := n04PositiveGeometry_controlled_height_material_envelope G A CQ d
  refine ⟨B, hB, ?_⟩
  intro p center base high U hU state hstate hsector i JH H hH hHR x hx hlow hraw
    k hk hkpos a b hab inv q J v
  have hroot (y : V) (hy : y ∈ U) (side : Bool) (θ : ℝ) :=
    controlled_source_height_root G (hstate y hy) (hsector y hy) i side θ
  have hinverse (side : Bool) (θ : ℝ) :
      (n04PositiveSourceHeight (X.src i side) (W.A X.e₀) (state x)
        (n04PositiveEndpoint i side, θ))⁻¹ ≤ M i :=
    ((G.endpoint_bounds (state x) (hstate x hx) (hsector x hx) i).height_inverse side θ).trans
      (hM i).2.2.1
  have hraw' (side : Bool) (j : ℕ) (hj : j ≤ n) (e : ℕ) (he : e ≤ K)
      (u : ℕ) (hu : u ≤ s) (θ : ℝ) (z : Fin e → V)
      (hz : ∀ t, p base (z t) ≤ 1) (R : ℝ) (hR : 1 ≤ R)
      (hxR : p high (x - center) ≤ R) (hzR : ∀ t, p high (z t) ≤ R) :
      ‖(JH side j hj u θ).D e x z‖ ≤ M i * parameterHeightWeight H e *
        R ^ (((u + shift * e : ℕ) : ℝ) / (((s + shift * K : ℕ) : ℝ) + 1)) :=
    (hraw side j hj e he u hu θ z hz R hR hxR hzR).trans
      (mul_le_mul_of_nonneg_right
        (mul_le_mul_of_nonneg_right (hM i).2.1 (parameterHeightWeight_nonneg hH e))
        (Real.rpow_nonneg (zero_le_one.trans hR) _))
  have hsmall := n04PositiveGeometry_controlledHeight_log_smallness G i
  have hout := hbound p center base high U hU
    (n04PositiveLeft i) (n04PositiveRight i) (G.δ i) (G.width_pos i) (G.width_one i)
    (fun y side => n04PositiveSourceHeight (X.src i side) (W.A X.e₀) (state y))
    (fun y hy side θ => (hroot y hy side θ).1)
    (fun y hy side θ => (hroot y hy side θ).2)
    JH H (M i) hH hHR (hM i).1 (hM i).2.2.2.1 x hx hlow hinverse hraw'
    (G.Clog * G.M i ^ (2 * n + 1)) hsmall.1
    (G.log_bound (state x) (hstate x hx) (hsector x hx) i) hsmall.2
    k hk hkpos a b hab inv q J v
  exact hout.trans (mul_le_mul_of_nonneg_right
    (mul_le_mul_of_nonneg_right (hM i).2.2.2.2 hH)
    (oneHighVariationWeight_nonneg p base high (x - center) v))

end ContinuousFlexibility.Analysis
