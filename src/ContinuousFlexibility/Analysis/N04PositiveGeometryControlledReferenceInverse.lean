import ContinuousFlexibility.Analysis.N04PositiveGeometryControlledFamilyMaterial
import ContinuousFlexibility.Analysis.N04PositiveGeometryReferencePullbackCosts
import ContinuousFlexibility.Analysis.N04RealizationFixedRadialPullback
import ContinuousFlexibility.Analysis.WholePositiveReferenceGauge

/-!
# The actual inverse chart in the fixed reference gauge

The stored inverse chart is the chosen transport at the genuine fixed
reference inverse. Its radial chain coefficients change the material
constant only. The original parameter height factor and the complete
normalized spatial-plus-parameter exponent remain unchanged.
-/

noncomputable section

namespace ContinuousFlexibility.Analysis

open Set ContinuousFlexibility.Statements
open scoped ContDiff BigOperators

variable {V : Type*} [TopologicalSpace V] [AddCommGroup V] [Module ℝ V]
  [IsTopologicalAddGroup V] [ContinuousSMul ℝ V]

/-- The genuine fixed radial chain formula preserves a separate
parameter-order shift in the normalized exponent. -/
theorem n04PositiveGeometry_fixedRadial_shifted_parameter_bound
    {U : Set V} {I : Set ℝ} {Ω : Set PolarPoint}
    {χ : ℝ → ℝ} {f : V → PolarPoint → ℝ}
    (hI : IsOpen I) (hΩ : IsOpen Ω) (hχ : ContDiff ℝ ∞ χ)
    (RF : MixedJetRegularity U Ω f)
    (hmap : ∀ r ∈ I, ∀ θ : ℝ, (χ r, θ) ∈ Ω)
    (a b k budget shift : ℕ) {q : PolarPoint} (hq : q ∈ I ×ˢ (univ : Set ℝ))
    (J : SmoothDirections U (fun x => mixedDerivative a b (fun p => f x (χ p.1, p.2)) q))
    {x : V} (hx : x ∈ U) (v : Fin k → V) {M R : ℝ} (hM : 0 ≤ M) (hR : 1 ≤ R)
    (hbound : ∀ i : Fin (a + 1),
      |((RF.parameter i.val b (χ q.1, q.2) (hmap q.1 hq.1 q.2)).D k x v)| ≤
        M * R ^ (((i.val + b + shift * k : ℕ) : ℝ) / ((budget : ℝ) + 1))) :
    |J.D k x v| ≤ (∑ i : Fin (a + 1), |radialChainCoefficient χ a i q.1|) *
      M * R ^ (((a + b + shift * k : ℕ) : ℝ) / ((budget : ℝ) + 1)) := by
  rw [n04Realization_fixedRadial_parameterJet_formula hI hΩ hχ RF hmap a b hq J k hx v]
  have hterm (i : Fin (a + 1)) :
      |((RF.parameter i.val b (χ q.1, q.2) (hmap q.1 hq.1 q.2)).D k x v)| ≤
        M * R ^ (((a + b + shift * k : ℕ) : ℝ) / ((budget : ℝ) + 1)) := by
    have he : (((i.val + b + shift * k : ℕ) : ℝ) / ((budget : ℝ) + 1)) ≤
        (((a + b + shift * k : ℕ) : ℝ) / ((budget : ℝ) + 1)) := by
      apply div_le_div_of_nonneg_right _ (by positivity)
      exact_mod_cast Nat.add_le_add_right
        (Nat.add_le_add_right (Nat.le_of_lt_succ i.isLt) b) (shift * k)
    exact (hbound i).trans
      (mul_le_mul_of_nonneg_left (Real.rpow_le_rpow_of_exponent_le hR he) hM)
  calc
    _ ≤ ∑ i : Fin (a + 1), |radialChainCoefficient χ a i q.1| *
        |((RF.parameter i.val b (χ q.1, q.2) (hmap q.1 hq.1 q.2)).D k x v)| := by
      simpa only [abs_mul] using Finset.abs_sum_le_sum_abs
        (fun i : Fin (a + 1) => radialChainCoefficient χ a i q.1 *
          ((RF.parameter i.val b (χ q.1, q.2) (hmap q.1 hq.1 q.2)).D k x v)) Finset.univ
    _ ≤ ∑ i : Fin (a + 1), |radialChainCoefficient χ a i q.1| *
        (M * R ^ (((a + b + shift * k : ℕ) : ℝ) / ((budget : ℝ) + 1))) :=
      Finset.sum_le_sum (fun i _ => mul_le_mul_of_nonneg_left (hterm i) (abs_nonneg _))
    _ = _ := by rw [← Finset.sum_mul, mul_assoc]

/-- Each literal component of the chosen inverse chart consumes the
actual transport mixed prefix. The same fixed reference inverse and the
same positive sample are retained, at every parameter order. -/
theorem n04PositiveGeometry_controlledReferenceInverse_shifted_bound
    {W : N04RealizationStart} {X : N04RealizationChoice W} {n : ℕ}
    (G : N04PositiveGeometryControlledFamily W X n)
    (Y H₀ : N04PositiveComponent W.D.a W.D.b (deriv W.D.w) → ℝ → ℝ)
    (href : N04PositiveReferenceFamily (W.A X.e₀) X.src 4 Y H₀)
    (hmaterial : N04PositiveReferenceMaterialBounds W.T X.cell Y H₀)
    (k a b : ℕ) {A : ℝ} (hA : 1 ≤ A) :
    ∃ B : ℝ, 1 ≤ B ∧
    ∀ (U : Set V), ∀ state : V → AnnularState W.S × ℝ,
    ∀ i : N04PositiveComponent W.D.a W.D.b (deriv W.D.w), ∀ angle : Bool,
    ∀ RF : MixedJetRegularity U univ (fun x p => if angle then
        (G.toN04PositiveGeometryControlData.τ (state x) i p).2
      else (G.toN04PositiveGeometryControlData.τ (state x) i p).1),
    ∀ x ∈ U, ∀ v : Fin k → V,
    ∀ H R : ℝ, 0 ≤ H → 1 ≤ R → ∀ budget shift : ℕ,
    (∀ u w : ℕ, u + w ≤ a + b → ∀ p : PolarPoint,
      |(RF.parameter u w p (mem_univ p)).D k x v| ≤
        A * W.U.E0 (W.U.sample (X.cell i)) ^ A * parameterHeightWeight H k *
          R ^ (((u + w + shift * k : ℕ) : ℝ) / ((budget : ℝ) + 1))) →
    ∀ q ∈ CanonicalGeometry.unitStrip,
    ∀ J : SmoothDirections U (fun z => mixedDerivative a b (fun p => if angle then
        (wholePositiveReferenceGaugeInverse (G.toN04PositiveGeometryControlData.τ (state z) i)
          (positiveReferenceCylinderInverse (Y i)) p).2
      else (wholePositiveReferenceGaugeInverse (G.toN04PositiveGeometryControlData.τ (state z) i)
          (positiveReferenceCylinderInverse (Y i)) p).1) q),
      |J.D k x v| ≤ B * W.U.E0 (W.U.sample (X.cell i)) ^ B * parameterHeightWeight H k *
        R ^ (((a + b + shift * k : ℕ) : ℝ) / ((budget : ℝ) + 1)) := by
  have hsmooth (i) := n04PositiveGeometry_reference_scalar_geometry (href i).1
  obtain ⟨Br, hBr, hchain⟩ := n04PositiveGeometry_reference_chain_mass_material_cost
    W.floor hmaterial (fun i => (hsmooth i).2.1) (a + b)
  obtain ⟨B₀, hB₀, hpack⟩ := coefficientEnvelope_pack (Br * A) (Br + A)
  let B : ℝ := max 1 B₀
  have hB : 1 ≤ B := le_max_left _ _
  have hB₀B : B₀ ≤ B := le_max_right _ _
  refine ⟨B, hB, ?_⟩
  intro U state i angle RF x hx v H R hH hR budget shift hraw q hq J
  let E : ℝ := W.U.E0 (W.U.sample (X.cell i))
  have hE : 1 ≤ E := (W.floor _).trans (le_enlargedMaterialData_E0 W.T _)
  have hcost : (Br * E ^ Br) * (A * E ^ A) ≤ B * E ^ B := calc
    _ = (Br * A) * E ^ (Br + A) := by
      rw [Real.rpow_add (zero_lt_one.trans_le hE)]
      ac_rfl
    _ ≤ B₀ * E ^ B₀ := hpack E hE
    _ ≤ B * E ^ B := mul_le_mul hB₀B (Real.rpow_le_rpow_of_exponent_le hE hB₀B)
      (Real.rpow_nonneg (zero_le_one.trans hE) _) (zero_le_one.trans hB)
  let f : V → PolarPoint → ℝ := fun z p => if angle then
    (G.toN04PositiveGeometryControlData.τ (state z) i p).2
    else (G.toN04PositiveGeometryControlData.τ (state z) i p).1
  let χ := Function.invFun (Y i)
  have hmap : ∀ r ∈ Ioo (0 : ℝ) 1, ∀ θ : ℝ,
      (χ r, θ) ∈ (univ : Set PolarPoint) := fun _ _ _ => mem_univ _
  let M : ℝ := A * E ^ A * parameterHeightWeight H k
  have hM : 0 ≤ M := mul_nonneg
    (mul_nonneg (zero_le_one.trans hA) (Real.rpow_nonneg (zero_le_one.trans hE) _))
    (parameterHeightWeight_nonneg hH _)
  change SmoothDirections U (fun z => mixedDerivative a b (fun p => f z (χ p.1, p.2)) q) at J
  have hout := n04PositiveGeometry_fixedRadial_shifted_parameter_bound
    isOpen_Ioo isOpen_univ (hsmooth i).2.1 RF hmap a b k budget shift hq J hx v hM hR
    (fun j => hraw j.val b (by omega) (χ q.1, q.2))
  have hmass := hchain i a (Nat.le_add_right _ _) q.1
  calc
    _ ≤ (∑ j : Fin (a + 1), |radialChainCoefficient χ a j q.1|) * M *
        R ^ (((a + b + shift * k : ℕ) : ℝ) / ((budget : ℝ) + 1)) := hout
    _ ≤ (Br * E ^ Br) * M *
        R ^ (((a + b + shift * k : ℕ) : ℝ) / ((budget : ℝ) + 1)) :=
      mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right hmass hM)
        (Real.rpow_nonneg (zero_le_one.trans hR) _)
    _ = ((Br * E ^ Br) * (A * E ^ A)) * parameterHeightWeight H k *
        R ^ (((a + b + shift * k : ℕ) : ℝ) / ((budget : ℝ) + 1)) := by
      simp only [M, mul_assoc]
    _ ≤ _ := mul_le_mul_of_nonneg_right
      (mul_le_mul_of_nonneg_right hcost (parameterHeightWeight_nonneg hH _))
      (Real.rpow_nonneg (zero_le_one.trans hR) _)

end ContinuousFlexibility.Analysis
