import ContinuousFlexibility.Analysis.N04PositiveGeometryForwardKernelSlab
import ContinuousFlexibility.Analysis.N04PositiveGeometryControlledFamilyMaterial

/-!
# The actual controlled family's finite radial inverse kernel

The kernel uses the same stored widths and coefficient margins as the
chosen transport. Its full inverse jets have one sample polynomial
bound, selected before both the positive component and the free finite
coefficient vector. The actual pulled-back endpoint coefficients lie
strictly inside this domain on the chosen state neighborhood.
-/

noncomputable section

namespace ContinuousFlexibility.Analysis

open Set ContinuousFlexibility.Statements
open scoped ContDiff

namespace N04PositiveGeometryControlData

variable {W : N04RealizationStart} {X : N04RealizationChoice W} {n : ℕ}

def radialCoefficientDomain (G : N04PositiveGeometryControlData W X n)
    (i : N04PositiveComponent W.D.a W.D.b (deriv W.D.w)) :
    Set (N04PositiveRadialCoefficients n) :=
  n04PositiveGeometry_radialCoefficientDomain n ((G.M i)⁻¹ / 2) (G.Mσ i)

def radialKernel (G : N04PositiveGeometryControlData W X n)
    (i : N04PositiveComponent W.D.a W.D.b (deriv W.D.w)) :
    N04PositiveRadialCoefficients n × ℝ → ℝ :=
  n04PositiveGeometry_radialKernel n (n04PositiveLeft i) (n04PositiveRight i)
    (G.buffer.centerLeft i) (G.buffer.centerRight i)
    (endpointFiberWidths n (n04PositiveLeft i) (n04PositiveRight i)
      (G.buffer.centerLeft i) (G.buffer.centerRight i) ((G.M i)⁻¹ / 2) (G.Mσ i))

def radialInverseKernel (G : N04PositiveGeometryControlData W X n)
    (i : N04PositiveComponent W.D.a W.D.b (deriv W.D.w))
    (q : N04PositiveRadialCoefficients n × ℝ) : ℝ :=
  Function.invFun (fun t => G.radialKernel i (q.1, t)) q.2

end N04PositiveGeometryControlData

private theorem control_ordered
    {W : N04RealizationStart} {X : N04RealizationChoice W} {n : ℕ}
    (G : N04PositiveGeometryControlData W X n)
    (i : N04PositiveComponent W.D.a W.D.b (deriv W.D.w)) :
    n04PositiveLeft i < G.buffer.centerLeft i ∧
      G.buffer.centerLeft i < G.buffer.centerRight i ∧
      G.buffer.centerRight i < n04PositiveRight i :=
  ⟨(G.buffer.ordered i).1, (G.buffer.ordered i).2.1.trans
    ((G.buffer.ordered i).2.2.1.trans (G.buffer.ordered i).2.2.2.1),
    (G.buffer.ordered i).2.2.2.2⟩

/-- The strict margins retained by the forward construction put its
actual inverse-fiber coefficients in the open finite kernel domain. -/
theorem n04PositiveGeometry_controlled_coefficients_mem
    {W : N04RealizationStart} {X : N04RealizationChoice W} {n : ℕ}
    (G : N04PositiveGeometryControlledFamily W X n)
    {z : AnnularState W.S × ℝ} (hz : z ∈ stateNeighborhood W.S W.C G.base G.ε)
    (hs : stateSector W.S z.1)
    (i : N04PositiveComponent W.D.a W.D.b (deriv W.D.w)) (θ : ℝ) :
    (fun side (j : Fin (n + 1)) =>
      G.toN04PositiveGeometryControlData.coefficients z i side (j + 1) θ) ∈
        G.toN04PositiveGeometryControlData.radialCoefficientDomain i := by
  intro side
  constructor
  · have hm : 0 < (G.M i)⁻¹ := inv_pos.mpr (zero_lt_one.trans_le (G.input_one i))
    have h := (half_lt_self hm).trans_le (G.coefficient_lower z hz hs i side θ)
    simpa only [Fin.val_zero, zero_add] using h
  · intro j
    exact (G.coefficient_bound z hz hs i side (j + 1) (by omega) (by omega) θ).trans_lt
      (half_lt_self (zero_lt_one.trans_le (G.inverse_one i)))

theorem n04PositiveGeometry_controlled_inverseKernel_contDiffOn
    {W : N04RealizationStart} {X : N04RealizationChoice W} {n : ℕ}
    (G : N04PositiveGeometryControlledFamily W X n)
    (i : N04PositiveComponent W.D.a W.D.b (deriv W.D.w)) :
    ContDiffOn ℝ ∞ (G.toN04PositiveGeometryControlData.radialInverseKernel i)
      (G.toN04PositiveGeometryControlData.radialCoefficientDomain i ×ˢ univ) :=
  n04PositiveGeometry_radialKernel_inverse_contDiffOn n
    (control_ordered G.toN04PositiveGeometryControlData i).1
    (control_ordered G.toN04PositiveGeometryControlData i).2.1
    (control_ordered G.toN04PositiveGeometryControlData i).2.2
    (half_pos (inv_pos.mpr (zero_lt_one.trans_le (G.input_one i))))
    (zero_le_one.trans (G.inverse_one i))

/-- Quantitative inverse bounds for the same selected family. They
involve no bound or regularity assumption on an inverse map. -/
theorem n04PositiveGeometry_controlled_radialKernels_bounds
    {W : N04RealizationStart} {X : N04RealizationChoice W} {n : ℕ}
    (G : N04PositiveGeometryControlledFamily W X n) (inverse : Bool) :
    ∀ k : ℕ, ∃ C Q : ℝ, 0 < C ∧ 0 ≤ Q ∧
      ∀ (i : N04PositiveComponent W.D.a W.D.b (deriv W.D.w))
        (a : N04PositiveRadialCoefficients n),
        a ∈ G.toN04PositiveGeometryControlData.radialCoefficientDomain i →
      ∀ x ∈ Icc (n04PositiveLeft i) (n04PositiveRight i),
        ‖iteratedFDeriv ℝ k (if inverse then
          G.toN04PositiveGeometryControlData.radialInverseKernel i else
          G.toN04PositiveGeometryControlData.radialKernel i)
          (a, x)‖ ≤ C * W.U.E0 (W.U.sample (X.cell i)) ^ Q := by
  let E := fun i => W.U.E0 (W.U.sample (X.cell i))
  have hE (i) : 1 ≤ E i := (W.floor _).trans (le_enlargedMaterialData_E0 W.T _)
  obtain ⟨A, hA, hcost⟩ := n04PositiveGeometry_controlledFamily_material_bounds G
  have hApos : 0 < A := zero_lt_one.trans_le hA
  have hf : Continuous (deriv W.D.w) :=
    (n04b_profileGeometry_of_through03 W.through03).2.2.1.1.continuous_deriv (by simp)
  have hbounded (i) :
      n04PositiveLeft i ∈ Icc W.D.a W.D.b ∧
      n04PositiveRight i ∈ Icc W.D.a W.D.b ∧
      G.buffer.centerLeft i ∈ Icc W.D.a W.D.b ∧
      G.buffer.centerRight i ∈ Icc W.D.a W.D.b := by
    have hb := n04PositiveComponent_bounds hf i
    have ho := control_ordered G.toN04PositiveGeometryControlData i
    exact ⟨⟨hb.1, hb.2.1.le.trans hb.2.2⟩,
      ⟨hb.1.trans hb.2.1.le, hb.2.2⟩,
      ⟨hb.1.trans ho.1.le, ho.2.1.le.trans (ho.2.2.le.trans hb.2.2)⟩,
      ⟨hb.1.trans (ho.1.le.trans ho.2.1.le), ho.2.2.le.trans hb.2.2⟩⟩
  have hradial (f : N04PositiveComponent W.D.a W.D.b (deriv W.D.w) → ℝ)
      (hb : ∀ i, f i ∈ Icc W.D.a W.D.b) :
      HasPositiveEnvelope E (fun i => |f i|) := by
    apply (hasPositiveEnvelope_const E hE (|W.D.a| + |W.D.b|)).mono
    intro i
    apply abs_le.mpr
    have hi := hb i
    constructor <;> linarith only [hi.1, hi.2, neg_abs_le W.D.a,
      le_abs_self W.D.b, abs_nonneg W.D.a, abs_nonneg W.D.b]
  have hMcost : HasPositiveEnvelope E G.Mσ :=
    ⟨A, A, hApos, hApos, hcost.inverse⟩
  have hwidth (side : Bool) : HasPositiveEnvelope E (fun i =>
      |(endpointFiberWidths n (n04PositiveLeft i) (n04PositiveRight i)
        (G.buffer.centerLeft i) (G.buffer.centerRight i) ((G.M i)⁻¹ / 2) (G.Mσ i) side)⁻¹|) :=
    ⟨A, A, hApos, hApos, fun i => hcost.fiber_width i side⟩
  have hspan (side : Bool) : HasPositiveEnvelope E (fun i =>
      |((if side then n04PositiveRight i else G.buffer.centerLeft i) -
        (if side then G.buffer.centerRight i else n04PositiveLeft i))⁻¹|) := by
    refine ⟨A, A, hApos, hApos, ?_⟩
    intro i
    cases side with
    | false =>
      change |(G.buffer.centerLeft i - n04PositiveLeft i)⁻¹| ≤ A * E i ^ A
      rw [abs_of_pos (inv_pos.mpr
        (sub_pos.mpr (control_ordered G.toN04PositiveGeometryControlData i).1))]
      exact (hcost.buffer_gaps i).1
    | true =>
      change |(n04PositiveRight i - G.buffer.centerRight i)⁻¹| ≤ A * E i ^ A
      rw [abs_of_pos (inv_pos.mpr
        (sub_pos.mpr (control_ordered G.toN04PositiveGeometryControlData i).2.2))]
      exact (hcost.buffer_gaps i).2.2.2.2
  have hlower : HasPositiveEnvelope E (fun i =>
      |(endpointFiberLower n (n04PositiveLeft i) (n04PositiveRight i)
        (G.buffer.centerLeft i) (G.buffer.centerRight i) ((G.M i)⁻¹ / 2) (G.Mσ i))⁻¹|) :=
    ⟨A, A, hApos, hApos, hcost.radial_lower_inverse⟩
  cases inverse with
  | false =>
    exact n04PositiveGeometry_radialKernel_forward_bounds hE n
      n04PositiveLeft n04PositiveRight G.buffer.centerLeft G.buffer.centerRight
      (fun i => (G.M i)⁻¹ / 2) G.Mσ
      (fun i => (control_ordered G.toN04PositiveGeometryControlData i).1)
      (fun i => (control_ordered G.toN04PositiveGeometryControlData i).2.1)
      (fun i => (control_ordered G.toN04PositiveGeometryControlData i).2.2)
      (fun i => half_pos (inv_pos.mpr (zero_lt_one.trans_le (G.input_one i))))
      (fun i => zero_le_one.trans (G.inverse_one i))
      (hradial _ (fun i => (hbounded i).1)) (hradial _ (fun i => (hbounded i).2.1))
      (hradial _ (fun i => (hbounded i).2.2.1)) (hradial _ (fun i => (hbounded i).2.2.2))
      hMcost hwidth hspan
  | true =>
    exact n04PositiveGeometry_radialKernel_inverse_bounds hE n
      n04PositiveLeft n04PositiveRight G.buffer.centerLeft G.buffer.centerRight
      (fun i => (G.M i)⁻¹ / 2) G.Mσ
      (fun i => (control_ordered G.toN04PositiveGeometryControlData i).1)
      (fun i => (control_ordered G.toN04PositiveGeometryControlData i).2.1)
      (fun i => (control_ordered G.toN04PositiveGeometryControlData i).2.2)
      (fun i => half_pos (inv_pos.mpr (zero_lt_one.trans_le (G.input_one i))))
      (fun i => zero_le_one.trans (G.inverse_one i))
      (hradial _ (fun i => (hbounded i).1)) (hradial _ (fun i => (hbounded i).2.1))
      (hradial _ (fun i => (hbounded i).2.2.1)) (hradial _ (fun i => (hbounded i).2.2.2))
      hMcost hwidth hspan hlower

theorem n04PositiveGeometry_controlled_inverseKernel_bounds
    {W : N04RealizationStart} {X : N04RealizationChoice W} {n : ℕ}
    (G : N04PositiveGeometryControlledFamily W X n) :
    ∀ k : ℕ, ∃ C Q : ℝ, 0 < C ∧ 0 ≤ Q ∧
      ∀ (i : N04PositiveComponent W.D.a W.D.b (deriv W.D.w))
        (a : N04PositiveRadialCoefficients n),
        a ∈ G.toN04PositiveGeometryControlData.radialCoefficientDomain i →
      ∀ x ∈ Icc (n04PositiveLeft i) (n04PositiveRight i),
        ‖iteratedFDeriv ℝ k (G.toN04PositiveGeometryControlData.radialInverseKernel i)
          (a, x)‖ ≤ C * W.U.E0 (W.U.sample (X.cell i)) ^ Q :=
  n04PositiveGeometry_controlled_radialKernels_bounds G true

theorem n04PositiveGeometry_controlled_forwardKernel_bounds
    {W : N04RealizationStart} {X : N04RealizationChoice W} {n : ℕ}
    (G : N04PositiveGeometryControlledFamily W X n) :
    ∀ k : ℕ, ∃ C Q : ℝ, 0 < C ∧ 0 ≤ Q ∧
      ∀ (i : N04PositiveComponent W.D.a W.D.b (deriv W.D.w))
        (a : N04PositiveRadialCoefficients n),
        a ∈ G.toN04PositiveGeometryControlData.radialCoefficientDomain i →
      ∀ x ∈ Icc (n04PositiveLeft i) (n04PositiveRight i),
        ‖iteratedFDeriv ℝ k (G.toN04PositiveGeometryControlData.radialKernel i)
          (a, x)‖ ≤ C * W.U.E0 (W.U.sample (X.cell i)) ^ Q :=
  n04PositiveGeometry_controlled_radialKernels_bounds G false

end ContinuousFlexibility.Analysis
