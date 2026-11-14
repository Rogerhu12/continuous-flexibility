module

public import ContinuousFlexibility.Analysis.N04PositiveGeometryInverseBoundsAngularKernel
public import ContinuousFlexibility.Analysis.N04PositiveGeometryInverseBoundsControlled
public import ContinuousFlexibility.Analysis.N04PositiveGeometryInverseBoundsBoundaryData

/-!
# The stored angular kernel and its material envelope

The finite packet contains the actual endpoint angular defects. The
unwrapped angle is kept outside the packet. The coefficient envelope
may depend on a requested finite jet prefix; the selected angular width
and the original component sample remain fixed.
-/

@[expose] public section

noncomputable section

namespace ContinuousFlexibility.Analysis

open Set ContinuousFlexibility.Statements
open scoped ContDiff

theorem n04PositiveGeometry_angularKernel_contDiff (n : ℕ) (l r δ : ℝ) :
    ContDiff ℝ ∞ (n04PositiveGeometry_angularKernel n l r δ) := by
  have hpatch (c : ℝ) (side : Bool) : ContDiff ℝ ∞
      (fun p : N04PositiveRadialCoefficients n × ℝ =>
        n04PositiveGeometry_angularPatchKernel n c δ (p.1 side) p.2) := by
    apply ContDiff.sum
    intro j _
    have ha : ContDiff ℝ ∞ (fun p : N04PositiveRadialCoefficients n × ℝ => p.1 side j) :=
      ((contDiff_apply ℝ ℝ j).comp (contDiff_apply ℝ (Fin (n + 1) → ℝ) side)).comp
        contDiff_fst
    exact (((contDiff_positiveEndpointCutoff c δ).comp contDiff_snd).mul
      (((contDiff_snd.sub contDiff_const).pow (j : ℕ)).div_const _)).mul ha
  exact (hpatch l false).add (hpatch r true)

namespace N04PositiveGeometryControlData

variable {W : N04RealizationStart} {X : N04RealizationChoice W} {n : ℕ}

def angularCoefficients (G : N04PositiveGeometryControlData W X n)
    (z : AnnularState W.S × ℝ)
    (i : N04PositiveComponent W.D.a W.D.b (deriv W.D.w)) (θ : ℝ) :
    N04PositiveRadialCoefficients (n + 1) := fun side j =>
  radialBoundaryJet (fun p => (n04PositiveSourceMap (X.src i side) (W.A X.e₀) z p).2)
    (n04PositiveEndpoint i side) j θ - if (j : ℕ) = 0 then θ else 0

def angularKernel (G : N04PositiveGeometryControlData W X n)
    (i : N04PositiveComponent W.D.a W.D.b (deriv W.D.w)) :
    N04PositiveRadialCoefficients (n + 1) × ℝ → ℝ :=
  n04PositiveGeometry_angularKernel (n + 1) (n04PositiveLeft i) (n04PositiveRight i)
    (endpointAngularWidth (n + 1) (n04PositiveLeft i) (n04PositiveRight i)
      (G.buffer.centerLeft i) (G.buffer.centerRight i) (G.M i)⁻¹ (G.M i))

theorem angle_eq_angularKernel (G : N04PositiveGeometryControlData W X n)
    (z : AnnularState W.S × ℝ)
    (i : N04PositiveComponent W.D.a W.D.b (deriv W.D.w)) (p : PolarPoint) :
    G.angle z i p = p.2 + G.angularKernel i (G.angularCoefficients z i p.2, p.1) := by
  let Ψ := oneSidedEndpointRepresentative (n + 2) (n04PositiveLeft i) (n04PositiveRight i)
    (fun side p => (n04PositiveSourceMap (X.src i side) (W.A X.e₀) z p).2)
  let A := rawEndpointAngularData (n04PositiveLeft i) (n04PositiveRight i) Ψ
  have hc : (fun side (j : Fin (n + 2)) =>
      A side j p.2 - if (j : ℕ) = 0 then p.2 else 0) = G.angularCoefficients z i p.2 := by
    funext side j
    change radialBoundaryJet
      (oneSidedBoundaryTaylorRepresentative (n + 2) (n04PositiveEndpoint i side)
        (fun q => (n04PositiveSourceMap (X.src i side) (W.A X.e₀) z q).2))
      (n04PositiveEndpoint i side) j p.2 - _ = _
    rw [radialBoundaryJet_oneSidedBoundaryTaylorRepresentative _ _ _ (by omega)]
    rfl
  exact (n04PositiveGeometry_angularKernel_formula (n + 1)
    (n04PositiveLeft i) (n04PositiveRight i)
    (endpointAngularWidth (n + 1) (n04PositiveLeft i) (n04PositiveRight i)
      (G.buffer.centerLeft i) (G.buffer.centerRight i) (G.M i)⁻¹ (G.M i)) p.1 p.2 A).trans
      (congrArg (fun a => p.2 + G.angularKernel i (a, p.1)) hc)

end N04PositiveGeometryControlData

theorem n04PositiveGeometry_controlled_angularKernel_bounds
    {W : N04RealizationStart} {X : N04RealizationChoice W} {n : ℕ}
    (G : N04PositiveGeometryControlledFamily W X n) {A : ℝ} (hA : 1 ≤ A) :
    ∀ k : ℕ, ∃ C Q : ℝ, 0 < C ∧ 0 ≤ Q ∧
      ∀ (i : N04PositiveComponent W.D.a W.D.b (deriv W.D.w))
        (a : N04PositiveRadialCoefficients (n + 1)),
        ‖a‖ ≤ A * W.U.E0 (W.U.sample (X.cell i)) ^ A →
      ∀ x ∈ Icc W.D.a W.D.b,
        ‖iteratedFDeriv ℝ k (G.toN04PositiveGeometryControlData.angularKernel i) (a, x)‖ ≤
          C * W.U.E0 (W.U.sample (X.cell i)) ^ Q := by
  let I := N04PositiveComponent W.D.a W.D.b (deriv W.D.w)
  let E : I → ℝ := fun i => W.U.E0 (W.U.sample (X.cell i))
  have hE (i) : 1 ≤ E i := (W.floor _).trans (le_enlargedMaterialData_E0 W.T _)
  let P := N04PositiveRadialCoefficients (n + 1)
  let J := {z : I × (P × ℝ) // ‖z.2.1‖ ≤ A * E z.1 ^ A ∧ z.2.2 ∈ Icc W.D.a W.D.b}
  let e : J → I := fun z => z.1.1
  let p : J → P × ℝ := fun z => z.1.2
  have hraw : HasPositiveEnvelope E (fun i => A * E i ^ A) :=
    ⟨A, A, zero_lt_one.trans_le hA, zero_lt_one.trans_le hA, fun _ => le_rfl⟩
  have hrad : HasPositiveEnvelope E (fun _ => |W.D.a| + |W.D.b|) :=
    hasPositiveEnvelope_const E hE _
  have hp : HasPositiveEnvelope (fun z : J => E (e z)) (fun z => ‖p z‖) := by
    apply (n04PositiveGeometry_envelope_reindex (hraw.add hE hrad) e).mono
    intro z
    have hx : |z.1.2.2| ≤ |W.D.a| + |W.D.b| := by
      apply abs_le.mpr
      have hz := z.2.2
      constructor <;> linarith only [hz.1, hz.2, neg_abs_le W.D.a,
        le_abs_self W.D.b, abs_nonneg W.D.a, abs_nonneg W.D.b]
    rw [Prod.norm_def, Real.norm_eq_abs]
    exact max_le (z.2.1.trans (le_add_of_nonneg_right
      (add_nonneg (abs_nonneg _) (abs_nonneg _))))
      (hx.trans (le_add_of_nonneg_left (mul_nonneg (zero_le_one.trans hA)
        (Real.rpow_nonneg (zero_le_one.trans (hE _)) _))))
  have hf : Continuous (deriv W.D.w) :=
    (n04b_profileGeometry_of_through03 W.through03).2.2.1.1.continuous_deriv (by simp)
  have hend (side : Bool) : HasPositiveEnvelope E (fun i => |n04PositiveEndpoint i side|) := by
    apply hrad.mono
    intro i
    have hi := n04PositiveComponent_bounds hf i
    have he : n04PositiveEndpoint i side ∈ Icc W.D.a W.D.b := by
      cases side with
      | false => exact ⟨hi.1, hi.2.1.le.trans hi.2.2⟩
      | true => exact ⟨hi.1.trans hi.2.1.le, hi.2.2⟩
    apply abs_le.mpr
    constructor <;> linarith only [he.1, he.2, neg_abs_le W.D.a,
        le_abs_self W.D.b, abs_nonneg W.D.a, abs_nonneg W.D.b]
  obtain ⟨B, hB, hmat⟩ := n04PositiveGeometry_controlledFamily_material_bounds G
  have hwidth : HasPositiveEnvelope E (fun i =>
      |(endpointAngularWidth (n + 1) (n04PositiveLeft i) (n04PositiveRight i)
        (G.buffer.centerLeft i) (G.buffer.centerRight i) (G.M i)⁻¹ (G.M i))⁻¹|) :=
    ⟨B, B, zero_lt_one.trans_le hB, zero_lt_one.trans_le hB, hmat.angular_width⟩
  have hb := n04PositiveGeometry_angularKernel_bounds (fun z : J => hE (e z)) (n + 1) p
    (fun z => n04PositiveLeft (e z)) (fun z => n04PositiveRight (e z))
    (fun z => endpointAngularWidth (n + 1) (n04PositiveLeft (e z)) (n04PositiveRight (e z))
      (G.buffer.centerLeft (e z)) (G.buffer.centerRight (e z)) (G.M (e z))⁻¹ (G.M (e z))) hp
    (n04PositiveGeometry_envelope_reindex (hend false) e)
    (n04PositiveGeometry_envelope_reindex (hend true) e)
    (n04PositiveGeometry_envelope_reindex hwidth e)
  intro k
  obtain ⟨C, Q, hC, hQ, hb⟩ := hb.jets k
  exact ⟨C, Q, hC, hQ.le, fun i a ha x hx => hb ⟨(i, (a, x)), ha, hx⟩⟩

end ContinuousFlexibility.Analysis
