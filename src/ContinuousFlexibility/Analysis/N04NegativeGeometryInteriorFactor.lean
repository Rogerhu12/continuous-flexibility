module

public import ContinuousFlexibility.Analysis.N04NegativeGeometryGaugePerturbation
public import ContinuousFlexibility.Analysis.PositiveEndpointCutoff

/-!
# An explicit nonconstant interior height multiplier

The existing smooth cutoff is placed strictly between the left endpoint
and the fixed middle. Adding one gives a multiplier in `[1,2]`, equal to
two at the cutoff center and identically one near both endpoints and the
entire fixed middle.
-/

@[expose] public section

noncomputable section

namespace ContinuousFlexibility.Analysis

open Set Filter ContinuousFlexibility.Statements
open scoped Topology ContDiff

def n04NegativeGeometryInteriorFactor (l c : ℝ) (p : PolarPoint) : ℝ :=
  1 + positiveEndpointCutoff ((l + c) / 2) ((c - l) / 4) p.1

/-- The multiplier is exactly two at the center of its interior bump. -/
theorem n04NegativeGeometry_interiorFactor_center (l c θ : ℝ) :
    n04NegativeGeometryInteriorFactor l c ((l + c) / 2, θ) = 2 := by
  have hc : positiveEndpointCutoff ((l + c) / 2) ((c - l) / 4) ((l + c) / 2) = 1 :=
    (positiveEndpointCutoff_one_germ ((l + c) / 2) ((c - l) / 4)).self_of_nhds
  change 1 + positiveEndpointCutoff ((l + c) / 2) ((c - l) / 4) ((l + c) / 2) = 2
  rw [hc]
  norm_num

/-- The same explicit factor has every spatial property needed for
admissibility. No state parameter enters this assertion. -/
theorem n04NegativeGeometry_interiorFactor_spec {l r c d : ℝ}
    (hlc : l < c) (hcr : c ≤ r) :
    N04NegativeGeometryHeightFactor (n04NegativeGeometryInteriorFactor l c) l r c d := by
  let a : ℝ := (l + c) / 2
  let δ : ℝ := (c - l) / 4
  have hδ : 0 < δ := div_pos (sub_pos.mpr hlc) (by norm_num)
  have hone {x : ℝ} (hsep : δ ≤ |x - a|) :
      (fun y => 1 + positiveEndpointCutoff a δ y) =ᶠ[𝓝 x] (fun _ => (1 : ℝ)) := by
    filter_upwards [positiveEndpointCutoff_zero_germ_of_separation hδ hsep] with y hy
    change 1 + positiveEndpointCutoff a δ y = 1
    rw [show positiveEndpointCutoff a δ y = 0 from hy, add_zero]
  have hleft : δ ≤ |l - a| := by
    have h := neg_le_abs (l - a)
    dsimp only [a, δ] at *
    linarith
  have hright {x : ℝ} (hx : c ≤ x) : δ ≤ |x - a| := by
    have h := le_abs_self (x - a)
    dsimp only [a, δ] at *
    linarith
  refine {
    smooth := contDiff_const.add ((contDiff_positiveEndpointCutoff a δ).comp contDiff_fst)
    positive := ?_
    bound := ?_
    endpoint := ?_
    period := fun _ _ => rfl
    even := fun _ _ => rfl
    middle := ?_ }
  · intro p
    change 0 < 1 + positiveEndpointCutoff a δ p.1
    linarith [positiveEndpointCutoff_nonneg a δ p.1]
  · intro p
    change 1 + positiveEndpointCutoff a δ p.1 ≤ 2 ∧
      (1 + positiveEndpointCutoff a δ p.1)⁻¹ ≤ 2
    have hlow : 1 ≤ 1 + positiveEndpointCutoff a δ p.1 :=
      le_add_of_nonneg_right (positiveEndpointCutoff_nonneg a δ p.1)
    have hinv : (1 + positiveEndpointCutoff a δ p.1)⁻¹ ≤ 1 := by
      simpa only [one_div, inv_one] using
        one_div_le_one_div_of_le (show (0 : ℝ) < 1 by norm_num) hlow
    exact ⟨by linarith [positiveEndpointCutoff_le_one a δ p.1], hinv.trans (by norm_num)⟩
  · intro side θ
    cases side with
    | false => exact (hone hleft).comp_tendsto (continuous_fst.tendsto (l, θ))
    | true => exact (hone (hright hcr)).comp_tendsto (continuous_fst.tendsto (r, θ))
  · intro x hx θ
    exact (hone (hright hx.1)).comp_tendsto (continuous_fst.tendsto (x, θ))

/-- The bump center is inside the physical positive interval. -/
theorem n04NegativeGeometry_interiorFactor_center_mem {l r c : ℝ}
    (hlc : l < c) (hcr : c ≤ r) : (l + c) / 2 ∈ Ioo l r := by
  constructor <;> linarith

/-- A canonical multiplier family from the existing normalization buffer. -/
def n04NegativeGeometryBufferFactors {a b : ℝ} {f : ℝ → ℝ} {K : Set ℝ}
    (B : N04PositiveNormalizationBuffer a b f K) :
    N04PositiveComponent a b f → PolarPoint → ℝ :=
  fun i => n04NegativeGeometryInteriorFactor (n04PositiveLeft i) (B.centerLeft i)

theorem n04NegativeGeometry_bufferFactors_spec
    {a b : ℝ} {f : ℝ → ℝ} {K : Set ℝ}
    (B : N04PositiveNormalizationBuffer a b f K) (i : N04PositiveComponent a b f) :
    N04NegativeGeometryHeightFactor (n04NegativeGeometryBufferFactors B i)
      (n04PositiveLeft i) (n04PositiveRight i) (B.centerLeft i) (B.centerRight i) := by
  have h := B.ordered i
  exact n04NegativeGeometry_interiorFactor_spec h.1
    (h.2.1.trans (h.2.2.1.trans (h.2.2.2.1.trans h.2.2.2.2))).le

end ContinuousFlexibility.Analysis
