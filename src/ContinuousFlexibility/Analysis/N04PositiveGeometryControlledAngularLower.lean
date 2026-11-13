import ContinuousFlexibility.Analysis.N04PositiveGeometryInverseBoundsBoundaryData

/-!
# The actual angular lower bound of the selected transport

The chosen endpoint interpolation keeps half its original lower bound
on the entire physical cylinder. Its reciprocal is charged to the same
stored material envelope, without selecting another width or radius.
-/

noncomputable section

namespace ContinuousFlexibility.Analysis

open Set ContinuousFlexibility.Statements

variable {W : N04RealizationStart} {X : N04RealizationChoice W} {n : ℕ}

theorem n04PositiveGeometry_controlled_angle_lower
    (G : N04PositiveGeometryControlledFamily W X n)
    {z : AnnularState W.S × ℝ} (hz : z ∈ stateNeighborhood W.S W.C G.base G.ε)
    (hs : stateSector W.S z.1)
    (i : N04PositiveComponent W.D.a W.D.b (deriv W.D.w)) (r θ : ℝ) :
    (G.M i)⁻¹ / 2 ≤
      deriv (fun η => G.toN04PositiveGeometryControlData.angle z i (r, η)) θ := by
  have ho := G.buffer.ordered i
  exact n04Realization_oneSidedTransport_angle_lower n ho.1
    (ho.2.1.trans (ho.2.2.1.trans ho.2.2.2.1)) ho.2.2.2.2
    (inv_pos.mpr (zero_lt_one.trans_le (G.input_one i)))
    (inv_le_one_of_one_le₀ (G.input_one i)) (zero_le_one.trans (G.input_one i))
    (fun side => n04Coordinates_actualAtlas_positiveEndpoint_of_source
      W.hT W.hS W.through03 W.field X.e₀ (X.src i side)
      (stateNeighborhood_mono W.S W.C G.base_le G.radius_le hz) hs)
    (G.endpoint_bounds z hz hs i) r θ

theorem n04PositiveGeometry_controlled_angle_inverse_slope_bound
    (G : N04PositiveGeometryControlledFamily W X n)
    {z : AnnularState W.S × ℝ} (hz : z ∈ stateNeighborhood W.S W.C G.base G.ε)
    (hs : stateSector W.S z.1)
    (i : N04PositiveComponent W.D.a W.D.b (deriv W.D.w)) (r θ : ℝ) :
    |(deriv (fun η => G.toN04PositiveGeometryControlData.angle z i (r, η)) θ)⁻¹| ≤
      2 * G.M i := by
  have hM : 0 < G.M i := zero_lt_one.trans_le (G.input_one i)
  have hκ : 0 < (G.M i)⁻¹ / 2 := half_pos (inv_pos.mpr hM)
  have hb := n04PositiveGeometry_controlled_angle_lower G hz hs i r θ
  rw [abs_of_pos (inv_pos.mpr (hκ.trans_le hb))]
  calc
    _ ≤ ((G.M i)⁻¹ / 2)⁻¹ := by
      simpa only [one_div] using one_div_le_one_div_of_le hκ hb
    _ = 2 * G.M i := by field_simp [hM.ne']

end ContinuousFlexibility.Analysis
