import ContinuousFlexibility.Analysis.N01ControlLengthBound
import ContinuousFlexibility.Analysis.MaterialPlateauRadialLoss
import ContinuousFlexibility.Analysis.DisjointIntervalPacking

/-!
# Quantitative overlap of the expanded control plateaus

At a fixed radius, every expanded plateau containing that radius has
an actual component whose length is bounded below by the same positive
quantity. The original components are pairwise disjoint and lie in the
annulus. Lebesgue interval packing therefore bounds the number of
overlapping expanded supports by one fixed endpoint-weight power.
-/

noncomputable section

namespace ContinuousFlexibility.Statements

open Set
open ContinuousFlexibility.Analysis

theorem N01Properties.controlPlateau_overlap_bound
    {D : ReferenceData} {T : MaterialData} {S : PhysicalSpacesData}
    {C : NonlinearGeometryData S} {base loss : ℕ} {ε : ℝ}
    (hN : N01Properties D T S C base loss ε) (hT : IsMaterialData D T) :
    ∃ K A : ℝ, 0 < K ∧ 0 ≤ A ∧ ∀ t ∈ Ioo D.a D.b,
      {m : ℕ | t ∈ Icc
        (C.left m - endpointPlateauWidth D (C.left m) (C.right m))
        (C.right m + endpointPlateauWidth D (C.left m) (C.right m))}.Finite ∧
      ({m : ℕ | t ∈ Icc
        (C.left m - endpointPlateauWidth D (C.left m) (C.right m))
        (C.right m + endpointPlateauWidth D (C.left m) (C.right m))}.ncard : ℝ) ≤
        K * T.E0 t ^ A := by
  obtain ⟨c, R, hc, hR, hlength⟩ := hN.actualCell_length_lower_bound hT
  obtain ⟨K, A, hK, hA, hweight⟩ := materialCell_plateau_radial_weight_bound hN.1.1 hT hR.le
  obtain ⟨_, _, hcells⟩ := hN.actualCell_travel_lower_bound
  have hgeom : RadialProfileGeometry D := hN.1.1.choose_spec.1
  have hcontrol : controlGeometryConditions D S C := hN.2.2.2.1
  have hwidth : 0 < D.b - D.a := sub_pos.mpr hgeom.2.1
  refine ⟨(D.b - D.a) * K / c, A, div_pos (mul_pos hwidth hK) hc, hA,
    fun t ht => ?_⟩
  let labels : Set ℕ := {m | t ∈ Icc
    (C.left m - endpointPlateauWidth D (C.left m) (C.right m))
    (C.right m + endpointPlateauWidth D (C.left m) (C.right m))}
  have hEt : 0 < T.E0 t := (hT.2.1 t ht).2.2.1
  have hden : 0 < K * T.E0 t ^ A := mul_pos hK (Real.rpow_pos_of_pos hEt _)
  let δ : ℝ := c / (K * T.E0 t ^ A)
  have hδ : 0 < δ := div_pos hc hden
  have hinterval : ∀ m ∈ labels,
      D.a ≤ C.left m ∧ C.left m ≤ C.right m ∧ C.right m ≤ D.b :=
    fun m _ => ⟨(hcontrol.1 m).1.le, (hcontrol.1 m).2.1.le, (hcontrol.1 m).2.2.le⟩
  have hdisjoint : labels.PairwiseDisjoint (fun m => Ioo (C.left m) (C.right m)) :=
    fun m _ n _ hmn => hcontrol.2.2.1 m n hmn
  have hminimum : ∀ m ∈ labels, δ ≤ C.right m - C.left m := by
    intro m hm
    obtain ⟨_, j, hj, _⟩ := hcells m
    have hE : 0 < radialE (D.cellIndex j) := Real.exp_pos _
    have hER : 0 < radialE (D.cellIndex j) ^ R := Real.rpow_pos_of_pos hE _
    have hW := hweight j (C.left m) (C.right m)
      (hcontrol.1 m).1 (hcontrol.1 m).2.1 (hcontrol.1 m).2.2 hj t hm
    have hcl : c ≤ (K * T.E0 t ^ A) * (C.right m - C.left m) := by
      calc
        _ = c * (radialE (D.cellIndex j) ^ R * radialE (D.cellIndex j) ^ (-R)) := by
          rw [← Real.rpow_add hE R (-R), add_neg_cancel, Real.rpow_zero, mul_one]
        _ = radialE (D.cellIndex j) ^ R * (c * radialE (D.cellIndex j) ^ (-R)) := by ring
        _ ≤ radialE (D.cellIndex j) ^ R * (C.right m - C.left m) :=
          mul_le_mul_of_nonneg_left (hlength m j hj) hER.le
        _ ≤ (K * T.E0 t ^ A) * (C.right m - C.left m) :=
          mul_le_mul_of_nonneg_right hW (sub_pos.mpr (hcontrol.1 m).2.1).le
    exact (div_le_iff₀ hden).mpr (by simpa only [mul_comm] using hcl)
  obtain ⟨hfinite, hcount⟩ := finite_ncard_mul_le_of_disjoint_Ioo
    labels C.left C.right hgeom.2.1.le hδ hinterval hdisjoint hminimum
  refine ⟨hfinite, ?_⟩
  calc
    (labels.ncard : ℝ) ≤ (D.b - D.a) / δ := (le_div_iff₀ hδ).mpr hcount
    _ = ((D.b - D.a) * K / c) * T.E0 t ^ A := by
      dsimp only [δ]
      rw [div_div_eq_mul_div]
      ring

end ContinuousFlexibility.Statements
