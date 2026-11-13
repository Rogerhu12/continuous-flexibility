import ContinuousFlexibility.Analysis.N04PositiveGeometryControlledLabelPrefix
import ContinuousFlexibility.Analysis.N04PositiveGeometryControlledRootLabelSample
import ContinuousFlexibility.Analysis.N04PositiveGeometryBoundaryFormulaPrefix

/-!
# Label displacements at the original positive sample

The original circle estimate carries a height factor even at parameter
order zero. A uniform height bound absorbs precisely that extra factor.
Every positive parameter order keeps the full height at the supplied
positive midpoint, with the low order chosen before all jet prefixes.
-/

noncomputable section

namespace ContinuousFlexibility.Analysis

open Set ContinuousFlexibility.Statements

private theorem height_le_parameterWeight
    {H L : ℝ} (hH : 0 ≤ H) (hHL : H ≤ L) (hL : 1 ≤ L) (k : ℕ) :
    H ≤ L * parameterHeightWeight H k := by
  by_cases hk : k = 0
  · simpa only [parameterHeightWeight, if_pos hk, mul_one] using hHL
  · simpa only [parameterHeightWeight, if_neg hk] using
      le_mul_of_one_le_left hH hL

/-- Any actual circle displacement prefix transfers to the retained
positive sample, including its zeroth value and entire angular reserve. -/
theorem n04PositiveGeometry_labelDefect_sample_bridge
    (W : N04RealizationStart) (X : N04RealizationChoice W)
    (base : ℕ) (ε : ℝ) (reserve : ℕ)
    (f : Bool → ℕ → (StateDirections W.S × ℝ) × ℝ → ℝ)
    (hprefix : N04LabelDefectPrefix (pairGrading (sectorGrading W.S) realGrading)
      (sectorNeighborhood W.S base ε ε)
      (fun b side m θ x => iteratedDeriv b (fun α => f side m (x, α)) θ)
      (fun m => W.T.H (W.T.sample m) ^ (3 / 4 : ℝ)) base reserve) :
    ∃ low : ℕ, base ≤ low ∧ ∀ K : ℕ, ∃ shift : ℕ,
      ∀ s : ℕ, ∃ A : ℝ, 1 ≤ A ∧
      ∀ i side m, (X.src i side).val = some m →
      ∀ J : SmoothDirections (sectorNeighborhood W.S base ε ε ×ˢ univ) (f (!side) m),
      ∀ z ∈ sectorNeighborhood W.S base ε ε,
      pairGrading (sectorGrading W.S) realGrading low z ≤ 1 → ∀ θ : ℝ,
      ∀ R : ℝ, 1 ≤ R →
      pairGrading (sectorGrading W.S) realGrading (low + s + shift * K + 1) z ≤ R →
      N04BoundaryWordBounds J K s reserve z θ
        (fun v => pairGrading (sectorGrading W.S) realGrading low v ≤ 1 ∧
          pairGrading (sectorGrading W.S) realGrading (low + s + shift * K + 1) v ≤ R)
        (A * W.U.E0 (W.U.sample (X.cell i)) ^ A)
        (W.U.H (W.U.sample (X.cell i)) ^ (3 / 4 : ℝ))
        (R ^ (1 / (((s + shift * K : ℕ) : ℝ) + 1))) shift := by
  let low : ℕ := hprefix.choose
  let heightData := n04PositiveGeometry_sample_height_bound W X
    (by norm_num : (0 : ℝ) < 3 / 4)
  let L : ℝ := max 1 heightData.choose
  have hL : 1 ≤ L := le_max_left _ _
  refine ⟨low, hprefix.choose_spec.1, fun K => ?_⟩
  let prefix := hprefix.choose_spec.2 K
  let shift : ℕ := prefix.choose
  refine ⟨shift, fun s => ?_⟩
  let orderData := prefix.choose_spec s
  let B₀ : ℝ := orderData.choose
  let transfer := n04PositiveGeometry_positiveSource_circle_material_weight W X
    (3 / 4 : ℝ) (A := 0) (C := B₀) (by norm_num)
    (zero_le_one.trans orderData.choose_spec.1)
  let B : ℝ := transfer.choose
  let packData := coefficientEnvelope_pack (B * L) B
  let A₀ : ℝ := packData.choose
  let A : ℝ := max 1 A₀
  have hA : 1 ≤ A := le_max_left _ _
  refine ⟨A, hA, ?_⟩
  intro i side m hm J z hz hzlow θ R hR hzR
  let E : ℝ := W.U.E0 (W.U.sample (X.cell i))
  let H : ℝ := W.U.H (W.U.sample (X.cell i)) ^ (3 / 4 : ℝ)
  let M : ℝ := A * E ^ A
  let t : ℝ := R ^ (1 / (((s + shift * K : ℕ) : ℝ) + 1))
  have hE : 1 ≤ E := (W.floor _).trans (le_enlargedMaterialData_E0 W.T _)
  have hH : 0 ≤ H := (heightData.choose_spec.2 i).1
  have hHL : H ≤ L := (heightData.choose_spec.2 i).2.trans (le_max_right _ _)
  have hcost : (B * L) * E ^ B ≤ M :=
    (packData.choose_spec.2 E hE).trans
      (mul_le_mul (le_max_right _ _) (Real.rpow_le_rpow_of_exponent_le hE (le_max_right _ _))
        (Real.rpow_nonneg (zero_le_one.trans hE) _) (zero_le_one.trans hA))
  have hsample (k : ℕ) : B₀ * W.T.H (W.T.sample m) ^ (3 / 4 : ℝ) ≤
      M * parameterHeightWeight H k := by
    have hraw : B₀ * W.T.H (W.T.sample m) ^ (3 / 4 : ℝ) ≤ B * E ^ B * H := by
      simpa only [Real.rpow_zero, mul_one] using transfer.choose_spec.2 i side m hm
    calc
      _ ≤ B * E ^ B * H := hraw
      _ ≤ B * E ^ B * (L * parameterHeightWeight H k) :=
        mul_le_mul_of_nonneg_left (height_le_parameterWeight hH hHL hL k)
          (mul_nonneg (zero_le_one.trans transfer.choose_spec.1)
            (Real.rpow_nonneg (zero_le_one.trans hE) _))
      _ = ((B * L) * E ^ B) * parameterHeightWeight H k := by ring
      _ ≤ M * parameterHeightWeight H k :=
        mul_le_mul_of_nonneg_right hcost (parameterHeightWeight_nonneg hH k)
  have htpow (u : ℕ) : t ^ u =
      R ^ ((u : ℝ) / (((s + shift * K : ℕ) : ℝ) + 1)) := by
    dsimp only [t]
    rw [← Real.rpow_natCast, ← Real.rpow_mul (zero_le_one.trans hR)]
    congr 1
    ring
  apply n04PositiveGeometry_boundaryWord_of_angular J (smoothDirections_angularStateSlice J)
    K s reserve z hz θ _ M H t shift
  intro k hk u hu d hd v hv
  have hraw := orderData.choose_spec.2 k hk u hu (u + d) (Nat.add_le_add_left hd u)
    (!side) m θ (smoothDirections_angularStateSlice J (u + d) θ) z hz hzlow v
    (fun j => (hv j).1) R hR hzR (fun j => (hv j).2)
  have hnorm : ‖(smoothDirections_angularStateSlice J (u + d) θ).D k z v‖ ≤
      B₀ * W.T.H (W.T.sample m) ^ (3 / 4 : ℝ) *
        R ^ (((u + shift * k : ℕ) : ℝ) / (((s + shift * K : ℕ) : ℝ) + 1)) := by
    simpa only [Real.norm_eq_abs] using hraw
  exact (hnorm.trans (mul_le_mul_of_nonneg_right (hsample k)
    (Real.rpow_nonneg (zero_le_one.trans hR) _))).trans_eq
      (congrArg (fun a : ℝ => M * parameterHeightWeight H k * a)
        (htpow (u + shift * k))).symm

end ContinuousFlexibility.Analysis
