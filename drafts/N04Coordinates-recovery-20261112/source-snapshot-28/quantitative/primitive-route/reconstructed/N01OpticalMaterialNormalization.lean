import ContinuousFlexibility.Analysis.MaterialEnvelopeNormalization

/-!
# Material normalization before choosing the positive reference family

The actual envelope majorant preserves the same reference, spaces,
geometric data and Through03 witness. Its values are at least one, so a
later coefficient/exponent pair can be packed into the frozen single
constant. The same raw optical lower bound survives because increasing
the envelope decreases its negative power. No canonical family is
chosen before this normalization.
-/

noncomputable section

namespace ContinuousFlexibility.Analysis

open Set ContinuousFlexibility.Statements

theorem nonlinearPropertiesThrough03_optical_enlargedMaterialData
    {D : ReferenceData} {T : MaterialData} {S : PhysicalSpacesData}
    {C : NonlinearGeometryData S} {R : ReturnEquationData S}
    {L : ReturnCorrectionData S} {base loss : ℕ} {ε K : ℝ}
    (hT : IsMaterialData D T) (hS : IsPhysicalSpaces D T S)
    (hN : NonlinearPropertiesThrough03 D T S C R L base loss ε)
    (hK : 0 < K)
    (hoptical : ∀ m x, x ∈ Ioo (C.left m) (C.right m) →
      K⁻¹ * T.E0 (T.sample (C.cell m)) ^ (-K) *
        min (x - C.left m) (C.right m - x) ≤ -deriv D.w x / (x * D.w x)) :
    IsMaterialData D (enlargedMaterialData T) ∧
    IsPhysicalSpaces D (enlargedMaterialData T) S ∧
    NonlinearPropertiesThrough03 D (enlargedMaterialData T) S C R L base loss ε ∧
    (∀ x ∈ Ioo D.a D.b, 1 ≤ (enlargedMaterialData T).E0 x) ∧
    ∀ m x, x ∈ Ioo (C.left m) (C.right m) →
      K⁻¹ * (enlargedMaterialData T).E0
          ((enlargedMaterialData T).sample (C.cell m)) ^ (-K) *
        min (x - C.left m) (C.right m - x) ≤ -deriv D.w x / (x * D.w x) := by
  have hD : IsAccumulatingProfile D := hN.1.1.1.1
  refine ⟨isMaterialData_enlargedMaterialData hD hT,
    isPhysicalSpaces_enlargedMaterialData hS,
    nonlinearPropertiesThrough03_enlargedMaterialData hT hN,
    (fun x hx => one_le_enlargedMaterialData_E0 hT hx), ?_⟩
  intro m x hx
  have hsample : T.sample (C.cell m) ∈ Ioo D.a D.b :=
    materialSample_mem_interval hD hT (C.cell m)
  have hE : 0 < T.E0 (T.sample (C.cell m)) := (hT.2.1 _ hsample).2.2.1
  have hE' : 0 < (enlargedMaterialData T).E0 (T.sample (C.cell m)) :=
    zero_lt_one.trans_le (one_le_enlargedMaterialData_E0 hT hsample)
  have hpower : (enlargedMaterialData T).E0 (T.sample (C.cell m)) ^ (-K) ≤
      T.E0 (T.sample (C.cell m)) ^ (-K) := by
    rw [Real.rpow_neg hE'.le, Real.rpow_neg hE.le]
    exact inv_anti₀ (Real.rpow_pos_of_pos hE K)
      (Real.rpow_le_rpow hE.le (le_enlargedMaterialData_E0 T _) hK.le)
  have hmin : 0 ≤ min (x - C.left m) (C.right m - x) :=
    le_min (sub_nonneg.mpr hx.1.le) (sub_nonneg.mpr hx.2.le)
  exact (mul_le_mul_of_nonneg_right
    (mul_le_mul_of_nonneg_left hpower (inv_pos.mpr hK).le) hmin).trans
    (hoptical m x hx)

end ContinuousFlexibility.Analysis
