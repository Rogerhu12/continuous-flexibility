import ContinuousFlexibility.Analysis.N05ReferenceHeightWindow

/-!
# Zeroth primitive values on the actual reference pieces

The unit-strip estimates are evaluated at the affine normalization of an
actual physical point. This recovers the prescribed height ratios and the
inverse physical length on the same canonical data, without relabelling
pieces or choosing a different nonlinear witness.

The reference-jet premise is an explicit hypothesis of these lemmas.
Producing it from a full nonlinear construction is a separate obligation
of the shared interface.
-/

noncomputable section

namespace ContinuousFlexibility.Statements

open Set
open CanonicalGeometry

theorem n05_reference_unitPoint_normalization
    {S : PhysicalSpacesData} (K : CanonicalData S) (m : ℕ)
    {r θ : ℝ} (hr : r ∈ Ioo (K.physicalLeft m) (K.physicalRight m)) :
    let p : PolarPoint := ((r - K.physicalLeft m) /
      (K.physicalRight m - K.physicalLeft m), θ)
    p ∈ unitStrip ∧ physicalUnitPoint K m p = (r, θ) := by
  let a : ℝ := K.physicalLeft m
  let b : ℝ := K.physicalRight m
  have hab : 0 < b - a := sub_pos.mpr (hr.1.trans hr.2)
  have hleft : 0 < (r - a) / (b - a) := div_pos (sub_pos.mpr hr.1) hab
  have hright : (r - a) / (b - a) < 1 := (div_lt_one hab).mpr (by linarith only [hr.2])
  refine ⟨⟨⟨hleft, hright⟩, mem_univ _⟩, ?_⟩
  apply Prod.ext
  · change a + (b - a) * ((r - a) / (b - a)) = r
    field_simp [hab.ne'] <;> ring
  · rfl

/-- Zeroth-order bounds are literal values of the existing primitive atoms. -/
theorem n05_reference_primitive_atom_value_bound
    {D : ReferenceData} {T : MaterialData} {S : PhysicalSpacesData}
    {C : NonlinearGeometryData S} {L : ReturnCorrectionData S} {K : CanonicalData S}
    (hJ : ReferenceJets D T S C L K) :
    ∃ B : ℝ, 0 < B ∧ ∀ m a p, p ∈ unitStrip →
      |atom D T S C L K (C.referenceState, 0) m a p| ≤
        B * T.E0 (T.sample (K.cell m)) ^ B := by
  obtain ⟨B, hB, hb⟩ := hJ.2 0
  refine ⟨B, hB, fun m a p hp => ?_⟩
  simpa only [mixedDerivative, iteratedDeriv_zero, Prod.eta] using
    hb m a p hp 0 0 (by omega)

/-- Both actual material-height ratios and the inverse physical length
are consequences of the primitive reference jets. -/
theorem n05_reference_primitive_height_ratios_and_width
    {D : ReferenceData} {T : MaterialData} {S : PhysicalSpacesData}
    {C : NonlinearGeometryData S} {L : ReturnCorrectionData S} {K : CanonicalData S}
    {base loss : ℕ} {ε : ℝ}
    (h04 : N04Properties D T S C L K base loss ε)
    (hJ : ReferenceJets D T S C L K) :
    ∃ B : ℝ, 0 < B ∧
      (∀ m r, r ∈ Ioo (K.physicalLeft m) (K.physicalRight m) →
        T.H r / T.H (T.sample (K.cell m)) ≤ B * T.E0 (T.sample (K.cell m)) ^ B ∧
        T.H (T.sample (K.cell m)) / T.H r ≤ B * T.E0 (T.sample (K.cell m)) ^ B) ∧
      (∀ m, (K.physicalRight m - K.physicalLeft m)⁻¹ ≤
        B * T.E0 (T.sample (K.cell m)) ^ B) := by
  obtain ⟨B, hB, hb⟩ := n05_reference_primitive_atom_value_bound hJ
  refine ⟨B, hB, ?_, ?_⟩
  · intro m r hr
    let p : PolarPoint := ((r - K.physicalLeft m) /
      (K.physicalRight m - K.physicalLeft m), 0)
    obtain ⟨hp, hpoint⟩ := n05_reference_unitPoint_normalization K m (θ := 0) hr
    change physicalUnitPoint K m p = (r, (0 : ℝ)) at hpoint
    have hratio := hb m .ratioH p hp
    have hinverse := hb m .ratioHInverse p hp
    simp only [atom] at hratio hinverse
    rw [hpoint] at hratio hinverse
    exact ⟨(le_abs_self _).trans hratio, (le_abs_self _).trans hinverse⟩
  · intro m
    have hp : ((1 / 2 : ℝ), (0 : ℝ)) ∈ unitStrip := by
      exact ⟨⟨by norm_num, by norm_num⟩, mem_univ _⟩
    have hw := hb m .physicalLengthInverse (1 / 2, 0) hp
    change |(K.physicalRight m - K.physicalLeft m)⁻¹| ≤ _ at hw
    exact (le_abs_self _).trans hw

/-- The primitive material ratios yield a cubic window on every actual
reference cell meeting an actual reference piece. -/
theorem n05_reference_primitive_cubic_window
    {D : ReferenceData} {T : MaterialData} {S : PhysicalSpacesData}
    {C : NonlinearGeometryData S} {L : ReturnCorrectionData S} {K : CanonicalData S}
    {base loss : ℕ} {ε : ℝ}
    (hD : IsAccumulatingProfile D) (hT : IsMaterialData D T)
    (h04 : N04Properties D T S C L K base loss ε)
    (hJ : ReferenceJets D T S C L K) :
    ∃ A : ℝ, 0 < A ∧ ∀ m j r,
      r ∈ Ioo (K.physicalLeft m) (K.physicalRight m) → r ∈ D.cells j →
        |radialS (D.cellIndex j) - radialS (D.cellIndex (K.cell m))| ≤
          A * (radialQ (D.cellIndex (K.cell m)) + 1) := by
  obtain ⟨B, hB, hratio, _⟩ := n05_reference_primitive_height_ratios_and_width h04 hJ
  exact n05_reference_cubic_window_of_height_ratios hD hT hB hratio

end ContinuousFlexibility.Statements
