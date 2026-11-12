import ContinuousFlexibility.Analysis.N07aNeighborhood
import ContinuousFlexibility.Analysis.MaterialSampleBounds

/-!
# One actual neighborhood controls every current atom

The zero-order current estimate and the material height gain give a
uniform radius for all pieces and atoms. The smaller neighborhood keeps
the actual directional tower by restriction.
-/

noncomputable section

namespace ContinuousFlexibility.Analysis

open Set ContinuousFlexibility.Statements

attribute [local instance]
  n07aNonlinearAnnularGroup n07aNonlinearAnnularModule
  n07aNonlinearAnnularAddGroup n07aNonlinearAnnularSMul n07aNonlinearAnnularSub
  n07aNonlinearAnnularParameterGroup n07aNonlinearAnnularParameterModule
  n07aNonlinearAnnularParameterAddGroup n07aNonlinearAnnularParameterSMul
  n07aNonlinearAnnularParameterSub
  n07aNonlinearDirectionsGroup n07aNonlinearDirectionsModule
  n07aNonlinearDirectionsAddGroup n07aNonlinearDirectionsSMul n07aNonlinearDirectionsSub
  n07aNonlinearSectorParameterGroup n07aNonlinearSectorParameterModule
  n07aNonlinearSectorParameterAddGroup n07aNonlinearSectorParameterSMul
  n07aNonlinearSectorParameterSub

/-- No piece, point or atom is chosen before the new radius. The current
jets on that radius are the restriction of the original actual tower. -/
theorem n04Coordinates_currentAtoms_uniformly_close
    {D : ReferenceData} {T : MaterialData} {S : PhysicalSpacesData}
    {C : NonlinearGeometryData S} {L : ReturnCorrectionData S} {K : CanonicalData S}
    {base : ℕ} {ε δ : ℝ}
    (hD : IsAccumulatingProfile D) (hT : IsMaterialData D T)
    (hcur : CanonicalGeometry.CurrentJets D T S C L K base ε)
    (hε : 0 < ε) (hδ : 0 < δ) :
    ∃ base' : ℕ, base ≤ base' ∧ ∃ ε' : ℝ, 0 < ε' ∧ ε' ≤ ε ∧
      sectorNeighborhood S base' ε' ε' ⊆ sectorNeighborhood S base ε ε ∧
      CanonicalGeometry.CurrentJets D T S C L K base' ε' ∧
      ∀ z ∈ sectorNeighborhood S base' ε' ε', ∀ m v p,
        p ∈ CanonicalGeometry.unitStrip →
          |CanonicalGeometry.atom D T S C L K (liftSectorParameter S C z) m v p -
            CanonicalGeometry.atom D T S C L K (C.referenceState, 0) m v p| < δ := by
  let loss : ℕ := hcur.2.1.choose
  have hdiff := hcur.2.1.choose_spec
  obtain ⟨B, hB, hb⟩ := hdiff 0
  obtain ⟨CH, hCH, hCHb⟩ := material_sample_height_coefficient_power_bounded
    hD hT K.cell B (by norm_num : (0 : ℝ) < 3 / 4)
  let M : ℝ := B * CH
  have hM : 0 < M := mul_pos hB hCH
  let base' : ℕ := max base loss
  let ε' : ℝ := min ε (δ / (2 * M))
  have hε' : 0 < ε' := lt_min hε (div_pos hδ (mul_pos (by norm_num) hM))
  have hle : ε' ≤ ε := min_le_left _ _
  have hU : sectorNeighborhood S base' ε' ε' ⊆ sectorNeighborhood S base ε ε :=
    n07a_sectorNeighborhood_mono (S := S) (le_max_left _ _) hle
  have hδ' : M * (2 * ε') ≤ δ := by
    have hsmall : ε' ≤ δ / (2 * M) := min_le_right _ _
    have hmul := (le_div_iff₀ (mul_pos (by norm_num : (0 : ℝ) < 2) hM)).mp hsmall
    nlinarith only [hmul]
  refine ⟨base', le_max_left _ _, ε', hε', hle, hU,
    n07a_currentJets_restrict hD hT hcur (le_max_left _ _) hle, ?_⟩
  intro z hz m v p hp
  have hfirst : sectorGrading S loss z.1 < ε' :=
    (solve_sectorGrading_monotone S (le_max_right base loss) z.1).trans_lt hz.1
  have hsecond : |z.2| < ε' := hz.2
  have heq : CanonicalGeometry.parameterGrading S loss z =
      sectorGrading S loss z.1 + |z.2| :=
    pairGrading_apply (E := StateDirections S) (F := ℝ)
      (sectorGrading S) realGrading loss z
  have hG : CanonicalGeometry.parameterGrading S loss z < 2 * ε' := by
    rw [heq]
    linarith only [hfirst, hsecond]
  have hcoeff : B * T.E0 (T.sample (K.cell m)) ^ B *
      T.H (T.sample (K.cell m)) ^ (3 / 4 : ℝ) ≤ M := by
    calc
      _ = B * (T.H (T.sample (K.cell m)) ^ (3 / 4 : ℝ) *
          T.E0 (T.sample (K.cell m)) ^ B) := by ring
      _ ≤ B * CH := mul_le_mul_of_nonneg_left (hCHb m) hB.le
  have hactual : |CanonicalGeometry.atom D T S C L K
        (liftSectorParameter S C z) m v p -
      CanonicalGeometry.atom D T S C L K (C.referenceState, 0) m v p| ≤
        B * T.E0 (T.sample (K.cell m)) ^ B *
          T.H (T.sample (K.cell m)) ^ (3 / 4 : ℝ) *
            CanonicalGeometry.parameterGrading S loss z := by
    simpa only [CanonicalGeometry.differenceJets, spaces_mixedDerivative_zero,
      Nat.zero_add] using hb z (hU hz) m v ⟨p, hp⟩ 0 0 (by omega)
  exact (hactual.trans
    (mul_le_mul_of_nonneg_right hcoeff (apply_nonneg _ _))).trans_lt
      ((mul_lt_mul_of_pos_left hG hM).trans_le hδ')

end ContinuousFlexibility.Analysis
