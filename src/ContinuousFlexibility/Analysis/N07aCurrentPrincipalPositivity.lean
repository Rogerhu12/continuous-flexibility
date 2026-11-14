module

public import ContinuousFlexibility.Analysis.N07aCurrentPrincipalBounds
public import ContinuousFlexibility.Analysis.N07aNeighborhood

/-!
# Positivity of the actual current canonical leading coefficient

The reference inverse-coefficient bound and the genuine H^(3/4) difference
gain give one neighborhood for every piece. No lower bound E0 ≥ 1 and no
positivity certificate for a new coefficient are used.
-/

@[expose] public section

noncomputable section

namespace ContinuousFlexibility.Analysis

open Set

set_option backward.isDefEq.respectTransparency true
open ContinuousFlexibility.Statements

attribute [local instance]
  n07aNonlinearAnnularGroup
  n07aNonlinearAnnularModule
  n07aNonlinearAnnularAddGroup
  n07aNonlinearAnnularSMul
  n07aNonlinearAnnularSub
  n07aNonlinearAnnularParameterGroup
  n07aNonlinearAnnularParameterModule
  n07aNonlinearAnnularParameterAddGroup
  n07aNonlinearAnnularParameterSMul
  n07aNonlinearAnnularParameterSub
  n07aNonlinearDirectionsGroup
  n07aNonlinearDirectionsModule
  n07aNonlinearDirectionsAddGroup
  n07aNonlinearDirectionsSMul
  n07aNonlinearDirectionsSub
  n07aNonlinearSectorParameterGroup
  n07aNonlinearSectorParameterModule
  n07aNonlinearSectorParameterAddGroup
  n07aNonlinearSectorParameterSMul
  n07aNonlinearSectorParameterSub

variable {D : ReferenceData} {T : MaterialData} {S : PhysicalSpacesData}
  {C : NonlinearGeometryData S} {L : ReturnCorrectionData S} {K : CanonicalData S}
  {base : ℕ} {ε : ℝ}

private theorem n07a_positive_of_relative_difference
    {a a₀ d r : ℝ} (ha₀ : 0 < a₀) (hi : a₀⁻¹ ≤ r)
    (hd : |a - a₀| ≤ d) (hsmall : d * r < 1) : 0 < a := by
  have hd0 : 0 ≤ d := (abs_nonneg _).trans hd
  have hb : |a - a₀| * a₀⁻¹ < 1 :=
    (mul_le_mul hd hi (inv_pos.mpr ha₀).le hd0).trans_lt hsmall
  have hlt : |a - a₀| < a₀ := by
    apply (mul_lt_mul_iff_left₀ (inv_pos.mpr ha₀)).mp
    simpa only [mul_inv_cancel₀ ha₀.ne'] using hb
  have hleft := (abs_lt.mp hlt).1
  linarith

private theorem n07a_currentPrincipal_numeric_smallness
    {B₀ B₁ M E H p : ℝ}
    (hB₀ : 0 < B₀) (hB₁ : 0 < B₁) (hM : 0 < M) (hE : 0 < E)
    (hp : 0 ≤ p) (hEnv : H ^ (3 / 4 : ℝ) * E ^ (B₀ + B₁) ≤ M)
    (hsmall : p < 2 * (4 * (B₀ * B₁ * M))⁻¹) :
    (B₁ * E ^ B₁ * H ^ (3 / 4 : ℝ) * p) * (B₀ * E ^ B₀) < 1 := by
  have hQ : 0 < B₀ * B₁ * M := mul_pos (mul_pos hB₀ hB₁) hM
  calc
    _ = B₀ * B₁ * (H ^ (3 / 4 : ℝ) * E ^ (B₀ + B₁)) * p := by
      rw [Real.rpow_add hE]
      ring
    _ ≤ (B₀ * B₁ * M) * p :=
      mul_le_mul_of_nonneg_right
        (mul_le_mul_of_nonneg_left hEnv (mul_nonneg hB₀.le hB₁.le)) hp
    _ < (B₀ * B₁ * M) * (2 * (4 * (B₀ * B₁ * M))⁻¹) :=
      mul_lt_mul_of_pos_left hsmall hQ
    _ = (1 / 2 : ℝ) := by
      field_simp [hB₀.ne', hB₁.ne', hM.ne']
      ring
    _ < 1 := by norm_num

private theorem n07a_parameterSize_small
    {base loss : ℕ} {ε δ : ℝ} (hloss : loss ≤ base) (he : ε ≤ δ)
    {z : CanonicalGeometry.Parameter S} (hz : z ∈ sectorNeighborhood S base ε ε) :
    CanonicalGeometry.parameterGrading S loss z < 2 * δ := by
  have h₁ : sectorGrading S loss z.1 < δ :=
    ((solve_sectorGrading_monotone S hloss z.1).trans_lt hz.1).trans_le he
  have h₂ : |z.2| < δ := hz.2.trans_le he
  have heq : CanonicalGeometry.parameterGrading S loss z =
      sectorGrading S loss z.1 + |z.2| := by
    exact pairGrading_apply (E := StateDirections S) (F := ℝ)
      (sectorGrading S) realGrading loss z
  exact heq.le.trans_lt (by linarith only [h₁, h₂])

private theorem n07a_principal_positive_from_bounds
    (hD : IsAccumulatingProfile D) (hT : IsMaterialData D T)
    (hprincipal : CanonicalGeometry.ReferencePrincipal T S C K)
    {loss : ℕ} {B₀ B₁ : ℝ} (hB₀ : 0 < B₀) (hB₁ : 0 < B₁)
    (hB₀b : ∀ m y, y ∈ canonicalOpen S K m →
      ((K.coefficients (C.referenceState, 0) m).a y)⁻¹ ≤
        B₀ * T.E0 (T.sample (K.cell m)) ^ B₀)
    (hB₁b : ∀ z ∈ sectorNeighborhood S base ε ε, ∀ m y,
        y ∈ canonicalOpen S K m →
          |(K.coefficients (liftSectorParameter S C z) m).a y -
            (K.coefficients (C.referenceState, 0) m).a y| ≤
            B₁ * T.E0 (T.sample (K.cell m)) ^ B₁ *
              T.H (T.sample (K.cell m)) ^ (3 / 4 : ℝ) *
                CanonicalGeometry.parameterGrading S loss z)
    (hε : 0 < ε) :
    ∃ base' : ℕ, base ≤ base' ∧ ∃ ε' : ℝ, 0 < ε' ∧ ε' ≤ ε ∧
      ∀ z ∈ sectorNeighborhood S base' ε' ε', ∀ m p,
        p ∈ canonicalOpen S K m →
          0 < (K.coefficients (liftSectorParameter S C z) m).a p := by
  have henv := n07a_materialSample_envelope_bound hD hT
    (by norm_num : 0 < (3 / 4 : ℝ)) (B₀ + B₁)
  let M : ℝ := henv.choose
  have hM : 0 < M := henv.choose_spec.1
  have hMb := henv.choose_spec.2
  let Q : ℝ := B₀ * B₁ * M
  have hQ : 0 < Q := mul_pos (mul_pos hB₀ hB₁) hM
  let δ : ℝ := (4 * Q)⁻¹
  have hδ : 0 < δ := inv_pos.mpr (mul_pos (by norm_num) hQ)
  let ε' : ℝ := min ε δ
  have he' : 0 < ε' := lt_min hε hδ
  have he : ε' ≤ ε := min_le_left _ _
  have hed : ε' ≤ δ := min_le_right _ _
  refine ⟨max base loss, le_max_left _ _, ε', he', he, ?_⟩
  intro z hz m y hy
  have hU : z ∈ sectorNeighborhood S base ε ε :=
    n07a_sectorNeighborhood_mono (S := S) (le_max_left base loss) he hz
  have hparam : CanonicalGeometry.parameterGrading S loss z < 2 * δ :=
    n07a_parameterSize_small (S := S) (le_max_right base loss) hed hz
  have hp0 : 0 ≤ CanonicalGeometry.parameterGrading S loss z := apply_nonneg _ _
  have hsamp := hT.2.1 _
    (materialSample_mem_radialCore hT hD.choose_spec.2.1 (K.cell m))
  exact n07a_positive_of_relative_difference (hprincipal.1 m y hy).1
    (hB₀b m y hy) (hB₁b z hU m y hy)
    (n07a_currentPrincipal_numeric_smallness hB₀ hB₁ hM hsamp.2.2.1 hp0
      (hMb (K.cell m)) hparam)

theorem n07a_currentPrincipal_positive_neighborhood
    (hD : IsAccumulatingProfile D) (hT : IsMaterialData D T)
    (href : CanonicalGeometry.ReferenceJets D T S C L K)
    (hprincipal : CanonicalGeometry.ReferencePrincipal T S C K)
    (hcur : CanonicalGeometry.CurrentJets D T S C L K base ε)
    (hε : 0 < ε) (hinterval : ∀ m, K.left m < K.right m) :
    ∃ base' : ℕ, base ≤ base' ∧ ∃ ε' : ℝ, 0 < ε' ∧ ε' ≤ ε ∧
      ∀ z ∈ sectorNeighborhood S base' ε' ε', ∀ m p,
        p ∈ canonicalOpen S K m →
          0 < (K.coefficients (liftSectorParameter S C z) m).a p := by
  have hdiff := n07a_currentPrincipal_difference_bound hcur hinterval
  let loss : ℕ := hdiff.choose
  let B₁ : ℝ := hdiff.choose_spec.choose
  have hB₁ : 0 < B₁ := hdiff.choose_spec.choose_spec.1
  have hB₁b := hdiff.choose_spec.choose_spec.2
  have hinv := n07a_referencePrincipal_inverse_bound href hprincipal hinterval
  let B₀ : ℝ := hinv.choose
  have hB₀ : 0 < B₀ := hinv.choose_spec.1
  have hB₀b := hinv.choose_spec.2
  exact n07a_principal_positive_from_bounds (loss := loss) hD hT hprincipal
    hB₀ hB₁ hB₀b hB₁b hε

end ContinuousFlexibility.Analysis
