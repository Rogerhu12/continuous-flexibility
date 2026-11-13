import ContinuousFlexibility.Analysis.N04RealizationPrincipalHalfBounds

/-!
# One state neighborhood preserves all actual interior travel lower bounds

The first parameter jet alone chooses the neighborhood. Its positive
height factor absorbs every sampled material power, including the
inverse reference travel on a smaller root overlap. All later state and
spatial orders therefore use the same positive value interval.
-/

noncomputable section

namespace ContinuousFlexibility.Analysis

open Set ContinuousFlexibility.Statements CanonicalGeometry

set_option backward.isDefEq.respectTransparency true

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

/-- The index may contain a component, side and physical point. The
radius and low base precede all of them and every later derivative order. -/
theorem n04NegativeChart_current_half_reference
    {D : ReferenceData} {T : MaterialData} {S : PhysicalSpacesData} {I : Type*}
    (hD : IsAccumulatingProfile D) (hT : IsMaterialData D T)
    (sample : I → ℕ) (base loss : ℕ) (ε : ℝ) (hε : 0 < ε)
    (f : I → Parameter S → ℝ)
    (J : ∀ i, SmoothDirections (sectorNeighborhood S base ε ε) (f i))
    (c P B A : ℝ) (hc : 0 < c) (hB : 0 < B)
    (href : ∀ i, 0 < f i 0 ∧
      (f i 0)⁻¹ ≤ B * T.E0 (T.sample (sample i)) ^ A)
    (hfirst : ∀ i z, z ∈ sectorNeighborhood S base ε ε → ∀ v : Fin 1 → Parameter S,
      |(J i).D 1 z v| ≤ c * T.E0 (T.sample (sample i)) ^ P *
        T.H (T.sample (sample i)) ^ (3 / 4 : ℝ) *
          oneHighVariationWeight (parameterGrading S) base loss z v) :
    ∃ b : ℕ, ∃ η : ℝ, base ≤ b ∧ 0 < η ∧ η ≤ ε ∧ η ≤ 1 / 2 ∧
      ∀ i z, z ∈ sectorNeighborhood S b η η →
        f i 0 / 2 ≤ f i z ∧ 0 < f i z ∧
          (f i z)⁻¹ ≤ 2 * B * T.E0 (T.sample (sample i)) ^ A := by
  obtain ⟨N, hN, hbound⟩ := n07a_materialSample_envelope_bound hD hT
    (by norm_num : 0 < (3 / 4 : ℝ)) (P + A)
  let Q : ℝ := c * B * N
  let b : ℕ := max base loss
  let δ : ℝ := (12 * Q)⁻¹
  let η : ℝ := min ε (min (1 / 2) δ)
  have hQ : 0 < Q := mul_pos (mul_pos hc hB) hN
  have hδ : 0 < δ := inv_pos.mpr (mul_pos (by norm_num) hQ)
  have hη : 0 < η := lt_min hε (lt_min (by norm_num) hδ)
  have hηε : η ≤ ε := min_le_left _ _
  have hηhalf : η ≤ 1 / 2 := (min_le_right _ _).trans (min_le_left _ _)
  have hηδ : η ≤ δ := (min_le_right _ _).trans (min_le_right _ _)
  have hmono := n07aParameterGrading_monotone S
  have hzero : (0 : Parameter S) ∈ sectorNeighborhood S base ε ε := by
    constructor
    · change sectorGrading S base 0 < ε
      exact (sectorGrading S base).map_zero'.trans_lt hε
    · change |(0 : ℝ)| < ε
      simpa only [abs_zero] using hε
  refine ⟨b, η, le_max_left _ _, hη, hηε, hηhalf, fun i z hz => ?_⟩
  have hzU : z ∈ sectorNeighborhood S base ε ε :=
    n07a_sectorNeighborhood_mono (S := S) (le_max_left _ _) hηε hz
  have hp : parameterGrading S b z < 2 * η := by
    rw [show parameterGrading S b z = sectorGrading S b z.1 + |z.2| from
      pairGrading_apply (E := StateDirections S) (F := ℝ)
        (sectorGrading S) realGrading b z]
    linarith only [hz.1, hz.2]
  have hlow : parameterGrading S base z ≤ 1 := by
    have hb := hmono (le_max_left base loss) z
    linarith only [hb, hp, hηhalf]
  have hsmall : parameterGrading S b z < (6 * Q)⁻¹ := by
    calc
      _ < 2 * η := hp
      _ ≤ 2 * δ := mul_le_mul_of_nonneg_left hηδ (by norm_num)
      _ = (6 * Q)⁻¹ := by dsimp only [δ]; field_simp [hQ.ne']; ring
  let E : ℝ := T.E0 (T.sample (sample i))
  let H : ℝ := T.H (T.sample (sample i)) ^ (3 / 4 : ℝ)
  let M : ℝ := c * E ^ P * H
  have hsamp := hT.2.1 _
    (materialSample_mem_radialCore hT hD.choose_spec.2.1 (sample i))
  have hM : 0 ≤ M := mul_nonneg
    (mul_nonneg hc.le (Real.rpow_nonneg hsamp.2.2.1.le P))
    (Real.rpow_nonneg hsamp.2.1.le _)
  have hprod : M * (B * E ^ A) ≤ Q := by
    calc
      _ = c * B * (H * E ^ (P + A)) := by
        dsimp only [M]
        rw [Real.rpow_add hsamp.2.2.1]
        ring
      _ ≤ c * B * N := mul_le_mul_of_nonneg_left
        (hbound (sample i)) (mul_nonneg hc.le hB.le)
  have hfirstHigh : ∀ y ∈ sectorNeighborhood S base ε ε, ∀ v : Fin 1 → Parameter S,
      |(J i).D 1 y v| ≤ M * oneHighVariationWeight (parameterGrading S) base b y v := by
    intro y hy v
    exact (hfirst i y hy v).trans (mul_le_mul_of_nonneg_left
      (oneHighVariationWeight_mono hmono le_rfl (le_max_right base loss) y v) hM)
  have hb := n04Realization_firstJet_half_reference (J i) (parameterGrading S) base b
    (hmono (le_max_left base loss)) (sectorNeighborhood_convex S base ε ε) hzero
    hM hQ hprod (href i).1 (href i).2 hfirstHigh hzU hlow hsmall
  simpa only [mul_assoc] using hb

end ContinuousFlexibility.Analysis

/-- info: 'ContinuousFlexibility.Analysis.n04NegativeChart_current_half_reference'
depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms ContinuousFlexibility.Analysis.n04NegativeChart_current_half_reference
