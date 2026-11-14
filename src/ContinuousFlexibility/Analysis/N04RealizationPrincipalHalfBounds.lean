module

public import ContinuousFlexibility.Analysis.N04RealizationDifferenceValue
public import ContinuousFlexibility.Analysis.N07aCurrentPrincipalBounds
public import ContinuousFlexibility.Analysis.SectorParameterGeometry
public import ContinuousFlexibility.Analysis.StateNeighborhood

/-!
# A half-reference lower bound from the genuine first parameter jet

The neighborhood is chosen using only parameter order one. The actual
coefficient, atlas, sample, and all later higher-order towers are unchanged.
No current-jet certificate is used to prove positivity.
-/

@[expose] public section

noncomputable section

namespace ContinuousFlexibility.Analysis

open Set ContinuousFlexibility.Statements

private theorem half_reference_of_relative_error
    {a a₀ d r : ℝ} (ha₀ : 0 < a₀) (hi : a₀⁻¹ ≤ r)
    (hd : |a - a₀| ≤ d) (hsmall : d * r < 1 / 2) :
    a₀ / 2 ≤ a ∧ 0 < a ∧ a⁻¹ ≤ 2 * r := by
  have hd0 : 0 ≤ d := (abs_nonneg _).trans hd
  have hb : |a - a₀| * a₀⁻¹ < 1 / 2 :=
    (mul_le_mul hd hi (inv_pos.mpr ha₀).le hd0).trans_lt hsmall
  have hdiv : |a - a₀| / a₀ < 1 / 2 := by
    simpa only [div_eq_mul_inv] using hb
  have herr : |a - a₀| < a₀ / 2 := by
    have h := (div_lt_iff₀ ha₀).mp hdiv
    linarith
  have ha : a₀ / 2 ≤ a := by
    have h := (abs_lt.mp herr).1
    linarith
  refine ⟨ha, (half_pos ha₀).trans_le ha, ?_⟩
  calc
    a⁻¹ ≤ (a₀ / 2)⁻¹ := inv_anti₀ (half_pos ha₀) ha
    _ = 2 * a₀⁻¹ := by simp only [div_eq_mul_inv, mul_inv_rev, inv_inv]
    _ ≤ 2 * r := mul_le_mul_of_nonneg_left hi (by norm_num)

/-- A genuine first parameter jet controls the relative error on a
convex neighborhood. This numerical form also applies to optical travel. -/
theorem n04Realization_firstJet_half_reference
    {X : Type*} [TopologicalSpace X] [AddCommGroup X] [Module ℝ X]
    [IsTopologicalAddGroup X] [ContinuousSMul ℝ X]
    {U : Set X} {f : X → ℝ} (J : SmoothDirections U f)
    (p : ℕ → Seminorm ℝ X) (base high : ℕ)
    (horder : p base ≤ p high) (hconvex : Convex ℝ U) (hzero : (0 : X) ∈ U)
    {M r Q : ℝ} (hM : 0 ≤ M) (hQ : 0 < Q) (hprod : M * r ≤ Q)
    (hf0 : 0 < f 0) (hi : (f 0)⁻¹ ≤ r)
    (hfirst : ∀ y ∈ U, ∀ v : Fin 1 → X,
      |J.D 1 y v| ≤ M * oneHighVariationWeight p base high y v)
    {x : X} (hx : x ∈ U) (hlow : p base x ≤ 1)
    (hsmall : p high x < (6 * Q)⁻¹) :
    f 0 / 2 ≤ f x ∧ 0 < f x ∧ (f x)⁻¹ ≤ 2 * r := by
  have hsegment : ∀ t ∈ Icc (0 : ℝ) 1, (0 : X) + t • x ∈ U := by
    intro t ht
    simpa only [smul_zero, zero_add] using
      hconvex hzero hx (sub_nonneg.mpr ht.2) ht.1 (sub_add_cancel 1 t)
  have hd := n04Realization_smoothDirections_difference_value_bound
    J p base high 0 x horder hsegment hlow hM
    (fun y hy v => by simpa only [sub_zero] using hfirst y hy v)
  simp only [zero_add] at hd
  apply half_reference_of_relative_error hf0 hi hd
  calc
    ((3 * M) * p high x) * r = 3 * (M * r) * p high x := by ring
    _ ≤ (3 * Q) * p high x := mul_le_mul_of_nonneg_right
      (mul_le_mul_of_nonneg_left hprod (by norm_num)) (apply_nonneg _ _)
    _ < (3 * Q) * (6 * Q)⁻¹ :=
      mul_lt_mul_of_pos_left hsmall (mul_pos (by norm_num) hQ)
    _ = 1 / 2 := by field_simp [hQ.ne']; ring

set_option backward.isDefEq.respectTransparency true

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
  {base loss : ℕ} {ε : ℝ}

/-- One genuine first-jet estimate fixes a neighborhood for all subsequent
positive-principal and reciprocal estimates. Its radius has no dependence
on any higher parameter or spatial order. -/
theorem n04Realization_positive_principal_half_reference
    (hD : IsAccumulatingProfile D) (hT : IsMaterialData D T)
    (href : CanonicalGeometry.ReferenceJets D T S C L K)
    (hprincipal : CanonicalGeometry.ReferencePrincipal T S C K)
    (hinterval : ∀ m, K.left m < K.right m) (hε : 0 < ε)
    (J : ∀ m, K.positive m = true → ∀ y, y ∈ canonicalOpen S K m →
      SmoothDirections (sectorNeighborhood S base ε ε)
        (fun z => (K.coefficients (liftSectorParameter S C z) m).a y))
    (c P : ℝ) (hc : 0 < c)
    (hfirst : ∀ m hm y hy, ∀ z ∈ sectorNeighborhood S base ε ε,
      ∀ v : Fin 1 → CanonicalGeometry.Parameter S,
        |(J m hm y hy).D 1 z v| ≤
          c * T.E0 (T.sample (K.cell m)) ^ P *
            T.H (T.sample (K.cell m)) ^ (3 / 4 : ℝ) *
              oneHighVariationWeight (CanonicalGeometry.parameterGrading S) base loss z v) :
    ∃ B : ℝ, 0 < B ∧ ∃ base' : ℕ, base ≤ base' ∧
      ∃ ε' : ℝ, 0 < ε' ∧ ε' ≤ ε ∧
        ∀ z ∈ sectorNeighborhood S base' ε' ε',
          ∀ m, K.positive m = true → ∀ y ∈ canonicalOpen S K m,
            (K.coefficients (C.referenceState, 0) m).a y / 2 ≤
                (K.coefficients (liftSectorParameter S C z) m).a y ∧
              0 < (K.coefficients (liftSectorParameter S C z) m).a y ∧
              ((K.coefficients (liftSectorParameter S C z) m).a y)⁻¹ ≤
                2 * B * T.E0 (T.sample (K.cell m)) ^ B := by
  have hinv := n07a_referencePrincipal_inverse_bound href hprincipal hinterval
  let B : ℝ := hinv.choose
  have hB : 0 < B := hinv.choose_spec.1
  have hBb := hinv.choose_spec.2
  have henv := n07a_materialSample_envelope_bound hD hT
    (by norm_num : 0 < (3 / 4 : ℝ)) (P + B)
  let N : ℝ := henv.choose
  have hN : 0 < N := henv.choose_spec.1
  let Q : ℝ := c * B * N
  have hQ : 0 < Q := mul_pos (mul_pos hc hB) hN
  let high : ℕ := max base loss
  let δ : ℝ := (12 * Q)⁻¹
  have hδ : 0 < δ := inv_pos.mpr (mul_pos (by norm_num) hQ)
  let η : ℝ := min ε (min (1 / 2) δ)
  have hη : 0 < η := lt_min hε (lt_min (by norm_num) hδ)
  have hηε : η ≤ ε := min_le_left _ _
  have hηhalf : η ≤ 1 / 2 := (min_le_right _ _).trans (min_le_left _ _)
  have hηδ : η ≤ δ := (min_le_right _ _).trans (min_le_right _ _)
  have hmono : Monotone (CanonicalGeometry.parameterGrading S) :=
    n07aParameterGrading_monotone S
  have hzero : (0 : CanonicalGeometry.Parameter S) ∈ sectorNeighborhood S base ε ε := by
    constructor
    · change sectorGrading S base 0 < ε
      exact (sectorGrading S base).map_zero'.trans_lt hε
    · change |(0 : ℝ)| < ε
      simpa only [abs_zero] using hε
  have hzeroLift : liftSectorParameter S C (0 : CanonicalGeometry.Parameter S) =
      (C.referenceState, 0) :=
    (liftSectorParameter_eq_affine S C 0).trans
      ((congrArg (fun w : AnnularState S × ℝ => (C.referenceState, 0) + w)
        (ContinuousLinearMap.map_zero (sectorParameterInclusion S))).trans (add_zero _))
  refine ⟨B, hB, high, le_max_left _ _, η, hη, hηε, ?_⟩
  intro z hz m hm y hy
  have hzU : z ∈ sectorNeighborhood S base ε ε :=
    n07a_sectorNeighborhood_mono (S := S) (le_max_left _ _) hηε hz
  have hp : CanonicalGeometry.parameterGrading S high z < 2 * η := by
    rw [show CanonicalGeometry.parameterGrading S high z =
      sectorGrading S high z.1 + |z.2| from
        pairGrading_apply (E := StateDirections S) (F := ℝ)
          (sectorGrading S) realGrading high z]
    linarith only [hz.1, hz.2]
  have hlow : CanonicalGeometry.parameterGrading S base z ≤ 1 := by
    have hb := hmono (le_max_left base loss) z
    linarith only [hb, hp, hηhalf]
  have hsmall : CanonicalGeometry.parameterGrading S high z < (6 * Q)⁻¹ := by
    calc
      _ < 2 * η := hp
      _ ≤ 2 * δ := mul_le_mul_of_nonneg_left hηδ (by norm_num)
      _ = (6 * Q)⁻¹ := by dsimp only [δ]; field_simp [hQ.ne']; ring
  have hsamp := hT.2.1 _
    (materialSample_mem_radialCore hT hD.choose_spec.2.1 (K.cell m))
  let M : ℝ := c * T.E0 (T.sample (K.cell m)) ^ P *
    T.H (T.sample (K.cell m)) ^ (3 / 4 : ℝ)
  have hM : 0 ≤ M := mul_nonneg
    (mul_nonneg hc.le (Real.rpow_nonneg hsamp.2.2.1.le P))
    (Real.rpow_nonneg hsamp.2.1.le _)
  have hprod : M * (B * T.E0 (T.sample (K.cell m)) ^ B) ≤ Q := by
    calc
      _ = c * B * (T.H (T.sample (K.cell m)) ^ (3 / 4 : ℝ) *
          T.E0 (T.sample (K.cell m)) ^ (P + B)) := by
        dsimp only [M]
        rw [Real.rpow_add hsamp.2.2.1 P B]
        ring
      _ ≤ c * B * N := mul_le_mul_of_nonneg_left (henv.choose_spec.2 (K.cell m))
        (mul_nonneg hc.le hB.le)
      _ = Q := rfl
  have ha0 : 0 < (K.coefficients (liftSectorParameter S C 0) m).a y := by
    rw [hzeroLift]
    exact (hprincipal.1 m y hy).1
  have hi : ((K.coefficients (liftSectorParameter S C 0) m).a y)⁻¹ ≤
      B * T.E0 (T.sample (K.cell m)) ^ B := by
    rw [hzeroLift]
    exact hBb m y hy
  have hfirstHigh : ∀ w ∈ sectorNeighborhood S base ε ε,
      ∀ v : Fin 1 → CanonicalGeometry.Parameter S,
        |(J m hm y hy).D 1 w v| ≤ M *
          oneHighVariationWeight (CanonicalGeometry.parameterGrading S) base high w v := by
    intro w hw v
    exact (hfirst m hm y hy w hw v).trans (mul_le_mul_of_nonneg_left
      (ContinuousFlexibility.Analysis.oneHighVariationWeight_mono
        hmono le_rfl (le_max_right base loss) w v) hM)
  have h := n04Realization_firstJet_half_reference (J m hm y hy)
    (CanonicalGeometry.parameterGrading S) base high (hmono (le_max_left base loss))
    (sectorNeighborhood_convex S base ε ε) hzero hM hQ hprod ha0 hi
    hfirstHigh hzU hlow hsmall
  simpa only [hzeroLift, mul_assoc] using h

end ContinuousFlexibility.Analysis
