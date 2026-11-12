import ContinuousFlexibility.Analysis.N07aInverseChartDifferentialDifference
import ContinuousFlexibility.Analysis.N07aForwardChartBounds
import ContinuousFlexibility.Analysis.N07aAngularReferenceSourceEnvelopes
import ContinuousFlexibility.Analysis.MaterialEnvelopeNormalization
import ContinuousFlexibility.Analysis.NeumannPackage

/-!
# First forward differentials with their actual sampled envelope

Reference unit jets and the actual interval lengths give a polynomial
sample-envelope bound for the reference forward differential. A single
smaller neighborhood makes the relative inverse differential small; its
height gain is used only for that choice of neighborhood. The resulting
bound for the actual forward differential retains its sampled E0 power.
-/

noncomputable section

namespace ContinuousFlexibility.Analysis

open Set ContinuousFlexibility.Statements
open scoped ContDiff

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

private theorem n04Realization_unitInverse_first_norm
    {S : PhysicalSpacesData} {K : CanonicalData S} (m : ℕ)
    (hlen : K.left m < K.right m) {f : PolarPoint → ℝ}
    (hf : ContDiffOn ℝ ∞ f CanonicalGeometry.unitStrip)
    {M : ℝ} (hM : 1 ≤ M)
    (hinv : |(K.right m - K.left m)⁻¹| ≤ M)
    (hjet : ∀ p ∈ CanonicalGeometry.unitStrip, ∀ i j : ℕ, i + j ≤ 1 →
      |mixedDerivative i j f p| ≤ M)
    {x : PolarPoint} (hx : x ∈ canonicalOpen S K m) :
    ‖fderiv ℝ (f ∘ n07aCanonicalUnitInversePoint K m) x‖ ≤ 2 * M ^ 2 := by
  have hM0 : 0 ≤ M := zero_le_one.trans hM
  have hs : ContDiffOn ℝ ∞ (f ∘ n07aCanonicalUnitInversePoint K m)
      (canonicalOpen S K m) :=
    hf.comp n07aCanonicalUnitInversePoint_contDiff.contDiffOn
      (n07aCanonicalUnitInversePoint_maps hlen)
  have hbound := norm_iteratedFDeriv_le_of_mixedDerivative
    (isOpen_Ioo.prod isOpen_univ) hs 1 hx (pow_nonneg hM0 2)
    (by
      intro i j hij
      have hpoint := n07aCanonicalUnitInversePoint_maps hlen hx
      have hp : |(K.right m - K.left m)⁻¹ ^ i| ≤ M := by
        have hi : i = 0 ∨ i = 1 := by omega
        rcases hi with rfl | rfl
        · simpa only [pow_zero, abs_one] using hM
        · simpa only [pow_one] using hinv
      rw [n07a_mixedDerivative_unitInverse, Real.norm_eq_abs, abs_mul]
      exact (mul_le_mul hp (hjet _ hpoint i j hij.le)
        (abs_nonneg _) hM0).trans_eq (pow_two M).symm)
  simpa only [norm_iteratedFDeriv_one, pow_one] using hbound

variable {D : ReferenceData} {T : MaterialData} {S : PhysicalSpacesData}
  {C : NonlinearGeometryData S} {L : ReturnCorrectionData S} {K : CanonicalData S}
  {base : ℕ} {ε : ℝ}

/-- The reference differential has a genuine E0 polynomial cost. The
same reference atoms supply the physical inverse length and canonical
length; no sampled subpower replacement is made. -/
theorem n04Realization_referenceForwardFirstE0_bound
    (href : CanonicalGeometry.ReferenceJets D T S C L K)
    (hlen : ∀ m, K.left m < K.right m)
    (hphysical : ∀ m, K.physicalLeft m < K.physicalRight m)
    (hfloor : ∀ m, 1 ≤ T.E0 (T.sample (K.cell m))) :
    ∃ B : ℝ, 0 < B ∧ ∀ m x, x ∈ referencePhysicalPieceOpen S K m →
      ‖fderiv ℝ (K.chart (C.referenceState, 0) m) x‖ ≤
        B * T.E0 (T.sample (K.cell m)) ^ B := by
  obtain ⟨A, hA, hjet⟩ := href.2 1
  let R : ℝ := 1 + A
  have hR : 1 ≤ R := by dsimp only [R]; linarith only [hA]
  have hR0 : 0 ≤ R := zero_le_one.trans hR
  obtain ⟨B, hB, hpack⟩ := coefficientEnvelope_pack (5 * R ^ 3) (R * 3)
  refine ⟨B, hB, fun m x hx => ?_⟩
  let E : ℝ := T.E0 (T.sample (K.cell m))
  let M : ℝ := R * E ^ R
  have hE : 1 ≤ E := hfloor m
  have hE0 : 0 ≤ E := zero_le_one.trans hE
  have hM : 1 ≤ M := by
    simpa only [one_mul] using mul_le_mul hR
      (Real.one_le_rpow hE hR0) zero_le_one hR0
  have hM0 : 0 ≤ M := zero_le_one.trans hM
  have hAM : A * E ^ A ≤ M := mul_le_mul
    (by dsimp only [R]; linarith : A ≤ R)
    (Real.rpow_le_rpow_of_exponent_le hE (by dsimp only [R]; linarith : A ≤ R))
    (Real.rpow_nonneg hE0 A) hR0
  have hp : ((1 / 2, 0) : PolarPoint) ∈ CanonicalGeometry.unitStrip := by
    constructor <;> norm_num
  have hlength : |K.right m - K.left m| ≤ M := by
    have hb := hjet m .canonicalLength (1 / 2, 0) hp 0 0 (by omega)
    have hb' : |K.right m - K.left m| ≤ A * E ^ A := by
      simpa only [spaces_mixedDerivative_zero, CanonicalGeometry.atom] using hb
    exact hb'.trans hAM
  have hinv : |(K.physicalRight m - K.physicalLeft m)⁻¹| ≤ M := by
    have hb := hjet m .physicalLengthInverse (1 / 2, 0) hp 0 0 (by omega)
    have hb' : |(K.physicalRight m - K.physicalLeft m)⁻¹| ≤ A * E ^ A := by
      simpa only [spaces_mixedDerivative_zero, CanonicalGeometry.atom] using hb
    exact hb'.trans hAM
  let f : CanonicalGeometry.Atom → PolarPoint → ℝ := fun a =>
    n07aPhysicalAtomField D T S C L K a 0 m
  have hf (a : CanonicalGeometry.Atom) :
      f a = CanonicalGeometry.atom D T S C L K (C.referenceState, 0) m a ∘
        n07aCanonicalUnitInversePoint (n07aPhysicalIntervalData K) m := by
    simp only [f, n07aPhysicalAtomField, n07a_lift_zero_parameter]
  have hs (a : CanonicalGeometry.Atom) :
      ContDiffOn ℝ ∞ (f a) (referencePhysicalPieceOpen S K m) := by
    rw [hf a]
    exact (href.1 m a).1.comp n07aCanonicalUnitInversePoint_contDiff.contDiffOn
      (n07aCanonicalUnitInversePoint_maps (K := n07aPhysicalIntervalData K) (hphysical m))
  have hb (a : CanonicalGeometry.Atom) : ‖fderiv ℝ (f a) x‖ ≤ 2 * M ^ 2 := by
    rw [hf a]
    exact n04Realization_unitInverse_first_norm (K := n07aPhysicalIntervalData K)
      m (hphysical m) (href.1 m a).1 hM hinv
      (fun p hp i j hij => (hjet m a p hp i j hij).trans hAM) hx
  have hpair := n07a_coordinatePair_iteratedFDeriv_bound
    ((hs .chartRadial).contDiffAt ((isOpen_Ioo.prod isOpen_univ).mem_nhds hx))
    ((hs .chartAngleDefect).contDiffAt ((isOpen_Ioo.prod isOpen_univ).mem_nhds hx))
    (K.left m) (K.right m - K.left m) (n := 1) (by omega)
  have heq := n07a_forwardChart_eq_rawAtoms
    (D := D) (T := T) (S := S) (C := C) (L := L)
    m (hlen m) (hphysical m) (0 : CanonicalGeometry.Parameter S)
  rw [n07a_lift_zero_parameter] at heq
  have hforward : ‖fderiv ℝ (K.chart (C.referenceState, 0) m) x‖ ≤
      M * (2 * M ^ 2) + 1 + 2 * M ^ 2 := by
    rw [heq]
    simp only [norm_iteratedFDeriv_one] at hpair
    exact hpair.trans (add_le_add (add_le_add
      (mul_le_mul hlength (hb .chartRadial) (norm_nonneg _)
        hM0) le_rfl) (hb .chartAngleDefect))
  have hM23 : M ^ 2 ≤ M ^ 3 := pow_le_pow_right₀ hM (by omega)
  have hM3 : 1 ≤ M ^ 3 := one_le_pow₀ hM
  have hpoly : M * (2 * M ^ 2) + 1 + 2 * M ^ 2 ≤ 5 * M ^ 3 := by
    nlinarith only [hM23, hM3]
  have he : 5 * M ^ 3 = (5 * R ^ 3) * E ^ (R * 3) := by
    dsimp only [M]
    rw [mul_pow, ← Real.rpow_mul_natCast hE0 R 3]
    ring
  exact hforward.trans (hpoly.trans (he.trans_le (hpack E hE)))

private theorem n04Realization_actual_inverse_norm
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [CompleteSpace E]
    (P₀ P G₀ V : E →L[ℝ] E)
    (h₀ : ∀ v, P₀ (G₀ v) = v) (hV : ∀ v, V (P v) = v)
    (hrel : ‖(P - P₀).comp G₀‖ < 1 / 2) : ‖V‖ ≤ 2 * ‖G₀‖ := by
  let N : E →L[ℝ] E :=
    G₀.comp (neumannInverse ((P - P₀).comp G₀) (by linarith only [hrel]))
  have hright : ∀ v, P (N v) = v := perturbation_rightInverse P₀ P G₀ h₀ hrel
  have heq : V = N := by
    apply ContinuousLinearMap.ext
    intro v
    calc
      V v = V (P (N v)) := congrArg V (hright v).symm
      _ = N v := hV (N v)
  rw [heq]
  exact perturbation_norm_le P₀ P G₀ hrel

/-- A single chosen sample-envelope constant bounds every actual forward
first differential on the same moving-domain neighborhood. -/
def N04RealizationForwardFirstE0Bound
    (T : MaterialData) (S : PhysicalSpacesData) (C : NonlinearGeometryData S)
    (K : CanonicalData S) (base : ℕ) (ε B : ℝ) : Prop :=
  ∀ z ∈ sectorNeighborhood S base ε ε, ∀ m x,
    x ∈ physicalPieceOpen S K (liftSectorParameter S C z) m →
      ‖fderiv ℝ (K.chart (liftSectorParameter S C z) m) x‖ ≤
        B * T.E0 (T.sample (K.cell m)) ^ B

/-- The same reference/current primitive jets give a polynomial forward
first bound on one smaller neighborhood. Subpower absorption is used
only to choose that neighborhood, and is not the output estimate. -/
theorem n04Realization_actualForwardFirstE0_neighborhood
    (hD : IsAccumulatingProfile D) (hT : IsMaterialData D T) (hε : 0 < ε)
    (hrefState : referenceStateConditions D S C)
    (hgeom : CanonicalGeometry D S C K base ε)
    (href : CanonicalGeometry.ReferenceJets D T S C L K)
    (hcur : CanonicalGeometry.CurrentJets D T S C L K base ε)
    (hfloor : ∀ m, 1 ≤ T.E0 (T.sample (K.cell m))) :
    ∃ base' : ℕ, base ≤ base' ∧ ∃ η : ℝ, 0 < η ∧ η ≤ ε ∧
      ∃ B : ℝ, 0 < B ∧ N04RealizationForwardFirstE0Bound T S C K base' η B := by
  obtain ⟨low, e, he, he0, heb⟩ := n07a_inverseChart_fderiv_difference_bound
    hD hT hε hrefState hgeom href hcur
  obtain ⟨B₀, hB₀, hbb⟩ := n04Realization_referenceForwardFirstE0_bound href
    (fun m => (hgeom.referenceBounds m).2.1)
    (fun m => (hgeom.referenceBounds m).1) hfloor
  let b : ℕ → ℝ := fun m => B₀ * T.E0 (T.sample (K.cell m)) ^ B₀
  have hb : N07aSampleSubpower T K b := N07aSampleSubpower.mul hD hT
    (N07aSampleSubpower.const hD hT B₀) (N07aSampleSubpower.e0_rpow hD hT B₀)
  have hb0 (m : ℕ) : 0 ≤ b m :=
    mul_nonneg hB₀.le (Real.rpow_nonneg (zero_le_one.trans (hfloor m)) _)
  obtain ⟨A, hA, hAb⟩ := (N07aSampleSubpower.mul hD hT he hb).height_absorption
    hD hT (by norm_num : 0 < (3 / 4 : ℝ))
  obtain ⟨B, hB, hpack⟩ := coefficientEnvelope_pack (2 * B₀) B₀
  let η : ℝ := min ε (1 / (4 * A))
  have hη : 0 < η := lt_min hε (div_pos zero_lt_one (mul_pos (by norm_num) hA))
  have hηε : η ≤ ε := min_le_left _ _
  have hηA : η ≤ 1 / (4 * A) := min_le_right _ _
  refine ⟨max base low, le_max_left _ _, η, hη, hηε, B, hB, ?_⟩
  intro z hz m x hx
  have hzold : z ∈ sectorNeighborhood S base ε ε :=
    n07a_sectorNeighborhood_mono (le_max_left _ _) hηε hz
  have hzstate := liftSectorParameter_mem_stateNeighborhood (S := S) (C := C) hzold le_rfl
  have hs := hrefState.liftSectorParameter_sector z
  have hc := hgeom.charts (liftSectorParameter S C z) hzstate hs m
  let y : PolarPoint := K.chart (liftSectorParameter S C z) m x
  have hy : y ∈ canonicalOpen S K m := hc.1 hx
  have hxy : K.inverseChart (liftSectorParameter S C z) m y = x := hc.2.2.1 x hx
  have hzref : (C.referenceState, 0) ∈ stateNeighborhood S C base ε := by
    constructor
    · change stateGrading S base (C.referenceState - C.referenceState) < ε
      have hzero : stateGrading S base (0 : AnnularState S) = 0 :=
        (stateGrading S base).map_zero'
      simpa only [sub_self, hzero] using hε
    · simpa only [abs_zero] using hε
  let x₀ : PolarPoint := K.inverseChart (C.referenceState, 0) m y
  have hx₀ : x₀ ∈ referencePhysicalPieceOpen S K m := by
    rw [← hgeom.referenceDomain m]
    exact (hgeom.charts (C.referenceState, 0) hzref hrefState.stateSector m).2.1 hy
  let P₀ : PolarPoint →L[ℝ] PolarPoint := fderiv ℝ (K.inverseChart (C.referenceState, 0) m) y
  let P : PolarPoint →L[ℝ] PolarPoint := fderiv ℝ (K.inverseChart (liftSectorParameter S C z) m) y
  let G₀ : PolarPoint →L[ℝ] PolarPoint := fderiv ℝ (K.chart (C.referenceState, 0) m) x₀
  let V : PolarPoint →L[ℝ] PolarPoint := fderiv ℝ (K.chart (liftSectorParameter S C z) m) x
  have hG₀ : ‖G₀‖ ≤ b m := hbb m x₀ hx₀
  have hP₀ : ∀ v, P₀ (G₀ v) = v := by
    intro v
    simpa only [ContinuousLinearMap.comp_apply, ContinuousLinearMap.id_apply] using
      congrArg (fun Q : PolarPoint →L[ℝ] PolarPoint => Q v)
        (n07a_actualChart_fderiv_inverse hgeom hzref hrefState.stateSector m hy).2
  have hVP : ∀ v, V (P v) = v := by
    intro v
    have h := congrArg (fun Q : PolarPoint →L[ℝ] PolarPoint => Q v)
      (n07a_actualChart_fderiv_inverse hgeom hzstate hs m hy).1
    simpa only [ContinuousLinearMap.comp_apply, ContinuousLinearMap.id_apply, hxy] using h
  have hp : 0 ≤ CanonicalGeometry.parameterGrading S low z := apply_nonneg _ _
  have hsample := hT.2.1 _
    (materialSample_mem_radialCore hT hD.choose_spec.2.1 (K.cell m))
  have hH : 0 ≤ T.H (T.sample (K.cell m)) ^ (3 / 4 : ℝ) :=
    Real.rpow_nonneg hsample.2.1.le _
  have hsmall : A * CanonicalGeometry.parameterGrading S low z < 1 / 2 := by
    calc
      _ < A * (2 * η) := mul_lt_mul_of_pos_left
        (n07a_parameterGrading_lt_twice_radius (le_max_right _ _) hz) hA
      _ ≤ A * (2 * (1 / (4 * A))) :=
        mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_left hηA (by norm_num)) hA.le
      _ = 1 / 2 := by field_simp [hA.ne'] <;> ring
  have hrel : ‖(P - P₀).comp G₀‖ < 1 / 2 := by
    calc
      _ ≤ ‖P - P₀‖ * ‖G₀‖ := ContinuousLinearMap.opNorm_comp_le _ _
      _ ≤ (e m * T.H (T.sample (K.cell m)) ^ (3 / 4 : ℝ) *
          CanonicalGeometry.parameterGrading S low z) * b m :=
        mul_le_mul (heb z hzold m y hy) hG₀ (norm_nonneg _)
          (mul_nonneg (mul_nonneg (he0 m) hH) hp)
      _ = (T.H (T.sample (K.cell m)) ^ (3 / 4 : ℝ) * |e m * b m|) *
          CanonicalGeometry.parameterGrading S low z := by
        rw [abs_of_nonneg (mul_nonneg (he0 m) (hb0 m))]
        ring
      _ ≤ A * CanonicalGeometry.parameterGrading S low z :=
        mul_le_mul_of_nonneg_right (hAb m) hp
      _ < 1 / 2 := hsmall
  have hbound : ‖V‖ ≤ 2 * b m :=
    (n04Realization_actual_inverse_norm P₀ P G₀ V hP₀ hVP hrel).trans
      (mul_le_mul_of_nonneg_left hG₀ (by norm_num))
  have hpackinput : 2 * b m = (2 * B₀) * T.E0 (T.sample (K.cell m)) ^ B₀ := by
    dsimp only [b]
    ring
  exact hbound.trans (hpackinput.trans_le (hpack _ (hfloor m)))

end ContinuousFlexibility.Analysis
