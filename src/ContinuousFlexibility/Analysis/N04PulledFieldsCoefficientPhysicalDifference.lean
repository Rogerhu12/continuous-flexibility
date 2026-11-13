import ContinuousFlexibility.Analysis.N04PulledFieldsCoefficientDifferenceIdentity
import ContinuousFlexibility.Analysis.N04PulledFieldsActualErrorPhysical
import ContinuousFlexibility.Analysis.N04PulledFieldsPhysicalDifferenceCost
import ContinuousFlexibility.Analysis.N04PulledFieldsCoefficientCurrent

/-!
# Full physical height for the retained corrected coefficients

The original coefficient increment and the actual correction error both
have physical full-height bounds. Their genuine jet identity combines
these estimates on one low box, uniformly for all three coefficients.
Only the final step enlarges the material envelope; the physical point
and the reference coefficient remain unchanged.
-/

noncomputable section

namespace ContinuousFlexibility.Analysis

open Set ContinuousFlexibility.Statements CanonicalGeometry

local instance n04PulledFieldsCoefficientPhysicalDifferenceStateSMul (S : PhysicalSpacesData) :
    SMul ℝ (AnnularState S) := Prod.instSMul

set_option backward.isDefEq.respectTransparency false

private theorem n04PulledFields_physicalDifference_envelope
    (k : ℕ) {value reference originalRef C Q E E' H weight : ℝ}
    (href : reference = originalRef) (hC : 0 ≤ C) (hQ : 0 ≤ Q)
    (hE : 0 ≤ E) (hEE : E ≤ E') (hH : 0 ≤ H) (hweight : 0 ≤ weight)
    (hb : |value - (if k = 0 then originalRef else 0)| ≤ C * E ^ Q * H * weight) :
    |value - (if k = 0 then reference else 0)| ≤ C * E' ^ Q * H * weight := by
  rw [href]
  exact hb.trans (mul_le_mul_of_nonneg_right
    (mul_le_mul_of_nonneg_right
      (mul_le_mul_of_nonneg_left (Real.rpow_le_rpow hE hEE hQ) hC) hH) hweight)

/-- The actual corrected family on any smaller parameter domain has a
common physical full-height difference bound. The supplied towers are
arbitrary genuine towers of the retained physical coefficients. -/
theorem n04PulledFields_startCoefficient_physicalDifference
    (W : N04RealizationStart) {U : Set (StateDirections W.S × ℝ)} (hU : IsOpen U)
    (hsub : U ⊆ sectorNeighborhood W.S W.base W.ε W.ε)
    (RF : ∀ i : Fin 3, MixedJetRegularity U (annularOpen W.D)
      (fun z => canonicalCoefficientComponent i
        (W.L.coefficients (liftSectorParameter W.S W.C z)))) :
    ∃ B : ℕ, ∀ k : ℕ, ∃ L : ℕ, ∀ s : ℕ, ∃ C Q : ℝ,
      0 ≤ C ∧ 0 ≤ Q ∧ ∀ i z, z ∈ U →
      pairGrading (sectorGrading W.S) realGrading B z ≤ 1 →
      ∀ (y : annularOpen W.D) (a b : ℕ), a + b ≤ s →
      ∀ v : Fin k → StateDirections W.S × ℝ,
        |((RF i).parameter a b y.val y.property).D k z v -
          (if k = 0 then mixedDerivative a b
            (canonicalCoefficientComponent i (W.L.coefficients (W.C.referenceState, 0))) y.val
            else 0)| ≤ C * W.T.E0 y.val.1 ^ Q * W.T.H y.val.1 ^ (3 / 4 : ℝ) *
              oneHighVariationWeight (pairGrading (sectorGrading W.S) realGrading)
                B (s + L) z v := by
  let RO₀ := fun i => n04Realization_annularOriginalMixedRegularity
    W.through03.1.1 W.hS W.hT i
  let RA₀ := fun i => n04PulledFields_actualErrorMixedRegularity W.cutoff
    W.through03.1.1 W.hS W.hT W.through03.1.2 (n04PulledFields_errorProjection i)
  let RO : ∀ i : Fin 3, MixedJetRegularity U (annularOpen W.D)
      (fun z => originalCoefficientEntry W.D W.S W.C i (liftSectorParameter W.S W.C z)) :=
    fun i => ⟨fun z hz => (RO₀ i).spatial z (hsub hz),
      fun a b y hy => ((RO₀ i).parameter a b y hy).restrict hU hsub⟩
  let RA : ∀ i : Fin 3, MixedJetRegularity U (annularOpen W.D)
      (fun z y => n04PulledFields_errorProjection i
        (returnCorrectionCoefficientError W.D W.S W.C W.R W.cutoff.cutoff
          (liftSectorParameter W.S W.C z) y
            (W.R.residual (liftSectorParameter W.S W.C z)))) :=
    fun i => ⟨fun z hz => (RA₀ i).spatial z (hsub hz),
      fun a b y hy => ((RA₀ i).parameter a b y hy).restrict hU hsub⟩
  let D : ∀ k : ℕ, Fin 3 → (StateDirections W.S × ℝ) → annularOpen W.D →
      ℕ → ℕ → (Fin k → StateDirections W.S × ℝ) → ℝ := fun k i z y a b v =>
    ((RF i).parameter a b y.val y.property).D k z v -
      (if k = 0 then mixedDerivative a b
        (canonicalCoefficientComponent i (W.L.coefficients (W.C.referenceState, 0))) y.val else 0)
  let O : ∀ k : ℕ, Fin 3 → (StateDirections W.S × ℝ) → annularOpen W.D →
      ℕ → ℕ → (Fin k → StateDirections W.S × ℝ) → ℝ := fun k i z y a b v =>
    ((RO i).parameter a b y.val y.property).D k z v -
      (if k = 0 then mixedDerivative a b
        (originalCoefficientEntry W.D W.S W.C i (W.C.referenceState, 0)) y.val else 0)
  let A : ∀ k : ℕ, Fin 3 → (StateDirections W.S × ℝ) → annularOpen W.D →
      ℕ → ℕ → (Fin k → StateDirections W.S × ℝ) → ℝ := fun k i z y a b v =>
    ((RA i).parameter a b y.val y.property).D k z v
  apply n04PulledFields_finite_heightDifference
    (pairGrading (sectorGrading W.S) realGrading) (sectorPairGrading_monotone W.S) U
    (fun y : annularOpen W.D => W.T.E0 y.val.1)
    (fun y : annularOpen W.D => W.T.H y.val.1 ^ (3 / 4 : ℝ))
    (fun y => W.floor y.val.1)
    (fun y => Real.rpow_nonneg (W.hT.2.1 y.val.1 y.property.1).2.1.le _)
    W.base W.loss D O A
  · intro k i z hz y a b v
    exact n04PulledFields_startCoefficient_differenceJet W i hsub
      (RF i) (RO i) (RA i) k a b z hz y.val y.property v
  · intro k s
    let data := n04PulledFields_originalCoefficient_difference_physicalOneHigh
      W.through03.1.1 W.hS W.hT k s
    exact ⟨data.choose, data.choose_spec.choose, data.choose_spec.choose_spec.1.le,
      data.choose_spec.choose_spec.2.1, fun i z hz y a b hab v =>
      data.choose_spec.choose_spec.2.2 i a b hab y.val y.property U hU hsub
        ((RO i).parameter a b y.val y.property) z hz v⟩
  · intro i
    let data := n04PulledFields_actualError_physicalOneHigh W.cutoff
      W.through03.1.1 W.hS W.hT W.through03.1.2 W.host i (RA₀ i)
    refine ⟨data.choose, fun k => ?_⟩
    let order := data.choose_spec k
    refine ⟨order.choose, fun s => ?_⟩
    let bound := order.choose_spec s
    exact ⟨bound.choose, bound.choose_spec.choose, bound.choose_spec.choose_spec.1,
      bound.choose_spec.choose_spec.2.1, fun z hz hzlow y a b hab v =>
      bound.choose_spec.choose_spec.2.2 z (hsub hz) hzlow y.val y.property a b hab v⟩

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

/-- The retained three physical coefficients satisfy the complete
physical difference certificate, with no additional quantitative premise. -/
theorem n04PulledFields_coefficient_physicalDifference
    (G : N04RealizationGauge) (η : (G.W.S.height (3 / 4 : ℝ)).Space)
    {base : ℕ} {ε : ℝ} (hadm : G.Admissible base ε) :
    N04PulledFieldsPhysicalDifferenceOneHigh G η base ε (G.coefficientField η)
      (n04PulledFields_coefficientMixedOn G η hadm) := by
  have hsub : sectorNeighborhood (G.S η) base ε ε ⊆
      sectorNeighborhood G.W.S G.W.base G.W.ε G.W.ε :=
    sectorNeighborhood_mono (G.S η) hadm.1 hadm.2.2.1 hadm.2.2.1
  have href : G.lift η (0 : Parameter (G.S η)) = G.ref η := by
    apply Prod.ext
    · change G.W.C.referenceState + (0 : AnnularState G.W.S) = G.W.C.referenceState
      exact add_zero _
    · rfl
  let data := n04PulledFields_startCoefficient_physicalDifference G.W
    (isOpen_sectorNeighborhood (G.S η) base ε ε) hsub
    (n04PulledFields_coefficientMixedOn G η hadm)
  refine ⟨data.choose, fun k => ?_⟩
  let order := data.choose_spec k
  refine ⟨order.choose, fun s => ?_⟩
  let bound := order.choose_spec s
  refine ⟨bound.choose, bound.choose_spec.choose, bound.choose_spec.choose_spec.1,
    bound.choose_spec.choose_spec.2.1, fun i z hz hzlow y hy a b hab v => ?_⟩
  have hrefMixed := congrArg
    (fun w : AnnularState (G.S η) × ℝ => mixedDerivative a b (G.coefficientField η i w) y) href
  exact n04PulledFields_physicalDifference_envelope k hrefMixed
    bound.choose_spec.choose_spec.1 bound.choose_spec.choose_spec.2.1
    (zero_le_one.trans (G.W.floor y.1)) (le_enlargedMaterialData_E0 G.W.T y.1)
    (Real.rpow_nonneg (G.W.hT.2.1 y.1 hy.1).2.1.le _)
    (oneHighVariationWeight_nonneg _ _ _ _ _)
    (bound.choose_spec.choose_spec.2.2 i z hz hzlow ⟨y, hy⟩ a b hab v)

end ContinuousFlexibility.Analysis
