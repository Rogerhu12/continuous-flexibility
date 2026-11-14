module

public import ContinuousFlexibility.Analysis.N07aActualCoefficientBlocks
public import ContinuousFlexibility.Analysis.N07aModeProductBounds
public import ContinuousFlexibility.Analysis.N07aRelativeCanonicalPairing
public import ContinuousFlexibility.Analysis.N07aCubicMatrixRows

/-!
# The actual potential blocks, with their prescribed sign

The potential part of the original relative operator is multiplication
by the signed current-minus-reference potential.  Its ordinary and
frequency-commutator bounds retain the genuine height gain and one
parameter seminorm.
-/

@[expose] public section

noncomputable section

namespace ContinuousFlexibility.Analysis

open Set Filter MeasureTheory ContinuousFlexibility.Statements CanonicalGeometry

set_option backward.isDefEq.respectTransparency true

attribute [local instance]
  n07aNonlinearAnnularGroup n07aNonlinearAnnularModule
  n07aNonlinearAnnularAddGroup n07aNonlinearAnnularSMul n07aNonlinearAnnularSub
  n07aNonlinearAnnularParameterGroup n07aNonlinearAnnularParameterModule
  n07aNonlinearAnnularParameterAddGroup n07aNonlinearAnnularParameterSMul n07aNonlinearAnnularParameterSub
  n07aNonlinearDirectionsGroup n07aNonlinearDirectionsModule
  n07aNonlinearDirectionsAddGroup n07aNonlinearDirectionsSMul n07aNonlinearDirectionsSub
  n07aNonlinearSectorParameterGroup n07aNonlinearSectorParameterModule
  n07aNonlinearSectorParameterAddGroup n07aNonlinearSectorParameterSMul n07aNonlinearSectorParameterSub

theorem n07aCylinderPower_zero (u : N07aIntervalL2) : n07aCylinderPower 0 u = u := by
  apply Lp.ext
  exact (n07aCylinderPower_ae 0 u).mono fun x hx => by
    simpa only [pow_zero, one_mul] using hx

private theorem n07aCosineMatrixEntry_const_mul (c : ℝ) (f : ℝ → ℝ) (l j : ℕ) :
    n07aCosineMatrixEntry (fun θ => c * f θ) l j = c * n07aCosineMatrixEntry f l j :=
  n07aTrigMatrixEntry_const_mul false c f l j

private theorem n07aUnitJetRow_zero (f : PolarPoint → ℝ) (x : ℝ) :
    n07aUnitJetRow f 0 0 x = fun θ => f (x, θ) := by
  funext θ
  exact congrFun (spaces_mixedDerivative_zero f) (x, θ)

variable {D : ReferenceData} {T : MaterialData} {S : PhysicalSpacesData}
  {C : NonlinearGeometryData S} {L : ReturnCorrectionData S} {K : CanonicalData S}
  {base : ℕ} {ε : ℝ}

def n07aRelativePotentialCoefficient
    (href : ReferenceJets D T S C L K) (hcur : CurrentJets D T S C L K base ε)
    (z : Parameter S) (hz : z ∈ sectorNeighborhood S base ε ε)
    (m : ℕ) (hm : K.left m < K.right m) : N07aCanonicalOpenCoefficient S K m :=
  (N07aCanonicalOpenCoefficient.constMul (if K.positive m then -1 else (1 : ℝ))
    (n07aCurrentOpenCoefficient href hcur z hz m hm 4)).sub
    (N07aCanonicalOpenCoefficient.constMul (if K.positive m then -1 else (1 : ℝ))
      (n07aReferenceOpenCoefficient href m hm 4))

theorem n07aRelativePotentialCoefficient_unit
    (href : ReferenceJets D T S C L K) (hcur : CurrentJets D T S C L K base ε)
    (z : Parameter S) (hz : z ∈ sectorNeighborhood S base ε ε)
    (m : ℕ) (hm : K.left m < K.right m) (x θ : ℝ) :
    (n07aRelativePotentialCoefficient href hcur z hz m hm).value
      (n07aIntervalUnitMap (K.left m) (K.right m) x, θ) =
      (if K.positive m then -1 else (1 : ℝ)) *
        n07aUnitDifferenceAtom D T S C L K z m .potential (x, θ) := by
  change (if K.positive m then -1 else (1 : ℝ)) *
      K.potential (liftSectorParameter S C z) m
        (n07aIntervalUnitMap (K.left m) (K.right m) x, θ) -
    (if K.positive m then -1 else (1 : ℝ)) *
      K.potential (C.referenceState, 0) m
        (n07aIntervalUnitMap (K.left m) (K.right m) x, θ) = _
  change _ = (if K.positive m then -1 else (1 : ℝ)) *
    (K.potential (liftSectorParameter S C z) m (canonicalUnitPoint K m (x, θ)) -
      K.potential (C.referenceState, 0) m (canonicalUnitPoint K m (x, θ)))
  rw [show canonicalUnitPoint K m (x, θ) =
    (n07aIntervalUnitMap (K.left m) (K.right m) x, θ) by
      simp only [canonicalUnitPoint, n07aIntervalUnitMap, add_comm]]
  ring

theorem n07a_actualPotential_block_bound
    (href : ReferenceJets D T S C L K) (hcur : CurrentJets D T S C L K base ε) :
    ∃ d : ℕ, ∀ s : ℕ, ∃ B : ℝ, 0 < B ∧
      ∀ z (hz : z ∈ sectorNeighborhood S base ε ε), ∀ m (hm : K.left m < K.right m),
      ∀ u : CanonicalL2 S K m, n07aAngularReflection m u = u → ∀ j l : ℕ,
      n07aAngularBand m hm j u = u → ∀ commute : Bool,
      ‖(((1 + |(((j : ℤ) - l : ℤ) : ℝ)|) ^ s) *
          (if commute then ((l : ℝ) - j) else 1)) •
        n07aCanonicalUnitMode hm ((n07aRelativePotentialCoefficient href hcur z hz m hm).mul u) l‖ ≤
        8 * n07aDifferenceBlockBudget T S K d s B z m *
          n07aAngularTail ((j : ℤ) - l) * ‖n07aCanonicalUnitMode hm u j‖ := by
  let estimates := n07a_actualDifference_jet_block_bounds href hcur
  let d : ℕ := estimates.choose
  refine ⟨d, fun s => ?_⟩
  let B : ℝ := (estimates.choose_spec s).choose
  have hB : 0 < B := (estimates.choose_spec s).choose_spec.1
  have hbnd := (estimates.choose_spec s).choose_spec.2
  refine ⟨B, hB, ?_⟩
  intro z hz m hm u hu j l hband commute
  let W := (1 + |(((j : ℤ) - l : ℤ) : ℝ)|) ^ s
  let M := 8 * n07aDifferenceBlockBudget T S K d s B z m * n07aAngularTail ((j : ℤ) - l)
  let κ := W * (if commute then ((l : ℝ) - j) else 1)
  have hW : 0 ≤ W := by positivity
  have hM : 0 ≤ M := (mul_nonneg hW (abs_nonneg _)).trans
    (hbnd z hz m .potential (1 / 2) (by norm_num) 0 0 (by norm_num) l j).1
  have hrow (x : ℝ) (hx : x ∈ Ioo (0 : ℝ) 1) :
      |κ * n07aCosineMatrixEntry
        (fun θ => (n07aRelativePotentialCoefficient href hcur z hz m hm).value
          (n07aIntervalUnitMap (K.left m) (K.right m) x, θ)) l j| ≤ M * cylinderWeight x ^ 0 := by
    have h := hbnd z hz m .potential x hx 0 0 (by norm_num) l j
    dsimp only at h
    simp only [n07aUnitJetRow_zero] at h
    have hraw : |κ * n07aCosineMatrixEntry
        (fun θ => n07aUnitDifferenceAtom D T S C L K z m .potential (x, θ)) l j| ≤ M := by
      cases commute
      · change |(W * 1) * n07aCosineMatrixEntry
          (fun θ => n07aUnitDifferenceAtom D T S C L K z m .potential (x, θ)) l j| ≤ M
        rw [mul_one, abs_mul, abs_of_nonneg hW]
        exact h.1
      · change |(W * ((l : ℝ) - j)) * n07aCosineMatrixEntry
          (fun θ => n07aUnitDifferenceAtom D T S C L K z m .potential (x, θ)) l j| ≤ M
        rw [mul_assoc, abs_mul, abs_of_nonneg hW]
        exact h.2.2.1
    have hsign : |if K.positive m then (-1 : ℝ) else 1| = 1 := by
      cases K.positive m <;> norm_num
    simp_rw [n07aRelativePotentialCoefficient_unit]
    rw [n07aCosineMatrixEntry_const_mul, mul_left_comm κ, abs_mul, hsign, one_mul,
      pow_zero, mul_one]
    exact hraw
  have hfinal := n07aCanonicalProduct_cosine_norm_le hm
    (n07aRelativePotentialCoefficient href hcur z hz m hm) u hu j l 0 hband hM hrow
  rw [n07aCylinderPower_zero] at hfinal
  exact hfinal

end ContinuousFlexibility.Analysis
