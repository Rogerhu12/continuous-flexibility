module

public import ContinuousFlexibility.Analysis.N04NegativeInverseForwardBounds
public import ContinuousFlexibility.Analysis.N04NegativeInverseSpatialLinear

/-!
# The retained negative chart as an actual inverse system

These interfaces use the literal stored chart, inverse and height of
the reference-gauged atlas. The source is the whole original negative
component and the target is the fixed root strip. A smaller parameter
neighborhood changes neither function nor spatial domain.
-/

@[expose] public section

noncomputable section

namespace ContinuousFlexibility.Analysis

open Set ContinuousFlexibility.Statements CanonicalGeometry

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

namespace N04RealizationGauge

variable (G : N04RealizationGauge)

abbrev negativeInverseComponent (m : ℕ) : Set PolarPoint :=
  Ioo (G.W.C.left m) (G.W.C.right m) ×ˢ univ

abbrev negativeInverseTarget (m : ℕ) : Set PolarPoint :=
  Ioo (0 : ℝ) (n04bRootCutRadius (G.W.C.travel m)) ×ˢ univ

def negativeInverseForwardOn
    (η : (G.W.S.height (3 / 4 : ℝ)).Space)
    {b : ℕ} {ε : ℝ} (hadm : G.Admissible b ε)
    (k m : ℕ) (side : Bool) (hi : G.e k = .inl (m, side)) :
    SmoothDirections (sectorNeighborhood G.W.S b ε ε ×ˢ G.negativeInverseComponent m)
      (fun x : Parameter G.W.S × PolarPoint => (G.V η).chart (G.lift η x.1) k x.2) :=
  ((G.W.negativeChartJointTower m side).restrict
    ((sectorNeighborhood_isOpen G.W.S b ε ε).prod (isOpen_Ioo.prod isOpen_univ))
    (fun x hx => ⟨sectorNeighborhood_mono G.W.S hadm.1 hadm.2.2.1 hadm.2.2.1 hx.1, hx.2⟩)).congrOn
    (fun x _ => congrFun
      (G.negativeInverse_actual_fields η x.1 k m side hi).2.2.2.2.1.symm x.2)

def negativeInverseCanonicalOn
    (η : (G.W.S.height (3 / 4 : ℝ)).Space)
    {b : ℕ} {ε : ℝ} (hadm : G.Admissible b ε)
    (k m : ℕ) (side : Bool) (hi : G.e k = .inl (m, side)) :
    SmoothDirections (sectorNeighborhood G.W.S b ε ε ×ˢ G.negativeInverseTarget m)
      (fun x : Parameter G.W.S × PolarPoint => (G.V η).inverseChart (G.lift η x.1) k x.2) :=
  ((G.W.negativeInverseJointTower m side).restrict
    ((sectorNeighborhood_isOpen G.W.S b ε ε).prod (isOpen_Ioo.prod isOpen_univ))
    (fun x hx => ⟨sectorNeighborhood_mono G.W.S hadm.1 hadm.2.2.1 hadm.2.2.1 hx.1, hx.2⟩)).congrOn
    (fun x _ => congrFun
      (G.negativeInverse_actual_fields η x.1 k m side hi).2.2.2.2.2.1.symm x.2)

def negativeInverseHeightOn
    (η : (G.W.S.height (3 / 4 : ℝ)).Space)
    {b : ℕ} {ε : ℝ} (hadm : G.Admissible b ε)
    (k m : ℕ) (side : Bool) (hi : G.e k = .inl (m, side)) :
    SmoothDirections (sectorNeighborhood G.W.S b ε ε ×ˢ G.negativeInverseComponent m)
      (fun x : Parameter G.W.S × PolarPoint => (G.V η).height (G.lift η x.1) k x.2) :=
  ((G.W.negativeHeightJointTower m side).restrict
    ((sectorNeighborhood_isOpen G.W.S b ε ε).prod (isOpen_Ioo.prod isOpen_univ))
    (fun x hx => ⟨sectorNeighborhood_mono G.W.S hadm.1 hadm.2.2.1 hadm.2.2.1 hx.1, hx.2⟩)).congrOn
    (fun x _ => congrFun
      (G.negativeInverse_actual_fields η x.1 k m side hi).2.2.2.2.2.2.symm x.2)

def negativeInversePulledHeightOn
    (η : (G.W.S.height (3 / 4 : ℝ)).Space)
    {b : ℕ} {ε : ℝ} (hadm : G.Admissible b ε)
    (k m : ℕ) (side : Bool) (hi : G.e k = .inl (m, side)) :
    SmoothDirections (sectorNeighborhood G.W.S b ε ε ×ˢ G.negativeInverseTarget m)
      (fun x : Parameter G.W.S × PolarPoint =>
        (G.V η).height (G.lift η x.1) k ((G.V η).inverseChart (G.lift η x.1) k x.2)) := by
  apply ((G.W.negativePulledHeightJointTower m side).restrict
    ((sectorNeighborhood_isOpen G.W.S b ε ε).prod (isOpen_Ioo.prod isOpen_univ))
    (fun x hx => ⟨sectorNeighborhood_mono G.W.S hadm.1 hadm.2.2.1 hadm.2.2.1 hx.1, hx.2⟩)).congrOn
  intro x hx
  have hf := G.negativeInverse_actual_fields η x.1 k m side hi
  exact (congrArg₂ (fun (F : PolarPoint → ℝ) (p : PolarPoint) => F p)
    hf.2.2.2.2.2.2 (congrFun hf.2.2.2.2.2.1 x.2)).symm

theorem negativeInverseCanonical_maps
    (η : (G.W.S.height (3 / 4 : ℝ)).Space)
    {b : ℕ} {ε : ℝ} (hadm : G.Admissible b ε)
    (k m : ℕ) (side : Bool) (hi : G.e k = .inl (m, side)) :
    MapsTo
      (fun x : Parameter G.W.S × PolarPoint => (G.V η).inverseChart (G.lift η x.1) k x.2)
      (sectorNeighborhood G.W.S b ε ε ×ˢ G.negativeInverseTarget m)
      (G.negativeInverseComponent m) := by
  intro x hx
  have hf := G.negativeInverse_actual_fields η x.1 k m side hi
  exact (congrArg (fun p : PolarPoint => p ∈ G.negativeInverseComponent m)
    (congrFun hf.2.2.2.2.2.1 x.2)).mpr
      (G.W.negativeInverse_maps_component m side
        (sectorNeighborhood_mono G.W.S hadm.1 hadm.2.2.1 hadm.2.2.1 hx.1) hx.2)

theorem negativeInverseCanonical_right
    (η : (G.W.S.height (3 / 4 : ℝ)).Space)
    {b : ℕ} {ε : ℝ} (hadm : G.Admissible b ε)
    (k m : ℕ) (side : Bool) (hi : G.e k = .inl (m, side))
    {x : Parameter G.W.S × PolarPoint}
    (hx : x ∈ sectorNeighborhood G.W.S b ε ε ×ˢ G.negativeInverseTarget m) :
    (G.V η).chart (G.lift η x.1) k ((G.V η).inverseChart (G.lift η x.1) k x.2) = x.2 := by
  have hf := G.negativeInverse_actual_fields η x.1 k m side hi
  exact (congrArg₂ (fun (F : PolarPoint → PolarPoint) (p : PolarPoint) => F p)
    hf.2.2.2.2.1 (congrFun hf.2.2.2.2.2.1 x.2)).trans
      (G.W.negativeInverse_right m side
        (sectorNeighborhood_mono G.W.S hadm.1 hadm.2.2.1 hadm.2.2.1 hx.1) hx.2)

theorem negativeInverseCanonical_jacobian_ne_zero
    (η : (G.W.S.height (3 / 4 : ℝ)).Space)
    {b : ℕ} {ε : ℝ} (hadm : G.Admissible b ε)
    (k m : ℕ) (side : Bool) (hi : G.e k = .inl (m, side))
    {x : Parameter G.W.S × PolarPoint}
    (hx : x ∈ sectorNeighborhood G.W.S b ε ε ×ˢ G.negativeInverseTarget m) :
    planeJacobian ((G.V η).chart (G.lift η x.1) k)
      ((G.V η).inverseChart (G.lift η x.1) k x.2) ≠ 0 := by
  have hz := sectorNeighborhood_mono G.W.S hadm.1 hadm.2.2.1 hadm.2.2.1 hx.1
  have hf := G.negativeInverse_actual_fields η x.1 k m side hi
  have he := congrArg₂
    (fun (F : PolarPoint → PolarPoint) (p : PolarPoint) => planeJacobian F p)
      hf.2.2.2.2.1 (congrFun hf.2.2.2.2.2.1 x.2)
  have hne := G.W.negativeChart_jacobian_ne_zero m side hz
    (G.W.negativeInverse_maps_component m side hz hx.2)
  exact fun hzero => hne (he.symm.trans hzero)

theorem negativeInverseUnit_maps
    (η : (G.W.S.height (3 / 4 : ℝ)).Space)
    (k m : ℕ) (side : Bool) (hi : G.e k = .inl (m, side)) :
    MapsTo (canonicalUnitPoint (G.V η) k) unitStrip (G.negativeInverseTarget m) := by
  intro q hq
  exact (congrArg (fun p : PolarPoint => p ∈ G.negativeInverseTarget m)
    (congrFun (G.negative_canonicalUnitPoint η k (m, side) hi) q)).mpr
      (G.W.negativeCanonicalUnit_mapsTo G.X.e₀ (G.negativeIndex (m, side)) m side
        (G.X.e₀.apply_symm_apply _) hq)

def negativeInverseCanonicalLinear
    (η : (G.W.S.height (3 / 4 : ℝ)).Space) (k : ℕ) : PolarPoint →L[ℝ] PolarPoint :=
  (((G.V η).right k - (G.V η).left k) • ContinuousLinearMap.fst ℝ ℝ ℝ).prod
    (ContinuousLinearMap.snd ℝ ℝ ℝ)

theorem negativeInverseUnit_eq_affine
    (η : (G.W.S.height (3 / 4 : ℝ)).Space) (k : ℕ) (q : PolarPoint) :
    canonicalUnitPoint (G.V η) k q = ((G.V η).left k, 0) +
      G.negativeInverseCanonicalLinear η k q := by
  simp only [negativeInverseCanonicalLinear, canonicalUnitPoint,
    ContinuousLinearMap.prod_apply, smul_apply, ContinuousLinearMap.coe_fst',
    ContinuousLinearMap.coe_snd', smul_eq_mul, Prod.mk_add_mk, zero_add]

theorem negativeInverseCanonicalLinear_norm
    (η : (G.W.S.height (3 / 4 : ℝ)).Space) (k : ℕ) :
    ‖G.negativeInverseCanonicalLinear η k‖ ≤
      1 + |(G.V η).right k - (G.V η).left k| := by
  apply ContinuousLinearMap.opNorm_le_bound _ (by positivity)
  intro q
  simp only [negativeInverseCanonicalLinear, ContinuousLinearMap.prod_apply,
    smul_apply, ContinuousLinearMap.coe_fst', ContinuousLinearMap.coe_snd', smul_eq_mul,
    Prod.norm_def, Real.norm_eq_abs, abs_mul]
  have h₁ : |q.1| ≤ ‖q‖ := by simpa only [Real.norm_eq_abs] using norm_fst_le q
  have h₂ : |q.2| ≤ ‖q‖ := by simpa only [Real.norm_eq_abs] using norm_snd_le q
  apply max_le
  · exact (mul_le_mul_of_nonneg_left h₁ (abs_nonneg _)).trans
      (mul_le_mul_of_nonneg_right (le_add_of_nonneg_left zero_le_one) (norm_nonneg q))
  · exact h₂.trans (le_mul_of_one_le_left (norm_nonneg q)
      (le_add_of_nonneg_right (abs_nonneg _)))

end N04RealizationGauge
end ContinuousFlexibility.Analysis

/-- info: 'ContinuousFlexibility.Analysis.N04RealizationGauge.negativeInverseCanonical_right' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms ContinuousFlexibility.Analysis.N04RealizationGauge.negativeInverseCanonical_right
