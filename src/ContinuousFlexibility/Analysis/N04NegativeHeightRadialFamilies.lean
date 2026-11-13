import ContinuousFlexibility.Analysis.N04NegativeGeometrySpatialRegularity
import ContinuousFlexibility.Analysis.N01CoefficientParameterTower
import ContinuousFlexibility.Analysis.N01CoefficientJointTower
import ContinuousFlexibility.Analysis.N04RealizationCubicRegularity
import ContinuousFlexibility.Analysis.N07aCanonicalUnitCoefficient

/-!
# The physical radial coefficient on a retained negative half

The optical correction leaves the radial coefficient unchanged. Its
physical unit pullback therefore has the genuine N01 coefficient
difference tower, multiplied only by a fixed power of the half length.
All fields here use the stored physical endpoints, independently of the
moving artificial cut and of the auxiliary column.
-/

noncomputable section

namespace ContinuousFlexibility.Analysis

open Set ContinuousFlexibility.Statements CanonicalGeometry
open scoped ContDiff

namespace N04RealizationGauge

variable (G : N04RealizationGauge)
  (η : (G.W.S.height (3 / 4 : ℝ)).Space)

def physicalRadialFamily : Parameter (G.S η) → ℕ → PolarPoint → ℝ :=
  fun z m q => ((G.L η).coefficients (G.lift η z)).a
    (physicalUnitPoint (G.V η) m q)

def physicalRadialRef : ℕ → PolarPoint → ℝ :=
  fun m q => ((G.L η).coefficients (G.ref η)).a
    (physicalUnitPoint (G.V η) m q)

theorem physicalRadialFamily_eq_original (z : Parameter G.W.S) (m : ℕ) (q : PolarPoint) :
    G.physicalRadialFamily η z m q =
      (originalCoefficients G.W.D G.W.S G.W.C
        (liftSectorParameter G.W.S G.W.C z)).a (physicalUnitPoint (G.V η) m q) := by
  change (G.W.L.coefficients (liftSectorParameter G.W.S G.W.C z)).a _ = _
  rw [G.W.coefficients_eq, returnCorrectedCoefficients_a]

theorem physicalRadialRef_eq_original (m : ℕ) (q : PolarPoint) :
    G.physicalRadialRef η m q =
      (originalCoefficients G.W.D G.W.S G.W.C (G.W.C.referenceState, 0)).a
        (physicalUnitPoint (G.V η) m q) := by
  change (G.W.L.coefficients (G.W.C.referenceState, 0)).a _ = _
  rw [G.W.coefficients_eq, returnCorrectedCoefficients_a]

theorem physicalRadialFamily_zero (m : ℕ) :
    G.physicalRadialFamily η 0 m = G.physicalRadialRef η m := by
  funext q
  change (G.W.L.coefficients
    (liftSectorParameter G.W.S G.W.C (0 : Parameter G.W.S))).a _ = _
  simp only [liftSectorParameter, Prod.fst_zero, Prod.snd_zero,
    ZeroMemClass.coe_zero, add_zero]
  rfl

theorem heightRadial_physicalUnitPoint_eq (m : ℕ) (j : ℕ × Bool)
    (hi : G.e m = .inl j) :
    physicalUnitPoint (G.V η) m =
      physicalUnitPoint (G.W.A G.X.e₀) (G.negativeIndex j) := by
  have hf := G.negative_fields η (G.W.C.referenceState, 0) m j hi
  funext q
  simp only [physicalUnitPoint, hf.2.2.1, hf.2.2.2.1]

theorem heightRadial_physicalBounds (m : ℕ) (j : ℕ × Bool)
    (hi : G.e m = .inl j) :
    G.W.D.a < (G.V η).physicalLeft m ∧
      (G.V η).physicalLeft m < (G.V η).physicalRight m ∧
      (G.V η).physicalRight m < G.W.D.b := by
  have hf := G.negative_fields η (G.W.C.referenceState, 0) m j hi
  rw [hf.2.2.1, hf.2.2.2.1]
  have hk : G.X.e₀ (G.negativeIndex j) = .inl j := G.X.e₀.apply_symm_apply _
  change G.W.D.a < n04bReferenceTypedLeft G.W.C
      (n04bActualReferenceCut G.W.through03) (G.X.e₀ (G.negativeIndex j)) ∧
    n04bReferenceTypedLeft G.W.C (n04bActualReferenceCut G.W.through03)
        (G.X.e₀ (G.negativeIndex j)) <
      n04bReferenceTypedRight G.W.C (n04bActualReferenceCut G.W.through03)
        (G.X.e₀ (G.negativeIndex j)) ∧
    n04bReferenceTypedRight G.W.C (n04bActualReferenceCut G.W.through03)
      (G.X.e₀ (G.negativeIndex j)) < G.W.D.b
  rw [hk]
  exact n04b_negativeHalf_bounds G.W.through03.1.1.2.2.2.1
    (n04bActualReferenceCut_mem G.W.through03) j

theorem heightRadial_physicalUnitPoint_mem (m : ℕ) (j : ℕ × Bool)
    (hi : G.e m = .inl j) {q : PolarPoint} (hq : q ∈ unitStrip) :
    physicalUnitPoint (G.V η) m q ∈
      Ioo (G.W.C.left j.1) (G.W.C.right j.1) ×ˢ (univ : Set ℝ) := by
  have hk : G.X.e₀ (G.negativeIndex j) = .inl (j.1, j.2) := G.X.e₀.apply_symm_apply _
  have hA := n04b_actualTypedAtlas_partA
    G.W.hT G.W.hS G.W.through03 G.W.field G.X.e₀
  rw [G.heightRadial_physicalUnitPoint_eq η m j hi]
  apply n04NegativeGeometry_referenceHalf_subset_component
    G.W.hT G.W.hS G.W.through03 G.W.field G.X.e₀
    (G.negativeIndex j) j.1 j.2 hk
  exact (n04NegativeGeometry_affine_unitPoint _ _
    (hA.referenceBounds (G.negativeIndex j)).1).2.1 hq

theorem heightRadial_physicalUnitPoint_mem_annulus (m : ℕ)
    (hm : G.Neg η m) {q : PolarPoint} (hq : q ∈ unitStrip) :
    physicalUnitPoint (G.V η) m q ∈ annularOpen G.W.D := by
  obtain ⟨j, hi⟩ := (G.neg_iff_inl η m).mp hm
  exact G.W.through03.1.1.negativeComponent_subset_annularOpen j.1
    (G.heightRadial_physicalUnitPoint_mem η m j hi hq)

theorem physicalRadial_spatial (z : Parameter G.W.S)
    (hz : z ∈ sectorNeighborhood G.W.S G.W.base G.W.ε G.W.ε)
    (m : ℕ) (hm : G.Neg η m) :
    ContDiffOn ℝ ∞ (G.physicalRadialFamily η z m) unitStrip ∧
      ∀ q ∈ unitStrip, G.physicalRadialFamily η z m (q + (0, Real.pi)) =
        G.physicalRadialFamily η z m q := by
  have hz' := liftSectorParameter_mem_stateNeighborhood (C := G.W.C) hz le_rfl
  have hs := G.W.through03.1.1.2.2.1.liftSectorParameter_sector z
  have hf := (G.W.field.smooth_coefficients _ hz' hs).1
  have hmap : MapsTo (physicalUnitPoint (G.V η) m) unitStrip (annularOpen G.W.D) :=
    fun _ hq => G.heightRadial_physicalUnitPoint_mem_annulus η m hm hq
  have hpoint : ContDiff ℝ ∞ (physicalUnitPoint (G.V η) m) :=
    (contDiff_const.add (contDiff_const.mul contDiff_fst)).prodMk contDiff_snd
  refine ⟨hf.comp hpoint.contDiffOn hmap, ?_⟩
  intro q hq
  have hper := (G.W.field.periodic_coefficients _ hz' hs
    (physicalUnitPoint (G.V η) m q).1 (hmap hq).1).1 q.2
  simpa only [physicalRadialFamily, physicalUnitPoint, Prod.fst_add, Prod.snd_add,
    add_zero] using hper

theorem physicalRadial_pos (z : Parameter G.W.S)
    (hz : z ∈ sectorNeighborhood G.W.S G.W.base G.W.ε G.W.ε)
    (m : ℕ) (hm : G.Neg η m) {q : PolarPoint} (hq : q ∈ unitStrip) :
    0 < G.physicalRadialFamily η z m q :=
  G.W.field.positive_a _ (liftSectorParameter_mem_stateNeighborhood hz le_rfl)
    (G.W.through03.1.1.2.2.1.liftSectorParameter_sector z) _
    (G.heightRadial_physicalUnitPoint_mem_annulus η m hm hq)

theorem physicalRadial_difference_mixed (z : Parameter G.W.S) (m i j : ℕ)
    (q : PolarPoint) :
    mixedDerivative i j
        (fun y => G.physicalRadialFamily η z m y - G.physicalRadialRef η m y) q =
      ((G.V η).physicalRight m - (G.V η).physicalLeft m) ^ i *
        coefficientFamily G.W.D G.W.S G.W.C 0 i j
          (physicalUnitPoint (G.V η) m q) (liftSectorParameter G.W.S G.W.C z) := by
  have heq :
      (fun y => G.physicalRadialFamily η z m y - G.physicalRadialRef η m y) =
        (fun y =>
          (originalCoefficients G.W.D G.W.S G.W.C
            (liftSectorParameter G.W.S G.W.C z)).a (physicalUnitPoint (G.V η) m y) -
          (originalCoefficients G.W.D G.W.S G.W.C (G.W.C.referenceState, 0)).a
            (physicalUnitPoint (G.V η) m y)) := by
    funext y
    rw [G.physicalRadialFamily_eq_original, G.physicalRadialRef_eq_original]
  rw [heq]
  simpa only [coefficientFamily, if_true, physicalUnitPoint] using
    n07a_mixedDerivative_radialAffine
      (fun p => (originalCoefficients G.W.D G.W.S G.W.C
          (liftSectorParameter G.W.S G.W.C z)).a p -
        (originalCoefficients G.W.D G.W.S G.W.C (G.W.C.referenceState, 0)).a p)
      ((G.V η).physicalLeft m)
      ((G.V η).physicalRight m - (G.V η).physicalLeft m) i j q

def heightRadialLabel (m : ℕ) (hm : G.Neg η m) : ℕ × Bool :=
  ((G.neg_iff_inl η m).mp hm).choose

theorem heightRadialLabel_spec (m : ℕ) (hm : G.Neg η m) :
    G.e m = .inl (G.heightRadialLabel η m hm) :=
  ((G.neg_iff_inl η m).mp hm).choose_spec

def heightRadialDifferenceTower (m : ℕ) (hm : G.Neg η m) (i j : ℕ) (q : unitStrip) :
    SmoothDirections (sectorNeighborhood G.W.S G.W.base G.W.ε G.W.ε)
      (fun z => mixedDerivative i j
        (fun y => G.physicalRadialFamily η z m y - G.physicalRadialRef η m y) q.val) := by
  let t := G.heightRadialLabel η m hm
  have hp := G.heightRadial_physicalUnitPoint_mem η m t
    (G.heightRadialLabel_spec η m hm) q.property
  let J := G.W.through03.1.1.sectorCoefficientTower (G.W.C.cell t.1) 0 i j
    (physicalUnitPoint (G.V η) m q.val) (G.W.host t.1 hp.1)
  let c := ((G.V η).physicalRight m - (G.V η).physicalLeft m) ^ i
  exact (smoothDirections_postcompCLM J (c • ContinuousLinearMap.id ℝ ℝ)).congr
    (fun z _ => by
      simp only [Function.comp_apply, smul_apply, ContinuousLinearMap.id_apply, smul_eq_mul]
      exact (G.physicalRadial_difference_mixed η z m i j q.val).symm)

theorem heightRadialDifferenceTower_apply (m : ℕ) (hm : G.Neg η m)
    (i j : ℕ) (q : unitStrip) (k : ℕ) {z : Parameter G.W.S}
    (hz : z ∈ sectorNeighborhood G.W.S G.W.base G.W.ε G.W.ε)
    (v : Fin k → Parameter G.W.S) :
    (G.heightRadialDifferenceTower η m hm i j q).D k z v =
      ((G.V η).physicalRight m - (G.V η).physicalLeft m) ^ i *
        (G.W.through03.1.1.sectorCoefficientTower
          (G.W.C.cell (G.heightRadialLabel η m hm).1) 0 i j
          (physicalUnitPoint (G.V η) m q.val)
          (G.W.host _ (G.heightRadial_physicalUnitPoint_mem η m _
            (G.heightRadialLabel_spec η m hm) q.property).1)).D k z v := by
  apply n04Realization_smoothDirections_D_const_mul _
    (G.heightRadialDifferenceTower η m hm i j q) _
    (fun x _ => G.physicalRadial_difference_mixed η x m i j q.val) k hz v

end N04RealizationGauge
end ContinuousFlexibility.Analysis
