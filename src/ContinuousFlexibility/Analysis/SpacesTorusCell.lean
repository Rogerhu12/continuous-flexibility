import ContinuousFlexibility.Analysis.SpacesTorusFourier
import ContinuousFlexibility.Analysis.SpacesRadialPartition
import ContinuousFlexibility.Analysis.SpacesMollifierL1
import Mathlib.Analysis.Real.Pi.Bounds

/-!
# Normalized torus coordinates on physical unit cells

A radial interval of length six and one full angular period carry exactly
`6π` times the normalized torus measure. The explicit coordinate map below
records that normalization as a measure-preserving map, so all subsequent
Fourier estimates use the actual prescribed cylinder measure.
-/

noncomputable section

namespace ContinuousFlexibility.Statements

open Set Filter MeasureTheory ContinuousFlexibility.Analysis
open scoped ENNReal Topology

set_option backward.isDefEq.respectTransparency false

/-- The representative in one half-open interval of length one. -/
def spacesUnitCircleRepresentative (a : ℝ) (x : UnitAddCircle) : ℝ :=
  (AddCircle.equivIoc 1 a x).val

theorem spacesUnitCircleRepresentative_preserving (a : ℝ) :
    MeasurePreserving (spacesUnitCircleRepresentative a) AddCircle.haarAddCircle
      (volume.restrict (Ioc a (a + 1))) := by
  have hc := AddCircle.measurePreserving_equivIoc (1 : ℝ) (a := a)
  rw [AddCircle.volume_eq_smul_haarAddCircle] at hc
  simp only [ENNReal.ofReal_one, one_smul] at hc
  have hs : MeasurePreserving (Subtype.val : Ioc a (a + 1) → ℝ)
      (Measure.comap Subtype.val volume) (volume.restrict (Ioc a (a + 1))) :=
    ⟨measurable_subtype_coe, map_comap_subtype_coe measurableSet_Ioc volume⟩
  exact hs.comp hc

theorem spaces_affineInterval_preserving (r : ℝ) (hr : 0 < r) (c a b : ℝ) :
    MeasurePreserving (fun x : ℝ => r * x + c) (volume.restrict (Ioc a b))
      (ENNReal.ofReal r⁻¹ • volume.restrict (Ioc (r * a + c) (r * b + c))) := by
  have hs : MeasurePreserving (fun x : ℝ => r * x) volume
      (ENNReal.ofReal r⁻¹ • volume) := by
    refine ⟨measurable_const_mul r, ?_⟩
    simpa only [abs_of_pos (inv_pos.mpr hr)] using Real.map_volume_mul_left hr.ne'
  have ht := (measurePreserving_add_right (volume : Measure ℝ) c).smul_measure (ENNReal.ofReal r⁻¹)
  have h := (ht.comp hs).restrict_preimage (s := Ioc (r * a + c) (r * b + c)) measurableSet_Ioc
  have he : (fun x : ℝ => r * x + c) ⁻¹' Ioc (r * a + c) (r * b + c) = Ioc a b := by
    ext x
    simp only [mem_preimage, mem_Ioc]
    constructor <;> intro hx <;> constructor <;> nlinarith [hx.1, hx.2]
  simpa only [Function.comp_def, he, Measure.restrict_smul] using h

/-- A full period cell, strictly wider than the localization envelopes. -/
def spacesPhysicalCell (n : ℤ) : Set PolarPoint :=
  Ioc ((n : ℝ) - 3) (n + 3) ×ˢ Ioc 0 Real.pi

def spacesPhysicalCellMeasure (n : ℤ) : Measure PolarPoint :=
  ENNReal.ofReal ((6 * Real.pi)⁻¹) • volume.restrict (spacesPhysicalCell n)

/-- The explicit normalized torus chart of a physical cell. -/
def spacesPhysicalCellChart (n : ℤ) (t : SpacesTorus) : PolarPoint :=
  (6 * spacesUnitCircleRepresentative (-(1 / 2 : ℝ)) (t 0) + n,
    Real.pi * spacesUnitCircleRepresentative 0 (t 1))

theorem spacesPhysicalCellChart_preserving (n : ℤ) :
    MeasurePreserving (spacesPhysicalCellChart n)
      (Measure.pi (fun _ : Fin 2 => AddCircle.haarAddCircle)) (spacesPhysicalCellMeasure n) := by
  let : SFinite angleMeasure := by unfold angleMeasure; infer_instance
  have hrep : MeasurePreserving (spacesUnitCircleRepresentative (-(1 / 2 : ℝ)))
      AddCircle.haarAddCircle (volume.restrict (Ioc (-(1 / 2 : ℝ)) (1 / 2))) := by
    convert spacesUnitCircleRepresentative_preserving (-(1 / 2 : ℝ)) using 1
    norm_num
  have hrept : MeasurePreserving (spacesUnitCircleRepresentative 0)
      AddCircle.haarAddCircle (volume.restrict (Ioc (0 : ℝ) 1)) := by
    simpa only [zero_add] using spacesUnitCircleRepresentative_preserving 0
  have hr := (spaces_affineInterval_preserving 6 (by norm_num) n (-(1 / 2 : ℝ)) (1 / 2)).comp hrep
  have hθ := (spaces_affineInterval_preserving Real.pi Real.pi_pos 0 0 1).comp hrept
  norm_num only [neg_add_cancel, zero_add, mul_zero, mul_one, add_zero] at hθ
  have hrad : MeasurePreserving
      (fun t : UnitAddCircle => 6 * spacesUnitCircleRepresentative (-(1 / 2 : ℝ)) t + n)
      AddCircle.haarAddCircle
      (ENNReal.ofReal (6 : ℝ)⁻¹ • volume.restrict (Ioc ((n : ℝ) - 3) (n + 3))) := by
    simpa only [Function.comp_def,
      show 6 * (-(1 / 2 : ℝ)) + n = (n : ℝ) - 3 by ring,
      show 6 * (1 / 2 : ℝ) + n = (n : ℝ) + 3 by ring] using hr
  have ht : MeasurePreserving
      (fun t : UnitAddCircle => Real.pi * spacesUnitCircleRepresentative 0 t)
      AddCircle.haarAddCircle (ENNReal.ofReal Real.pi⁻¹ • angleMeasure) := hθ
  have hp := (hrad.prod ht).comp
    (measurePreserving_finTwoArrow AddCircle.haarAddCircle)
  have hm : (ENNReal.ofReal (6 : ℝ)⁻¹ • volume.restrict (Ioc ((n : ℝ) - 3) (n + 3))).prod
      (ENNReal.ofReal Real.pi⁻¹ • angleMeasure) = spacesPhysicalCellMeasure n := by
    rw [Measure.prod_smul_left, Measure.prod_smul_right, smul_smul]
    simp only [angleMeasure, spacesPhysicalCellMeasure, spacesPhysicalCell,
      ← Measure.prod_restrict, Measure.volume_eq_prod]
    congr 1
    rw [← ENNReal.ofReal_mul (by positivity), mul_inv_rev]
    congr 1
    ring
  rw [hm] at hp
  exact hp

theorem spacesPhysicalCellChart_mem (n : ℤ) (t : SpacesTorus) :
    spacesPhysicalCellChart n t ∈ spacesPhysicalCell n := by
  have hr := (AddCircle.equivIoc 1 (-(1 / 2 : ℝ)) (t 0)).property
  have hθ := (AddCircle.equivIoc 1 0 (t 1)).property
  change _ < _ ∧ _ ≤ _ at hr hθ
  change (
      (n : ℝ) - 3 < 6 * spacesUnitCircleRepresentative (-(1 / 2 : ℝ)) (t 0) + n ∧
      6 * spacesUnitCircleRepresentative (-(1 / 2 : ℝ)) (t 0) + n ≤ n + 3) ∧
    (0 < Real.pi * spacesUnitCircleRepresentative 0 (t 1) ∧
      Real.pi * spacesUnitCircleRepresentative 0 (t 1) ≤ Real.pi)
  dsimp only [spacesUnitCircleRepresentative]
  constructor
  · constructor <;> linarith [hr.1, hr.2]
  · constructor <;> nlinarith [hθ.1, hθ.2, Real.pi_pos]


/-- Reduction to the normalized torus coordinates of one physical cell. -/
def spacesPhysicalCellQuotient (n : ℤ) (p : PolarPoint) : SpacesTorus :=
  ![(((p.1 - n) / 6 : ℝ) : UnitAddCircle), ((p.2 / Real.pi : ℝ) : UnitAddCircle)]

theorem spacesPhysicalCellQuotient_continuous (n : ℤ) : Continuous (spacesPhysicalCellQuotient n) := by
  apply continuous_pi
  intro i
  fin_cases i
  · exact (AddCircle.continuous_mk' (1 : ℝ)).comp
      ((continuous_fst.sub continuous_const).div_const 6)
  · exact (AddCircle.continuous_mk' (1 : ℝ)).comp (continuous_snd.div_const Real.pi)

theorem spacesPhysicalCellQuotient_chart (n : ℤ) (t : SpacesTorus) :
    spacesPhysicalCellQuotient n (spacesPhysicalCellChart n t) = t := by
  funext i
  fin_cases i
  · simp [spacesPhysicalCellQuotient, spacesPhysicalCellChart, spacesUnitCircleRepresentative]
  · simp [spacesPhysicalCellQuotient, spacesPhysicalCellChart, spacesUnitCircleRepresentative, Real.pi_ne_zero]

theorem spacesPhysicalCellChart_quotient (n : ℤ) {p : PolarPoint}
    (hp : p ∈ spacesPhysicalCell n) :
    spacesPhysicalCellChart n (spacesPhysicalCellQuotient n p) = p := by
  have hr : (p.1 - n) / 6 ∈ Ioc (-(1 / 2 : ℝ)) (-(1 / 2 : ℝ) + 1) := by
    constructor <;> linarith [hp.1.1, hp.1.2]
  have hθ : p.2 / Real.pi ∈ Ioc (0 : ℝ) (0 + 1) := by
    constructor
    · exact div_pos hp.2.1 Real.pi_pos
    · simpa only [zero_add] using (div_le_one Real.pi_pos).mpr hp.2.2
  simp only [spacesPhysicalCellChart, spacesPhysicalCellQuotient, Matrix.cons_val_zero,
    Matrix.cons_val_one, spacesUnitCircleRepresentative,
    AddCircle.equivIoc_coe_eq hr, AddCircle.equivIoc_coe_eq hθ]
  apply Prod.ext <;> dsimp only
  · ring
  · exact mul_div_cancel₀ _ Real.pi_ne_zero

theorem spacesPhysicalCellQuotient_preserving (n : ℤ) :
    MeasurePreserving (spacesPhysicalCellQuotient n) (spacesPhysicalCellMeasure n)
      (Measure.pi (fun _ : Fin 2 => AddCircle.haarAddCircle)) := by
  have hc := spacesPhysicalCellChart_preserving n
  have hq := (spacesPhysicalCellQuotient_continuous n).measurable
  refine ⟨hq, ?_⟩
  rw [← hc.map_eq, Measure.map_map hq hc.measurable]
  have he : spacesPhysicalCellQuotient n ∘ spacesPhysicalCellChart n = id :=
    funext (spacesPhysicalCellQuotient_chart n)
  rw [he, Measure.map_id]

theorem spacesPhysicalCell_measurable (n : ℤ) : MeasurableSet (spacesPhysicalCell n) :=
  measurableSet_Ioc.prod measurableSet_Ioc

theorem spacesPhysicalCellMeasure_ae_mem (n : ℤ) :
    ∀ᵐ p ∂spacesPhysicalCellMeasure n, p ∈ spacesPhysicalCell n := by
  unfold spacesPhysicalCellMeasure
  exact (ae_restrict_mem (spacesPhysicalCell_measurable n)).filter_mono
    (Measure.ae_smul_measure_le _)

theorem spacesPhysicalCellMeasure_le_cylinder (n : ℤ) :
    spacesPhysicalCellMeasure n ≤ materialCylinderMeasure := by
  have hc : ENNReal.ofReal ((6 * Real.pi)⁻¹) ≤ 1 := by
    apply ENNReal.ofReal_le_one.mpr
    apply inv_le_one_of_one_le₀
    linarith [Real.pi_gt_three]
  calc
    spacesPhysicalCellMeasure n ≤ (1 : ℝ≥0∞) • volume.restrict (spacesPhysicalCell n) :=
      by
        intro s
        simp only [spacesPhysicalCellMeasure, Measure.smul_apply, smul_eq_mul]
        gcongr
    _ = volume.restrict (spacesPhysicalCell n) := one_smul _ _
    _ ≤ materialCylinderMeasure := Measure.restrict_mono (by
      intro p hp
      exact ⟨mem_univ _, hp.2⟩) le_rfl

theorem spacesPhysicalCellMeasure_scale (n : ℤ) :
    ENNReal.ofReal (6 * Real.pi) • spacesPhysicalCellMeasure n =
      materialCylinderMeasure.restrict (Ioc ((n : ℝ) - 3) (n + 3) ×ˢ (univ : Set ℝ)) := by
  rw [spacesPhysicalCellMeasure, smul_smul,
    ← ENNReal.ofReal_mul (by positivity), mul_inv_cancel₀ (by positivity : 6 * Real.pi ≠ 0),
    ENNReal.ofReal_one, one_smul]
  unfold materialCylinderMeasure spacesPhysicalCell
  rw [Measure.restrict_restrict (measurableSet_Ioc.prod MeasurableSet.univ)]
  congr 1
  ext p
  simp only [mem_inter_iff, mem_prod, mem_univ, true_and, and_comm]

end ContinuousFlexibility.Statements
