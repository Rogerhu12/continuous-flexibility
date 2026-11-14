module

public import ContinuousFlexibility.Analysis.N04LiouvilleCharts
public import ContinuousFlexibility.Statements.Nonlinear
public import Mathlib.MeasureTheory.Measure.Prod
public import Mathlib.MeasureTheory.Measure.Typeclasses.NullSingletonClass
public import Mathlib.Topology.OpenPartialHomeomorph.Defs

/-!
# Closed reference charts and the planar reference partition

The oriented affine Liouville chart is a global homeomorphism with the
already defined inverse. Thus its stored inverse is the genuine smooth
inverse germ at every boundary point. The radial exceptional set of the
reference partition also gives a planar null exceptional set by taking
its product with the angular line.
-/

@[expose] public section

noncomputable section

namespace ContinuousFlexibility.Analysis

open Set Filter MeasureTheory
open scoped ContDiff Topology
open ContinuousFlexibility.Statements

theorem n04bUnitCoordinate_mem_Icc {l r : ℝ} (hlr : l < r)
    (reversed : Bool) {x : ℝ} (hx : x ∈ Icc l r) :
    n04UnitCoordinate l r reversed x ∈ Icc (0 : ℝ) 1 := by
  have hΔ : 0 < r - l := sub_pos.mpr hlr
  cases reversed with
  | false =>
    change 0 ≤ (x - l) / (r - l) ∧ (x - l) / (r - l) ≤ 1
    constructor
    · exact div_nonneg (sub_nonneg.mpr hx.1) hΔ.le
    · apply (div_le_iff₀ hΔ).mpr
      linarith [hx.2]
  | true =>
    change 0 ≤ (r - x) / (r - l) ∧ (r - x) / (r - l) ≤ 1
    constructor
    · exact div_nonneg (sub_nonneg.mpr hx.2) hΔ.le
    · apply (div_le_iff₀ hΔ).mpr
      linarith [hx.1]

theorem n04bUnitInverseCoordinate_mem_Icc {l r : ℝ} (hlr : l < r)
    (reversed : Bool) {y : ℝ} (hy : y ∈ Icc (0 : ℝ) 1) :
    n04UnitInverseCoordinate l r reversed y ∈ Icc l r := by
  have hΔ : 0 ≤ r - l := sub_nonneg.mpr hlr.le
  have h0 : 0 ≤ (r - l) * y := mul_nonneg hΔ hy.1
  have h1 : (r - l) * y ≤ (r - l) * 1 := mul_le_mul_of_nonneg_left hy.2 hΔ
  cases reversed with
  | false =>
    change l ≤ l + (r - l) * y ∧ l + (r - l) * y ≤ r
    constructor <;> linarith
  | true =>
    change l ≤ r - (r - l) * y ∧ r - (r - l) * y ≤ r
    constructor <;> linarith

theorem n04bUnitChart_mapsTo_closed {l r : ℝ} (hlr : l < r) (reversed : Bool) :
    MapsTo (n04UnitChart l r reversed)
      (Icc l r ×ˢ univ) (Icc (0 : ℝ) 1 ×ˢ univ) := by
  intro p hp
  exact ⟨n04bUnitCoordinate_mem_Icc hlr reversed hp.1, mem_univ _⟩

theorem n04bUnitInverseChart_mapsTo_closed {l r : ℝ} (hlr : l < r)
    (reversed : Bool) :
    MapsTo (n04UnitInverseChart l r reversed)
      (Icc (0 : ℝ) 1 ×ˢ univ) (Icc l r ×ˢ univ) := by
  intro p hp
  exact ⟨n04bUnitInverseCoordinate_mem_Icc hlr reversed hp.1, mem_univ _⟩

/-- The existing forward and inverse formulas form one global
homeomorphism, for either orientation. -/
def n04bUnitChartHomeomorph {l r : ℝ} (hlr : l < r) (reversed : Bool) :
    PolarPoint ≃ₜ PolarPoint where
  toFun := n04UnitChart l r reversed
  invFun := n04UnitInverseChart l r reversed
  left_inv := n04UnitInverseChart_chart hlr reversed
  right_inv := n04UnitChart_inverseChart hlr reversed
  continuous_toFun := (contDiff_n04UnitChart l r reversed).continuous
  continuous_invFun := (contDiff_n04UnitInverseChart l r reversed).continuous

@[simp] theorem n04bUnitChartHomeomorph_apply {l r : ℝ} (hlr : l < r)
    (reversed : Bool) (p : PolarPoint) :
    n04bUnitChartHomeomorph hlr reversed p = n04UnitChart l r reversed p := rfl

@[simp] theorem n04bUnitChartHomeomorph_symm_apply {l r : ℝ} (hlr : l < r)
    (reversed : Bool) (p : PolarPoint) :
    (n04bUnitChartHomeomorph hlr reversed).symm p =
      n04UnitInverseChart l r reversed p := rfl

theorem n04bUnitChart_bijOn_closed {l r : ℝ} (hlr : l < r) (reversed : Bool) :
    BijOn (n04UnitChart l r reversed)
      (Icc l r ×ˢ univ) (Icc (0 : ℝ) 1 ×ˢ univ) := by
  refine ⟨n04bUnitChart_mapsTo_closed hlr reversed, ?_, ?_⟩
  · intro p hp q hq heq
    apply (n04bUnitChartHomeomorph hlr reversed).injective
    simpa only [n04bUnitChartHomeomorph_apply] using heq
  · intro q hq
    exact ⟨n04UnitInverseChart l r reversed q,
      n04bUnitInverseChart_mapsTo_closed hlr reversed hq,
      n04UnitChart_inverseChart hlr reversed q⟩

/-- The stored inverse agrees with a genuine smooth inverse on a full
neighborhood; in the affine atlas it agrees globally. -/
theorem n04bUnitChart_boundaryInverseGerm {l r : ℝ} (hlr : l < r)
    (reversed : Bool) (p : PolarPoint) :
    CanonicalBoundaryInverseGerm (n04UnitChart l r reversed)
      (n04UnitInverseChart l r reversed) p := by
  let e := (n04bUnitChartHomeomorph hlr reversed).toOpenPartialHomeomorph
  have hF : (e : PolarPoint → PolarPoint) = n04UnitChart l r reversed := by
    funext q
    simp only [e, Homeomorph.toOpenPartialHomeomorph_apply, n04bUnitChartHomeomorph_apply]
  have hG : (e.symm : PolarPoint → PolarPoint) = n04UnitInverseChart l r reversed := by
    funext q
    simp only [e, Homeomorph.toOpenPartialHomeomorph_symm_apply,
      n04bUnitChartHomeomorph_symm_apply]
  refine ⟨e, hF, ?_, ?_, ?_⟩
  · simp only [e, Homeomorph.toOpenPartialHomeomorph_source, mem_univ]
  · rw [hG]
    exact (contDiff_n04UnitInverseChart l r reversed).contDiffAt
  · exact Filter.Eventually.of_forall (fun q => congrFun hG.symm q)

theorem n04b_closure_radial_strip {l r : ℝ} (hlr : l < r) :
    closure (Ioo l r ×ˢ (univ : Set ℝ)) = Icc l r ×ˢ (univ : Set ℝ) := by
  rw [closure_prod_eq, closure_Ioo hlr.ne, closure_univ]

theorem n04b_volume_radial_cylinder_eq_zero {E : Set ℝ} (hE : volume E = 0) :
    volume (E ×ˢ (univ : Set ℝ)) = 0 := by
  rw [Measure.volume_eq_prod, Measure.prod_prod, hE, zero_mul]

/-- A countable exceptional set of radii gives an actual planar null
partition of the corresponding cylindrical region. -/
theorem n04b_planar_partition_of_countable_radial
    {a b : ℝ} {left right : ℕ → ℝ} {E : Set ℝ} (hE : E.Countable)
    (hcover : ∀ r ∈ Ioo a b \ E, ∃! m, r ∈ Ioo (left m) (right m)) :
    ∃ E₂ : Set PolarPoint, volume E₂ = 0 ∧
      ∀ p ∈ (Ioo a b ×ˢ (univ : Set ℝ)) \ E₂,
        ∃! m, p ∈ Ioo (left m) (right m) ×ˢ (univ : Set ℝ) := by
  refine ⟨E ×ˢ univ, n04b_volume_radial_cylinder_eq_zero (hE.measure_zero volume), ?_⟩
  intro p hp
  have hpE : p.1 ∉ E := fun h => hp.2 ⟨h, mem_univ _⟩
  obtain ⟨m, hm, hunique⟩ := hcover p.1 ⟨hp.1.1, hpE⟩
  exact ⟨m, ⟨hm, mem_univ _⟩, fun n hn => hunique n hn.1⟩

end ContinuousFlexibility.Analysis
