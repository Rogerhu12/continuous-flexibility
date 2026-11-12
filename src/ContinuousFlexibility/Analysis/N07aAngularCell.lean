import ContinuousFlexibility.Statements.Nonlinear
import ContinuousFlexibility.Analysis.SpacesTorusCellLp

/-!
# Exact torus coordinates of a canonical source piece

Only the radial interval changes between canonical pieces. After division
by its area, its actual measure is transported to the normalized torus by
an explicit affine chart. These maps act on the existing `Lp` classes;
no pointwise representative or radial regularity is assumed.
-/

noncomputable section

namespace ContinuousFlexibility.Statements

open Set Filter MeasureTheory ContinuousFlexibility.Analysis
open scoped ENNReal Topology

variable {S : PhysicalSpacesData} {K : CanonicalData S}

def n07aAngularCell (m : ℕ) : Set PolarPoint :=
  Ioc (K.left m) (K.right m) ×ˢ Ioc 0 Real.pi

def n07aAngularCellArea (m : ℕ) : ℝ := (K.right m - K.left m) * Real.pi

theorem n07aAngularCellArea_pos (m : ℕ) (hm : K.left m < K.right m) :
    0 < n07aAngularCellArea (K := K) m := mul_pos (sub_pos.mpr hm) Real.pi_pos

theorem n07aCanonicalMeasure_eq_halfOpen (m : ℕ) :
    canonicalMeasure S K m = volume.restrict (n07aAngularCell (K := K) m) := by
  rw [canonicalMeasure, n07aAngularCell, Measure.volume_eq_prod,
    ← Measure.prod_restrict, ← Measure.prod_restrict, restrict_Ioo_eq_restrict_Ioc]

def n07aAngularCellMeasure (m : ℕ) : Measure PolarPoint :=
  ENNReal.ofReal (n07aAngularCellArea (K := K) m)⁻¹ • canonicalMeasure S K m

def n07aAngularCellChart (m : ℕ) (t : SpacesTorus) : PolarPoint :=
  ((K.right m - K.left m) * spacesUnitCircleRepresentative 0 (t 0) + K.left m,
    Real.pi * spacesUnitCircleRepresentative 0 (t 1))

theorem n07aAngularCellChart_preserving (m : ℕ) (hm : K.left m < K.right m) :
    MeasurePreserving (n07aAngularCellChart (K := K) m)
      (Measure.pi (fun _ : Fin 2 => AddCircle.haarAddCircle))
      (n07aAngularCellMeasure (K := K) m) := by
  let : SFinite angleMeasure := by unfold angleMeasure; infer_instance
  have hrep : MeasurePreserving (spacesUnitCircleRepresentative 0)
      AddCircle.haarAddCircle (volume.restrict (Ioc (0 : ℝ) 1)) := by
    simpa only [zero_add] using spacesUnitCircleRepresentative_preserving 0
  have hr := (spaces_affineInterval_preserving (K.right m - K.left m)
    (sub_pos.mpr hm) (K.left m) 0 1).comp hrep
  have hθ := (spaces_affineInterval_preserving Real.pi Real.pi_pos 0 0 1).comp hrep
  have hrad : MeasurePreserving
      (fun t : UnitAddCircle =>
        (K.right m - K.left m) * spacesUnitCircleRepresentative 0 t + K.left m)
      AddCircle.haarAddCircle
      (ENNReal.ofReal (K.right m - K.left m)⁻¹ •
        volume.restrict (Ioc (K.left m) (K.right m))) := by
    simpa only [Function.comp_def, mul_zero, zero_add, mul_one, sub_add_cancel] using hr
  have hang : MeasurePreserving
      (fun t : UnitAddCircle => Real.pi * spacesUnitCircleRepresentative 0 t)
      AddCircle.haarAddCircle (ENNReal.ofReal Real.pi⁻¹ • angleMeasure) := by
    simpa only [Function.comp_def, mul_zero, zero_add, mul_one, add_zero, angleMeasure]
      using hθ
  have hp := (hrad.prod hang).comp (measurePreserving_finTwoArrow AddCircle.haarAddCircle)
  have hmeas :
      (ENNReal.ofReal (K.right m - K.left m)⁻¹ •
        volume.restrict (Ioc (K.left m) (K.right m))).prod
      (ENNReal.ofReal Real.pi⁻¹ • angleMeasure) = n07aAngularCellMeasure (K := K) m := by
    rw [Measure.prod_smul_left, Measure.prod_smul_right, smul_smul]
    rw [n07aAngularCellMeasure, n07aCanonicalMeasure_eq_halfOpen]
    simp only [angleMeasure, n07aAngularCell, ← Measure.prod_restrict,
      Measure.volume_eq_prod]
    congr 1
    rw [← ENNReal.ofReal_mul (by positivity), n07aAngularCellArea, mul_inv_rev]
    congr 1
    ring
  rw [hmeas] at hp
  exact hp

theorem n07aAngularCellChart_mem (m : ℕ) (hm : K.left m < K.right m) (t : SpacesTorus) :
    n07aAngularCellChart (K := K) m t ∈ n07aAngularCell (K := K) m := by
  have hr := (AddCircle.equivIoc 1 0 (t 0)).property
  have hθ := (AddCircle.equivIoc 1 0 (t 1)).property
  simp only [zero_add, mem_Ioc] at hr hθ
  change (
      K.left m < (K.right m - K.left m) * spacesUnitCircleRepresentative 0 (t 0) + K.left m ∧
      (K.right m - K.left m) * spacesUnitCircleRepresentative 0 (t 0) + K.left m ≤ K.right m) ∧
    (0 < Real.pi * spacesUnitCircleRepresentative 0 (t 1) ∧
      Real.pi * spacesUnitCircleRepresentative 0 (t 1) ≤ Real.pi)
  dsimp only [spacesUnitCircleRepresentative]
  constructor
  · constructor <;> nlinarith [hr.1, hr.2]
  · constructor <;> nlinarith [hθ.1, hθ.2, Real.pi_pos]

def n07aAngularCellQuotient (m : ℕ) (p : PolarPoint) : SpacesTorus :=
  ![(((p.1 - K.left m) / (K.right m - K.left m) : ℝ) : UnitAddCircle),
    ((p.2 / Real.pi : ℝ) : UnitAddCircle)]

theorem n07aAngularCellQuotient_continuous (m : ℕ) :
    Continuous (n07aAngularCellQuotient (K := K) m) := by
  apply continuous_pi
  intro i
  fin_cases i
  · exact (AddCircle.continuous_mk' (1 : ℝ)).comp
      ((continuous_fst.sub continuous_const).div_const (K.right m - K.left m))
  · exact (AddCircle.continuous_mk' (1 : ℝ)).comp (continuous_snd.div_const Real.pi)

theorem n07aAngularCellQuotient_chart (m : ℕ) (hm : K.left m < K.right m)
    (t : SpacesTorus) :
    n07aAngularCellQuotient (K := K) m (n07aAngularCellChart (K := K) m t) = t := by
  have hd : K.right m - K.left m ≠ 0 := (sub_pos.mpr hm).ne'
  funext i
  fin_cases i
  · simp [n07aAngularCellQuotient, n07aAngularCellChart,
      spacesUnitCircleRepresentative, hd]
  · simp [n07aAngularCellQuotient, n07aAngularCellChart,
      spacesUnitCircleRepresentative, Real.pi_ne_zero]

theorem n07aAngularCellChart_quotient (m : ℕ) (hm : K.left m < K.right m)
    {p : PolarPoint} (hp : p ∈ n07aAngularCell (K := K) m) :
    n07aAngularCellChart (K := K) m (n07aAngularCellQuotient (K := K) m p) = p := by
  have hd : 0 < K.right m - K.left m := sub_pos.mpr hm
  have hr : (p.1 - K.left m) / (K.right m - K.left m) ∈ Ioc (0 : ℝ) (0 + 1) := by
    constructor
    · exact div_pos (sub_pos.mpr hp.1.1) hd
    · rw [zero_add, div_le_one hd]
      linarith [hp.1.2]
  have hθ : p.2 / Real.pi ∈ Ioc (0 : ℝ) (0 + 1) := by
    constructor
    · exact div_pos hp.2.1 Real.pi_pos
    · simpa only [zero_add] using (div_le_one Real.pi_pos).mpr hp.2.2
  simp only [n07aAngularCellChart, n07aAngularCellQuotient, Matrix.cons_val_zero,
    Matrix.cons_val_one, spacesUnitCircleRepresentative,
    AddCircle.equivIoc_coe_eq hr, AddCircle.equivIoc_coe_eq hθ]
  apply Prod.ext
  · dsimp only
    rw [mul_div_cancel₀ _ hd.ne', sub_add_cancel]
  · dsimp only
    exact mul_div_cancel₀ _ Real.pi_ne_zero

theorem n07aAngularCellQuotient_preserving (m : ℕ) (hm : K.left m < K.right m) :
    MeasurePreserving (n07aAngularCellQuotient (K := K) m)
      (n07aAngularCellMeasure (K := K) m)
      (Measure.pi (fun _ : Fin 2 => AddCircle.haarAddCircle)) := by
  have hc := n07aAngularCellChart_preserving m hm
  have hq := (n07aAngularCellQuotient_continuous (K := K) m).measurable
  refine ⟨hq, ?_⟩
  rw [← hc.map_eq, Measure.map_map hq hc.measurable]
  have he : n07aAngularCellQuotient (K := K) m ∘ n07aAngularCellChart (K := K) m = id :=
    funext (n07aAngularCellQuotient_chart m hm)
  rw [he, Measure.map_id]

theorem n07aAngularCellMeasure_ae_mem (m : ℕ) :
    ∀ᵐ p ∂n07aAngularCellMeasure (K := K) m, p ∈ n07aAngularCell (K := K) m := by
  rw [n07aAngularCellMeasure, n07aCanonicalMeasure_eq_halfOpen]
  exact (ae_restrict_mem (measurableSet_Ioc.prod measurableSet_Ioc)).filter_mono
    (Measure.ae_smul_measure_le _)

variable (E : Type*) [NormedAddCommGroup E] [NormedSpace ℝ E]

def n07aAngularCellToTorus (m : ℕ) (hm : K.left m < K.right m) :
    Lp E 2 (n07aAngularCellMeasure (K := K) m) →ₗᵢ[ℝ] SpacesTorusValueL2 E :=
  Lp.compMeasurePreservingₗᵢ ℝ _ (n07aAngularCellChart_preserving m hm)

def n07aAngularTorusToCell (m : ℕ) (hm : K.left m < K.right m) :
    SpacesTorusValueL2 E →ₗᵢ[ℝ] Lp E 2 (n07aAngularCellMeasure (K := K) m) :=
  Lp.compMeasurePreservingₗᵢ ℝ _ (n07aAngularCellQuotient_preserving m hm)

theorem n07aAngularCellToTorus_ae (m : ℕ) (hm : K.left m < K.right m)
    (u : Lp E 2 (n07aAngularCellMeasure (K := K) m)) :
    (n07aAngularCellToTorus E m hm u : SpacesTorus → E) =ᵐ[
      Measure.pi (fun _ : Fin 2 => AddCircle.haarAddCircle)]
      u ∘ n07aAngularCellChart (K := K) m :=
  Lp.coeFn_compMeasurePreserving u (n07aAngularCellChart_preserving m hm)

theorem n07aAngularTorusToCell_ae (m : ℕ) (hm : K.left m < K.right m)
    (u : SpacesTorusValueL2 E) :
    (n07aAngularTorusToCell E m hm u : PolarPoint → E) =ᵐ[n07aAngularCellMeasure (K := K) m]
      u ∘ n07aAngularCellQuotient (K := K) m :=
  Lp.coeFn_compMeasurePreserving u (n07aAngularCellQuotient_preserving m hm)

theorem n07aAngularTorusToCell_leftInverse (m : ℕ) (hm : K.left m < K.right m)
    (u : Lp E 2 (n07aAngularCellMeasure (K := K) m)) :
    n07aAngularTorusToCell E m hm (n07aAngularCellToTorus E m hm u) = u := by
  apply Lp.ext
  have hq := (n07aAngularCellQuotient_preserving m hm).quasiMeasurePreserving.ae_eq_comp
    (n07aAngularCellToTorus_ae E m hm u)
  filter_upwards [n07aAngularTorusToCell_ae E m hm (n07aAngularCellToTorus E m hm u), hq,
    n07aAngularCellMeasure_ae_mem (K := K) m] with p hp hq hmem
  exact hp.trans (hq.trans (congrArg u (n07aAngularCellChart_quotient m hm hmem)))

theorem n07aAngularCellToTorus_leftInverse (m : ℕ) (hm : K.left m < K.right m)
    (u : SpacesTorusValueL2 E) :
    n07aAngularCellToTorus E m hm (n07aAngularTorusToCell E m hm u) = u := by
  apply Lp.ext
  have hc := (n07aAngularCellChart_preserving m hm).quasiMeasurePreserving.ae_eq_comp
    (n07aAngularTorusToCell_ae E m hm u)
  filter_upwards [n07aAngularCellToTorus_ae E m hm (n07aAngularTorusToCell E m hm u), hc]
    with t ht hc
  exact ht.trans (hc.trans (congrArg u (n07aAngularCellQuotient_chart m hm t)))

/-- The actual normalized canonical piece is isometric to the normalized torus. -/
def n07aAngularCellTorusEquiv (m : ℕ) (hm : K.left m < K.right m) :
    Lp E 2 (n07aAngularCellMeasure (K := K) m) ≃ₗᵢ[ℝ] SpacesTorusValueL2 E where
  toFun := n07aAngularCellToTorus E m hm
  map_add' := (n07aAngularCellToTorus E m hm).map_add
  map_smul' := (n07aAngularCellToTorus E m hm).map_smul
  norm_map' := (n07aAngularCellToTorus E m hm).norm_map
  invFun := n07aAngularTorusToCell E m hm
  left_inv := n07aAngularTorusToCell_leftInverse E m hm
  right_inv := n07aAngularCellToTorus_leftInverse E m hm

end ContinuousFlexibility.Statements
