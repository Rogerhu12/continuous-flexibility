module

public import ContinuousFlexibility.Statements.Analysis
public import ContinuousFlexibility.Analysis.CanonicalSourceMeasure
public import Mathlib.Analysis.Calculus.Deriv.Comp
public import Mathlib.Tactic.Ring

/-!
# Change of variables from the physical interval to the material cylinder

The material coordinate is the actual function supplied by IsMaterialData.
Its derivative is diagonal, its Jacobian is the reciprocal of ell, and its
inverse on the physical interval is the actual radius function.  The
change-of-variables theorem therefore applies to every measurable angular
set.  The integral identities use totalized Bochner integrals; integrability
is asserted separately by the equivalence below.
-/

@[expose] public section

noncomputable section

namespace ContinuousFlexibility.Analysis

open Set MeasureTheory ContinuousFlexibility.Statements
open scoped ContDiff

set_option backward.isDefEq.respectTransparency false

def n07bMaterialChart (T : MaterialData) (p : PolarPoint) : PolarPoint :=
  (T.rho p.1, p.2)

theorem n07bMaterialChart_hasFDerivAt {D : ReferenceData} {T : MaterialData}
    (hT : IsMaterialData D T) {p : PolarPoint} (hp : p.1 ∈ Ioo D.a D.b) :
    HasFDerivAt (n07bMaterialChart T)
      (((1 / T.ell p.1) • ContinuousLinearMap.fst ℝ ℝ ℝ).prod
        (ContinuousLinearMap.snd ℝ ℝ ℝ)) p := by
  have hr : HasFDerivAt (fun q : PolarPoint => T.rho q.1)
      ((1 / T.ell p.1) • ContinuousLinearMap.fst ℝ ℝ ℝ) p := by
    simpa only [Function.comp_def] using
      (hT.2.2.1 p.1 hp).comp_hasFDerivAt p hasFDerivAt_fst
  exact hr.prodMk hasFDerivAt_snd

theorem n07b_contDiffAt_materialChart {D : ReferenceData} {T : MaterialData}
    (hT : IsMaterialData D T) {p : PolarPoint} (hp : p.1 ∈ Ioo D.a D.b) :
    ContDiffAt ℝ ∞ (n07bMaterialChart T) p := by
  have hr : ContDiffAt ℝ ∞ T.rho p.1 :=
    (hT.1 T.rho (by simp)).contDiffAt (isOpen_Ioo.mem_nhds hp)
  exact (hr.comp p contDiffAt_fst).prodMk contDiffAt_snd

theorem n07bMaterialChart_planeJacobian {D : ReferenceData} {T : MaterialData}
    (hT : IsMaterialData D T) {p : PolarPoint} (hp : p.1 ∈ Ioo D.a D.b) :
    planeJacobian (n07bMaterialChart T) p = 1 / T.ell p.1 := by
  simp only [planeJacobian, (n07bMaterialChart_hasFDerivAt hT hp).fderiv,
    ContinuousLinearMap.prod_apply, smul_apply,
    ContinuousLinearMap.coe_fst', ContinuousLinearMap.coe_snd',
    smul_eq_mul, mul_one, mul_zero, zero_mul, sub_zero]

theorem n07bMaterialChart_abs_det {D : ReferenceData} {T : MaterialData}
    (hT : IsMaterialData D T) {p : PolarPoint} (hp : p.1 ∈ Ioo D.a D.b) :
    |(fderiv ℝ (n07bMaterialChart T) p).det| = 1 / T.ell p.1 := by
  rw [← planeJacobian_eq_fderiv_det, n07bMaterialChart_planeJacobian hT hp,
    abs_of_pos (div_pos zero_lt_one (hT.2.1 p.1 hp).1)]

theorem n07bMaterialChart_injOn {D : ReferenceData} {T : MaterialData}
    (hT : IsMaterialData D T) (s : Set ℝ) :
    InjOn (n07bMaterialChart T) (Ioo D.a D.b ×ˢ s) := by
  intro p hp q hq hpq
  apply Prod.ext
  · exact hT.2.2.2.1.injOn hp.1 hq.1 (congrArg Prod.fst hpq)
  · change (n07bMaterialChart T p).2 = (n07bMaterialChart T q).2
    exact congrArg Prod.snd hpq

theorem n07bMaterialChart_image {D : ReferenceData} {T : MaterialData}
    (hT : IsMaterialData D T) (s : Set ℝ) :
    n07bMaterialChart T '' (Ioo D.a D.b ×ˢ s) = (univ : Set ℝ) ×ˢ s := by
  obtain ⟨_, _, _, _, _, _, _, hInv, _⟩ := hT
  ext p
  constructor
  · rintro ⟨q, hq, rfl⟩
    exact ⟨mem_univ _, hq.2⟩
  · intro hp
    refine ⟨(T.radius p.1, p.2), ⟨(hInv p.1).1, hp.2⟩, ?_⟩
    apply Prod.ext
    · exact (hInv p.1).2
    · rfl

/-- Actual integrability equivalence for the material change of variables. -/
theorem n07b_integrableOn_materialChart_iff {D : ReferenceData} {T : MaterialData}
    (hT : IsMaterialData D T) {s : Set ℝ} (hs : MeasurableSet s)
    (g : PolarPoint → ℝ) :
    IntegrableOn g ((univ : Set ℝ) ×ˢ s) ↔
      IntegrableOn (fun p => g (n07bMaterialChart T p) / T.ell p.1)
        (Ioo D.a D.b ×ˢ s) := by
  let : (volume : Measure PolarPoint).IsAddHaarMeasure := by
    rw [Measure.volume_eq_prod]
    infer_instance
  have hU : MeasurableSet (Ioo D.a D.b ×ˢ s) := measurableSet_Ioo.prod hs
  have hd : ∀ p ∈ Ioo D.a D.b ×ˢ s,
      HasFDerivWithinAt (n07bMaterialChart T) (fderiv ℝ (n07bMaterialChart T) p)
        (Ioo D.a D.b ×ˢ s) p :=
    fun p hp => (n07bMaterialChart_hasFDerivAt hT hp.1).differentiableAt.hasFDerivAt
      |>.hasFDerivWithinAt
  have hc := integrableOn_image_iff_integrableOn_abs_det_fderiv_smul
    (volume : Measure PolarPoint) hU hd (n07bMaterialChart_injOn hT s) g
  rw [n07bMaterialChart_image hT s] at hc
  apply hc.trans
  apply integrableOn_congr_fun _ hU
  intro p hp
  change |(fderiv ℝ (n07bMaterialChart T) p).det| • g (n07bMaterialChart T p) =
    g (n07bMaterialChart T p) / T.ell p.1
  rw [n07bMaterialChart_abs_det hT hp.1, smul_eq_mul]
  ring

/-- Genuine Jacobian change of variables, valid with totalized integrals. -/
theorem n07b_integral_materialChart {D : ReferenceData} {T : MaterialData}
    (hT : IsMaterialData D T) {s : Set ℝ} (hs : MeasurableSet s)
    (g : PolarPoint → ℝ) :
    (∫ p in Ioo D.a D.b ×ˢ s, g (n07bMaterialChart T p) / T.ell p.1) =
      ∫ p in (univ : Set ℝ) ×ˢ s, g p := by
  let : (volume : Measure PolarPoint).IsAddHaarMeasure := by
    rw [Measure.volume_eq_prod]
    infer_instance
  have hU : MeasurableSet (Ioo D.a D.b ×ˢ s) := measurableSet_Ioo.prod hs
  have hd : ∀ p ∈ Ioo D.a D.b ×ˢ s,
      HasFDerivWithinAt (n07bMaterialChart T) (fderiv ℝ (n07bMaterialChart T) p)
        (Ioo D.a D.b ×ˢ s) p :=
    fun p hp => (n07bMaterialChart_hasFDerivAt hT hp.1).differentiableAt.hasFDerivAt
      |>.hasFDerivWithinAt
  have hc := integral_image_eq_integral_abs_det_fderiv_smul
    (volume : Measure PolarPoint) hU hd (n07bMaterialChart_injOn hT s) g
  rw [n07bMaterialChart_image hT s] at hc
  symm
  rw [hc]
  apply setIntegral_congr_fun hU
  intro p hp
  change |(fderiv ℝ (n07bMaterialChart T) p).det| • g (n07bMaterialChart T p) =
    g (n07bMaterialChart T p) / T.ell p.1
  rw [n07bMaterialChart_abs_det hT hp.1, smul_eq_mul]
  ring

/-- The equivalence for the actual half-period material cylinder measure. -/
theorem n07b_integrable_materialCylinder_iff {D : ReferenceData} {T : MaterialData}
    (hT : IsMaterialData D T) (g : PolarPoint → ℝ) :
    Integrable g materialCylinderMeasure ↔
      IntegrableOn (fun p : PolarPoint => g (T.rho p.1, p.2) / T.ell p.1)
        (Ioo D.a D.b ×ˢ Ioc (0 : ℝ) Real.pi) := by
  exact n07b_integrableOn_materialChart_iff hT measurableSet_Ioc g

/-- Physical integration with reciprocal ell equals material integration. -/
theorem n07b_integral_materialCylinder {D : ReferenceData} {T : MaterialData}
    (hT : IsMaterialData D T) (g : PolarPoint → ℝ) :
    (∫ p in Ioo D.a D.b ×ˢ Ioc (0 : ℝ) Real.pi,
      g (T.rho p.1, p.2) / T.ell p.1) = ∫ p, g p ∂materialCylinderMeasure := by
  exact n07b_integral_materialChart hT measurableSet_Ioc g

end ContinuousFlexibility.Analysis
