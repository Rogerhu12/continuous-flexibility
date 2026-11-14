module

public import ContinuousFlexibility.Analysis.SpacesHeightBounds
public import ContinuousFlexibility.Analysis.SpacesTraceGeometry

/-!
# Weighted pointwise estimates for trace and multiplication

The material weight is comparable on every unit window. Multiplying the
elementary cylinder Sobolev estimate by the weight at the evaluation point
therefore costs exactly two differential orders, with no loss depending on
the requested weight power.
-/

@[expose] public section

noncomputable section

namespace ContinuousFlexibility.Statements

open Set Filter MeasureTheory ContinuousFlexibility.Analysis
open scoped Topology ContDiff ENNReal BigOperators

set_option backward.isDefEq.respectTransparency false

/-- A physical jet index retaining all three requested orders. -/
def spaces_full_jet_index (a b c s : ℕ) (h : a + b + c ≤ s) : JetIndex s :=
  ⟨![⟨a, by omega⟩, ⟨b, by omega⟩, ⟨c, by omega⟩], by simpa using h⟩

theorem spaces_full_jet_norm_le {D : ReferenceData} {T : MaterialData}
    {γ : ℝ} {f : PolarPoint → ℝ} (hf : HeightMember D T γ f)
    (a b c s : ℕ) (h : a + b + c ≤ s) :
    (eLpNorm (weightedPhysicalJet T γ a b c f) 2 materialCylinderMeasure).toReal ≤
      physicalNorm T γ s f := by
  simpa only [spaces_full_jet_index, Matrix.cons_val_zero, Matrix.cons_val_one,
    Matrix.cons_val, Matrix.head_cons, Matrix.tail_cons, Fin.isValue] using
    spaces_weightedPhysicalJet_norm_le hf s (spaces_full_jet_index a b c s h)

private theorem spaces_weighted_window_norm
    {D : ReferenceData} {T : MaterialData} (hT : IsMaterialData D T)
    {K : ℝ}
    (hcompare : ∀ (c : ℝ), 0 ≤ c → ∀ x y : ℝ, |x - y| ≤ 1 →
      T.M (T.radius x) ^ c ≤ Real.exp (c * K) * T.M (T.radius y) ^ c)
    {g : PolarPoint → ℝ} (hg : Continuous g) (c : ℕ)
    (hw : MemLp (fun p : PolarPoint => T.M (T.radius p.1) ^ c * g p)
      2 materialCylinderMeasure) (x : ℝ) :
    T.M (T.radius x) ^ c * cylinderWindowL2Norm x g ≤
      Real.exp ((c : ℝ) * K) *
        (eLpNorm (fun p : PolarPoint => T.M (T.radius p.1) ^ c * g p)
          2 materialCylinderMeasure).toReal := by
  obtain ⟨_, hpos, _, _, _, _, _, hinside, _⟩ := hT
  have hM (y : ℝ) : 0 ≤ T.M (T.radius y) :=
    zero_le_one.trans (hpos _ (hinside y).1).2.2.2
  let w : PolarPoint → ℝ := fun p => T.M (T.radius p.1) ^ c * g p
  have ha : AEStronglyMeasurable
      (fun p : PolarPoint => T.M (T.radius x) ^ c * g p) (cylinderWindowMeasure x) :=
    (continuous_const.mul hg).aestronglyMeasurable
  have hb : ∀ᵐ p ∂cylinderWindowMeasure x,
      ‖T.M (T.radius x) ^ c * g p‖ ≤ ‖Real.exp ((c : ℝ) * K) * w p‖ := by
    change ∀ᵐ p ∂volume.restrict (cylinderWindow x), _
    filter_upwards [ae_restrict_mem (measurableSet_Ioc.prod measurableSet_Ioc)] with p hp
    have hd : |x - p.1| ≤ 1 :=
      abs_le.mpr ⟨by linarith [hp.1.2], by linarith [hp.1.1]⟩
    have hc : T.M (T.radius x) ^ c ≤
        Real.exp ((c : ℝ) * K) * T.M (T.radius p.1) ^ c := by
      simpa only [Real.rpow_natCast] using hcompare (c : ℝ) (by positivity) x p.1 hd
    simpa only [w, Real.norm_eq_abs, abs_mul,
      abs_of_nonneg (pow_nonneg (hM x) c), abs_of_nonneg (pow_nonneg (hM p.1) c),
      abs_of_pos (Real.exp_pos _), mul_assoc] using
      mul_le_mul_of_nonneg_right hc (abs_nonneg (g p))
  have he := eLpNorm_mono_ae (p := 2) ha hb
  change eLpNorm ((T.M (T.radius x) ^ c) • g) 2 (cylinderWindowMeasure x) ≤
    eLpNorm ((Real.exp ((c : ℝ) * K)) • w) 2 (cylinderWindowMeasure x) at he
  rw [eLpNorm_const_smul, eLpNorm_const_smul, Real.enorm_eq_ofReal_abs,
    Real.enorm_eq_ofReal_abs, abs_of_nonneg (pow_nonneg (hM x) c),
    abs_of_pos (Real.exp_pos _)] at he
  have hrestrict : eLpNorm w 2 (cylinderWindowMeasure x) ≤
      eLpNorm w 2 materialCylinderMeasure := by
    rw [cylinderWindowMeasure_eq_materialCylinderRestrict]
    exact eLpNorm_mono_measure _ Measure.restrict_le_self
  have he' := he.trans (mul_le_mul_of_nonneg_left hrestrict zero_le)
  have hfin : ENNReal.ofReal (Real.exp ((c : ℝ) * K)) *
      eLpNorm w 2 materialCylinderMeasure ≠ (∞ : ℝ≥0∞) :=
    ENNReal.mul_ne_top ENNReal.ofReal_ne_top hw.eLpNorm_ne_top
  simpa only [cylinderWindowL2Norm, ENNReal.toReal_mul,
    ENNReal.toReal_ofReal (pow_nonneg (hM x) c),
    ENNReal.toReal_ofReal (Real.exp_pos _).le] using ENNReal.toReal_mono hfin he'

/-- All weighted mixed jets satisfy one family of pointwise estimates.
Only two differential orders are used, uniformly in the weight order. -/
theorem spaces_weighted_mixed_pointwise {D : ReferenceData} {T : MaterialData}
    (hT : IsMaterialData D T) :
    ∃ K : ℝ, 0 ≤ K ∧ ∀ (γ : ℝ) (f : PolarPoint → ℝ),
      HeightMember D T γ f → ∀ a b c s : ℕ, a + b + c + 2 ≤ s →
        ∀ p : PolarPoint,
          T.M (T.radius p.1) ^ c * |mixedDerivative a b (materialPullback T γ f) p| ≤
            (4 * Real.sqrt Real.pi * Real.exp ((c : ℝ) * K)) * physicalNorm T γ s f := by
  obtain ⟨K, hK, hcompare⟩ := material_M_unit_window_comparison hT
  refine ⟨K, hK, fun γ f hf a b c s hs p => ?_⟩
  let v := materialPullback T γ f
  let g := mixedDerivative a b v
  have hv : ContDiff ℝ ∞ v := contDiff_materialPullback hT hf.1
  have hg : ContDiff ℝ ∞ g := contDiff_mixedDerivative hv a b
  have hr : radialPartial g = mixedDerivative (a + 1) b v :=
    radialPartial_mixedDerivative hv a b
  have ht : angularPartial g = mixedDerivative a (b + 1) v :=
    angularPartial_mixedDerivative hv a b
  have hrt : radialPartial (angularPartial g) = mixedDerivative (a + 1) (b + 1) v := by
    rw [ht, radialPartial_mixedDerivative hv]
  have hp := mixedDerivative_angular_periodic
    (materialPullback_angular_periodic (T := T) (γ := γ) hf.2.2.1) a b p.1
  obtain ⟨θ, hθ, heθ⟩ := hp.exists_mem_Ico₀ Real.pi_pos p.2
  have hpoint : |g p| ≤ Real.sqrt Real.pi *
      (cylinderWindowL2Norm p.1 g + cylinderWindowL2Norm p.1 (radialPartial g) +
        cylinderWindowL2Norm p.1 (angularPartial g) +
          cylinderWindowL2Norm p.1 (radialPartial (angularPartial g))) := by
    have he : g p = g (p.1, θ) := heθ
    rw [he]
    exact abs_le_cylinderWindow_L2 hg p.1 θ ⟨hθ.1, hθ.2.le⟩
  have hterm (i j : ℕ) (hij : i + j + c ≤ s) :
      T.M (T.radius p.1) ^ c * cylinderWindowL2Norm p.1 (mixedDerivative i j v) ≤
        Real.exp ((c : ℝ) * K) * physicalNorm T γ s f := by
    exact (spaces_weighted_window_norm hT hcompare (contDiff_mixedDerivative hv i j).continuous c
      (hf.2.2.2.2 i j c) p.1).trans
      (mul_le_mul_of_nonneg_left (spaces_full_jet_norm_le hf i j c s hij) (Real.exp_pos _).le)
  have h0 := hterm a b (by omega)
  have h1 := hterm (a + 1) b (by omega)
  have h2 := hterm a (b + 1) (by omega)
  have h3 := hterm (a + 1) (b + 1) (by omega)
  rw [← hr] at h1
  rw [← ht] at h2
  rw [← hrt] at h3
  have hM : 0 ≤ T.M (T.radius p.1) := by
    obtain ⟨_, hpos, _, _, _, _, _, hinside, _⟩ := hT
    exact zero_le_one.trans (hpos _ (hinside p.1).1).2.2.2
  calc
    T.M (T.radius p.1) ^ c * |g p| ≤ T.M (T.radius p.1) ^ c *
        (Real.sqrt Real.pi * (cylinderWindowL2Norm p.1 g +
          cylinderWindowL2Norm p.1 (radialPartial g) +
          cylinderWindowL2Norm p.1 (angularPartial g) +
          cylinderWindowL2Norm p.1 (radialPartial (angularPartial g)))) :=
      mul_le_mul_of_nonneg_left hpoint (pow_nonneg hM _)
    _ = Real.sqrt Real.pi * (T.M (T.radius p.1) ^ c * cylinderWindowL2Norm p.1 g +
        T.M (T.radius p.1) ^ c * cylinderWindowL2Norm p.1 (radialPartial g) +
        T.M (T.radius p.1) ^ c * cylinderWindowL2Norm p.1 (angularPartial g) +
        T.M (T.radius p.1) ^ c * cylinderWindowL2Norm p.1 (radialPartial (angularPartial g))) := by ring
    _ ≤ Real.sqrt Real.pi *
        (Real.exp ((c : ℝ) * K) * physicalNorm T γ s f +
          Real.exp ((c : ℝ) * K) * physicalNorm T γ s f +
          Real.exp ((c : ℝ) * K) * physicalNorm T γ s f +
          Real.exp ((c : ℝ) * K) * physicalNorm T γ s f) :=
      mul_le_mul_of_nonneg_left (add_le_add (add_le_add (add_le_add h0 h1) h2) h3)
        (Real.sqrt_nonneg _)
    _ = _ := by ring

end ContinuousFlexibility.Statements
