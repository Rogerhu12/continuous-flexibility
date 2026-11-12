import ContinuousFlexibility.Analysis.N07bMaterialCoordinateMeasure
import ContinuousFlexibility.Analysis.SpacesTracePointwise
import ContinuousFlexibility.Analysis.SpacesLpCurveDerivative

/-!
# Physical integral densities for the actual material jets

The material cylinder's square norms have a reciprocal-ell density in
physical coordinates. These formulas supply an integrable physical majorant
for the canonical source estimate, retaining the actual decoded field and
its original material seminorm.
-/

noncomputable section

namespace ContinuousFlexibility.Analysis

open Set MeasureTheory
open ContinuousFlexibility.Statements

/-- The physical-coordinate density of one actual weighted material jet. -/
def n07bMaterialJetEnergyDensity (T : MaterialData) (β : ℝ)
    (a b c : ℕ) (f : PolarPoint → ℝ) (p : PolarPoint) : ℝ :=
  (T.M p.1 ^ c * mixedDerivative a b (materialPullback T β f)
    (T.rho p.1, p.2)) ^ 2 / T.ell p.1

theorem n07bMaterialJetEnergyDensity_nonneg
    {D : ReferenceData} {T : MaterialData} (hT : IsMaterialData D T)
    (β : ℝ) (a b c : ℕ) (f : PolarPoint → ℝ) {p : PolarPoint}
    (hp : p.1 ∈ Ioo D.a D.b) :
    0 ≤ n07bMaterialJetEnergyDensity T β a b c f p :=
  div_nonneg (sq_nonneg _) (hT.2.1 p.1 hp).1.le

/-- The actual inverse-radius identity gives the physical density pointwise. -/
theorem n07bMaterialJetEnergyDensity_eq
    {D : ReferenceData} {T : MaterialData} (hT : IsMaterialData D T)
    (β : ℝ) (a b c : ℕ) (f : PolarPoint → ℝ) {p : PolarPoint}
    (hp : p.1 ∈ Ioo D.a D.b) :
    n07bMaterialJetEnergyDensity T β a b c f p =
      weightedPhysicalJet T β a b c f (T.rho p.1, p.2) ^ 2 / T.ell p.1 := by
  have hinv := hT.2.2.2.2.2.2.2.2.1 p.1 hp
  simp only [n07bMaterialJetEnergyDensity, weightedPhysicalJet, hinv]

/-- A genuine physical height has an integrable physical density for each
of its material jets. -/
theorem n07bMaterialJetEnergyDensity_integrable
    {D : ReferenceData} {T : MaterialData} (hT : IsMaterialData D T)
    {β : ℝ} {f : PolarPoint → ℝ} (hf : HeightMember D T β f)
    (a b c : ℕ) :
    IntegrableOn (n07bMaterialJetEnergyDensity T β a b c f)
      (Ioo D.a D.b ×ˢ Ioc (0 : ℝ) Real.pi) := by
  have hjet := hf.2.2.2.2 a b c
  have hi := (n07b_integrable_materialCylinder_iff hT
    (fun p => weightedPhysicalJet T β a b c f p ^ 2)).mp hjet.integrable_sq
  exact (integrableOn_congr_fun
    (fun p hp => (n07bMaterialJetEnergyDensity_eq hT β a b c f hp.1).symm)
    (measurableSet_Ioo.prod measurableSet_Ioc)).mp hi

/-- Exact integral-to-Hilbert-norm conversion, with integrability supplied
by HeightMember. -/
theorem n07bMaterialJetEnergyDensity_integral
    {D : ReferenceData} {T : MaterialData} (hT : IsMaterialData D T)
    {β : ℝ} {f : PolarPoint → ℝ} (hf : HeightMember D T β f)
    (a b c : ℕ) :
    (∫ p in Ioo D.a D.b ×ˢ Ioc (0 : ℝ) Real.pi,
      n07bMaterialJetEnergyDensity T β a b c f p) =
      (eLpNorm (weightedPhysicalJet T β a b c f) 2 materialCylinderMeasure).toReal ^ 2 := by
  have hjet := hf.2.2.2.2 a b c
  calc
    _ = ∫ p in Ioo D.a D.b ×ˢ Ioc (0 : ℝ) Real.pi,
        weightedPhysicalJet T β a b c f (T.rho p.1, p.2) ^ 2 / T.ell p.1 :=
      setIntegral_congr_fun (measurableSet_Ioo.prod measurableSet_Ioc)
        (fun p hp => n07bMaterialJetEnergyDensity_eq hT β a b c f hp.1)
    _ = ∫ p, weightedPhysicalJet T β a b c f p ^ 2 ∂materialCylinderMeasure :=
      n07b_integral_materialCylinder hT (fun p => weightedPhysicalJet T β a b c f p ^ 2)
    _ = ‖hjet.toLp (weightedPhysicalJet T β a b c f)‖ ^ 2 :=
      (spaces_lp_norm_sq_toLp hjet).symm
    _ = _ := by rw [Lp.norm_toLp]

/-- Every physical jet density is controlled by the original finite-order
physical seminorm, whenever the three jet orders fit within that order. -/
theorem n07bMaterialJetEnergyDensity_integral_le
    {D : ReferenceData} {T : MaterialData} (hT : IsMaterialData D T)
    {β : ℝ} {f : PolarPoint → ℝ} (hf : HeightMember D T β f)
    (a b c s : ℕ) (horder : a + b + c ≤ s) :
    (∫ p in Ioo D.a D.b ×ˢ Ioc (0 : ℝ) Real.pi,
      n07bMaterialJetEnergyDensity T β a b c f p) ≤ physicalNorm T β s f ^ 2 := by
  rw [n07bMaterialJetEnergyDensity_integral hT hf a b c]
  exact pow_le_pow_left₀ ENNReal.toReal_nonneg
    (spaces_full_jet_norm_le hf a b c s horder) 2

end ContinuousFlexibility.Analysis
