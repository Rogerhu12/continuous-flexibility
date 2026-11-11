import ContinuousFlexibility.Analysis.MaterialDivergenceEnvelopes

/-!
# One weighted L² envelope along a bounded affine height family

Only the scalar coefficients vary. The envelope is made from the two
fixed decoded height jets and is independent of the family parameter.
-/

noncomputable section

namespace ContinuousFlexibility.Statements

open Set MeasureTheory
open scoped ContDiff

theorem PhysicalJetEnvelopes.bounded_scalar_mul
    {ι : Type*} {T : MaterialData} {γ : ℝ}
    {f : ι → PolarPoint → ℝ} (henv : PhysicalJetEnvelopes T γ f)
    (c : ι → ℝ) {C : ℝ} (hC : 0 ≤ C) (hc : ∀ i, |c i| ≤ C) :
    PhysicalJetEnvelopes T γ (fun i p => c i * f i p) := by
  intro a b d
  obtain ⟨G, hG, hGpos, hb⟩ := henv a b d
  refine ⟨fun p => C * G p, hG.const_mul C,
    fun p => mul_nonneg hC (hGpos p), fun i p => ?_⟩
  rw [weightedPhysicalJet_const_mul, abs_mul]
  exact mul_le_mul (hc i) (hb i p) (abs_nonneg _) hC

theorem physicalJetEnvelopes_affine_family
    {ι : Type*} {D : ReferenceData} {T : MaterialData} {γ : ℝ}
    {u v : PolarPoint → ℝ} (hT : IsMaterialData D T)
    (hu : ContDiffOn ℝ ∞ u (annularOpen D)) (hv : ContDiffOn ℝ ∞ v (annularOpen D))
    (huLp : ∀ a b d, MemLp (weightedPhysicalJet T γ a b d u) 2 materialCylinderMeasure)
    (hvLp : ∀ a b d, MemLp (weightedPhysicalJet T γ a b d v) 2 materialCylinderMeasure)
    (c : ι → ℝ) {C : ℝ} (hC : 0 ≤ C) (hc : ∀ i, |c i| ≤ C) :
    PhysicalJetEnvelopes T γ (fun i p => u p + c i * v p) := by
  have huenv : PhysicalJetEnvelopes T γ (fun _ : ι => u) := physicalJetEnvelopes_const huLp
  have hvenv : PhysicalJetEnvelopes T γ (fun _ : ι => v) := physicalJetEnvelopes_const hvLp
  exact PhysicalJetEnvelopes.add hT (fun _ => hu) (fun _ => contDiffOn_const.mul hv)
    huenv (hvenv.bounded_scalar_mul c hC hc)

theorem physicalJetEnvelopes_decode_affine_family
    {ι : Type*} {D : ReferenceData} {T : MaterialData} {γ : ℝ} {H : SobolevModelData}
    (hH : IsSobolevModel D T γ H) (hT : IsMaterialData D T)
    (u v : H.Space) (c : ι → ℝ) {C : ℝ} (hC : 0 ≤ C) (hc : ∀ i, |c i| ≤ C) :
    PhysicalJetEnvelopes T γ (fun i => H.decode (u + c i • v)) := by
  have hu := hH.2.2.2.1 u
  have hv := hH.2.2.2.1 v
  have henv := physicalJetEnvelopes_affine_family hT hu.1 hv.1
    hu.2.2.2.2 hv.2.2.2.2 c hC hc
  apply PhysicalJetEnvelopes.congr_on_annularOpen hT henv
  intro i p hp
  simp only [map_add, map_smul, Pi.add_apply, Pi.smul_apply, smul_eq_mul]

end ContinuousFlexibility.Statements
