module

public import ContinuousFlexibility.Analysis.N06UnitWeakGraphData
public import ContinuousFlexibility.Analysis.N06MaterialAbsorption
public import ContinuousFlexibility.Analysis.N06WeakAngularLeibniz

/-!
# Physical canonical jet rows with their original material weights

The stored volume row and its physical representative differ by the
specific scalar in IsVolumeModel.forget. That scalar multiplies every
weak angular derivative, and preserves the original reflection condition.
-/

@[expose] public section

noncomputable section

namespace ContinuousFlexibility.Analysis

open Set Filter MeasureTheory
open scoped BigOperators Topology
open ContinuousFlexibility.Statements

set_option backward.isDefEq.respectTransparency false

def n06MaterialJetRow {S : PhysicalSpacesData} (T : MaterialData) (K : CanonicalData S)
    (γ t : ℝ) {b : ℕ} (F : CanonicalVolumeJets S K b) (m : ℕ) :
    PiLp 2 (fun _ : Fin (b + 1) => CanonicalL2 S K m) :=
  (T.M (T.sample (K.cell m)) ^ (-t) * T.H (T.sample (K.cell m)) ^ γ) • F m

theorem n06MaterialJetRow_zero_eq_forget
    {T : MaterialData} {S : PhysicalSpacesData} {K : CanonicalData S}
    {V : VolumeModelData S K} (hV : IsVolumeModel T S K V)
    (γ t : ℝ) (b : ℕ) (F : V.level γ t b) (m : ℕ) :
    n06MaterialJetRow T K γ t F.val m 0 = V.forget γ t b F m := by
  rw [hV.2.2.2 γ t b F m]
  rfl

theorem n06MaterialJetRow_norm
    {D : ReferenceData} {T : MaterialData} {S : PhysicalSpacesData} {K : CanonicalData S}
    (hD : IsAccumulatingProfile D) (hT : IsMaterialData D T)
    (γ t : ℝ) {b : ℕ} (F : CanonicalVolumeJets S K b) (m : ℕ) :
    ‖n06MaterialJetRow T K γ t F m‖ =
      (T.M (T.sample (K.cell m)) ^ (-t) * T.H (T.sample (K.cell m)) ^ γ) * ‖F m‖ := by
  have hpos := hT.2.1 _ (spaces_trace_sample_mem hD hT (K.cell m))
  have hnonneg : 0 ≤ T.M (T.sample (K.cell m)) ^ (-t) *
      T.H (T.sample (K.cell m)) ^ γ :=
    mul_nonneg (Real.rpow_nonneg (zero_le_one.trans hpos.2.2.2) _)
      (Real.rpow_nonneg hpos.2.1.le _)
  simp only [n06MaterialJetRow, norm_smul, Real.norm_eq_abs, abs_of_nonneg hnonneg]

/-- Multiplication by a real scalar preserves any fixed angular reflection sign. -/
theorem n06_canonical_reflection_smul
    {S : PhysicalSpacesData} {K : CanonicalData S} {m : ℕ}
    (σ c : ℝ) (f : CanonicalL2 S K m)
    (hf : (fun p : PolarPoint => f (p.1, Real.pi - p.2))
      =ᵐ[canonicalMeasure S K m] fun p => σ * f p) :
    (fun p : PolarPoint => (c • f : CanonicalL2 S K m) (p.1, Real.pi - p.2))
      =ᵐ[canonicalMeasure S K m] fun p => σ * (c • f : CanonicalL2 S K m) p := by
  have hr := n06_measurePreserving_canonicalAngularReflection.quasiMeasurePreserving.ae_eq_comp
    (Lp.coeFn_smul c f)
  filter_upwards [hr, hf, Lp.coeFn_smul c f] with p hpr hpf hps
  simp only [Function.comp_apply, Pi.smul_apply, smul_eq_mul] at hpr hps
  rw [hpr, hpf, hps]
  ring

theorem n06MaterialJetRow_weak
    {T : MaterialData} {S : PhysicalSpacesData} {K : CanonicalData S} {b : ℕ}
    (γ t : ℝ) (F : CanonicalVolumeJets S K b)
    (hF : F ∈ canonicalVolumeGraph S K b) (m : ℕ) (j : Fin (b + 1)) :
    WeakCanonicalAngularDerivative S K m
      (n06MaterialJetRow T K γ t F m 0) (n06MaterialJetRow T K γ t F m j) j.val := by
  simpa only [n06MaterialJetRow, PiLp.smul_apply] using
    (hF.2 m j).n06_smul
      (T.M (T.sample (K.cell m)) ^ (-t) * T.H (T.sample (K.cell m)) ^ γ)

theorem n06MaterialJetRow_reflection
    {T : MaterialData} {S : PhysicalSpacesData} {K : CanonicalData S} {b : ℕ}
    (γ t : ℝ) (F : CanonicalVolumeJets S K b)
    (hF : F ∈ canonicalVolumeGraph S K b) (m : ℕ) :
    (fun p : PolarPoint => n06MaterialJetRow T K γ t F m 0 (p.1, Real.pi - p.2))
      =ᵐ[canonicalMeasure S K m] (n06MaterialJetRow T K γ t F m 0 : PolarPoint → ℝ) := by
  have heven : (fun p : PolarPoint => F m 0 (p.1, Real.pi - p.2))
      =ᵐ[canonicalMeasure S K m] fun p => (1 : ℝ) * F m 0 p := by
    filter_upwards [hF.1 m] with p hp
    simpa only [one_mul] using hp
  have h := n06_canonical_reflection_smul 1
    (T.M (T.sample (K.cell m)) ^ (-t) * T.H (T.sample (K.cell m)) ^ γ) (F m 0) heven
  simpa only [one_mul, n06MaterialJetRow, PiLp.smul_apply] using h

end ContinuousFlexibility.Analysis
