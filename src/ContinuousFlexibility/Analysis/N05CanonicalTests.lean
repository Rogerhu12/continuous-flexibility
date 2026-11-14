module

public import ContinuousFlexibility.Statements.Nonlinear
public import ContinuousFlexibility.Analysis.CylinderTestPairing

/-!
# Canonical cylinder test pairings

The canonical measure is the actual finite cylinder measure. Its L²
pairings and angular reflection are continuous maps on the quotient spaces.
These maps will define the weak derivative graph by closed kernels.
-/

@[expose] public section

noncomputable section

namespace ContinuousFlexibility.Statements

open Set Filter MeasureTheory
open scoped ContDiff Topology RealInnerProductSpace InnerProductSpace

instance n05CanonicalMeasure_finite (S : PhysicalSpacesData) (K : CanonicalData S)
    (m : ℕ) : IsFiniteMeasure (canonicalMeasure S K m) := by
  refine ⟨?_⟩
  rw [canonicalMeasure, Measure.restrict_apply_univ]
  have hc : IsCompact (Icc (K.left m) (K.right m) ×ˢ Icc (0 : ℝ) Real.pi) :=
    isCompact_Icc.prod isCompact_Icc
  have hsub : Ioo (K.left m) (K.right m) ×ˢ Ioc (0 : ℝ) Real.pi ⊆
      Icc (K.left m) (K.right m) ×ˢ Icc (0 : ℝ) Real.pi :=
    fun _ h => ⟨⟨h.1.1.le, h.1.2.le⟩, ⟨h.2.1.le, h.2.2⟩⟩
  exact lt_of_le_of_lt (measure_mono hsub) hc.measure_lt_top

theorem n05Canonical_memLp_of_continuous (S : PhysicalSpacesData) (K : CanonicalData S)
    (m : ℕ) {φ : PolarPoint → ℝ} (hφ : Continuous φ) :
    MemLp φ 2 (canonicalMeasure S K m) := by
  have hc : IsCompact (Icc (K.left m) (K.right m) ×ˢ Icc (0 : ℝ) Real.pi) :=
    isCompact_Icc.prod isCompact_Icc
  obtain ⟨B, hB⟩ := hc.bddAbove_image hφ.norm.continuousOn
  refine MemLp.of_bound hφ.aestronglyMeasurable B ?_
  have ha : ∀ᵐ p ∂canonicalMeasure S K m,
      p ∈ Ioo (K.left m) (K.right m) ×ˢ Ioc (0 : ℝ) Real.pi :=
    ae_restrict_mem (measurableSet_Ioo.prod measurableSet_Ioc)
  filter_upwards [ha] with p hp
  exact hB ⟨p, ⟨⟨hp.1.1.le, hp.1.2.le⟩, ⟨hp.2.1.le, hp.2.2⟩⟩, rfl⟩

theorem n05CanonicalTest_memLp {S : PhysicalSpacesData} {K : CanonicalData S} {m : ℕ}
    {φ : PolarPoint → ℝ} (hφ : CanonicalTest S K m φ) :
    MemLp φ 2 (canonicalMeasure S K m) :=
  n05Canonical_memLp_of_continuous S K m hφ.1.continuous

theorem n05CanonicalTest_angular_memLp {S : PhysicalSpacesData} {K : CanonicalData S}
    {m : ℕ} {φ : PolarPoint → ℝ} (hφ : CanonicalTest S K m φ) (j : ℕ) :
    MemLp (mixedDerivative 0 j φ) 2 (canonicalMeasure S K m) :=
  n05Canonical_memLp_of_continuous S K m (contDiff_mixedDerivative hφ.1 0 j).continuous

def n05CanonicalTestPairing (S : PhysicalSpacesData) (K : CanonicalData S) (m : ℕ)
    (φ : PolarPoint → ℝ) (hφ : MemLp φ 2 (canonicalMeasure S K m)) :
    CanonicalL2 S K m →L[ℝ] ℝ :=
  innerSL ℝ (hφ.toLp φ)

theorem n05CanonicalTestPairing_apply (S : PhysicalSpacesData) (K : CanonicalData S)
    (m : ℕ) (φ : PolarPoint → ℝ) (hφ : MemLp φ 2 (canonicalMeasure S K m))
    (u : CanonicalL2 S K m) :
    n05CanonicalTestPairing S K m φ hφ u = ∫ p, u p * φ p ∂canonicalMeasure S K m := by
  change ⟪hφ.toLp φ, u⟫_ℝ = _
  rw [L2.inner_def]
  apply integral_congr_ae
  filter_upwards [MemLp.coeFn_toLp hφ] with p hp
  rw [hp]
  simp only [RCLike.inner_apply, conj_trivial]

theorem n05CanonicalMeasure_eq_prod (S : PhysicalSpacesData) (K : CanonicalData S)
    (m : ℕ) :
    canonicalMeasure S K m =
      ((volume : Measure ℝ).restrict (Ioo (K.left m) (K.right m))).prod angleMeasure := by
  change ((volume : Measure ℝ).prod (volume : Measure ℝ)).restrict
      (Ioo (K.left m) (K.right m) ×ˢ Ioc 0 Real.pi) =
    ((volume : Measure ℝ).restrict (Ioo (K.left m) (K.right m))).prod
      ((volume : Measure ℝ).restrict (Ioc 0 Real.pi))
  rw [← Measure.prod_restrict]

theorem n05CanonicalReflection_measurePreserving (S : PhysicalSpacesData)
    (K : CanonicalData S) (m : ℕ) :
    MeasurePreserving cylinderAngularReflection (canonicalMeasure S K m)
      (canonicalMeasure S K m) := by
  let : SFinite angleMeasure := by unfold angleMeasure; infer_instance
  rw [n05CanonicalMeasure_eq_prod]
  exact (MeasurePreserving.id
    ((volume : Measure ℝ).restrict (Ioo (K.left m) (K.right m)))).prod
    measurePreserving_angleReflection

def n05CanonicalReflection (S : PhysicalSpacesData) (K : CanonicalData S) (m : ℕ) :
    CanonicalL2 S K m →ₗᵢ[ℝ] CanonicalL2 S K m :=
  Lp.compMeasurePreservingₗᵢ ℝ cylinderAngularReflection
    (n05CanonicalReflection_measurePreserving S K m)

theorem n05CanonicalReflection_ae (S : PhysicalSpacesData) (K : CanonicalData S)
    (m : ℕ) (u : CanonicalL2 S K m) :
    (n05CanonicalReflection S K m u : PolarPoint → ℝ) =ᵐ[canonicalMeasure S K m]
      fun p => u (p.1, Real.pi - p.2) :=
  Lp.coeFn_compMeasurePreserving u (n05CanonicalReflection_measurePreserving S K m)

theorem n05CanonicalReflection_fixed_iff (S : PhysicalSpacesData) (K : CanonicalData S)
    (m : ℕ) (u : CanonicalL2 S K m) :
    n05CanonicalReflection S K m u = u ↔
      (fun p : PolarPoint => u (p.1, Real.pi - p.2)) =ᵐ[canonicalMeasure S K m]
        (u : PolarPoint → ℝ) := by
  constructor
  · intro h
    have he := n05CanonicalReflection_ae S K m u
    rw [h] at he
    exact he.symm
  · intro h
    exact Lp.ext ((n05CanonicalReflection_ae S K m u).trans h)

def n05CanonicalJetCoordinate (S : PhysicalSpacesData) (K : CanonicalData S)
    (s m : ℕ) (j : Fin (s + 1)) : CanonicalVolumeJets S K s →L[ℝ] CanonicalL2 S K m :=
  (PiLp.proj (𝕜 := ℝ) 2 (fun _ : Fin (s + 1) => CanonicalL2 S K m) j).comp
    (lp.evalCLM ℝ (fun n => PiLp 2 (fun _ : Fin (s + 1) => CanonicalL2 S K n)) 2 m)

@[simp] theorem n05CanonicalJetCoordinate_apply (S : PhysicalSpacesData)
    (K : CanonicalData S) (s m : ℕ) (j : Fin (s + 1)) (v : CanonicalVolumeJets S K s) :
    n05CanonicalJetCoordinate S K s m j v = v m j := rfl

end ContinuousFlexibility.Statements
