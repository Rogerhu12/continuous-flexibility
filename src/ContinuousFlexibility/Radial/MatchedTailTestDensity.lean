module

public import ContinuousFlexibility.Radial.TailTestPairing
public import Mathlib.Analysis.Distribution.AEEqOfIntegralContDiff
public import Mathlib.Analysis.InnerProductSpace.Projection.Submodule

/-!
# Compact tests are dense in the actual weighted tail space

A smooth positive density on the open tail suffices. Testing an orthogonal
vector against a compact test divided by that density gives its ordinary
distributional pairing. The fundamental lemma then shows that the vector
vanishes. Consequently identities and norm bounds for the existing
continuous operator extend from compact smooth sources to every L² source.
No finiteness of the total tail mass is required.
-/

@[expose] public section

noncomputable section

namespace ContinuousFlexibility.Radial

open Set Filter MeasureTheory
open scoped Topology ContDiff InnerProductSpace
open ContinuousFlexibility.Statements

/-- Actual L² classes represented by smooth functions compactly supported
inside the open tail. -/
def matchedTailSmoothTests (T : DeepTailData) : Submodule ℝ (DeepTailL2 T) where
  carrier := {f | ∃ φ : ℝ → ℝ, ContDiff ℝ ∞ φ ∧ HasCompactSupport φ ∧
    tsupport φ ⊆ Ioo T.entrance T.endpoint ∧ (f : ℝ → ℝ) =ᵐ[deepTailMeasure T] φ}
  zero_mem' := by
    refine ⟨0, contDiff_const, HasCompactSupport.zero, ?_, ?_⟩
    · simp only [tsupport_zero, empty_subset]
    · exact Lp.coeFn_zero ℝ 2 (deepTailMeasure T)
  add_mem' := by
    rintro f g ⟨φ, hφ, hcφ, hsφ, hf⟩ ⟨ψ, hψ, hcψ, hsψ, hg⟩
    refine ⟨φ + ψ, hφ.add hψ, hcφ.add hcψ,
      (tsupport_add φ ψ).trans (union_subset hsφ hsψ), ?_⟩
    filter_upwards [Lp.coeFn_add f g, hf, hg] with x hx hfx hgx
    simpa only [Pi.add_apply, hfx, hgx] using hx
  smul_mem' := by
    rintro a f ⟨φ, hφ, hcφ, hsφ, hf⟩
    refine ⟨fun x => a * φ x, contDiff_const.mul hφ, hcφ.mul_left,
      tsupport_mul_subset_right.trans hsφ, ?_⟩
    filter_upwards [Lp.coeFn_smul a f, hf] with x hx hfx
    simpa only [Pi.smul_apply, smul_eq_mul, hfx] using hx

/-- Density is proved for the actual weighted measure, not an auxiliary
sequence space. -/
theorem matchedTailSmoothTests_dense {T : DeepTailData}
    (hp : ContDiffOn ℝ ∞ T.p (Ioo T.entrance T.endpoint))
    (hpos : ∀ x ∈ Ioo T.entrance T.endpoint, 0 < T.p x) :
    Dense (matchedTailSmoothTests T : Set (DeepTailL2 T)) := by
  have horth : (matchedTailSmoothTests T)ᗮ = ⊥ := by
    apply le_antisymm ?_ bot_le
    intro u hu
    rw [Submodule.mem_bot]
    have hz : ∀ᵐ x ∂volume, x ∈ Ioo T.entrance T.endpoint → u x = 0 := by
      apply isOpen_Ioo.ae_eq_zero_of_integral_contDiff_smul_eq_zero
        (tail_locallyIntegrableOn hp hpos u)
      intro φ hφ hc hs
      let ht := tail_div_test_memLp hp hpos hφ hc hs
      have hmem : ht.toLp (fun x => φ x / T.p x) ∈ matchedTailSmoothTests T :=
        ⟨fun x => φ x / T.p x, tail_contDiff_div_test hp hpos hφ hs,
          hc.of_isClosed_subset (isClosed_tsupport _) (tail_tsupport_div_test φ),
          (tail_tsupport_div_test φ).trans hs, MemLp.coeFn_toLp ht⟩
      have hh := (Submodule.mem_orthogonal (matchedTailSmoothTests T) u).mp hu _ hmem
      change tailTestPairing T φ ht u = 0 at hh
      rw [tailTestPairing_apply hp hpos hs] at hh
      simpa only [smul_eq_mul, mul_comm] using hh
    have hac : deepTailMeasure T ≪ volume :=
      (withDensity_absolutelyContinuous (volume.restrict (Ioo T.entrance T.endpoint))
        (fun x => ENNReal.ofReal (T.p x))).trans Measure.absolutelyContinuous_restrict
    have hm : ∀ᵐ x ∂deepTailMeasure T, x ∈ Ioo T.entrance T.endpoint :=
      (withDensity_absolutelyContinuous (volume.restrict (Ioo T.entrance T.endpoint))
        (fun x => ENNReal.ofReal (T.p x))).ae_le
          (ae_restrict_mem measurableSet_Ioo)
    apply Lp.eq_zero_iff_ae_eq_zero.mpr
    filter_upwards [hac.ae_le hz, hm] with x hx hxm
    exact hx hxm
  exact Submodule.dense_iff_topologicalClosure_eq_top.mpr
    ((matchedTailSmoothTests T).topologicalClosure_eq_top_iff.mpr horth)

/-- A norm estimate on compact smooth sources controls the operator already
defined on the full Hilbert space. -/
theorem matchedTail_opNorm_le_of_compactTests {T : DeepTailData}
    (hp : ContDiffOn ℝ ∞ T.p (Ioo T.entrance T.endpoint))
    (hpos : ∀ x ∈ Ioo T.entrance T.endpoint, 0 < T.p x)
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    (A : DeepTailL2 T →L[ℝ] E) {C : ℝ} (hC : 0 ≤ C)
    (hbound : ∀ (f : DeepTailL2 T) (φ : ℝ → ℝ),
      ContDiff ℝ ∞ φ → HasCompactSupport φ →
      tsupport φ ⊆ Ioo T.entrance T.endpoint →
      (f : ℝ → ℝ) =ᵐ[deepTailMeasure T] φ → ‖A f‖ ≤ C * ‖f‖) :
    ‖A‖ ≤ C := by
  apply ContinuousLinearMap.opNorm_le_bound A hC
  intro f
  have hc : IsClosed {g : DeepTailL2 T | ‖A g‖ ≤ C * ‖g‖} :=
    isClosed_le A.continuous.norm (continuous_const.mul continuous_norm)
  have hs : (matchedTailSmoothTests T : Set (DeepTailL2 T)) ⊆
      {g : DeepTailL2 T | ‖A g‖ ≤ C * ‖g‖} := by
    rintro g ⟨φ, hφ, hcφ, hsφ, hg⟩
    exact hbound g φ hφ hcφ hsφ hg
  exact (closure_minimal hs hc) (matchedTailSmoothTests_dense hp hpos f)

/-- Equality on the same concrete compact tests identifies two actual
continuous operators on every L² source. -/
theorem matchedTail_eq_of_compactTests {T : DeepTailData}
    (hp : ContDiffOn ℝ ∞ T.p (Ioo T.entrance T.endpoint))
    (hpos : ∀ x ∈ Ioo T.entrance T.endpoint, 0 < T.p x)
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    (A B : DeepTailL2 T →L[ℝ] E)
    (heq : ∀ (f : DeepTailL2 T) (φ : ℝ → ℝ),
      ContDiff ℝ ∞ φ → HasCompactSupport φ →
      tsupport φ ⊆ Ioo T.entrance T.endpoint →
      (f : ℝ → ℝ) =ᵐ[deepTailMeasure T] φ → A f = B f) :
    A = B := by
  ext f
  have hs : (matchedTailSmoothTests T : Set (DeepTailL2 T)) ⊆
      {g : DeepTailL2 T | A g = B g} := by
    rintro g ⟨φ, hφ, hcφ, hsφ, hg⟩
    exact heq g φ hφ hcφ hsφ hg
  exact (closure_minimal hs (isClosed_eq A.continuous B.continuous))
    (matchedTailSmoothTests_dense hp hpos f)

end ContinuousFlexibility.Radial
