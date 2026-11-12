import ContinuousFlexibility.Analysis.N07aCanonicalScalarColumns
import ContinuousFlexibility.Analysis.N07aCanonicalTestOperator
import ContinuousFlexibility.Analysis.N07aAngularCutoff

/-!
# The actual cutoff height and its scalar source column

The cutoff height is smooth only on the open piece. A genuine radial
cutoff supplies a compact canonical test with the same germ at any
interior point. Applying N04 there identifies its differential expression
with the actual left scalar column, with the original sign convention.
-/

noncomputable section

namespace ContinuousFlexibility.Analysis

open Set Filter MeasureTheory ContinuousFlexibility.Statements
open scoped ContDiff Topology

variable {D : ReferenceData} {T : MaterialData} {S : PhysicalSpacesData}
  {C : NonlinearGeometryData S} {L : ReturnCorrectionData S} {K : CanonicalData S}
  {base loss : ℕ} {ε : ℝ} {z : AnnularState S × ℝ} {m : ℕ}

theorem n07a_canonicalOpen_germ_test {f : PolarPoint → ℝ}
    (hf : ContDiffOn ℝ ∞ f (canonicalOpen S K m))
    (hfp : ∀ p ∈ canonicalOpen S K m, f (p + (0, Real.pi)) = f p)
    {p : PolarPoint} (hp : p ∈ canonicalOpen S K m) :
    ∃ W : PolarPoint → ℝ, CanonicalTest S K m W ∧ W =ᶠ[𝓝 p] f := by
  have hab : K.left m < K.right m := hp.1.1.trans hp.1.2
  obtain ⟨k, hk⟩ := n07aAngularIntervalCutoff_exists_one_nhds
    (K.left m) (K.right m) hab hp.1
  let c := n07aAngularIntervalCutoff (K.left m) (K.right m) hab k
  have htest : CanonicalTest S K m (fun q => c q.1) := by
    refine ⟨(n07aAngularIntervalCutoff_contDiff _ _ hab k).comp contDiff_fst,
      ?_, tsupport c, n07aAngularIntervalCutoff_compact _ _ hab k,
      n07aAngularIntervalCutoff_tsupport _ _ hab k, ?_⟩
    · intro q
      simp only [Prod.fst_add, add_zero]
    · intro r hr θ
      exact image_eq_zero_of_notMem_tsupport hr
  refine ⟨fun q => f q * c q.1, n07a_canonicalTest_mul_on htest hf hfp, ?_⟩
  filter_upwards [continuous_fst.continuousAt.eventually hk] with q hq
  exact (congrArg (f q * ·) hq).trans (mul_one _)

def n07aCanonicalCutoffHeight (S : PhysicalSpacesData) (K : CanonicalData S)
    (z : AnnularState S × ℝ) (m : ℕ) : PolarPoint → ℝ :=
  canonicalHeight S K z m (fun q => S.chiLeft q.1)

theorem n07aCanonicalCutoffHeight_smooth
    (h04 : N04Properties D T S C L K base loss ε)
    (hz : z ∈ stateNeighborhood S C base ε) (hs : stateSector S z.1)
    (hχ : ContDiff ℝ ∞ S.chiLeft) :
    ContDiffOn ℝ ∞ (n07aCanonicalCutoffHeight S K z m) (canonicalOpen S K m) := by
  obtain ⟨_, hg, _, _, _, hgs, hh, hpoint⟩ := h04.1.charts z hz hs m
  exact (hχ.comp_contDiffOn hgs.fst).div (hh.comp hgs hg)
    (fun p hp => (hpoint _ (hg hp)).1.ne')

theorem n07aCanonicalCutoffHeight_periodic
    (h04 : N04Properties D T S C L K base loss ε)
    (hz : z ∈ stateNeighborhood S C base ε) (hs : stateSector S z.1) :
    ∀ p ∈ canonicalOpen S K m,
      n07aCanonicalCutoffHeight S K z m (p + (0, Real.pi)) =
        n07aCanonicalCutoffHeight S K z m p := by
  obtain ⟨_, hg, hgf, hfg, _, _, _, hpoint⟩ := h04.1.charts z hz hs m
  have hgp := n07a_current_inverseChart_periodic h04 hz hs m
  intro p hp
  simp only [n07aCanonicalCutoffHeight, canonicalHeight, hgp p hp,
    Prod.fst_add, add_zero, (hpoint _ (hg hp)).2.2.2]

theorem n07aCanonicalCutoffHeight_column
    (h04 : N04Properties D T S C L K base loss ε)
    (hz : z ∈ stateNeighborhood S C base ε) (hs : stateSector S z.1)
    (hχ : ContDiff ℝ ∞ S.chiLeft) :
    EqOn (n07aScalarColumn D S C L K z m 0)
      (fun p => divergenceOperator (K.coefficients z m)
        (n07aCanonicalCutoffHeight S K z m) p +
          (if K.positive m then -1 else (1 : ℝ)) * K.potential z m p *
            n07aCanonicalCutoffHeight S K z m p)
      (canonicalOpen S K m) := by
  obtain ⟨_, hg, hgf, hfg, hfs, _, _, hpoint⟩ := h04.1.charts z hz hs m
  intro p hp
  obtain ⟨W, hW, hgerm⟩ := n07a_canonicalOpen_germ_test
    (n07aCanonicalCutoffHeight_smooth h04 hz hs hχ)
    (n07aCanonicalCutoffHeight_periodic h04 hz hs) hp
  have hq := hg hp
  have hchart : Tendsto (K.chart z m) (𝓝 (K.inverseChart z m p)) (𝓝 p) := by
    simpa only [hfg p hp] using
      (hfs.contDiffAt ((h04.1.domains z hz hs m).1.mem_nhds hq)).continuousAt.tendsto
  have hraw : n07aPhysicalTestPullback S K z m W =ᶠ[𝓝 (K.inverseChart z m p)]
      fun q => S.chiLeft q.1 := by
    filter_upwards [n07aPhysicalTestPullback_germ z m W (h04.1.domains z hz hs m).1 hq,
      hgerm.comp_tendsto hchart,
      (h04.1.domains z hz hs m).1.mem_nhds hq] with q htest hcomp hqin
    simp only [Function.comp_apply] at hcomp
    rw [htest, hcomp]
    simp only [n07aCanonicalCutoffHeight, canonicalHeight, hgf q hqin]
    field_simp [(hpoint q hqin).1.ne']
  have hd := n07a_divergenceOperator_unknown_germ (L.coefficients z) hraw
  have he := n07aPhysicalTestPullback_source_operator h04 hz hs hW hp
  change canonicalSource S K z m (divergenceOperator (L.coefficients z)
    (n07aPhysicalTestPullback S K z m W)) p = _ at he
  have hc : canonicalSource S K z m (divergenceOperator (L.coefficients z)
      (n07aPhysicalTestPullback S K z m W)) p = n07aScalarColumn D S C L K z m 0 p := by
    change K.height z m (K.inverseChart z m p) *
      divergenceOperator (L.coefficients z) (n07aPhysicalTestPullback S K z m W)
        (K.inverseChart z m p) / |planeJacobian (K.chart z m) (K.inverseChart z m p)| = _
    rw [hd]
    rfl
  rw [hc] at he
  dsimp only at he
  rw [n07a_divergenceOperator_unknown_germ (K.coefficients z m) hgerm,
    hgerm.self_of_nhds] at he
  exact he

end ContinuousFlexibility.Analysis
