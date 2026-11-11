import ContinuousFlexibility.Analysis.N07aAngularInverseLipschitz

/-!
# One continuous inverse extension with the genuine boundary jets

A Lipschitz extension is used only to choose values on the closed strip.
The inverse-function theorem proves that those values agree locally with
a genuine smooth inverse. Thus all boundary derivatives below belong to
the actual interior inverse, not to the arbitrary inverse candidate.
-/

noncomputable section

namespace ContinuousFlexibility.Analysis

open Set Filter ContinuousFlexibility.Statements
open scoped Topology ContDiff NNReal

theorem n07a_eventuallyEq_on_closure {f g : PolarPoint → PolarPoint}
    {s : Set PolarPoint} {a : PolarPoint}
    (hf : ∀ᶠ p in 𝓝 a, ContinuousAt f p)
    (hg : ∀ᶠ p in 𝓝 a, ContinuousAt g p)
    (he : ∀ᶠ p in 𝓝 a, p ∈ s → f p = g p) :
    ∀ᶠ p in 𝓝 a, p ∈ closure s → f p = g p := by
  obtain ⟨V, hV, hVo, haV⟩ := mem_nhds_iff.mp he
  filter_upwards [hVo.mem_nhds haV, hf, hg] with p hp hf hg hpcl
  have : NeBot (𝓝[s] p) := mem_closure_iff_nhdsWithin_neBot.mp hpcl
  have hsame : f =ᶠ[𝓝[s] p] g := by
    filter_upwards [self_mem_nhdsWithin,
      nhdsWithin_le_nhds (hVo.mem_nhds hp)] with q hq hqV
    exact hV hqV hq
  exact tendsto_nhds_unique_of_eventuallyEq
    (hf.tendsto.mono_left nhdsWithin_le_nhds)
    (hg.tendsto.mono_left nhdsWithin_le_nhds) hsame

theorem n07a_inverseExtension_boundary
    {f g g₀ : PolarPoint → PolarPoint} {s t : Set PolarPoint} {a : PolarPoint}
    (ha : a ∈ closure s) (hmap : MapsTo f s t)
    (hgf : ∀ p ∈ s, g (f p) = p) (hfg : ∀ q ∈ t, f (g q) = q)
    (hf : ContDiffAt ℝ ∞ f a) (hdet : (fderiv ℝ f a).det ≠ 0)
    {M : ℝ≥0} (hg : LipschitzOnWith M g t)
    (hg₀ : Continuous g₀) (hgg₀ : EqOn g g₀ t) :
    g₀ (f a) = a ∧ ContDiffWithinAt ℝ ∞ g₀ (closure t) (f a) ∧
      HasFDerivWithinAt g₀
        (((fderiv ℝ f a).toContinuousLinearEquivOfDetNeZero hdet).symm :
          PolarPoint →L[ℝ] PolarPoint) (closure t) (f a) := by
  obtain ⟨G, hG, hGa, hGd, he⟩ :=
    n07a_boundary_inverse_germ ha hmap hgf hfg hf hdet hg
  have hG0 : ContDiffAt ℝ 0 G (f a) := hG.of_le (by simp)
  have hGc : ∀ᶠ q in 𝓝 (f a), ContinuousAt G q :=
    (hG0.eventually (by simp)).mono fun _ hq => hq.continuousAt
  have he₀ : ∀ᶠ q in 𝓝 (f a), q ∈ t → g₀ q = G q := by
    filter_upwards [he] with q hq hqt
    exact (hgg₀ hqt).symm.trans (hq hqt)
  have hec := n07a_eventuallyEq_on_closure
    (Eventually.of_forall fun _ => hg₀.continuousAt) hGc he₀
  have hfa : f a ∈ closure t := hf.continuousAt.continuousWithinAt.mem_closure ha hmap
  have hvalue : g₀ (f a) = G (f a) := hec.self_of_nhds hfa
  have hwithin : g₀ =ᶠ[𝓝[closure t] (f a)] G := by
    filter_upwards [hec.filter_mono nhdsWithin_le_nhds, self_mem_nhdsWithin] with q hq hqt
    exact hq hqt
  exact ⟨hvalue.trans hGa,
    hG.contDiffWithinAt.congr_of_eventuallyEq hwithin hvalue,
    hGd.hasFDerivWithinAt.congr_of_eventuallyEq hwithin hvalue⟩

variable {D : ReferenceData} {T : MaterialData} {S : PhysicalSpacesData}
  {C : NonlinearGeometryData S} {L : ReturnCorrectionData S} {K : CanonicalData S}
  {base loss : ℕ} {ε : ℝ} {z : AnnularState S × ℝ}

/-- Every actual piece has one continuous closed inverse whose boundary
jets are supplied by the smooth forward chart. -/
theorem n07a_exists_actual_inverseExtension
    (h04 : N04Properties D T S C L K base loss ε)
    (hz : z ∈ stateNeighborhood S C base ε) (hs : stateSector S z.1) (m : ℕ)
    (hLip : ∃ M : ℝ≥0, LipschitzOnWith M (K.inverseChart z m) (canonicalOpen S K m)) :
    ∃ g₀ : PolarPoint → PolarPoint,
      Continuous g₀ ∧ EqOn (K.inverseChart z m) g₀ (canonicalOpen S K m) ∧
      ∀ p, p.1 ∈ Icc (K.physicalLeft m) (K.physicalRight m) →
        g₀ (K.chart z m p) = p ∧
        ContDiffWithinAt ℝ ∞ g₀ (Icc (K.left m) (K.right m) ×ˢ univ) (K.chart z m p) := by
  obtain ⟨M, hM⟩ := hLip
  obtain ⟨g₀, hg₀, hgg₀⟩ := hM.extend_finite_dimension
  refine ⟨g₀, hg₀.continuous, hgg₀, ?_⟩
  intro p hp
  have hgeom := h04.2.2.2.2.2.2.2.1 z hz hs m
  have hclosed := h04.2.2.2.2.2.2.2.2.1 z hz hs m p hp
  have hpcl : p ∈ closure (physicalPieceOpen S K m) := by
    rw [physicalPieceOpen, closure_prod_eq, closure_Ioo (h04.2.2.2.1 m).1.ne, closure_univ]
    exact ⟨hp, mem_univ _⟩
  have hdet : (fderiv ℝ (K.chart z m) p).det ≠ 0 := by
    simpa only [← n07a_planeJacobian_eq_det] using hclosed.2.2.1
  have h := n07a_inverseExtension_boundary hpcl hgeom.1 hgeom.2.2.1 hgeom.2.2.2.1
    hclosed.1 hdet hM hg₀.continuous hgg₀
  refine ⟨h.1, ?_⟩
  simpa only [canonicalOpen, closure_prod_eq,
    closure_Ioo (h04.2.2.2.1 m).2.1.ne, closure_univ] using h.2.1

end ContinuousFlexibility.Analysis
