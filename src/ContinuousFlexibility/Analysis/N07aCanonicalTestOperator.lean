module

public import ContinuousFlexibility.Analysis.N07aCanonicalTestPullback
public import ContinuousFlexibility.Analysis.N07aCanonicalTestDivergence

/-!
# The exact operator on genuine pulled-back tests

The physical test is the actual gauge pullback on the open piece. Its
zero extension has the same germ there, so the original N04 operator
identity applies without assuming a global chart or height extension.
The sign of the positive-piece convention remains explicit.
-/

@[expose] public section

noncomputable section

namespace ContinuousFlexibility.Analysis

open Set Filter ContinuousFlexibility.Statements
open scoped ContDiff Topology

variable {D : ReferenceData} {T : MaterialData} {S : PhysicalSpacesData}
  {C : NonlinearGeometryData S} {L : ReturnCorrectionData S} {K : CanonicalData S}
  {base loss : ℕ} {ε : ℝ} {z : AnnularState S × ℝ} {m : ℕ}

theorem n07aPhysicalTestPullback_height
    (h04 : N04Properties D T S C L K base loss ε)
    (hz : z ∈ stateNeighborhood S C base ε) (hs : stateSector S z.1)
    (W : PolarPoint → ℝ) :
    EqOn (canonicalHeight S K z m (n07aPhysicalTestPullback S K z m W)) W
      (canonicalOpen S K m) := by
  obtain ⟨_, hg, _, hfg, _, _, _, hp⟩ := h04.1.charts z hz hs m
  intro p hpm
  have hq := hg hpm
  have hh := (hp _ hq).1.ne'
  simp only [canonicalHeight, n07aPhysicalTestPullback, ite_eq_left hq, hfg p hpm]
  field_simp [hh]

theorem n07aPhysicalTestPullback_source_operator
    (h04 : N04Properties D T S C L K base loss ε)
    (hz : z ∈ stateNeighborhood S C base ε) (hs : stateSector S z.1)
    {W : PolarPoint → ℝ} (hW : CanonicalTest S K m W) :
    EqOn (canonicalSource S K z m
        (divergenceOperator (L.coefficients z) (n07aPhysicalTestPullback S K z m W)))
      (fun p => divergenceOperator (K.coefficients z m) W p +
        (if K.positive m then -1 else (1 : ℝ)) * K.potential z m p * W p)
      (canonicalOpen S K m) := by
  have hop := h04.2.1.2.2.1
  have hg := (h04.1.charts z hz hs m).2.1
  intro p hp
  have hq := hg hp
  have he := n07a_divergenceOperator_unknown_germ (L.coefficients z)
    (n07aPhysicalTestPullback_germ z m W (h04.1.domains z hz hs m).1 hq)
  have hsource : canonicalSource S K z m
      (divergenceOperator (L.coefficients z) (n07aPhysicalTestPullback S K z m W)) p =
      canonicalSource S K z m (divergenceOperator (L.coefficients z)
        (fun q => K.height z m q * W (K.chart z m q))) p := by
    simp only [canonicalSource, he]
  rw [hsource]
  have h := hop z hz hs m W hW.1 p hp
  cases hb : K.positive m <;> simp [canonicalOperator, hb] at h ⊢ <;> linarith

end ContinuousFlexibility.Analysis
