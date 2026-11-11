import ContinuousFlexibility.Analysis.N07aCanonicalTestPullback
import ContinuousFlexibility.Analysis.N07aCanonicalGreenPairing

/-!
# The exact operator on genuine pulled-back tests

The physical test is the actual gauge pullback on the open piece. Its
zero extension has the same germ there, so the original N04 operator
identity applies without assuming a global chart or height extension.
The sign of the positive-piece convention remains explicit.
-/

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
  rcases h04 with ⟨_, _, _, _, _, _, _, hgeom, _⟩
  obtain ⟨_, hg, _, hfg, _, _, _, hp⟩ := hgeom z hz hs m
  intro p hpm
  have hq := hg hpm
  have hh := (hp _ hq).1.ne'
  simp only [canonicalHeight, n07aPhysicalTestPullback, ite_eq_left hq.1, hfg p hpm]
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
  rcases h04 with ⟨_, _, _, _, _, _, _, hgeom, _, _, _, _, _, hop, _⟩
  obtain ⟨_, hg, _, _, _, _, _, _⟩ := hgeom z hz hs m
  intro p hp
  have hq := hg hp
  have he := n07a_divergenceOperator_unknown_germ (L.coefficients z)
    (n07aPhysicalTestPullback_germ z m W hq)
  have hsource : canonicalSource S K z m
      (divergenceOperator (L.coefficients z) (n07aPhysicalTestPullback S K z m W)) p =
      canonicalSource S K z m (divergenceOperator (L.coefficients z)
        (fun q => K.height z m q * W (K.chart z m q))) p := by
    simp only [canonicalSource, he]
  rw [hsource]
  have h := hop z hz hs m W hW.1 p hp
  cases hb : K.positive m <;> simp [canonicalOperator, hb] at h ⊢ <;> linarith

/-- Open smooth periodic coefficients send a genuine compact test to a
genuine compact test under the actual symmetric divergence expression. -/
theorem n07a_canonicalTest_divergence (A : SymmetricCoefficients)
    (ha : ContDiffOn ℝ ∞ A.a (canonicalOpen S K m))
    (hb : ContDiffOn ℝ ∞ A.b (canonicalOpen S K m))
    (hc : ContDiffOn ℝ ∞ A.c (canonicalOpen S K m))
    (hap : ∀ p ∈ canonicalOpen S K m, A.a (p + (0, Real.pi)) = A.a p)
    (hbp : ∀ p ∈ canonicalOpen S K m, A.b (p + (0, Real.pi)) = A.b p)
    (hcp : ∀ p ∈ canonicalOpen S K m, A.c (p + (0, Real.pi)) = A.c p)
    {W : PolarPoint → ℝ} (hW : CanonicalTest S K m W) :
    CanonicalTest S K m (divergenceOperator A W) := by
  have hWr := n07a_canonicalTest_mixedDerivative hW 1 0
  have hWt := n07a_canonicalTest_mixedDerivative hW 0 1
  let qr := fun p => A.a p * mixedDerivative 1 0 W p + A.b p * mixedDerivative 0 1 W p
  let qt := fun p => A.b p * mixedDerivative 1 0 W p + A.c p * mixedDerivative 0 1 W p
  have hqr : CanonicalTest S K m qr := n07a_canonicalTest_add
    (n07a_canonicalTest_mul_on hWr ha hap) (n07a_canonicalTest_mul_on hWt hb hbp)
  have hqt : CanonicalTest S K m qt := n07a_canonicalTest_add
    (n07a_canonicalTest_mul_on hWr hb hbp) (n07a_canonicalTest_mul_on hWt hc hcp)
  have he : divergenceOperator A W =
      fun p => mixedDerivative 1 0 qr p + mixedDerivative 0 1 qt p := by
    funext p
    simp only [divergenceOperator, n07a_radialPartial_eq_mixed hW.1,
      n07a_angularPartial_eq_mixed hW.1]
    change radialPartial qr p + angularPartial qt p = _
    rw [n07a_radialPartial_eq_mixed hqr.1, n07a_angularPartial_eq_mixed hqt.1]
  rw [he]
  exact n07a_canonicalTest_add (n07a_canonicalTest_mixedDerivative hqr 1 0)
    (n07a_canonicalTest_mixedDerivative hqt 0 1)

end ContinuousFlexibility.Analysis
