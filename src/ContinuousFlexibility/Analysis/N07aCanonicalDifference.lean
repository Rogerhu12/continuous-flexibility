import ContinuousFlexibility.Statements.Nonlinear
import ContinuousFlexibility.Scalar.Linearization

/-!
# Exact local differences of the canonical operator

The negative-piece difference is the actual potential multiplier. The
source identities retain the current coordinate and height factors, so a
moving auxiliary column is never silently replaced by its reference value.
-/

noncomputable section

namespace ContinuousFlexibility.Analysis

open Set Filter ContinuousFlexibility.Statements
open scoped Topology ContDiff

/-- A divergence operator depends only on the coefficient germs. -/
theorem n07a_divergenceOperator_eq_of_germs
    {A B : SymmetricCoefficients} {p : PolarPoint}
    (ha : A.a =ᶠ[𝓝 p] B.a) (hb : A.b =ᶠ[𝓝 p] B.b)
    (hc : A.c =ᶠ[𝓝 p] B.c) (u : PolarPoint → ℝ) :
    divergenceOperator A u p = divergenceOperator B u p := by
  have hr : (fun q => A.a q * radialPartial u q + A.b q * angularPartial u q)
      =ᶠ[𝓝 p] (fun q => B.a q * radialPartial u q + B.b q * angularPartial u q) := by
    filter_upwards [ha, hb] with q hqa hqb
    rw [hqa, hqb]
  have hθ : (fun q => A.b q * radialPartial u q + A.c q * angularPartial u q)
      =ᶠ[𝓝 p] (fun q => B.b q * radialPartial u q + B.c q * angularPartial u q) := by
    filter_upwards [hb, hc] with q hqb hqc
    rw [hqb, hqc]
  unfold divergenceOperator
  exact congrArg₂ (fun r t : PolarPoint →L[ℝ] ℝ => r (1, 0) + t (0, 1))
    hr.fderiv_eq hθ.fderiv_eq

/-- No differentiated principal coefficient remains in the perturbation
on an actual negative piece. -/
theorem n07a_canonicalOperator_negative_difference
    {D : ReferenceData} {T : MaterialData} {S : PhysicalSpacesData}
    {C : NonlinearGeometryData S} {L : ReturnCorrectionData S} {K : CanonicalData S}
    {base loss : ℕ} {ε : ℝ}
    (h04 : N04Properties D T S C L K base loss ε)
    {z z₀ : AnnularState S × ℝ}
    (hz : z ∈ stateNeighborhood S C base ε) (hs : stateSector S z.1)
    (hz₀ : z₀ ∈ stateNeighborhood S C base ε) (hs₀ : stateSector S z₀.1)
    (m : ℕ) (hm : K.positive m = false) (u : PolarPoint → ℝ)
    (hu : ContDiff ℝ ∞ u) {p : PolarPoint} (hp : p ∈ canonicalOpen S K m) :
    canonicalOperator S K L z m u p - canonicalOperator S K L z₀ m u p =
      (K.potential z m p - K.potential z₀ m p) * u p := by
  have hform := h04.2.1.2.2.1
  have hnegative := h04.2.1.2.2.2.1
  have hopen : IsOpen (canonicalOpen S K m) := isOpen_Ioo.prod isOpen_univ
  have hnear : ∀ᶠ q in 𝓝 p, q ∈ canonicalOpen S K m := hopen.mem_nhds hp
  have hsame :
      divergenceOperator (K.coefficients z m) u p =
        divergenceOperator (K.coefficients z₀ m) u p := by
    apply n07a_divergenceOperator_eq_of_germs
    · filter_upwards [hnear] with q hq
      exact (hnegative z hz hs m hm q hq).1.trans (hnegative z₀ hz₀ hs₀ m hm q hq).1.symm
    · filter_upwards [hnear] with q hq
      exact (hnegative z hz hs m hm q hq).2.1.trans
        (hnegative z₀ hz₀ hs₀ m hm q hq).2.1.symm
    · filter_upwards [hnear] with q hq
      exact (hnegative z hz hs m hm q hq).2.2.trans
        (hnegative z₀ hz₀ hs₀ m hm q hq).2.2.symm
  rw [hform z hz hs m u hu p hp, hform z₀ hz₀ hs₀ m u hu p hp, hsame]
  ring

/-- The actual source transformation is linear at each fixed state. -/
theorem n07a_canonicalSource_sub
    (S : PhysicalSpacesData) (K : CanonicalData S) (z : AnnularState S × ℝ)
    (m : ℕ) (f g : PolarPoint → ℝ) (p : PolarPoint) :
    canonicalSource S K z m (fun q => f q - g q) p =
      canonicalSource S K z m f p - canonicalSource S K z m g p := by
  simp only [canonicalSource]
  ring

theorem n07a_canonicalSource_const_mul
    (S : PhysicalSpacesData) (K : CanonicalData S) (z : AnnularState S × ℝ)
    (m : ℕ) (c : ℝ) (f : PolarPoint → ℝ) (p : PolarPoint) :
    canonicalSource S K z m (fun q => c * f q) p =
      c * canonicalSource S K z m f p := by
  simp only [canonicalSource]
  ring

/-- The current auxiliary column difference retains both actual source
transformations. This identity does not require radiality of `psi`. -/
theorem n07a_canonicalSource_scalar_column_difference
    (S : PhysicalSpacesData) (K : CanonicalData S) (z z₀ : AnnularState S × ℝ)
    (m : ℕ) (c : ℝ) (f : PolarPoint → ℝ) (p : PolarPoint) :
    canonicalSource S K z m (fun q => c * f q) p -
        canonicalSource S K z₀ m (fun q => c * f q) p =
      c * (canonicalSource S K z m f p - canonicalSource S K z₀ m f p) := by
  rw [n07a_canonicalSource_const_mul, n07a_canonicalSource_const_mul]
  ring

end ContinuousFlexibility.Analysis
