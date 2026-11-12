import ContinuousFlexibility.Analysis.N06PhysicalHeightAffinePairing
import ContinuousFlexibility.Analysis.N06PhysicalPeriodicity
import Mathlib.Analysis.InnerProductSpace.LinearMap

/-!
# Limits of the actual full-period physical pairings

Finite-mode approximants need not satisfy the original global graph equation.
For a fixed compact physical test, convergence in each actual canonical L2
space and convergence of the left-height scalar suffice. The genuine finite
piece formulas retain both angular halves and the literal affine cutoff.
No endpoint trace convergence or periodicity of the paired function is used.
-/

noncomputable section

namespace ContinuousFlexibility.Analysis

open Filter MeasureTheory
open scoped Topology

/-- A fixed L2 test is continuous on its original L2 space. -/
theorem n06_tendsto_integral_lp_pairing
    {α : Type*} [MeasurableSpace α] {μ : Measure α}
    {W : ℕ → Lp ℝ 2 μ} {w : Lp ℝ 2 μ} {φ : α → ℝ}
    (hφ : MemLp φ 2 μ) (hW : Tendsto W atTop (𝓝 w)) :
    Tendsto (fun n => ∫ p, W n p * φ p ∂μ) atTop
      (𝓝 (∫ p, w p * φ p ∂μ)) := by
  let t : Lp ℝ 2 μ := hφ.toLp φ
  have he (v : Lp ℝ 2 μ) :
      innerSL ℝ t v = ∫ p, v p * φ p ∂μ := by
    rw [innerSL_apply_apply, L2.inner_def]
    apply integral_congr_ae
    filter_upwards [hφ.coeFn_toLp] with p hp
    simp only [RCLike.inner_apply, conj_trivial]
    exact congrArg (fun x : ℝ => v p * x) hp
  simpa only [Function.comp_def, he] using
    (innerSL ℝ t).continuous.continuousAt.tendsto.comp hW

end ContinuousFlexibility.Analysis

namespace ContinuousFlexibility.Statements

open Set Filter MeasureTheory ContinuousFlexibility.Analysis
open scoped Topology BigOperators

variable {D : ReferenceData} {T : MaterialData} {S : PhysicalSpacesData}
  {C : NonlinearGeometryData S} {L : ReturnCorrectionData S} {K : CanonicalData S}
  {base loss : ℕ} {ε : ℝ} {z : AnnularState S × ℝ}

/-- Piecewise L2 convergence passes the full physical height pairing,
including its actual left-cutoff contribution. -/
theorem n06_tendsto_physicalHeight_pairing
    (hS : IsPhysicalSpaces D T S)
    (h04 : N04Properties D T S C L K base loss ε)
    (hz : z ∈ stateNeighborhood S C base ε) (hs : stateSector S z.1)
    {W : ℕ → CanonicalL2Sequence S K} {w : CanonicalL2Sequence S K}
    {a : ℕ → ℝ} {aL : ℝ}
    (hW : ∀ m, Tendsto (fun n => W n m) atTop (𝓝 (w m)))
    (ha : Tendsto a atTop (𝓝 aL))
    {J : Set ℝ}
    (hfinite : (n06PhysicalSupportPieces K z J).Finite)
    {g : PolarPoint → ℝ}
    (h₀ : ∀ m, MemLp (canonicalSource S K z m g) 2 (canonicalMeasure S K m))
    (h₁ : ∀ m, MemLp (canonicalSource S K z m (fun q => g (q + (0, Real.pi))))
      2 (canonicalMeasure S K m))
    (hsupport : ∀ r, r ∉ J → ∀ θ, g (r, θ) = 0) :
    Tendsto (fun n => ∫ r in D.a..D.b, radialAngularMean (fun θ =>
      n06PhysicalHeight K z (fun m => (W n m : PolarPoint → ℝ)) (a n) (r, θ) *
        g (r, θ))) atTop
      (𝓝 (∫ r in D.a..D.b, radialAngularMean (fun θ =>
        n06PhysicalHeight K z (fun m => (w m : PolarPoint → ℝ)) aL (r, θ) *
          g (r, θ)))) := by
  classical
  have ht (m : ℕ) := n06_canonicalSource_average_memLp m (h₀ m) (h₁ m)
  have hp (m : ℕ) := n06_tendsto_integral_lp_pairing (ht m) (hW m)
  have hsum := tendsto_finsetSum hfinite.toFinset (fun m _ => hp m)
  have hlim := (hsum.const_mul Real.pi⁻¹).add
    (ha.mul_const (∫ r in D.a..D.b,
      radialAngularMean (fun θ => S.chiLeft r * g (r, θ))))
  have he (v : CanonicalL2Sequence S K) (c : ℝ) :=
    n06_physicalHeight_affine_pairing hS h04 hz hs v c hfinite h₀ h₁ hsupport
  simpa only [he] using hlim

/-- Piecewise L2 convergence also passes the actual reconstructed source
pairing. The two true height transforms of the test supply integrability. -/
theorem n06_tendsto_physicalSource_pairing
    (hab : D.a ≤ D.b)
    (h04 : N04Properties D T S C L K base loss ε)
    (hz : z ∈ stateNeighborhood S C base ε) (hs : stateSector S z.1)
    {F : ℕ → CanonicalSequence S K} {f : CanonicalSequence S K}
    (hF : ∀ m, Tendsto (fun n => F n m) atTop (𝓝 (f m)))
    {J : Set ℝ}
    (hfinite : (n06PhysicalSupportPieces K z J).Finite)
    {φ : PolarPoint → ℝ}
    (h₀ : ∀ m, MemLp (canonicalHeight S K z m φ) 2 (canonicalMeasure S K m))
    (h₁ : ∀ m, MemLp (canonicalHeight S K z m (fun q => φ (q + (0, Real.pi))))
      2 (canonicalMeasure S K m))
    (hsupport : ∀ r, r ∉ J → ∀ θ, φ (r, θ) = 0) :
    Tendsto (fun n => ∫ r in D.a..D.b, radialAngularMean (fun θ =>
      n06PhysicalSource K z (fun m => (F n m : PolarPoint → ℝ)) (r, θ) *
        φ (r, θ))) atTop
      (𝓝 (∫ r in D.a..D.b, radialAngularMean (fun θ =>
        n06PhysicalSource K z (fun m => (f m : PolarPoint → ℝ)) (r, θ) *
          φ (r, θ)))) := by
  classical
  have ht (m : ℕ) := n06_canonicalHeight_average_memLp m (h₀ m) (h₁ m)
  have hp (m : ℕ) := n06_tendsto_integral_lp_pairing (ht m) (hF m)
  have hlim := (tendsto_finsetSum hfinite.toFinset (fun m _ => hp m)).const_mul Real.pi⁻¹
  have he (v : CanonicalSequence S K) :=
    n06_fullCanonical_source_pairing hab h04 hz hs hfinite v
      (n06_physical_representation h04 hz hs (0 : CanonicalUnknown S K) v).1.2
      (n06PhysicalSource_periodic h04 hz hs _) h₀ h₁ hsupport
  simpa only [he] using hlim

end ContinuousFlexibility.Statements
