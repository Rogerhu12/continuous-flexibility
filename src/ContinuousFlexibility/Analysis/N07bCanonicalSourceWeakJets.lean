import ContinuousFlexibility.Analysis.N05CanonicalTests
import ContinuousFlexibility.Analysis.CircleJetEncoding
import ContinuousFlexibility.Analysis.N07bCanonicalSourceSymmetry

/-!
# Actual angular jets in the canonical weak graph

On each interior radial slice, periodic integration by parts identifies
the classical angular jet with the frozen weak angular derivative. The
two actual L² assumptions make both test products integrable, so Fubini
transfers this identity to the canonical measure. Smoothness is required
only on the canonical open piece; the totalized inverse is unrestricted
outside that piece.
-/

noncomputable section

namespace ContinuousFlexibility.Analysis

open Set Filter MeasureTheory ContinuousFlexibility.Statements
open scoped ContDiff Topology

set_option backward.isDefEq.respectTransparency false

variable {S : PhysicalSpacesData} {K : CanonicalData S} {m : ℕ}

theorem n07b_contDiff_canonical_angular_slice {f : PolarPoint → ℝ}
    (hf : ContDiffOn ℝ ∞ f (canonicalOpen S K m)) {r : ℝ}
    (hr : r ∈ Ioo (K.left m) (K.right m)) :
    ContDiff ℝ ∞ (fun θ : ℝ => f (r, θ)) := by
  apply contDiff_iff_contDiffAt.mpr
  intro θ
  have hfr : ContDiffAt ℝ ∞ f (r, θ) :=
    hf.contDiffAt ((isOpen_Ioo.prod isOpen_univ).mem_nhds ⟨hr, mem_univ θ⟩)
  exact hfr.comp θ (contDiffAt_const.prodMk contDiffAt_id)

/-- The actual integral identity needed by the canonical source lift.
Only the zeroth and the indicated angular jet need to be in L². -/
theorem n07b_integral_canonicalAngularJet_mul {f φ : PolarPoint → ℝ}
    (hf : ContDiffOn ℝ ∞ f (canonicalOpen S K m))
    (hp : ∀ r ∈ Ioo (K.left m) (K.right m),
      Function.Periodic (fun θ => f (r, θ)) Real.pi) (j : ℕ)
    (h₀ : MemLp f 2 (canonicalMeasure S K m))
    (hj : MemLp (mixedDerivative 0 j f) 2 (canonicalMeasure S K m))
    (hφ : CanonicalTest S K m φ) :
    (∫ p, mixedDerivative 0 j f p * φ p ∂canonicalMeasure S K m) =
      (-1 : ℝ) ^ j * ∫ p, f p * mixedDerivative 0 j φ p ∂canonicalMeasure S K m := by
  let : SFinite angleMeasure := by unfold angleMeasure; infer_instance
  have hi : Integrable (fun p => mixedDerivative 0 j f p * φ p)
      (canonicalMeasure S K m) := hj.integrable_mul (n05CanonicalTest_memLp hφ)
  have hi' : Integrable (fun p => f p * mixedDerivative 0 j φ p)
      (canonicalMeasure S K m) :=
    h₀.integrable_mul (n05CanonicalTest_angular_memLp hφ j)
  rw [n05CanonicalMeasure_eq_prod] at hi hi' ⊢
  rw [integral_prod _ hi, integral_prod _ hi', ← integral_const_mul]
  apply integral_congr_ae
  filter_upwards [ae_restrict_mem measurableSet_Ioo] with r hr
  have hφr : ContDiff ℝ ∞ (fun θ : ℝ => φ (r, θ)) :=
    hφ.1.comp (contDiff_const.prodMk contDiff_id)
  have hφp : Function.Periodic (fun θ : ℝ => φ (r, θ)) Real.pi := by
    intro θ
    simpa only [Prod.mk_add_mk, add_zero] using hφ.2.1 (r, θ)
  simpa only [mixedDerivative, iteratedDeriv_zero] using
    integral_angle_iteratedDeriv_mul (n07b_contDiff_canonical_angular_slice hf hr)
      (hp r hr) j hφr hφp

/-- Passing to the genuine L² classes preserves the actual test identity. -/
theorem n07b_weakCanonicalAngularDerivative_of_smooth {f : PolarPoint → ℝ}
    (hf : ContDiffOn ℝ ∞ f (canonicalOpen S K m))
    (hp : ∀ r ∈ Ioo (K.left m) (K.right m),
      Function.Periodic (fun θ => f (r, θ)) Real.pi) (j : ℕ)
    (h₀ : MemLp f 2 (canonicalMeasure S K m))
    (hj : MemLp (mixedDerivative 0 j f) 2 (canonicalMeasure S K m)) :
    WeakCanonicalAngularDerivative S K m
      (h₀.toLp f) (hj.toLp (mixedDerivative 0 j f)) j := by
  intro φ hφ
  have hleft :
      (∫ p, hj.toLp (mixedDerivative 0 j f) p * φ p ∂canonicalMeasure S K m) =
        ∫ p, mixedDerivative 0 j f p * φ p ∂canonicalMeasure S K m := by
    apply integral_congr_ae
    filter_upwards [MemLp.coeFn_toLp hj] with p hp
    rw [hp]
  have hright :
      (∫ p, h₀.toLp f p * mixedDerivative 0 j φ p ∂canonicalMeasure S K m) =
        ∫ p, f p * mixedDerivative 0 j φ p ∂canonicalMeasure S K m := by
    apply integral_congr_ae
    filter_upwards [MemLp.coeFn_toLp h₀] with p hp
    rw [hp]
  rw [hleft, hright]
  exact n07b_integral_canonicalAngularJet_mul hf hp j h₀ hj hφ

variable {D : ReferenceData} {C : NonlinearGeometryData S}
  {base : ℕ} {ε : ℝ} {z : AnnularState S × ℝ}

/-- For the actual canonical source, PartA supplies the angular period.
The remaining inputs are exactly its interior smoothness and actual jet
integrability, with no condition on an extension of the inverse chart. -/
theorem n07b_canonicalSource_weakAngular_integral
    (hK : Blueprint.N04PartA D S C K base ε)
    (hz : z ∈ stateNeighborhood S C base ε) (hs : stateSector S z.1)
    (f : PolarPoint → ℝ) (hp : Function.Periodic f (0, Real.pi)) (m j : ℕ)
    (hf : ContDiffOn ℝ ∞ (canonicalSource S K z m f) (canonicalOpen S K m))
    (h₀ : MemLp (canonicalSource S K z m f) 2 (canonicalMeasure S K m))
    (hj : MemLp (mixedDerivative 0 j (canonicalSource S K z m f)) 2
      (canonicalMeasure S K m)) {φ : PolarPoint → ℝ} (hφ : CanonicalTest S K m φ) :
    (∫ p, mixedDerivative 0 j (canonicalSource S K z m f) p * φ p
      ∂canonicalMeasure S K m) =
      (-1 : ℝ) ^ j * ∫ p, canonicalSource S K z m f p * mixedDerivative 0 j φ p
        ∂canonicalMeasure S K m :=
  n07b_integral_canonicalAngularJet_mul hf
    (fun _ hr => n07b_canonicalSource_periodic hK hz hs f hp m hr) j h₀ hj hφ

theorem n07b_canonicalSource_weakCanonicalAngularDerivative
    (hK : Blueprint.N04PartA D S C K base ε)
    (hz : z ∈ stateNeighborhood S C base ε) (hs : stateSector S z.1)
    (f : PolarPoint → ℝ) (hp : Function.Periodic f (0, Real.pi)) (m j : ℕ)
    (hf : ContDiffOn ℝ ∞ (canonicalSource S K z m f) (canonicalOpen S K m))
    (h₀ : MemLp (canonicalSource S K z m f) 2 (canonicalMeasure S K m))
    (hj : MemLp (mixedDerivative 0 j (canonicalSource S K z m f)) 2
      (canonicalMeasure S K m)) :
    WeakCanonicalAngularDerivative S K m
      (h₀.toLp (canonicalSource S K z m f))
      (hj.toLp (mixedDerivative 0 j (canonicalSource S K z m f))) j :=
  n07b_weakCanonicalAngularDerivative_of_smooth hf
    (fun _ hr => n07b_canonicalSource_periodic hK hz hs f hp m hr) j h₀ hj

end ContinuousFlexibility.Analysis
