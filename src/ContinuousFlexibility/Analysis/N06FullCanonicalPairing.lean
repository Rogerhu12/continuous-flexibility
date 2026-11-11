import ContinuousFlexibility.Analysis.N06FiniteCanonicalPairing
import ContinuousFlexibility.Analysis.N06FullPhysicalPairing

/-!
# Full physical means in the original finite canonical coordinates

The actual represented field is half-periodic, while the paired function
can be arbitrary. Both angular halves are retained through its average.
This includes the genuine current operator test without requiring any
periodicity of the corrected physical coefficients.
-/

noncomputable section

namespace ContinuousFlexibility.Statements

open Set MeasureTheory
open scoped BigOperators

set_option backward.isDefEq.respectTransparency false

variable {D : ReferenceData} {T : MaterialData} {S : PhysicalSpacesData}
  {C : NonlinearGeometryData S} {L : ReturnCorrectionData S} {K : CanonicalData S}
  {base loss : ℕ} {ε : ℝ} {z : AnnularState S × ℝ}

theorem n06_canonicalSource_average (m : ℕ) (φ : PolarPoint → ℝ) :
    canonicalSource S K z m (n06_radialTestAverage φ) =
      fun p => (canonicalSource S K z m φ p +
        canonicalSource S K z m (fun q => φ (q + (0, Real.pi))) p) / 2 := by
  funext p
  simp only [canonicalSource, n06_radialTestAverage, n06_halfPeriodAverage,
    Prod.add_def, add_zero, Prod.eta, div_eq_mul_inv]
  ring

theorem n06_canonicalHeight_average (m : ℕ) (φ : PolarPoint → ℝ) :
    canonicalHeight S K z m (n06_radialTestAverage φ) =
      fun p => (canonicalHeight S K z m φ p +
        canonicalHeight S K z m (fun q => φ (q + (0, Real.pi))) p) / 2 := by
  funext p
  simp only [canonicalHeight, n06_radialTestAverage, n06_halfPeriodAverage,
    Prod.add_def, add_zero, Prod.eta, div_eq_mul_inv]
  ring

theorem n06_canonicalSource_average_memLp (m : ℕ) {φ : PolarPoint → ℝ}
    (h₀ : MemLp (canonicalSource S K z m φ) 2 (canonicalMeasure S K m))
    (h₁ : MemLp (canonicalSource S K z m (fun q => φ (q + (0, Real.pi))))
      2 (canonicalMeasure S K m)) :
    MemLp (canonicalSource S K z m (n06_radialTestAverage φ))
      2 (canonicalMeasure S K m) := by
  rw [n06_canonicalSource_average]
  simpa only [div_eq_mul_inv, Pi.add_apply] using
    (h₀.add h₁).mul_const (2 : ℝ)⁻¹

theorem n06_canonicalHeight_average_memLp (m : ℕ) {φ : PolarPoint → ℝ}
    (h₀ : MemLp (canonicalHeight S K z m φ) 2 (canonicalMeasure S K m))
    (h₁ : MemLp (canonicalHeight S K z m (fun q => φ (q + (0, Real.pi))))
      2 (canonicalMeasure S K m)) :
    MemLp (canonicalHeight S K z m (n06_radialTestAverage φ))
      2 (canonicalMeasure S K m) := by
  rw [n06_canonicalHeight_average]
  simpa only [div_eq_mul_inv, Pi.add_apply] using
    (h₀.add h₁).mul_const (2 : ℝ)⁻¹

theorem n06_average_radial_support {J : Set ℝ} {φ : PolarPoint → ℝ}
    (hφ : ∀ r, r ∉ J → ∀ θ, φ (r, θ) = 0) :
    ∀ r, r ∉ J → ∀ θ, n06_radialTestAverage φ (r, θ) = 0 := by
  intro r hr θ
  simp only [n06_radialTestAverage, n06_halfPeriodAverage, hφ r hr, zero_add, zero_div]

theorem n06_fullCanonical_height_pairing
    (hab : D.a ≤ D.b) (h04 : N04Properties D T S C L K base loss ε)
    (hz : z ∈ stateNeighborhood S C base ε) (hs : stateSector S z.1)
    {J : Set ℝ}
    (hfinite : {m : ℕ |
      (Ioo (K.physicalLeft m) (K.physicalRight m) ∩ J).Nonempty}.Finite)
    (W : CanonicalSequence S K) {η φ : PolarPoint → ℝ}
    (hrep : ∀ m, (W m : PolarPoint → ℝ) =ᵐ[canonicalMeasure S K m]
      canonicalHeight S K z m η)
    (hperiod : Function.Periodic η (0, Real.pi))
    (h₀ : ∀ m, MemLp (canonicalSource S K z m φ) 2 (canonicalMeasure S K m))
    (h₁ : ∀ m, MemLp (canonicalSource S K z m (fun q => φ (q + (0, Real.pi))))
      2 (canonicalMeasure S K m))
    (hsupport : ∀ r, r ∉ J → ∀ θ, φ (r, θ) = 0) :
    (∫ r in D.a..D.b, radialAngularMean (fun θ => η (r, θ) * φ (r, θ))) =
      Real.pi⁻¹ * ∑ m ∈ hfinite.toFinset,
        ∫ p, W m p * canonicalSource S K z m (n06_radialTestAverage φ) p
          ∂canonicalMeasure S K m := by
  have hfirst := n06_finiteCanonical_height_pairing h04 hz hs hfinite W hrep h₀ hsupport
  have hshift := n06_finiteCanonical_height_pairing h04 hz hs hfinite W hrep h₁
    (fun r hr θ => by simpa only [Prod.mk_add_mk, add_zero] using hsupport r hr (θ + Real.pi))
  have havg := n06_finiteCanonical_height_pairing h04 hz hs hfinite W hrep
    (fun m => n06_canonicalSource_average_memLp m (h₀ m) (h₁ m))
    (n06_average_radial_support hsupport)
  exact (n06_fullPhysical_pairing_of_two_halves hab hperiod hfirst.1 hshift.1).2.trans
    (congrArg (fun a : ℝ => Real.pi⁻¹ * a) havg.2)

theorem n06_fullCanonical_source_pairing
    (hab : D.a ≤ D.b) (h04 : N04Properties D T S C L K base loss ε)
    (hz : z ∈ stateNeighborhood S C base ε) (hs : stateSector S z.1)
    {J : Set ℝ}
    (hfinite : {m : ℕ |
      (Ioo (K.physicalLeft m) (K.physicalRight m) ∩ J).Nonempty}.Finite)
    (F : CanonicalSequence S K) {f φ : PolarPoint → ℝ}
    (hrep : ∀ m, (F m : PolarPoint → ℝ) =ᵐ[canonicalMeasure S K m]
      canonicalSource S K z m f)
    (hperiod : Function.Periodic f (0, Real.pi))
    (h₀ : ∀ m, MemLp (canonicalHeight S K z m φ) 2 (canonicalMeasure S K m))
    (h₁ : ∀ m, MemLp (canonicalHeight S K z m (fun q => φ (q + (0, Real.pi))))
      2 (canonicalMeasure S K m))
    (hsupport : ∀ r, r ∉ J → ∀ θ, φ (r, θ) = 0) :
    (∫ r in D.a..D.b, radialAngularMean (fun θ => f (r, θ) * φ (r, θ))) =
      Real.pi⁻¹ * ∑ m ∈ hfinite.toFinset,
        ∫ p, F m p * canonicalHeight S K z m (n06_radialTestAverage φ) p
          ∂canonicalMeasure S K m := by
  have hfirst := n06_finiteCanonical_source_pairing h04 hz hs hfinite F hrep h₀ hsupport
  have hshift := n06_finiteCanonical_source_pairing h04 hz hs hfinite F hrep h₁
    (fun r hr θ => by simpa only [Prod.mk_add_mk, add_zero] using hsupport r hr (θ + Real.pi))
  have havg := n06_finiteCanonical_source_pairing h04 hz hs hfinite F hrep
    (fun m => n06_canonicalHeight_average_memLp m (h₀ m) (h₁ m))
    (n06_average_radial_support hsupport)
  exact (n06_fullPhysical_pairing_of_two_halves hab hperiod hfirst.1 hshift.1).2.trans
    (congrArg (fun a : ℝ => Real.pi⁻¹ * a) havg.2)

end ContinuousFlexibility.Statements
