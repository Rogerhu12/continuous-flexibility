module

public import ContinuousFlexibility.Analysis.N06CanonicalFourierCutoff
public import ContinuousFlexibility.Analysis.N06EvenFourierCutoff
public import ContinuousFlexibility.Analysis.N06WeakCylinderPDE

/-!
# The original canonical weak jet row is the limit of its cosine cutoffs

The frozen zeroth-order reflection condition is enough to identify the
Fourier cutoff with finite synthesis in the reference cosine basis. The
coefficients are exactly the half-period coefficients used by the genuine
weak cylinder equation, and every stored angular jet converges in its
original canonical L2 norm.
-/

@[expose] public section

noncomputable section

namespace ContinuousFlexibility.Analysis

open Set Filter MeasureTheory
open scoped BigOperators ContDiff Topology
open ContinuousFlexibility.Radial ContinuousFlexibility.Statements

set_option backward.isDefEq.respectTransparency false

/-- The finite synthesis uses the same actual coefficients as the weak PDE. -/
def n06CylinderCosineCut (N : ℕ) (U : PolarPoint → ℝ) : PolarPoint → ℝ :=
  r11bFiniteSynthesis (Finset.range (N + 1))
    (n06HalfCosineCoefficient U) referenceAngularBasis

theorem n06CylinderCosineCut_angularJet (N : ℕ) (U : PolarPoint → ℝ) (j : ℕ) :
    mixedDerivative 0 j (n06CylinderCosineCut N U) =
      r11bFiniteSynthesis (Finset.range (N + 1))
        (n06HalfCosineCoefficient U) (fun i => iteratedDeriv j (referenceAngularBasis i)) :=
  n06_mixedAngularDerivative_finiteSynthesis _ _ _
    (fun i _ => contDiff_referenceAngularBasis i) j

/-- The equality holds for actual derivatives of the same finite polynomials,
not just for the zeroth L2 classes. -/
theorem n06CylinderFourierCut_angularJet_eq_cosine_ae
    {μ : Measure ℝ} [SFinite μ] {U : PolarPoint → ℝ}
    (hU : MemLp U 2 (μ.prod angleMeasure))
    (he : (fun p : PolarPoint => U (p.1, Real.pi - p.2)) =ᵐ[μ.prod angleMeasure] U)
    (N j : ℕ) :
    mixedDerivative 0 j (n06CylinderFourierCut (n06FourierCutoff N) U)
      =ᵐ[μ.prod angleMeasure] mixedDerivative 0 j (n06CylinderCosineCut N U) := by
  have hsections : ∀ᵐ r ∂μ, ∀ θ : ℝ,
      mixedDerivative 0 j (n06CylinderFourierCut (n06FourierCutoff N) U) (r, θ) =
        mixedDerivative 0 j (n06CylinderCosineCut N U) (r, θ) := by
    filter_upwards [r11b_memLp_product_sections hU, Measure.ae_ae_of_ae_prod he]
      with r hr her
    intro θ
    rw [n06CylinderCosineCut_angularJet]
    change iteratedDeriv j (n06CircleFourierCut (n06FourierCutoff N)
        (fun η => U (r, η))) θ =
      ∑ i ∈ Finset.range (N + 1),
        (Real.pi⁻¹ * ∫ η, U (r, η) * referenceAngularBasis i η ∂angleMeasure) *
          iteratedDeriv j (referenceAngularBasis i) θ
    exact n06CircleFourierCut_jet_eq_halfCosineSum hr her N j θ
  filter_upwards [(Measure.quasiMeasurePreserving_fst
    (μ := μ) (ν := angleMeasure)).ae hsections] with p hp
  exact hp p.2

theorem n06_canonicalFourierCut_angularJet_eq_cosine_ae
    {S : PhysicalSpacesData} {K : CanonicalData S} {m : ℕ}
    (U : CanonicalL2 S K m)
    (he : (fun p : PolarPoint => U (p.1, Real.pi - p.2))
      =ᵐ[canonicalMeasure S K m] (U : PolarPoint → ℝ)) (N j : ℕ) :
    mixedDerivative 0 j (n06CylinderFourierCut (n06FourierCutoff N) U)
      =ᵐ[canonicalMeasure S K m] mixedDerivative 0 j (n06CylinderCosineCut N U) := by
  have heprod : (fun p : PolarPoint => U (p.1, Real.pi - p.2))
      =ᵐ[(volume.restrict (Ioo (K.left m) (K.right m))).prod angleMeasure]
        (U : PolarPoint → ℝ) :=
    (congrArg (fun μ : Measure PolarPoint =>
      (fun p : PolarPoint => U (p.1, Real.pi - p.2)) =ᵐ[μ] (U : PolarPoint → ℝ))
        (n06_canonicalMeasure_eq_radial_prod (S := S) (K := K) m)).mp he
  have hp := n06CylinderFourierCut_angularJet_eq_cosine_ae
    (n06_canonicalL2_memLp_prod U) heprod N j
  exact (congrArg (fun μ : Measure PolarPoint =>
    mixedDerivative 0 j (n06CylinderFourierCut (n06FourierCutoff N) U)
      =ᵐ[μ] mixedDerivative 0 j (n06CylinderCosineCut N U))
        (n06_canonicalMeasure_eq_radial_prod (S := S) (K := K) m)).mpr hp

theorem n06_canonicalCosineCut_angularJet_memLp
    {S : PhysicalSpacesData} {K : CanonicalData S} {m : ℕ}
    (U : CanonicalL2 S K m)
    (he : (fun p : PolarPoint => U (p.1, Real.pi - p.2))
      =ᵐ[canonicalMeasure S K m] (U : PolarPoint → ℝ)) (N j : ℕ) :
    MemLp (mixedDerivative 0 j (n06CylinderCosineCut N U)) 2
      (canonicalMeasure S K m) :=
  (memLp_congr_ae (n06_canonicalFourierCut_angularJet_eq_cosine_ae U he N j)).mp
    (n06_canonicalFourierCut_angularJet_memLp U (n06FourierCutoff N) j)

/-- The entire original row is strongly approximated by the actual derivatives
of one finite cosine synthesis, using exactly the PDE's radial coefficients. -/
theorem n06_canonicalCosineCut_jetRow_tendsto
    {S : PhysicalSpacesData} {K : CanonicalData S} {m b : ℕ}
    (v : Fin (b + 1) → CanonicalL2 S K m)
    (he : (fun p : PolarPoint => v 0 (p.1, Real.pi - p.2))
      =ᵐ[canonicalMeasure S K m] (v 0 : PolarPoint → ℝ))
    (hv : ∀ k, WeakCanonicalAngularDerivative S K m (v 0) (v k) k.val) :
    ∃ hJ : ∀ N : ℕ, ∀ k : Fin (b + 1), MemLp
        (mixedDerivative 0 k.val (n06CylinderCosineCut N (v 0))) 2
          (canonicalMeasure S K m),
      Tendsto (fun N => ∑ k : Fin (b + 1),
        ‖(hJ N k).toLp (mixedDerivative 0 k.val (n06CylinderCosineCut N (v 0))) - v k‖ ^ 2)
        atTop (𝓝 0) := by
  obtain ⟨hF, hlim⟩ := n06_canonicalFourierCut_jetRow_tendsto v hv
  let hJ (N : ℕ) (k : Fin (b + 1)) :=
    n06_canonicalCosineCut_angularJet_memLp (v 0) he N k.val
  have heq (N : ℕ) (k : Fin (b + 1)) :
      (hJ N k).toLp (mixedDerivative 0 k.val (n06CylinderCosineCut N (v 0))) =
        (hF N k).toLp
          (mixedDerivative 0 k.val (n06CylinderFourierCut (n06FourierCutoff N) (v 0))) :=
    (hJ N k).toLp_congr (hF N k)
      (n06_canonicalFourierCut_angularJet_eq_cosine_ae (v 0) he N k.val).symm
  refine ⟨hJ, ?_⟩
  have hfun : (fun N => ∑ k : Fin (b + 1),
      ‖(hJ N k).toLp (mixedDerivative 0 k.val (n06CylinderCosineCut N (v 0))) - v k‖ ^ 2) =
      fun N => ∑ k : Fin (b + 1),
        ‖(hF N k).toLp
          (mixedDerivative 0 k.val (n06CylinderFourierCut (n06FourierCutoff N) (v 0))) - v k‖ ^ 2 := by
    funext N
    apply Finset.sum_congr rfl
    intro k _
    rw [heq N k]
  rw [hfun]
  exact hlim

end ContinuousFlexibility.Analysis
