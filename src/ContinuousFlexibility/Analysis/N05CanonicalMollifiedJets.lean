import ContinuousFlexibility.Analysis.N05CanonicalMollifierL2Approximation
import ContinuousFlexibility.Analysis.N05CanonicalCutoffApproximation
import ContinuousFlexibility.Analysis.SpacesPhysicalReconstruction

/-!
# Mollification of actual weak jets on canonical cells

The periodic mollification of a cylinder L² class converges strongly
after restriction to a canonical cell. Any actual weak mixed derivative
is approximated by the corresponding ordinary derivative of the same
smooth function. This includes radial derivatives whenever they exist.
-/

noncomputable section

namespace ContinuousFlexibility.Statements

open Set Filter MeasureTheory ContinuousFlexibility.Analysis
open scoped ContDiff Topology Convolution

theorem n05CanonicalMeasure_le_cylinder (S : PhysicalSpacesData)
    (K : CanonicalData S) (m : ℕ) :
    canonicalMeasure S K m ≤ materialCylinderMeasure := by
  rw [← n05CanonicalMeasure_eq_cylinder_restrict S K m]
  exact Measure.restrict_le_self

theorem n05CanonicalZeroExtension_canonical_ae (S : PhysicalSpacesData)
    (K : CanonicalData S) (m : ℕ) (u : CanonicalL2 S K m) :
    (n05CanonicalZeroExtension S K m u : PolarPoint → ℝ) =ᵐ[canonicalMeasure S K m] u := by
  have hz := (n05CanonicalZeroExtension_ae S K m u).filter_mono
    (ae_mono (n05CanonicalMeasure_le_cylinder S K m))
  have ha : ∀ᵐ p ∂canonicalMeasure S K m,
      p ∈ Ioo (K.left m) (K.right m) ×ˢ Ioc (0 : ℝ) Real.pi :=
    ae_restrict_mem (measurableSet_Ioo.prod measurableSet_Ioc)
  filter_upwards [hz, ha] with p hp hm
  rw [hp, indicator_of_mem (show p ∈ n05CanonicalRadialWindow S K m from ⟨hm.1, mem_univ _⟩)]

def n05CanonicalCylinderMollification (u : CylinderL2)
    (φ : ContDiffBump (0 : PolarPoint)) : PolarPoint → ℝ :=
  planarConvolution (cylinderPeriodicExtension u) (φ.normed volume)

theorem n05CanonicalCylinderMollification_contDiff (u : CylinderL2)
    (φ : ContDiffBump (0 : PolarPoint)) :
    ContDiff ℝ ∞ (n05CanonicalCylinderMollification u φ) :=
  contDiff_planarConvolution (locallyIntegrable_cylinderPeriodicExtension u)
    φ.contDiff_normed φ.hasCompactSupport_normed

theorem n05CanonicalCylinderMollification_periodic (u : CylinderL2)
    (φ : ContDiffBump (0 : PolarPoint)) :
    Function.Periodic (n05CanonicalCylinderMollification u φ) (0, Real.pi) :=
  planarConvolution_periodic_left (cylinderPeriodicExtension_periodic u)

def n05CanonicalMollifiedJet (S : PhysicalSpacesData) (K : CanonicalData S)
    (m : ℕ) (u : CylinderL2) (φ : ContDiffBump (0 : PolarPoint)) (a b : ℕ) :
    CanonicalL2 S K m :=
  (n05Canonical_memLp_of_continuous S K m
    (contDiff_mixedDerivative (n05CanonicalCylinderMollification_contDiff u φ) a b).continuous).toLp
      (mixedDerivative a b (n05CanonicalCylinderMollification u φ))

theorem n05CanonicalMollifiedJet_ae (S : PhysicalSpacesData) (K : CanonicalData S)
    (m : ℕ) (u : CylinderL2) (φ : ContDiffBump (0 : PolarPoint)) (a b : ℕ) :
    (n05CanonicalMollifiedJet S K m u φ a b : PolarPoint → ℝ)
      =ᵐ[canonicalMeasure S K m] mixedDerivative a b (n05CanonicalCylinderMollification u φ) :=
  MemLp.coeFn_toLp _

theorem n05CanonicalMollifiedJet_zero_ae (S : PhysicalSpacesData) (K : CanonicalData S)
    (m : ℕ) (u : CylinderL2) (φ : ContDiffBump (0 : PolarPoint)) :
    (n05CanonicalMollifiedJet S K m u φ 0 0 : PolarPoint → ℝ)
      =ᵐ[canonicalMeasure S K m] n05CanonicalCylinderMollification u φ := by
  filter_upwards [n05CanonicalMollifiedJet_ae S K m u φ 0 0] with p hp
  simpa only [mixedDerivative, iteratedDeriv_zero, Prod.eta] using hp

theorem n05CanonicalMollifiedJet_of_weak (S : PhysicalSpacesData)
    (K : CanonicalData S) (m : ℕ) {u w : CylinderL2} {a b : ℕ}
    (h : HasWeakMixedDerivative u w a b) (φ : ContDiffBump (0 : PolarPoint)) :
    n05CanonicalMollifiedJet S K m u φ a b = n05CanonicalMollifiedJet S K m w φ 0 0 := by
  apply Lp.ext
  filter_upwards [n05CanonicalMollifiedJet_ae S K m u φ a b,
    n05CanonicalMollifiedJet_zero_ae S K m w φ] with p hp hq
  rw [hp, hq]
  exact congrFun (h.periodicConvolution φ.contDiff_normed φ.hasCompactSupport_normed) p

theorem n05CanonicalMollifiedJet_zero_tendsto (S : PhysicalSpacesData)
    (K : CanonicalData S) (m : ℕ) {ι : Type*} {l : Filter ι}
    {φ : ι → ContDiffBump (0 : PolarPoint)}
    (hφ : Tendsto (fun i => (φ i).rOut) l (𝓝 0))
    (u : CylinderL2) (v : CanonicalL2 S K m)
    (huv : (u : PolarPoint → ℝ) =ᵐ[canonicalMeasure S K m] v) :
    Tendsto (fun i => n05CanonicalMollifiedJet S K m u (φ i) 0 0) l (𝓝 v) := by
  let C : Set PolarPoint := Icc (K.left m) (K.right m) ×ˢ Icc (0 : ℝ) Real.pi
  have hC : IsCompact C := isCompact_Icc.prod isCompact_Icc
  have hext : cylinderPeriodicExtension u =ᵐ[canonicalMeasure S K m] v :=
    ((cylinderPeriodicExtension_ae u).filter_mono
      (ae_mono (n05CanonicalMeasure_le_cylinder S K m))).trans huv
  have ht : Tendsto (fun i => ∫ p in C,
      (n05CanonicalCylinderMollification u (φ i) p - cylinderPeriodicExtension u p) ^ 2)
      l (𝓝 0) := by
    simpa only [n05CanonicalCylinderMollification, spaces_planarConvolution_eq_left] using
      n05_cylinderPeriodicExtension_local_L2_mollification hφ u hC
  have he (i : ι) :
      ‖n05CanonicalMollifiedJet S K m u (φ i) 0 0 - v‖ ^ 2 =
        ∫ p, (n05CanonicalCylinderMollification u (φ i) p - cylinderPeriodicExtension u p) ^ 2
          ∂canonicalMeasure S K m := by
    rw [spacesLpReal_norm_sq]
    apply integral_congr_ae
    filter_upwards [Lp.coeFn_sub (n05CanonicalMollifiedJet S K m u (φ i) 0 0) v,
      n05CanonicalMollifiedJet_zero_ae S K m u (φ i), hext] with p hp hq hr
    rw [hp]
    simp only [Pi.sub_apply]
    rw [hq, hr]
  have hb (i : ι) :
      ‖n05CanonicalMollifiedJet S K m u (φ i) 0 0 - v‖ ^ 2 ≤
        ∫ p in C,
          (n05CanonicalCylinderMollification u (φ i) p - cylinderPeriodicExtension u p) ^ 2 := by
    have hm : MemLp (n05CanonicalCylinderMollification u (φ i)) 2 (volume.restrict C) :=
      (memLp_two_iff_integrable_sq
        (n05CanonicalCylinderMollification_contDiff u (φ i)).continuous.aestronglyMeasurable).mpr
          (((n05CanonicalCylinderMollification_contDiff u (φ i)).continuous.pow 2).continuousOn.integrableOn_compact hC)
    have hi := (hm.sub (memLp_cylinderPeriodicExtension_restrict_compact u hC)).integrable_sq
    rw [he i]
    change (∫ p in Ioo (K.left m) (K.right m) ×ˢ Ioc (0 : ℝ) Real.pi,
      (n05CanonicalCylinderMollification u (φ i) p - cylinderPeriodicExtension u p) ^ 2) ≤ _
    exact setIntegral_mono_set hi (Eventually.of_forall (fun _ => sq_nonneg _))
      (Eventually.of_forall (fun p hp => ⟨⟨hp.1.1.le, hp.1.2.le⟩, ⟨hp.2.1.le, hp.2.2⟩⟩))
  have hn₂ := squeeze_zero (fun i => sq_nonneg
    ‖n05CanonicalMollifiedJet S K m u (φ i) 0 0 - v‖) hb ht
  have hn : Tendsto (fun i => ‖n05CanonicalMollifiedJet S K m u (φ i) 0 0 - v‖)
      l (𝓝 (0 : ℝ)) := by
    have hsqrt := Real.continuous_sqrt.continuousAt.tendsto.comp hn₂
    simpa only [Function.comp_def, Real.sqrt_sq (norm_nonneg _), Real.sqrt_zero] using hsqrt
  exact (tendsto_iff_dist_tendsto_zero).mpr (by simpa only [dist_eq_norm] using hn)

theorem n05CanonicalMollifiedJet_weak_tendsto (S : PhysicalSpacesData)
    (K : CanonicalData S) (m : ℕ) {ι : Type*} {l : Filter ι}
    {φ : ι → ContDiffBump (0 : PolarPoint)}
    (hφ : Tendsto (fun i => (φ i).rOut) l (𝓝 0))
    {u w : CylinderL2} {a b : ℕ} (h : HasWeakMixedDerivative u w a b)
    (v : CanonicalL2 S K m) (hwv : (w : PolarPoint → ℝ) =ᵐ[canonicalMeasure S K m] v) :
    Tendsto (fun i => n05CanonicalMollifiedJet S K m u (φ i) a b) l (𝓝 v) := by
  simpa only [n05CanonicalMollifiedJet_of_weak S K m h] using
    n05CanonicalMollifiedJet_zero_tendsto S K m hφ w v hwv

theorem n05CanonicalMollifiedCutoffAngularJet_tendsto
    (S : PhysicalSpacesData) (K : CanonicalData S) (m n : ℕ)
    {f g : CanonicalL2 S K m} {j : ℕ}
    (h : WeakCanonicalAngularDerivative S K m f g j) :
    Tendsto (fun k => n05CanonicalMollifiedJet S K m
      (n05CanonicalZeroExtension S K m (n05CanonicalRadialCutoffOperator S K m n f))
      (spacesMollifierBump k) 0 j) atTop
      (𝓝 (n05CanonicalRadialCutoffOperator S K m n g)) := by
  have hw := n05WeakCanonicalAngularDerivative_cutoffExtension h
    (n05CanonicalRadialCutoffFunction (K.left m) (K.right m) n)
    (n05CanonicalRadialCutoffFunction_contDiff _ _ n)
    (n05CanonicalRadialCutoffFunction_hasCompactSupport _ _ n)
    (n05CanonicalRadialCutoffFunction_tsupport_subset _ _ n)
    1 (n05CanonicalRadialCutoffFunction_abs_le _ _ n)
  change HasWeakMixedDerivative
    (n05CanonicalZeroExtension S K m (n05CanonicalRadialCutoffOperator S K m n f))
    (n05CanonicalZeroExtension S K m (n05CanonicalRadialCutoffOperator S K m n g)) 0 j at hw
  exact n05CanonicalMollifiedJet_weak_tendsto S K m spacesMollifierBump_tendsto hw _
    (n05CanonicalZeroExtension_canonical_ae S K m _)

end ContinuousFlexibility.Statements
