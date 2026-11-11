import ContinuousFlexibility.Analysis.N01aJacobiTransfer
import ContinuousFlexibility.Analysis.N01aReferenceMeasure
import Mathlib.Analysis.Calculus.Deriv.Inverse
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Complex
import Mathlib.Topology.Compactness.Lindelof

/-!
# The reference second-mode multiplier is nonzero almost everywhere

The actual Jacobi energy transfer excludes zero Cauchy data for the
nontrivial reference kernel. Its interior zeros are therefore simple and
countable. The angular second-mode zeros are countable as well.
-/

noncomputable section

namespace ContinuousFlexibility.Statements

open Set Filter MeasureTheory
open scoped ContDiff Topology

theorem n01a_reference_phi_energy_pos {D : ReferenceData}
    (hD : RadialProfileGeometry D) (hN : RadialNaturalKernels D)
    {r : ℝ} (hr : r ∈ radialCore D) : 0 < n01aJacobiEnergy D.phi r := by
  obtain ⟨r₀, hr₀, hphi⟩ := hD.2.2.2.2.2.1
  have hleft : D.a < min r r₀ := lt_min hr.1 hr₀.1
  have hright : max r r₀ < D.b := max_lt hr.2 hr₀.2
  have hcore : Icc (min r r₀) (max r r₀) ⊆ radialCore D :=
    fun _ hx => ⟨hleft.trans_le hx.1, hx.2.trans_lt hright⟩
  have htransfer := n01aJacobiEnergy_transfer hD.1 hleft.le (min_le_max r r₀)
    hD.2.2.1.1 hD.2.2.2.1.1
    (fun x hx => hD.2.2.2.2.1 x (hcore hx)) (fun x hx => hN.1 x (hcore hx))
    (s := r) (t := r₀) ⟨min_le_left _ _, le_max_left _ _⟩
    ⟨min_le_right _ _, le_max_right _ _⟩
  by_contra hn
  have hz : n01aJacobiEnergy D.phi r = 0 :=
    le_antisymm (le_of_not_gt hn) (n01aJacobiEnergy_nonneg D.phi r)
  rw [hz, zero_mul] at htransfer
  exact (not_le_of_gt (n01aJacobiEnergy_pos hphi)) htransfer

theorem n01a_reference_phi_simple_zero {D : ReferenceData}
    (hD : RadialProfileGeometry D) (hN : RadialNaturalKernels D)
    {r : ℝ} (hr : r ∈ radialCore D) (hz : D.phi r = 0) : deriv D.phi r ≠ 0 := by
  intro hd
  have hp := n01a_reference_phi_energy_pos hD hN hr
  norm_num [n01aJacobiEnergy, hz, hd] at hp

theorem n01a_reference_phi_zero_isolated {D : ReferenceData}
    (hD : RadialProfileGeometry D) (hN : RadialNaturalKernels D)
    {r : ℝ} (hr : r ∈ radialCore D) (hz : D.phi r = 0) :
    ∀ᶠ x in 𝓝 r, D.phi x = 0 → x = r := by
  have hphi : ContDiff ℝ ∞ D.phi := hD.2.2.2.1.1
  have he : ∀ᶠ x in 𝓝[≠] r, D.phi x ≠ 0 :=
    (hphi.differentiable (by simp) r).hasDerivAt.eventually_ne
      (n01a_reference_phi_simple_zero hD hN hr hz)
  filter_upwards [eventually_nhdsWithin_iff.mp he] with x hx hzero
  by_contra hne
  exact hx (by simpa only [mem_compl_iff, mem_singleton_iff] using hne) hzero

theorem n01a_reference_phi_zeros_countable {D : ReferenceData}
    (hD : RadialProfileGeometry D) (hN : RadialNaturalKernels D) :
    {r ∈ radialCore D | D.phi r = 0}.Countable := by
  have hd : IsDiscrete {r ∈ radialCore D | D.phi r = 0} := by
    apply isDiscrete_iff_forall_mem_exists_isOpen.mpr
    intro r hr
    obtain ⟨δ, hδ, hb⟩ := Metric.mem_nhds_iff.mp
      (n01a_reference_phi_zero_isolated hD hN hr.1 hr.2)
    refine ⟨Metric.ball r δ, Metric.isOpen_ball, ?_⟩
    ext x
    constructor
    · rintro ⟨hx, hroot⟩
      exact Set.mem_singleton_iff.mpr (hb hx hroot.2)
    · intro hx
      rcases Set.mem_singleton_iff.mp hx with rfl
      exact ⟨Metric.mem_ball_self hδ, hr⟩
  exact (HereditarilyLindelofSpace.isLindelof _).countable_of_isDiscrete hd

theorem n01a_reference_phi_ne_zero_ae {D : ReferenceData}
    (hD : RadialProfileGeometry D) (hN : RadialNaturalKernels D) :
    ∀ᵐ r ∂volume.restrict (radialCore D), D.phi r ≠ 0 := by
  apply (ae_restrict_iff' (show MeasurableSet (radialCore D) from measurableSet_Ioo)).mpr
  filter_upwards [(n01a_reference_phi_zeros_countable hD hN).ae_notMem volume] with r hr hcore
  exact fun hz => hr ⟨hcore, hz⟩

theorem n01a_cosineMode_two_zeros_countable : {θ : ℝ | Radial.cosineMode 2 θ = 0}.Countable := by
  apply (Set.countable_range (fun k : ℤ => ((2 * (k : ℝ) + 1) * Real.pi) / 4)).mono
  intro θ hθ
  have hz : Radial.cosineMode 2 θ = 0 := hθ
  have hsqrt : Real.sqrt 2 ≠ 0 := (Real.sqrt_pos.mpr (by norm_num : (0 : ℝ) < 2)).ne'
  have hc : Real.cos (2 * θ) = 0 := by
    simpa only [Radial.cosineMode, Nat.cast_ofNat, mul_eq_zero, hsqrt, false_or] using hz
  obtain ⟨k, hk⟩ := Real.cos_eq_zero_iff.mp hc
  refine ⟨k, ?_⟩
  linarith

theorem n01a_cosineMode_two_ne_zero_ae : ∀ᵐ θ : ℝ, Radial.cosineMode 2 θ ≠ 0 := by
  simpa only [Set.mem_ofPred_eq] using n01a_cosineMode_two_zeros_countable.ae_notMem volume

theorem n01a_reference_phi_cosineMode_two_continuous {D : ReferenceData}
    (hD : RadialProfileGeometry D) :
    Continuous (fun p : PolarPoint => D.phi p.1 * Radial.cosineMode 2 p.2) := by
  have hphi : Continuous D.phi := hD.2.2.2.1.1.continuous
  unfold Radial.cosineMode
  fun_prop

theorem n01a_reference_phi_cosineMode_two_ne_zero_ae {D : ReferenceData}
    (hD : RadialProfileGeometry D) (hN : RadialNaturalKernels D) :
    ∀ᵐ p ∂radialPhysicalMeasure D, D.phi p.1 * Radial.cosineMode 2 p.2 ≠ 0 := by
  have hm : MeasurableSet {p : PolarPoint | D.phi p.1 * Radial.cosineMode 2 p.2 ≠ 0} :=
    (isClosed_eq (n01a_reference_phi_cosineMode_two_continuous hD)
      continuous_const).measurableSet.compl
  rw [radialPhysicalMeasure_eq_prod]
  apply (Measure.ae_prod_iff_ae_ae hm).mpr
  filter_upwards [n01a_reference_phi_ne_zero_ae hD hN] with r hr
  filter_upwards [ae_restrict_of_ae (s := Ioc (0 : ℝ) (2 * Real.pi))
    n01a_cosineMode_two_ne_zero_ae] with θ hθ
  exact mul_ne_zero hr hθ

end ContinuousFlexibility.Statements
