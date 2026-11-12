import ContinuousFlexibility.Radial.SelectedOuterWeakSolution
import Mathlib.MeasureTheory.Measure.OpenPos
import Mathlib.Analysis.Calculus.TangentCone.Real

/-!
# Recovery of ordinary-support Jacobi tests

A continuous weak flux with continuous forcing has its classical
derivative in the open interval. Subtracting the smooth test then gives
the actual homogeneous value/flux system. Its natural Robin uniqueness
recovers the test, including the regular cut.
-/

noncomputable section

namespace ContinuousFlexibility.Radial

open Set Filter MeasureTheory
open scoped Topology ContDiff
open ContinuousFlexibility.Analysis

theorem outerWeakDerivative_congr_source {a b : ℝ} {p f g : ℝ → ℝ}
    (h : HasIntervalWeakDerivative a b p f)
    (he : f =ᵐ[volume.restrict (Ioo a b)] g) :
    HasIntervalWeakDerivative a b p g := by
  intro ψ hψ hc hs
  rw [h ψ hψ hc hs]
  congr 1
  apply integral_congr_ae
  filter_upwards [ae_imp_of_ae_restrict he] with x hx
  by_cases hxi : x ∈ Ioo a b
  · rw [hx hxi]
  · have hz : ψ x = 0 := image_eq_zero_of_notMem_tsupport (fun h => hxi (hs h))
    simp only [hz, mul_zero]

private theorem selected_flux_classical_of_weak {a b : ℝ} (hab : a < b)
    {p g : ℝ → ℝ} (hp : ContinuousOn p (Ioo a b)) (hg : ContinuousOn g (Ioo a b))
    (hweak : HasIntervalWeakDerivative a b p g) :
    ∀ x ∈ Ioo a b, HasDerivAt p (g x) x := by
  obtain ⟨x₀, hx₀⟩ := nonempty_Ioo.mpr hab
  obtain ⟨c, P, _, he, hd⟩ := exists_interval_classical_rep
    (hp.locallyIntegrableOn measurableSet_Ioo) hg hx₀ hweak
  have hP : ContinuousOn P (Ioo a b) :=
    fun x hx => (hd x hx).continuousAt.continuousWithinAt
  have hsame := Measure.eqOn_open_of_ae_eq he isOpen_Ioo hp hP
  intro x hx
  apply (hd x hx).congr_of_eventuallyEq
  exact Filter.eventually_of_mem (isOpen_Ioo.mem_nhds hx) (fun y hy => hsame hy)

private theorem selected_test_left_jet_zero {a b : ℝ} {ψ : ℝ → ℝ}
    (hψ : ContDiff ℝ ∞ ψ) (hs : Function.support ψ ⊆ Ioo a b) :
    ψ a = 0 ∧ deriv ψ a = 0 := by
  have hz : ∀ x ∈ Iic a, ψ x = 0 := by
    intro x hx
    exact Function.notMem_support.mp (fun h => not_lt_of_ge hx (hs h).1)
  have hd : HasDerivWithinAt ψ 0 (Iic a) a :=
    (hasDerivAt_const a (0 : ℝ)).hasDerivWithinAt.congr_of_mem
      (fun x hx => hz x hx) (by simp)
  refine ⟨hz a (by simp), ?_⟩
  calc
    deriv ψ a = derivWithin ψ (Iic a) a :=
      ((hψ.differentiable (by simp) a).hasDerivAt.hasDerivWithinAt.derivWithin
        (uniqueDiffWithinAt_Iic a)).symm
    _ = 0 := hd.derivWithin (uniqueDiffWithinAt_Iic a)

theorem outerWeakSolution_recovers_test
    {μ : Measure ℝ} {a b J lam : ℝ} {w u p ψ : ℝ → ℝ} {v : ℝ × ℝ}
    (hab : a < b) (hlam : lam ≠ 0) (hw : ContDiff ℝ ∞ w)
    (hwn : ∀ x ∈ Ico a b, w x ≠ 0) (hr : ∀ x ∈ Ico a b, x ≠ 0)
    (hu : ContDiffOn ℝ 1 u (Ico a b)) (hp : ContinuousOn p (Ico a b))
    (hflux : ∀ x ∈ Ioo a b, p x = w x * deriv u x)
    (hweak : HasIntervalWeakDerivative a b p
      (fun x => J * deriv w x / x * u x + radialJacobi J w ψ x))
    (hRobin : outerStatePair v (u a, p a / lam) = 0)
    (hψ : ContDiff ℝ ∞ ψ) (hs : Function.support ψ ⊆ Ioo a b)
    (huLp : MemLp u 2 μ) (hψLp : MemLp ψ 2 μ)
    (hunique : ∀ y z : ℝ → ℝ,
      ContinuousOn y (Ico a b) → ContinuousOn z (Ico a b) →
      OuterFirstOrderSystem (fun x => lam / w x)
        (fun x => J * deriv w x / (lam * x)) y z (Ioo a b) →
      MemLp y 2 μ → outerStatePair v (y a, z a) = 0 →
      ∀ x ∈ Ico a b, y x = 0 ∧ z x = 0) :
    EqOn u ψ (Ico a b) := by
  have hdw : ContDiff ℝ ∞ (deriv w) := (contDiff_infty_iff_deriv.mp hw).2
  have hdψ : ContDiff ℝ ∞ (deriv ψ) := (contDiff_infty_iff_deriv.mp hψ).2
  have hfψ : ContDiff ℝ ∞ (fun x => w x * deriv ψ x) := hw.mul hdψ
  have hdfψ : ContDiff ℝ ∞ (deriv (fun x => w x * deriv ψ x)) :=
    (contDiff_infty_iff_deriv.mp hfψ).2
  have hpotential : ContinuousOn (fun x => J * deriv w x / x) (Ioo a b) :=
    (continuousOn_const.mul hdw.continuous.continuousOn).div continuousOn_id
      (fun x hx => hr x (Ioo_subset_Ico_self hx))
  have hJac : ContinuousOn (fun x => radialJacobi J w ψ x) (Ioo a b) :=
    hdfψ.continuous.continuousOn.sub (hpotential.mul hψ.continuous.continuousOn)
  have hpder := selected_flux_classical_of_weak hab
    (hp.mono Ioo_subset_Ico_self)
    ((hpotential.mul (hu.continuousOn.mono Ioo_subset_Ico_self)).add hJac) hweak
  let y : ℝ → ℝ := fun x => u x - ψ x
  let z : ℝ → ℝ := fun x => (p x - w x * deriv ψ x) / lam
  have hyc : ContinuousOn y (Ico a b) := hu.continuousOn.sub hψ.continuous.continuousOn
  have hzc : ContinuousOn z (Ico a b) :=
    (hp.sub hfψ.continuous.continuousOn).div_const lam
  have hsys : OuterFirstOrderSystem (fun x => lam / w x)
      (fun x => J * deriv w x / (lam * x)) y z (Ioo a b) := by
    intro x hx
    have hx' := Ioo_subset_Ico_self hx
    have hdu := ((hu.mono Ioo_subset_Ico_self).contDiffAt
      (isOpen_Ioo.mem_nhds hx)).differentiableAt (by norm_num)
    constructor
    · apply (hdu.hasDerivAt.sub (hψ.differentiable (by simp) x).hasDerivAt).congr_deriv
      dsimp only [z]
      rw [hflux x hx]
      field_simp [hlam, hwn x hx'] <;> ring
    · apply (((hpder x hx).sub (hfψ.differentiable (by simp) x).hasDerivAt).div_const lam).congr_deriv
      dsimp only [y, radialJacobi, Pi.add_apply, Pi.mul_apply]
      field_simp [hlam, hr x hx'] <;> ring
  obtain ⟨hψa, hdψa⟩ := selected_test_left_jet_zero hψ hs
  have hzRobin : outerStatePair v (y a, z a) = 0 := by
    simpa only [y, z, hψa, hdψa, mul_zero, sub_zero] using hRobin
  have hzero := hunique y z hyc hzc hsys (huLp.sub hψLp) hzRobin
  intro x hx
  exact sub_eq_zero.mp (hzero x hx).1

end ContinuousFlexibility.Radial
