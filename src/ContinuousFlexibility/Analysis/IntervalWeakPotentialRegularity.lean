import ContinuousFlexibility.Analysis.IntervalWeakRegularity
import ContinuousFlexibility.Analysis.IntervalWeakPotential

/-!
# C¹ representatives for weak equations with a continuous potential

All weak equations use actual scalar integrals. The representative is chosen
only after applying one-dimensional weak regularity; its primitive flux is
then rewritten with the new representative by ordinary a.e. congruence.
-/

noncomputable section

namespace ContinuousFlexibility.Analysis

open Set Filter MeasureTheory
open scoped ContDiff Topology

set_option backward.isDefEq.respectTransparency false

theorem intervalLocalPrimitive_congr_ae_Ioo {a b x₀ x : ℝ}
    {f g : ℝ → ℝ} (hfg : f =ᵐ[volume.restrict (Ioo a b)] g)
    (hx₀ : x₀ ∈ Ioo a b) (hx : x ∈ Ioo a b) :
    intervalLocalPrimitive f x₀ x = intervalLocalPrimitive g x₀ x := by
  have hfull : ∀ᵐ t ∂(volume : Measure ℝ), t ∈ Ioo a b → f t = g t :=
    (ae_restrict_iff' measurableSet_Ioo).mp hfg
  apply intervalIntegral.integral_congr_ae
  filter_upwards [hfull] with t ht
  intro hti
  apply ht
  rcases le_total x₀ x with h | h
  · rw [uIoc_of_le h] at hti
    exact ⟨hx₀.1.trans hti.1, hti.2.trans_lt hx.2⟩
  · rw [uIoc_of_ge h] at hti
    exact ⟨hx.1.trans hti.1, hti.2.trans_lt hx₀.2⟩

theorem intervalIntegral_mul_eq_integral_of_tsupport {a b : ℝ}
    (u p : ℝ → ℝ) (hp : tsupport p ⊆ Ioo a b) :
    (∫ x in a..b, u x * p x) = ∫ x, u x * p x := by
  apply intervalIntegral.integral_eq_integral_of_support_subset
  exact Function.support_mul_subset_right.trans
    ((subset_tsupport p).trans (hp.trans Ioo_subset_Ioc_self))

theorem exists_contDiffOn_one_rep_of_weak_potential_Ioo {a b : ℝ}
    (hab : a < b) {u f w V : ℝ → ℝ}
    (hu : MemLp u 2 (volume.restrict (Ioo a b)))
    (hf : MemLp f 2 (volume.restrict (Ioo a b)))
    (hw : ContDiff ℝ ∞ w) (hwn : ∀ x ∈ Ioo a b, w x ≠ 0)
    (hV : Continuous V) (x₀ : ℝ) (hx₀ : x₀ ∈ Ioo a b)
    (heq : ∀ φ : ℝ → ℝ, ContDiff ℝ ∞ φ → HasCompactSupport φ →
      tsupport φ ⊆ Ioo a b →
        (∫ x in a..b, u x *
          (deriv (fun y => w y * deriv φ y) x - V x * φ x)) =
            ∫ x in a..b, f x * φ x) :
    ∃ v : ℝ → ℝ, ∃ q : ℝ,
      u =ᵐ[volume.restrict (Ioo a b)] v ∧ ContDiffOn ℝ 1 v (Ioo a b) ∧
        ∀ x ∈ Ioo a b, w x * deriv v x =
          intervalLocalPrimitive (fun y => f y + v y * V y) x₀ x + q := by
  let H : ℝ → ℝ := fun x => f x + u x * V x
  have hH : IntegrableOn H (Ioo a b) volume :=
    (interval_memLp_integrable hf).add (interval_integrable_mul_continuous hu hV)
  have hdiv : ∀ φ : ℝ → ℝ, ContDiff ℝ ∞ φ → HasCompactSupport φ →
      tsupport φ ⊆ Ioo a b →
        (∫ x, u x * deriv (fun y => w y * deriv φ y) x) = ∫ x, H x * φ x := by
    intro φ hφ hφc hφs
    have h := heq φ hφ hφc hφs
    rw [interval_weak_potential_expand hab.le hu hw hV hφ] at h
    have hforce := interval_weak_forcing_expand hab.le hu hf hV
      (continuous_const : Continuous (fun _ : ℝ => (0 : ℝ))) hφ.continuous 0
    simp only [zero_mul, sub_zero] at hforce
    have hfluxs : tsupport (deriv (fun y => w y * deriv φ y)) ⊆ Ioo a b :=
      tsupport_deriv_subset.trans
        (tsupport_mul_subset_right.trans (tsupport_deriv_subset.trans hφs))
    rw [← intervalIntegral_mul_eq_integral_of_tsupport _ _ hfluxs,
      ← intervalIntegral_mul_eq_integral_of_tsupport _ _ hφs]
    change _ = ∫ x in a..b, (f x + u x * V x) * φ x
    rw [hforce]
    linarith
  obtain ⟨v, q, huv, hv, hflux⟩ :=
    exists_contDiffOn_one_rep_of_weak_divergence_Ioo hab hw.contDiffOn hwn
      (IntegrableOn.locallyIntegrableOn (interval_memLp_integrable hu))
      (IntegrableOn.locallyIntegrableOn hH)
      x₀ hx₀ hdiv
  refine ⟨v, q, huv, hv, fun x hx => ?_⟩
  rw [hflux x hx]
  congr 1
  apply intervalLocalPrimitive_congr_ae_Ioo _ hx₀ hx
  filter_upwards [huv] with y hy
  change f y + u y * V y = f y + v y * V y
  rw [hy]

end ContinuousFlexibility.Analysis
