module

public import ContinuousFlexibility.Radial.PositiveBufferEnergyProfiles
public import ContinuousFlexibility.Radial.PositiveBufferComparison
public import ContinuousFlexibility.Radial.PositiveBufferComparisonAffine

/-!
# Actual exterior minimizers and their conormal energy

The half-line profile is the genuine finite-energy minimizer constructed
above. Positivity and exponential comparison imply that its boundary flux
vanishes at infinity. Reflection treats the left and right exteriors using
one half-line argument.
-/

@[expose] public section

noncomputable section

namespace ContinuousFlexibility.Radial

open Real Set Filter MeasureTheory
open ContinuousFlexibility.Statements
open scoped Topology ContDiff

theorem positiveBuffer_right_unit_energy {V u d : ℝ → ℝ} {c m M : ℝ}
    (hm : 0 < m) (hM : 0 ≤ M)
    (huc : ContinuousOn u (Ici c)) (hdc : ContinuousOn d (Ici c))
    (hu : ∀ x ∈ Ici c, HasDerivAt u (d x) x)
    (hd : ∀ x ∈ Ioi c, HasDerivAt d (V x * u x) x)
    (hVm : ∀ x ∈ Ioi c, m ^ 2 ≤ V x) (hcut : u c = 1)
    (hbound : ∀ x ∈ Ici c, |u x| ≤ M)
    (hE : IntegrableOn (fun x => d x ^ 2 + V x * u x ^ 2) (Ioi c) volume) :
    (∫ x in Ioi c, d x ^ 2 + V x * u x ^ 2) = -d c ∧ m ≤ -d c := by
  have huO : ∀ x ∈ Ioi c, HasDerivAt u (d x) x :=
    fun x hx => hu x (Ioi_subset_Ici_self hx)
  have hcut0 : 0 ≤ u c := by rw [hcut]; norm_num
  have hbound' : ∀ x ∈ Ici c, u x ≤ M :=
    fun x hx => (le_abs_self (u x)).trans (hbound x hx)
  have hnonneg := positiveBuffer_halfline_solution_nonneg hm hM huc huO hd hVm hcut0 hbound
  have hflux0 := positiveBuffer_halfline_flux_tendsto_zero hm hM huc hdc hu hd hVm hnonneg hbound'
  have hflux := positiveBuffer_halfline_energy_eq_flux huc hdc huO hd hE hflux0
  have hlow := positiveBuffer_halfline_conormal_lower hm hM huc huO hd hVm hcut0 hbound'
    (hu c (mem_Ici.mpr le_rfl))
  exact ⟨by simpa only [hcut, one_mul] using hflux,
    by simpa only [hcut, mul_one] using hlow⟩

/-- For either exterior orientation the energy is the inward conormal and
is at least the mass. The only data used at infinity are the true finite
energy and boundedness of the smooth energy representative. -/
theorem positiveBuffer_exterior_unit_energy {V p : ℝ → ℝ} {O : Set ℝ} {c m M : ℝ}
    (hside : O = Ioi c ∨ O = Iio c) (hm : 0 < m) (hM : 0 ≤ M)
    (hp : ContDiff ℝ ∞ p)
    (hODE : ∀ x ∈ O, -deriv (deriv p) x + V x * p x = 0)
    (hVm : ∀ x ∈ closure O, m ^ 2 ≤ V x) (hcut : p c = 1)
    (hbound : ∀ x ∈ closure O, |p x| ≤ M)
    (hE : IntegrableOn (fun x => deriv p x ^ 2 + V x * p x ^ 2) O volume) :
    (∫ x in O, deriv p x ^ 2 + V x * p x ^ 2) =
      (if O = Ioi c then -deriv p c else deriv p c) ∧
      m ≤ ∫ x in O, deriv p x ^ 2 + V x * p x ^ 2 := by
  have hpd := (contDiff_infty_iff_deriv.mp hp).2
  have hp' (x : ℝ) : HasDerivAt p (deriv p x) x :=
    (hp.differentiable (by simp) x).hasDerivAt
  have hp'' (x : ℝ) (hx : x ∈ O) : HasDerivAt (deriv p) (V x * p x) x := by
    convert (hpd.differentiable (by simp) x).hasDerivAt using 1
    linarith [hODE x hx]
  rcases hside with rfl | rfl
  · have h := positiveBuffer_right_unit_energy hm hM hp.continuous.continuousOn
      hpd.continuous.continuousOn (fun x _ => hp' x) hp''
      (fun x hx => hVm x (subset_closure hx)) hcut
      (by simpa only [closure_Ioi] using hbound) hE
    refine ⟨by simpa only [if_pos rfl, ite_true] using h.1, ?_⟩
    rw [h.1]
    exact h.2
  · have hne : Iio c ≠ Ioi c := by
      intro heq
      have hx : c - 1 ∈ Ioi c := heq ▸ (show c - 1 ∈ Iio c by simp)
      have hx' := mem_Ioi.mp hx
      linarith
    have huR (x : ℝ) : HasDerivAt (fun t => p (-t)) (-deriv p (-x)) x := by
      have h := positiveBuffer_affine_hasDerivAt (a := 0) (b := -1) (x := x)
        (by simpa only [zero_add, neg_one_mul] using hp' (-x))
      simpa only [zero_add, neg_one_mul] using h
    have hdR (x : ℝ) (hx : x ∈ Ioi (-c)) :
        HasDerivAt (fun t => -deriv p (-t)) (V (-x) * p (-x)) x := by
      apply (positiveBuffer_reflection_homogeneous (fun y _ => hp' y) hp'' ?_).2
      exact mem_Iio.mpr (by linarith [mem_Ioi.mp hx])
    have hpre : (fun x : ℝ => -x) ⁻¹' Iio c = Ioi (-c) := by
      ext x
      simp only [mem_preimage, mem_Iio, mem_Ioi]
      constructor <;> intro h <;> linarith
    have hER : IntegrableOn
        (fun x => (-deriv p (-x)) ^ 2 + V (-x) * p (-x) ^ 2) (Ioi (-c)) volume := by
      have hcomp := (MeasurePreserving.integrableOn_comp_preimage
        (Measure.measurePreserving_neg (volume : Measure ℝ))
        (Homeomorph.neg ℝ).measurableEmbedding).2 hE
      simpa only [Function.comp_def, hpre, neg_sq] using hcomp
    have hVR : ∀ x ∈ Ioi (-c), m ^ 2 ≤ V (-x) := by
      intro x hx
      apply hVm (-x)
      exact subset_closure (mem_Iio.mpr (by linarith [mem_Ioi.mp hx]))
    have hMR : ∀ x ∈ Ici (-c), |p (-x)| ≤ M := by
      intro x hx
      apply hbound (-x)
      rw [closure_Iio]
      exact mem_Iic.mpr (by linarith [mem_Ici.mp hx])
    have h := positiveBuffer_right_unit_energy hm hM
      (hp.continuous.comp continuous_neg).continuousOn
      (hpd.continuous.comp continuous_neg).neg.continuousOn
      (fun x _ => huR x) hdR hVR
      (by simpa only [Function.comp_apply, neg_neg] using hcut) hMR hER
    simp only [Function.comp_apply, Pi.neg_apply, neg_neg] at h
    rw [positiveBuffer_reflection_energy] at h
    refine ⟨by simpa only [if_neg hne, ite_false] using h.1, ?_⟩
    rw [h.1]
    exact h.2

/-- Existence of the actual exterior unit-trace minimizer, including the
physical energy identity and both bounds on its conormal coefficient. -/
theorem positiveBuffer_exists_exterior_unit_profile {V : ℝ → ℝ}
    (hreal : ActualClosedFormRealization V) (hV : ContDiff ℝ ∞ V)
    {O : Set ℝ} {c m C₀ : ℝ} (hside : O = Ioi c ∨ O = Iio c)
    (hm : 0 < m) (hC₀ : 0 ≤ C₀)
    (hVm : ∀ x ∈ closure O ∪ Icc (c - 2 / m) (c + 2 / m), m ^ 2 ≤ V x)
    (hupper : ∀ x, |x - c| ≤ 2 / m → V x ≤ C₀ * m ^ 2) :
    ∃ p : ℝ → ℝ, ContDiff ℝ ∞ p ∧ p c = 1 ∧
      MemLp p 2 (volume.restrict O) ∧
      IntegrableOn (fun x => deriv p x ^ 2 + V x * p x ^ 2) O volume ∧
      (∀ x ∈ O, -deriv (deriv p) x + V x * p x = 0) ∧
      (∫ x in O, deriv p x ^ 2 + V x * p x ^ 2) =
        (if O = Ioi c then -deriv p c else deriv p c) ∧
      m ≤ (∫ x in O, deriv p x ^ 2 + V x * p x ^ 2) ∧
      (∫ x in O, deriv p x ^ 2 + V x * p x ^ 2) ≤
        4 * (morseCutoffDerivativeConstant ^ 2 + C₀) * m := by
  have hO : IsOpen O := by
    rcases hside with rfl | rfl
    · exact isOpen_Ioi
    · exact isOpen_Iio
  have hcl : closure O = insert c O := by
    rcases hside with rfl | rfl <;> simp only [closure_Ioi, closure_Iio, Ioi_insert, Iio_insert]
  have hS : IsClosed (insert c O) := by
    rw [← hcl]
    exact isClosed_closure
  have hc : c ∈ closure (insert c O)ᶜ := by
    rcases hside with rfl | rfl <;>
      simp only [Ioi_insert, Iio_insert, compl_Ici, compl_Iic, closure_Iio, closure_Ioi,
        mem_Iic, mem_Ici, le_refl]
  have hgeom : ∃ a b : ℝ, a < b ∧ Ioo a b ⊆ insert c O ∧
      ∀ᶠ x in 𝓝 c, x ∈ insert c O → x ∈ Icc a b := by
    rcases hside with rfl | rfl
    · refine ⟨c, c + 1, by linarith, ?_, ?_⟩
      · intro x hx
        exact mem_insert_of_mem c (mem_Ioi.mpr hx.1)
      · filter_upwards [Ioo_mem_nhds (show c - 1 < c by linarith)
          (show c < c + 1 by linarith)] with x hx hxs
        have hxc : c ≤ x := by simpa only [Ioi_insert, mem_Ici] using hxs
        exact ⟨hxc, hx.2.le⟩
    · refine ⟨c - 1, c, by linarith, ?_, ?_⟩
      · intro x hx
        exact mem_insert_of_mem c (mem_Iio.mpr hx.2)
      · filter_upwards [Ioo_mem_nhds (show c - 1 < c by linarith)
          (show c < c + 1 by linarith)] with x hx hxs
        have hxc : x ≤ c := by simpa only [Iio_insert, mem_Iic] using hxs
        exact ⟨hx.1.le, hxc⟩
  obtain ⟨a, b, hab, hsub, hnear⟩ := hgeom
  let φ := positiveBufferTraceLift c m
  have hφ := contDiff_positiveBufferTraceLift c m
  have hcφ := positiveBufferTraceLift_hasCompactSupport c hm
  have hVmS : ∀ x ∈ insert c O, m ^ 2 ≤ V x := by
    intro x hx
    exact hVm x (Or.inl (hcl.symm ▸ hx))
  have hpos : ∀ x ∈ insert c O ∪ Function.support φ, 0 ≤ V x := by
    intro x hx
    apply (sq_nonneg m).trans
    rcases hx with hx | hx
    · exact hVmS x hx
    · exact hVm x (Or.inr (positiveBufferTraceLift_tsupport_subset c hm (subset_tsupport φ hx)))
  obtain ⟨p, hp, hpc, hLp, hE, hODE, ⟨M, hM, hbound⟩, henergy⟩ :=
    positiveBuffer_exists_single_boundary_profile hreal hV hm hO hS hc hab hsub hnear hVmS
      φ hφ hcφ hpos
  have hcut : p c = 1 := by simpa only [φ, positiveBufferTraceLift_at_cut] using hpc
  have henergy' := positiveBuffer_exterior_unit_energy hside hm hM hp hODE
    (fun x hx => hVm x (Or.inl hx)) hcut (hcl.symm ▸ hbound) hE
  refine ⟨p, hp, hcut, hLp, hE, hODE, henergy'.1, henergy'.2, ?_⟩
  exact henergy.trans (positiveBufferTraceLift_energy_bound hV.continuous c hm hC₀ hupper)

end ContinuousFlexibility.Radial
