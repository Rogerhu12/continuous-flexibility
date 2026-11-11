import ContinuousFlexibility.Analysis.MaterialCoordinate
import Mathlib.Analysis.SpecialFunctions.SmoothTransition
import Mathlib.MeasureTheory.Integral.IntervalIntegral.ContDiff
import Mathlib.Analysis.Calculus.Deriv.MeanValue
import Mathlib.Analysis.Calculus.InverseFunctionTheorem.ContDiff
import Mathlib.Analysis.Calculus.InverseFunctionTheorem.Deriv

/-!
# A genuine global material coordinate on the unit interval

The positive scale is an explicit smooth interpolation of the two actual
endpoint scales. Its integral from `1/2` is a strictly increasing smooth
coordinate with limits `-∞` and `+∞` at the two ends. No profile-dependent
material scale is assumed here.
-/

noncomputable section

namespace ContinuousFlexibility.Analysis

open Set Filter MeasureTheory
open scoped Topology ContDiff

set_option backward.isDefEq.respectTransparency false

def materialIntervalTransition (t : ℝ) : ℝ := Real.smoothTransition (3 * t - 1)

def materialIntervalXL (t : ℝ) : ℝ := endpointX 1 t

def materialIntervalXR (t : ℝ) : ℝ := endpointX 1 (1 - t)

def materialIntervalEll (t : ℝ) : ℝ :=
  (1 - materialIntervalTransition t) * endpointEll 1 t +
    materialIntervalTransition t * endpointEll 1 (1 - t)

def materialIntervalDensity (t : ℝ) : ℝ := 1 / materialIntervalEll t

def materialIntervalRho (t : ℝ) : ℝ := ∫ s in (1 / 2 : ℝ)..t, materialIntervalDensity s

theorem contDiff_materialIntervalTransition : ContDiff ℝ ∞ materialIntervalTransition :=
  Real.smoothTransition.contDiff.comp ((contDiff_const.mul contDiff_id).sub contDiff_const)

theorem materialIntervalTransition_nonneg (t : ℝ) : 0 ≤ materialIntervalTransition t :=
  Real.smoothTransition.nonneg _

theorem materialIntervalTransition_le_one (t : ℝ) : materialIntervalTransition t ≤ 1 :=
  Real.smoothTransition.le_one _

theorem materialIntervalTransition_eq_zero {t : ℝ} (ht : t ≤ 1 / 3) :
    materialIntervalTransition t = 0 :=
  Real.smoothTransition.zero_of_nonpos (by linarith)

theorem materialIntervalTransition_eq_one {t : ℝ} (ht : 2 / 3 ≤ t) :
    materialIntervalTransition t = 1 :=
  Real.smoothTransition.one_of_one_le (by linarith)

theorem materialIntervalXL_pos {t : ℝ} (ht : t ∈ Ioo (0 : ℝ) 1) :
    0 < materialIntervalXL t := endpointX_pos ht.1 ht.2

theorem materialIntervalXR_pos {t : ℝ} (ht : t ∈ Ioo (0 : ℝ) 1) :
    0 < materialIntervalXR t := endpointX_pos (by linarith [ht.2]) (by linarith [ht.1])

theorem contDiffAt_materialIntervalXL {t : ℝ} (ht : t ∈ Ioo (0 : ℝ) 1) :
    ContDiffAt ℝ ∞ materialIntervalXL t := contDiffAt_endpointX (by norm_num) ht.1 ht.2

theorem contDiffAt_materialIntervalXR {t : ℝ} (ht : t ∈ Ioo (0 : ℝ) 1) :
    ContDiffAt ℝ ∞ materialIntervalXR t :=
  (contDiffAt_endpointX (by norm_num : (0 : ℝ) < 1) (by linarith [ht.2])
    (by linarith [ht.1])).comp t (contDiffAt_const.sub contDiffAt_id)

theorem materialIntervalEll_pos {t : ℝ} (ht : t ∈ Ioo (0 : ℝ) 1) :
    0 < materialIntervalEll t := by
  have hl := endpointEll_pos (d₀ := 1) ht.1
  have hr := endpointEll_pos (d₀ := 1) (by linarith [ht.2] : 0 < 1 - t)
  have hη := materialIntervalTransition_nonneg t
  rcases lt_or_eq_of_le (materialIntervalTransition_le_one t) with hlt | heq
  · exact add_pos_of_pos_of_nonneg (mul_pos (sub_pos.mpr hlt) hl) (mul_nonneg hη hr.le)
  · simpa [materialIntervalEll, heq] using hr

theorem materialIntervalEll_eq_left {t : ℝ} (ht : t ≤ 1 / 3) :
    materialIntervalEll t = endpointEll 1 t := by
  simp [materialIntervalEll, materialIntervalTransition_eq_zero ht]

theorem materialIntervalEll_eq_right {t : ℝ} (ht : 2 / 3 ≤ t) :
    materialIntervalEll t = endpointEll 1 (1 - t) := by
  simp [materialIntervalEll, materialIntervalTransition_eq_one ht]

theorem contDiffAt_materialIntervalEll {t : ℝ} (ht : t ∈ Ioo (0 : ℝ) 1) :
    ContDiffAt ℝ ∞ materialIntervalEll t := by
  have hL := contDiffAt_materialIntervalXL ht
  have hR := contDiffAt_materialIntervalXR ht
  have hLn : 1 + materialIntervalXL t ≠ 0 := by linarith [materialIntervalXL_pos ht]
  have hRn : 1 + materialIntervalXR t ≠ 0 := by linarith [materialIntervalXR_pos ht]
  have heL : ContDiffAt ℝ ∞ (endpointEll 1) t :=
    contDiffAt_id.div (contDiffAt_const.add hL) hLn
  have heR : ContDiffAt ℝ ∞ (fun s : ℝ => endpointEll 1 (1 - s)) t :=
    (contDiffAt_const.sub contDiffAt_id).div (contDiffAt_const.add hR) hRn
  exact ((contDiffAt_const.sub contDiff_materialIntervalTransition.contDiffAt).mul heL).add
    (contDiff_materialIntervalTransition.contDiffAt.mul heR)

theorem contDiffOn_materialIntervalEll : ContDiffOn ℝ ∞ materialIntervalEll (Ioo (0 : ℝ) 1) :=
  fun _ ht => (contDiffAt_materialIntervalEll ht).contDiffWithinAt

theorem materialIntervalDensity_pos {t : ℝ} (ht : t ∈ Ioo (0 : ℝ) 1) :
    0 < materialIntervalDensity t := one_div_pos.mpr (materialIntervalEll_pos ht)

theorem contDiffAt_materialIntervalDensity {t : ℝ} (ht : t ∈ Ioo (0 : ℝ) 1) :
    ContDiffAt ℝ ∞ materialIntervalDensity t :=
  contDiffAt_const.div (contDiffAt_materialIntervalEll ht) (materialIntervalEll_pos ht).ne'

theorem contDiffOn_materialIntervalDensity :
    ContDiffOn ℝ ∞ materialIntervalDensity (Ioo (0 : ℝ) 1) :=
  fun _ ht => (contDiffAt_materialIntervalDensity ht).contDiffWithinAt

theorem intervalIntegrable_materialIntervalDensity {a b : ℝ}
    (ha : a ∈ Ioo (0 : ℝ) 1) (hb : b ∈ Ioo (0 : ℝ) 1) :
    IntervalIntegrable materialIntervalDensity volume a b :=
  (contDiffOn_materialIntervalDensity.continuousOn.mono
    (ordConnected_Ioo.uIcc_subset ha hb)).intervalIntegrable

theorem hasDerivAt_materialIntervalRho {t : ℝ} (ht : t ∈ Ioo (0 : ℝ) 1) :
    HasDerivAt materialIntervalRho (1 / materialIntervalEll t) t :=
  intervalIntegral.integral_hasDerivAt_right
    (intervalIntegrable_materialIntervalDensity (by norm_num) ht)
    (contDiffOn_materialIntervalDensity.continuousOn.stronglyMeasurableAtFilter isOpen_Ioo t ht)
    (contDiffAt_materialIntervalDensity ht).continuousAt

theorem contDiffOn_materialIntervalRho : ContDiffOn ℝ ∞ materialIntervalRho (Ioo (0 : ℝ) 1) := by
  apply (contDiffOn_infty_iff_deriv_of_isOpen isOpen_Ioo).mpr
  refine ⟨fun _ ht => (hasDerivAt_materialIntervalRho ht).differentiableAt.differentiableWithinAt, ?_⟩
  exact contDiffOn_materialIntervalDensity.congr (fun _ ht => (hasDerivAt_materialIntervalRho ht).deriv)

theorem contDiffAt_materialIntervalRho {t : ℝ} (ht : t ∈ Ioo (0 : ℝ) 1) :
    ContDiffAt ℝ ∞ materialIntervalRho t :=
  (contDiffOn_materialIntervalRho t ht).contDiffAt (isOpen_Ioo.mem_nhds ht)

theorem materialIntervalRho_deriv_pos {t : ℝ} (ht : t ∈ Ioo (0 : ℝ) 1) :
    0 < deriv materialIntervalRho t := by
  rw [(hasDerivAt_materialIntervalRho ht).deriv]
  exact one_div_pos.mpr (materialIntervalEll_pos ht)

theorem strictMonoOn_materialIntervalRho : StrictMonoOn materialIntervalRho (Ioo (0 : ℝ) 1) := by
  apply strictMonoOn_of_deriv_pos (convex_Ioo 0 1) contDiffOn_materialIntervalRho.continuousOn
  intro t ht
  exact materialIntervalRho_deriv_pos (by simpa only [interior_Ioo] using ht)

@[simp] theorem materialIntervalRho_half : materialIntervalRho (1 / 2) = 0 := by
  simp [materialIntervalRho]

theorem exists_materialIntervalRho_eq_left :
    ∃ c : ℝ, ∀ t ∈ Ioo (0 : ℝ) (1 / 3),
      materialIntervalRho t = endpointRhoOfDistance 1 t + c := by
  apply isOpen_Ioo.exists_eq_add_of_deriv_eq isPreconnected_Ioo
  · intro t ht
    exact (hasDerivAt_materialIntervalRho ⟨ht.1, by linarith [ht.2]⟩).differentiableAt.differentiableWithinAt
  · intro t ht
    exact (hasDerivAt_endpointRhoOfDistance (by norm_num : (0 : ℝ) < 1) ht.1
      (by linarith [ht.2])).differentiableAt.differentiableWithinAt
  · intro t ht
    rw [(hasDerivAt_materialIntervalRho ⟨ht.1, by linarith [ht.2]⟩).deriv,
      (hasDerivAt_endpointRhoOfDistance (by norm_num : (0 : ℝ) < 1) ht.1
        (by linarith [ht.2])).deriv, materialIntervalEll_eq_left ht.2.le]

theorem hasDerivAt_reflectedEndpointRho {t : ℝ} (ht : t ∈ Ioo (0 : ℝ) 1) :
    HasDerivAt (fun s : ℝ => -endpointRhoOfDistance 1 (1 - s))
      (1 / endpointEll 1 (1 - t)) t := by
  have hs : HasDerivAt (fun s : ℝ => 1 - s) (-1) t := by
    convert (hasDerivAt_const t (1 : ℝ)).sub (hasDerivAt_id t) using 1
    · funext s
      rfl
    · norm_num
  have h := ((hasDerivAt_endpointRhoOfDistance (by norm_num : (0 : ℝ) < 1)
    (by linarith [ht.2] : 0 < 1 - t) (by linarith [ht.1] : 1 - t < 1)).comp t hs).neg
  apply h.congr_deriv
  ring

theorem exists_materialIntervalRho_eq_right :
    ∃ c : ℝ, ∀ t ∈ Ioo (2 / 3 : ℝ) 1,
      materialIntervalRho t = -endpointRhoOfDistance 1 (1 - t) + c := by
  apply isOpen_Ioo.exists_eq_add_of_deriv_eq isPreconnected_Ioo
  · intro t ht
    exact (hasDerivAt_materialIntervalRho ⟨by linarith [ht.1], ht.2⟩).differentiableAt.differentiableWithinAt
  · intro t ht
    exact (hasDerivAt_reflectedEndpointRho ⟨by linarith [ht.1], ht.2⟩).differentiableAt.differentiableWithinAt
  · intro t ht
    rw [(hasDerivAt_materialIntervalRho ⟨by linarith [ht.1], ht.2⟩).deriv,
      (hasDerivAt_reflectedEndpointRho ⟨by linarith [ht.1], ht.2⟩).deriv,
      materialIntervalEll_eq_right ht.1.le]

theorem tendsto_reflectedDistance_zero :
    Tendsto (fun t : ℝ => 1 - t) (𝓝[<] (1 : ℝ)) (𝓝[>] (0 : ℝ)) := by
  apply tendsto_nhdsWithin_iff.mpr
  constructor
  · simpa using ((tendsto_const_nhds (x := (1 : ℝ))).sub (tendsto_id.mono_left nhdsWithin_le_nhds :
      Tendsto (fun t : ℝ => t) (𝓝[<] (1 : ℝ)) (𝓝 1)))
  · filter_upwards [self_mem_nhdsWithin] with t ht
    exact sub_pos.mpr (show t < 1 from ht)

theorem tendsto_materialIntervalRho_left :
    Tendsto materialIntervalRho (𝓝[>] (0 : ℝ)) atBot := by
  obtain ⟨c, hc⟩ := exists_materialIntervalRho_eq_left
  have h := (tendsto_endpointRhoOfDistance_atBot (by norm_num : (0 : ℝ) < 1)).atBot_add
    (tendsto_const_nhds (x := c))
  apply h.congr'
  have hu : ∀ᶠ t : ℝ in 𝓝[>] (0 : ℝ), t < 1 / 3 :=
    (eventually_lt_nhds (by norm_num : (0 : ℝ) < 1 / 3)).filter_mono nhdsWithin_le_nhds
  filter_upwards [self_mem_nhdsWithin, hu] with t ht0 ht1
  exact (hc t ⟨ht0, ht1⟩).symm

theorem tendsto_materialIntervalRho_right :
    Tendsto materialIntervalRho (𝓝[<] (1 : ℝ)) atTop := by
  obtain ⟨c, hc⟩ := exists_materialIntervalRho_eq_right
  have hneg := tendsto_neg_atBot_atTop.comp
    ((tendsto_endpointRhoOfDistance_atBot (by norm_num : (0 : ℝ) < 1)).comp
      tendsto_reflectedDistance_zero)
  have h := hneg.atTop_add (tendsto_const_nhds (x := c))
  apply h.congr'
  have hl : ∀ᶠ t : ℝ in 𝓝[<] (1 : ℝ), 2 / 3 < t :=
    (eventually_gt_nhds (by norm_num : (2 / 3 : ℝ) < 1)).filter_mono nhdsWithin_le_nhds
  filter_upwards [self_mem_nhdsWithin, hl] with t ht1 ht0
  exact (hc t ⟨ht0, ht1⟩).symm

theorem surjOn_materialIntervalRho : SurjOn materialIntervalRho (Ioo (0 : ℝ) 1) univ := by
  have hl : 𝓝[>] (0 : ℝ) ≤ 𝓟 (Ioo (0 : ℝ) 1) := by
    apply le_principal_iff.mpr
    have hu : ∀ᶠ t : ℝ in 𝓝[>] (0 : ℝ), t < 1 :=
      (eventually_lt_nhds (by norm_num : (0 : ℝ) < 1)).filter_mono nhdsWithin_le_nhds
    filter_upwards [self_mem_nhdsWithin, hu] with t ht0 ht1
    exact ⟨ht0, ht1⟩
  have hr : 𝓝[<] (1 : ℝ) ≤ 𝓟 (Ioo (0 : ℝ) 1) := by
    apply le_principal_iff.mpr
    have h0 : ∀ᶠ t : ℝ in 𝓝[<] (1 : ℝ), 0 < t :=
      (eventually_gt_nhds (by norm_num : (0 : ℝ) < 1)).filter_mono nhdsWithin_le_nhds
    filter_upwards [self_mem_nhdsWithin, h0] with t ht1 ht0
    exact ⟨ht0, ht1⟩
  exact fun y hy => isPreconnected_Ioo.intermediate_value_Iii hl hr
    contDiffOn_materialIntervalRho.continuousOn tendsto_materialIntervalRho_left
    tendsto_materialIntervalRho_right hy

theorem bijective_materialIntervalRho :
    Function.Bijective (fun t : Ioo (0 : ℝ) 1 => materialIntervalRho t) := by
  constructor
  · intro s t h
    apply Subtype.ext
    exact strictMonoOn_materialIntervalRho.injOn s.2 t.2 h
  · intro y
    obtain ⟨t, ht, heq⟩ := surjOn_materialIntervalRho (mem_univ y)
    exact ⟨⟨t, ht⟩, heq⟩

/-- The proved coordinate bijection on its actual open interval. -/
def materialIntervalEquiv : Ioo (0 : ℝ) 1 ≃ ℝ :=
  Equiv.ofBijective (fun t : Ioo (0 : ℝ) 1 => materialIntervalRho t) bijective_materialIntervalRho

/-- A real-valued inverse; membership in `(0,1)` is a proved property. -/
def materialIntervalInverse (y : ℝ) : ℝ := (materialIntervalEquiv.symm y).1

theorem materialIntervalInverse_mem (y : ℝ) : materialIntervalInverse y ∈ Ioo (0 : ℝ) 1 :=
  (materialIntervalEquiv.symm y).2

@[simp] theorem materialIntervalRho_inverse (y : ℝ) :
    materialIntervalRho (materialIntervalInverse y) = y := materialIntervalEquiv.apply_symm_apply y

@[simp] theorem materialIntervalInverse_rho {t : ℝ} (ht : t ∈ Ioo (0 : ℝ) 1) :
    materialIntervalInverse (materialIntervalRho t) = t :=
  congrArg Subtype.val (materialIntervalEquiv.symm_apply_apply ⟨t, ht⟩)

private theorem eventually_materialIntervalInverse_rho {t : ℝ} (ht : t ∈ Ioo (0 : ℝ) 1) :
    ∀ᶠ s in 𝓝 t, materialIntervalInverse (materialIntervalRho s) = s := by
  filter_upwards [isOpen_Ioo.mem_nhds ht] with s hs
  exact materialIntervalInverse_rho hs

theorem hasStrictDerivAt_materialIntervalInverse_rho {t : ℝ} (ht : t ∈ Ioo (0 : ℝ) 1) :
    HasStrictDerivAt materialIntervalInverse (materialIntervalEll t) (materialIntervalRho t) := by
  have h := ((contDiffAt_materialIntervalRho ht).hasStrictDerivAt (by simp)).to_local_left_inverse
    (materialIntervalRho_deriv_pos ht).ne' (eventually_materialIntervalInverse_rho ht)
  simpa only [(hasDerivAt_materialIntervalRho ht).deriv, one_div, inv_inv] using h

/-- Actual inverse-function regularity on the full real material axis. -/
theorem contDiffAt_materialIntervalInverse_rho {t : ℝ} (ht : t ∈ Ioo (0 : ℝ) 1) :
    ContDiffAt ℝ ∞ materialIntervalInverse (materialIntervalRho t) := by
  have h0 := (materialIntervalRho_deriv_pos ht).ne'
  let h := ((contDiffAt_materialIntervalRho ht).hasStrictDerivAt (by simp)).hasStrictFDerivAt_equiv h0
  let e := h.toOpenPartialHomeomorph materialIntervalRho
  have he : e.symm (materialIntervalRho t) = t := h.localInverse_apply_image
  have hd : HasDerivAt e (deriv materialIntervalRho t) (e.symm (materialIntervalRho t)) := by
    rw [he]
    exact (hasDerivAt_materialIntervalRho ht).differentiableAt.hasDerivAt
  have hc : ContDiffAt ℝ ∞ (e : ℝ → ℝ) (e.symm (materialIntervalRho t)) := by
    rw [he]
    exact contDiffAt_materialIntervalRho ht
  have hi := e.contDiffAt_symm_deriv h0 h.image_mem_toOpenPartialHomeomorph_target hd hc
  have heq : materialIntervalInverse =ᶠ[𝓝 (materialIntervalRho t)] (e.symm : ℝ → ℝ) :=
    h.localInverse_unique (eventually_materialIntervalInverse_rho ht)
  exact hi.congr_of_eventuallyEq heq

theorem contDiff_materialIntervalInverse : ContDiff ℝ ∞ materialIntervalInverse := by
  apply contDiff_iff_contDiffAt.mpr
  intro y
  have h := contDiffAt_materialIntervalInverse_rho (materialIntervalInverse_mem y)
  simpa only [materialIntervalRho_inverse] using h

theorem hasDerivAt_materialIntervalInverse (y : ℝ) :
    HasDerivAt materialIntervalInverse (materialIntervalEll (materialIntervalInverse y)) y := by
  have h := (hasStrictDerivAt_materialIntervalInverse_rho (materialIntervalInverse_mem y)).hasDerivAt
  simpa only [materialIntervalRho_inverse] using h

/-- The actual coordinate and inverse, packaged with proved continuity. -/
def materialIntervalHomeomorph : Ioo (0 : ℝ) 1 ≃ₜ ℝ where
  toEquiv := materialIntervalEquiv
  continuous_toFun := contDiffOn_materialIntervalRho.continuousOn.domRestrict
  continuous_invFun := contDiff_materialIntervalInverse.continuous.subtype_mk _

end ContinuousFlexibility.Analysis
