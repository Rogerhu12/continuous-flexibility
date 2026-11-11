import ContinuousFlexibility.Radial.MorseChainFlatExtension
import Mathlib.Analysis.ODE.ExistUnique
import Mathlib.Analysis.Calculus.BumpFunction.InnerProduct
import Mathlib.Analysis.Calculus.IteratedDeriv.Lemmas

/-!
# Smooth inward extension at a regular tail entrance

Infinite differentiability at a single point does not supply a common
smooth neighborhood. We instead solve the regular linear flux system on
both sides of the entrance, use uniqueness to identify its outward germ,
and cut off the new inward part.
-/

noncomputable section

namespace ContinuousFlexibility.Radial

open Set Filter Real
open scoped Topology ContDiff NNReal

/-- A smooth function on an open set has a globally smooth representative
of its germ at each point of that set. -/
theorem physical_smooth_extension_near {f : ℝ → ℝ} {U : Set ℝ} {c : ℝ}
    (hU : IsOpen U) (hf : ContDiffOn ℝ ∞ f U) (hc : c ∈ U) :
    ∃ F : ℝ → ℝ, ContDiff ℝ ∞ F ∧ F =ᶠ[𝓝 c] f := by
  obtain ⟨δ, hδ, hball⟩ := Metric.mem_nhds_iff.mp (hU.mem_nhds hc)
  let χ : ContDiffBump c := ⟨δ / 4, δ / 2, by positivity, by linarith⟩
  let F : ℝ → ℝ := fun x => χ x * f x
  have hsupp : tsupport (χ : ℝ → ℝ) ⊆ U := by
    rw [χ.tsupport_eq, Real.closedBall_eq_Icc]
    intro x hx
    apply hball
    rw [Real.ball_eq_Ioo]
    change c - δ / 2 ≤ x ∧ x ≤ c + δ / 2 at hx
    exact ⟨by linarith [hx.1], by linarith [hx.2]⟩
  refine ⟨F, contDiff_iff_contDiffAt.mpr ?_, ?_⟩
  · intro x
    by_cases hx : x ∈ tsupport (χ : ℝ → ℝ)
    · exact χ.contDiffAt.mul (hf.contDiffAt (hU.mem_nhds (hsupp hx)))
    · apply (contDiffAt_const : ContDiffAt ℝ ∞ (fun _ : ℝ => (0 : ℝ)) x).congr_of_eventuallyEq
      filter_upwards [notMem_tsupport_iff_eventuallyEq.mp hx] with y hy
      change χ y * f y = 0
      change χ y = 0 at hy
      rw [hy, zero_mul]
  · filter_upwards [χ.eventuallyEq_one] with x hx
    change χ x * f x = f x
    change χ x = 1 at hx
    rw [hx, one_mul]

/-- The height-flux state field for a regular scalar second-order equation. -/
def physicalLinearField (a b : ℝ → ℝ) (t : ℝ) (z : ℝ × ℝ) : ℝ × ℝ :=
  (a t * z.2, b t * z.1)

theorem physicalLinearField_lipschitz {a b : ℝ → ℝ} {t : ℝ} {K : ℝ≥0}
    (ha : ‖a t‖ ≤ (K : ℝ)) (hb : ‖b t‖ ≤ (K : ℝ)) :
    LipschitzWith K (physicalLinearField a b t) := by
  apply LipschitzWith.of_dist_le_mul
  intro x y
  simp only [dist_eq_norm, physicalLinearField, Prod.norm_def, Prod.fst_sub, Prod.snd_sub]
  rw [← mul_sub, ← mul_sub, norm_mul, norm_mul]
  exact max_le
    (mul_le_mul ha (le_max_right _ _) (norm_nonneg _) K.2)
    (mul_le_mul hb (le_max_left _ _) (norm_nonneg _) K.2)

/-- Local existence and smoothness for the actual linear state system.
The time coordinate is adjoined only for applying the standard autonomous
local existence theorem, then identified with the original parameter. -/
theorem physical_exists_smooth_linearState {a b : ℝ → ℝ}
    (ha : ContDiff ℝ ∞ a) (hb : ContDiff ℝ ∞ b) (c : ℝ) (z₀ : ℝ × ℝ) :
    ∃ z : ℝ → ℝ × ℝ, z c = z₀ ∧ ∃ ε : ℝ, 0 < ε ∧
      ContDiffOn ℝ ∞ z (Ioo (c - ε) (c + ε)) ∧
      ∀ t ∈ Ioo (c - ε) (c + ε), HasDerivAt z (physicalLinearField a b t (z t)) t := by
  let F : (ℝ × (ℝ × ℝ)) → ℝ × (ℝ × ℝ) :=
    fun q => (1, physicalLinearField a b q.1 q.2)
  have hF : ContDiff ℝ ∞ F :=
    contDiff_const.prodMk
      (((ha.comp contDiff_fst).mul (contDiff_snd.comp contDiff_snd)).prodMk
        ((hb.comp contDiff_fst).mul (contDiff_fst.comp contDiff_snd)))
  have hF₁ : ContDiffAt ℝ 1 F (c, z₀) := hF.contDiffAt.of_le (by simp)
  obtain ⟨α, hα₀, ε, hε, hα⟩ :=
    hF₁.exists_forall_mem_closedBall_exists_eq_forall_mem_Ioo_hasDerivAt₀ c
  have ht : ∀ t ∈ Ioo (c - ε) (c + ε),
      HasDerivAt (fun x => (α x).1) 1 t := by
    intro t ht
    exact (ContinuousLinearMap.fst ℝ ℝ (ℝ × ℝ)).hasFDerivAt.comp_hasDerivAt t (hα t ht)
  have htime : EqOn (fun t => (α t).1) id (Ioo (c - ε) (c + ε)) := by
    apply isOpen_Ioo.eqOn_of_deriv_eq (x := c) isPreconnected_Ioo
      (fun t ht' => (ht t ht').differentiableAt.differentiableWithinAt)
      differentiable_id.differentiableOn
    · intro t ht'
      rw [(ht t ht').deriv, deriv_id]
    · exact ⟨by linarith, by linarith⟩
    · exact congrArg Prod.fst hα₀
  have hsub : Icc (c - ε / 2) (c + ε / 2) ⊆ Ioo (c - ε) (c + ε) := by
    intro t ht'
    exact ⟨by linarith [ht'.1], by linarith [ht'.2]⟩
  have hαsmooth : ContDiffOn ℝ ∞ α (Icc (c - ε / 2) (c + ε / 2)) :=
    ODE.contDiffOn_enat_Icc_of_hasDerivWithinAt (u := univ)
      (f := fun (_ : ℝ) q => F q) (hF.comp contDiff_snd).contDiffOn
      (fun t ht' => (hα t (hsub ht')).hasDerivWithinAt) (mapsTo_univ _ _)
  refine ⟨fun t => (α t).2, congrArg Prod.snd hα₀, ε / 2, by positivity,
    hαsmooth.snd.mono Ioo_subset_Icc_self, ?_⟩
  intro t ht'
  have hd := (ContinuousLinearMap.snd ℝ ℝ (ℝ × ℝ)).hasFDerivAt.comp_hasDerivAt
    t (hα t (hsub (Ioo_subset_Icc_self ht')))
  change HasDerivAt (fun t => (α t).2)
    (physicalLinearField a b (α t).1 (α t).2) t at hd
  simpa only [htime (hsub (Ioo_subset_Icc_self ht')), id_eq] using hd

/-- A compact interval supplies one Lipschitz constant for the two
coefficient functions, so equal initial states give equal actual solutions. -/
theorem physical_linearState_eqOn {a b : ℝ → ℝ} {c d : ℝ}
    (ha : ContinuousOn a (Icc c d)) (hb : ContinuousOn b (Icc c d))
    {z Z : ℝ → ℝ × ℝ}
    (hz : ∀ t ∈ Icc c d, HasDerivAt z (physicalLinearField a b t (z t)) t)
    (hZ : ∀ t ∈ Icc c d, HasDerivAt Z (physicalLinearField a b t (Z t)) t)
    (hinit : z c = Z c) : EqOn z Z (Icc c d) := by
  obtain ⟨A, hA⟩ := (isCompact_Icc : IsCompact (Icc c d)).exists_bound_of_continuousOn ha
  obtain ⟨B, hB⟩ := (isCompact_Icc : IsCompact (Icc c d)).exists_bound_of_continuousOn hb
  let K : ℝ≥0 := ⟨max 0 (max A B), le_max_left _ _⟩
  have hK (t : ℝ) (ht : t ∈ Icc c d) :
      LipschitzWith K (physicalLinearField a b t) :=
    physicalLinearField_lipschitz
      ((hA t ht).trans ((le_max_left A B).trans (le_max_right _ _)))
      ((hB t ht).trans ((le_max_right A B).trans (le_max_right _ _)))
  exact ODE_solution_unique_of_mem_Icc_right (s := fun _ => univ)
    (fun t ht => (hK t (Ico_subset_Icc_self ht)).lipschitzOnWith)
    (HasDerivAt.continuousOn hz) (fun t ht => (hz t (Ico_subset_Icc_self ht)).hasDerivWithinAt)
    (fun _ _ => mem_univ _) (HasDerivAt.continuousOn hZ)
    (fun t ht => (hZ t (Ico_subset_Icc_self ht)).hasDerivWithinAt)
    (fun _ _ => mem_univ _) hinit

/-- A first-order identity on the open side also holds at a smooth
entrance when its two coefficient factors are continuous there. -/
theorem physical_firstOrder_at_entrance {f a g : ℝ → ℝ} {c d : ℝ}
    (hcd : c < d) (hf : ContDiffAt ℝ ∞ f c)
    (ha : ContinuousAt a c) (hg : ContinuousAt g c)
    (heq : ∀ x ∈ Ioo c d, deriv f x = a x * g x) :
    HasDerivAt f (a c * g c) c := by
  have hd : ContinuousAt (deriv f) c := (hf.derivWithin (m := ∞) (by simp)).continuousAt
  have hEq : deriv f =ᶠ[𝓝[>] c] (fun x => a x * g x) :=
    Filter.mem_of_superset (Ioo_mem_nhdsGT hcd) (fun x hx => heq x hx)
  have hval : deriv f c = a c * g c := tendsto_nhds_unique
    (hd.tendsto.mono_left nhdsWithin_le_nhds)
    (((ha.mul hg).tendsto.mono_left nhdsWithin_le_nhds).congr' hEq.symm)
  exact hval ▸ (hf.differentiableAt (by simp)).hasDerivAt

/-- Extend the inward side of a regular entrance smoothly to the entire
half-line, preserving the original solution at every outward point. -/
theorem physical_extend_inward {f g a b : ℝ → ℝ} {U : Set ℝ} {c d : ℝ}
    (hU : IsOpen U) (hc : c ∈ U) (hcd : c < d)
    (ha : ContDiffOn ℝ ∞ a U) (hb : ContDiffOn ℝ ∞ b U)
    (hf₀ : ContDiffAt ℝ ∞ f c) (hg₀ : ContDiffAt ℝ ∞ g c)
    (hf : ContDiffOn ℝ ∞ f (Ioo c d)) (hg : ContDiffOn ℝ ∞ g (Ioo c d))
    (hdf : ∀ x ∈ Ioo c d, deriv f x = a x * g x)
    (hdg : ∀ x ∈ Ioo c d, deriv g x = b x * f x) :
    ∃ F : ℝ → ℝ, ContDiffOn ℝ ∞ F (Iio d) ∧ ∀ x, c ≤ x → F x = f x := by
  obtain ⟨a₀, ha₀, haeq⟩ := physical_smooth_extension_near hU ha hc
  obtain ⟨b₀, hb₀, hbeq⟩ := physical_smooth_extension_near hU hb hc
  obtain ⟨z, hz₀, ε, hε, hzsm, hzd⟩ := physical_exists_smooth_linearState ha₀ hb₀ c (f c, g c)
  have hnear : ∀ᶠ x in 𝓝 c,
      a₀ x = a x ∧ b₀ x = b x ∧ x ∈ Ioo (c - ε) (c + ε) ∧ x < d := by
    filter_upwards [haeq, hbeq, Ioo_mem_nhds (show c - ε < c by linarith)
      (show c < c + ε by linarith), eventually_lt_nhds hcd] with x ha' hb' hx hd
    exact ⟨ha', hb', hx, hd⟩
  obtain ⟨l, r, ⟨hl, hr⟩, hsub⟩ := hnear.exists_Ioo_subset
  let e := (c + r) / 2
  have hce : c < e := by dsimp [e]; linarith
  have her : e < r := by dsimp [e]; linarith
  have hsmall : ∀ x ∈ Icc c e,
      a₀ x = a x ∧ b₀ x = b x ∧ x ∈ Ioo (c - ε) (c + ε) ∧ x < d :=
    fun x hx => hsub ⟨hl.trans_le hx.1, hx.2.trans_lt her⟩
  have hfd₀ := physical_firstOrder_at_entrance hcd hf₀
    (ha.contDiffAt (hU.mem_nhds hc)).continuousAt hg₀.continuousAt hdf
  have hgd₀ := physical_firstOrder_at_entrance hcd hg₀
    (hb.contDiffAt (hU.mem_nhds hc)).continuousAt hf₀.continuousAt hdg
  have hstate : ∀ x ∈ Icc c e, HasDerivAt (fun t => (f t, g t))
      (physicalLinearField a₀ b₀ x (f x, g x)) x := by
    intro x hx
    have he := hsmall x hx
    have hfd : HasDerivAt f (a x * g x) x := by
      rcases eq_or_lt_of_le hx.1 with hxc | hxc
      · simpa only [← hxc] using hfd₀
      · have hx' : x ∈ Ioo c d := ⟨hxc, he.2.2.2⟩
        exact hdf x hx' ▸ ((hf.contDiffAt (isOpen_Ioo.mem_nhds hx')).differentiableAt
          (by simp)).hasDerivAt
    have hgd : HasDerivAt g (b x * f x) x := by
      rcases eq_or_lt_of_le hx.1 with hxc | hxc
      · simpa only [← hxc] using hgd₀
      · have hx' : x ∈ Ioo c d := ⟨hxc, he.2.2.2⟩
        exact hdg x hx' ▸ ((hg.contDiffAt (isOpen_Ioo.mem_nhds hx')).differentiableAt
          (by simp)).hasDerivAt
    simpa only [physicalLinearField, he.1, he.2.1] using hfd.prodMk hgd
  have hstates := physical_linearState_eqOn ha₀.continuous.continuousOn hb₀.continuous.continuousOn
    hstate (fun x hx => hzd x (hsmall x hx).2.2.1) hz₀.symm
  obtain ⟨F₀, hF₀, hFeq⟩ := physical_smooth_extension_near isOpen_Ioo hzsm.fst
    (show c ∈ Ioo (c - ε) (c + ε) from ⟨by linarith, by linarith⟩)
  let F : ℝ → ℝ := fun x => if x < c then F₀ x else f x
  have hFc : F =ᶠ[𝓝 c] F₀ := by
    filter_upwards [hFeq, eventually_lt_nhds hce] with x hx hxe
    dsimp only [F]
    split_ifs with hxc
    · rfl
    · exact (congrArg Prod.fst (hstates ⟨le_of_not_gt hxc, hxe.le⟩)).trans hx.symm
  refine ⟨F, ?_, fun x hx => if_neg (not_lt.mpr hx)⟩
  intro x hx
  have hs : ContDiffAt ℝ ∞ F x := by
    rcases lt_trichotomy x c with hxc | hxc | hxc
    · apply hF₀.contDiffAt.congr_of_eventuallyEq
      filter_upwards [eventually_lt_nhds hxc] with y hy
      exact if_pos hy
    · subst x
      exact hF₀.contDiffAt.congr_of_eventuallyEq hFc
    · apply (hf.contDiffAt (isOpen_Ioo.mem_nhds ⟨hxc, hx⟩)).congr_of_eventuallyEq
      filter_upwards [eventually_gt_nhds hxc] with y hy
      exact if_neg (not_lt.mpr hy.le)
  exact hs.contDiffWithinAt

/-- A regular inward entrance and all actual outward jet limits produce
a global smooth function flat at the right endpoint. -/
theorem physical_flat_extension_from_left {f g a b : ℝ → ℝ} {U : Set ℝ} {c d : ℝ}
    (hU : IsOpen U) (hc : c ∈ U) (hcd : c < d)
    (ha : ContDiffOn ℝ ∞ a U) (hb : ContDiffOn ℝ ∞ b U)
    (hf₀ : ContDiffAt ℝ ∞ f c) (hg₀ : ContDiffAt ℝ ∞ g c)
    (hf : ContDiffOn ℝ ∞ f (Ioo c d)) (hg : ContDiffOn ℝ ∞ g (Ioo c d))
    (hdf : ∀ x ∈ Ioo c d, deriv f x = a x * g x)
    (hdg : ∀ x ∈ Ioo c d, deriv g x = b x * f x)
    (hlim : ∀ k, Tendsto (iteratedDeriv k f) (𝓝[<] d) (𝓝 0)) :
    ∃ V : ℝ → ℝ, ContDiff ℝ ∞ V ∧ EqOn V f (Ioo c d) ∧
      ∀ k, iteratedDeriv k V d = 0 := by
  obtain ⟨F, hF, hFeq⟩ := physical_extend_inward hU hc hcd ha hb hf₀ hg₀ hf hg hdf hdg
  let V : ℝ → ℝ := fun x => if x < d then F x else 0
  have hVeq : EqOn V f (Ioo c d) := by
    intro x hx
    exact (if_pos hx.2).trans (hFeq x hx.1.le)
  have hV : ContDiffOn ℝ ∞ V (Iio d) := by
    intro x hx
    apply ((hF.contDiffAt (isOpen_Iio.mem_nhds hx)).congr_of_eventuallyEq ?_).contDiffWithinAt
    filter_upwards [eventually_lt_nhds hx] with y hy
    exact if_pos hy
  have hVlim (k : ℕ) : Tendsto (iteratedDeriv k V) (𝓝[<] d) (𝓝 0) := by
    apply (hlim k).congr'
    filter_upwards [Ioo_mem_nhdsLT hcd] with x hx
    have heq : V =ᶠ[𝓝 x] f :=
      Filter.mem_of_superset (isOpen_Ioo.mem_nhds hx) (fun y hy => hVeq hy)
    exact (heq.iteratedDeriv_eq k).symm
  have hflat := contDiff_flat_of_left_jet_limits hV
    (fun x hx => if_neg (not_lt.mpr hx)) hVlim
  exact ⟨V, hflat.1, hVeq, fun k => hflat.2 k d le_rfl⟩

/-- Reflection gives the corresponding global smooth extension flat at
the left endpoint, with no assumption on the original inward values. -/
theorem physical_flat_extension_from_right {f g a b : ℝ → ℝ} {U : Set ℝ} {c d : ℝ}
    (hU : IsOpen U) (hd : d ∈ U) (hcd : c < d)
    (ha : ContDiffOn ℝ ∞ a U) (hb : ContDiffOn ℝ ∞ b U)
    (hf₀ : ContDiffAt ℝ ∞ f d) (hg₀ : ContDiffAt ℝ ∞ g d)
    (hf : ContDiffOn ℝ ∞ f (Ioo c d)) (hg : ContDiffOn ℝ ∞ g (Ioo c d))
    (hdf : ∀ x ∈ Ioo c d, deriv f x = a x * g x)
    (hdg : ∀ x ∈ Ioo c d, deriv g x = b x * f x)
    (hlim : ∀ k, Tendsto (iteratedDeriv k f) (𝓝[>] c) (𝓝 0)) :
    ∃ V : ℝ → ℝ, ContDiff ℝ ∞ V ∧ EqOn V f (Ioo c d) ∧
      ∀ k, iteratedDeriv k V c = 0 := by
  let U' : Set ℝ := (fun t : ℝ => -t) ⁻¹' U
  have hmaps : MapsTo (fun t : ℝ => -t) (Ioo (-d) (-c)) (Ioo c d) := by
    intro t ht
    exact ⟨by linarith [ht.2], by linarith [ht.1]⟩
  have hf' : ContDiffOn ℝ ∞ (fun t => f (-t)) (Ioo (-d) (-c)) :=
    hf.comp contDiff_id.neg.contDiffOn hmaps
  have hg' : ContDiffOn ℝ ∞ (fun t => g (-t)) (Ioo (-d) (-c)) :=
    hg.comp contDiff_id.neg.contDiffOn hmaps
  have ha' : ContDiffOn ℝ ∞ (fun t => -a (-t)) U' :=
    (ha.comp contDiff_id.neg.contDiffOn (fun _ ht => ht)).neg
  have hb' : ContDiffOn ℝ ∞ (fun t => -b (-t)) U' :=
    (hb.comp contDiff_id.neg.contDiffOn (fun _ ht => ht)).neg
  have hf₀' : ContDiffAt ℝ ∞ (fun t => f (-t)) (-d) := by
    have hh : ContDiffAt ℝ ∞ f (-(-d)) := by simpa only [neg_neg] using hf₀
    exact hh.comp (-d) contDiffAt_id.neg
  have hg₀' : ContDiffAt ℝ ∞ (fun t => g (-t)) (-d) := by
    have hh : ContDiffAt ℝ ∞ g (-(-d)) := by simpa only [neg_neg] using hg₀
    exact hh.comp (-d) contDiffAt_id.neg
  have hdf' : ∀ t ∈ Ioo (-d) (-c), deriv (fun x => f (-x)) t = -a (-t) * g (-t) := by
    intro t ht
    rw [deriv_comp_neg, hdf (-t) (hmaps ht), neg_mul]
  have hdg' : ∀ t ∈ Ioo (-d) (-c), deriv (fun x => g (-x)) t = -b (-t) * f (-t) := by
    intro t ht
    rw [deriv_comp_neg, hdg (-t) (hmaps ht), neg_mul]
  have hn : Tendsto (fun t : ℝ => -t) (𝓝[<] (-c)) (𝓝[>] c) := by
    apply tendsto_nhdsWithin_of_tendsto_nhds_of_eventually_within
    · simpa only [neg_neg] using
        (continuous_neg.continuousAt (x := -c)).tendsto.mono_left nhdsWithin_le_nhds
    · filter_upwards [self_mem_nhdsWithin] with t ht
      change c < -t
      simpa only [neg_neg] using neg_lt_neg (show t < -c from ht)
  have hlim' (k : ℕ) : Tendsto (iteratedDeriv k (fun t => f (-t)))
      (𝓝[<] (-c)) (𝓝 0) := by
    have heq : iteratedDeriv k (fun t => f (-t)) =
        fun t => ((-1 : ℝ) ^ k) • iteratedDeriv k f (-t) :=
      funext (iteratedDeriv_comp_neg k f)
    rw [heq]
    simpa only [Function.comp_apply, smul_zero] using
      (tendsto_const_nhds (x := ((-1 : ℝ) ^ k))).smul ((hlim k).comp hn)
  obtain ⟨W, hW, hWeq, hWflat⟩ := physical_flat_extension_from_left
    (hU.preimage continuous_neg) (show -d ∈ U' by simpa only [U', mem_preimage, neg_neg] using hd)
    (neg_lt_neg hcd) ha' hb' hf₀' hg₀' hf' hg' hdf' hdg' hlim'
  refine ⟨fun x => W (-x), hW.comp contDiff_id.neg, ?_, ?_⟩
  · intro x hx
    have hx' : -x ∈ Ioo (-d) (-c) := ⟨neg_lt_neg hx.2, neg_lt_neg hx.1⟩
    simpa only [neg_neg] using hWeq hx'
  · intro k
    rw [iteratedDeriv_comp_neg, hWflat k, smul_zero]

end ContinuousFlexibility.Radial
