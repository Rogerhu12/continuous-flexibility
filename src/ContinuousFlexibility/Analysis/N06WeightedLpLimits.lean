module

public import ContinuousFlexibility.Analysis.N06IntervalPrimitiveLp
public import ContinuousFlexibility.Radial.R11bModeL2

/-!
# Limits of weighted L2 integrals on the unit interval

A coefficient continuous on the closed interval acts continuously on L2.
Weighted square integrals are then ordinary L2 inner products, including
the odd powers of the cylinder weight used by the cubic graph estimate.
-/

@[expose] public section

noncomputable section

namespace ContinuousFlexibility.Analysis

open Set Filter MeasureTheory
open scoped ContDiff Topology ENNReal

set_option backward.isDefEq.respectTransparency false

/-- Continuous coefficients preserve strong L2 convergence on the unit interval. -/
theorem n06_tendsto_unit_toLp_mul_continuous {ι : Type*} {l : Filter ι}
    {f : ι → ℝ → ℝ} {g p : ℝ → ℝ}
    (hf : ∀ i, MemLp (f i) 2 (volume.restrict (Ioo (0 : ℝ) 1)))
    (hg : MemLp g 2 (volume.restrict (Ioo (0 : ℝ) 1)))
    (hp : Continuous p)
    (hlim : Tendsto (fun i => (hf i).toLp (f i)) l (𝓝 (hg.toLp g))) :
    Tendsto (fun i => (n06_interval_memLp_mul_continuous (hf i) hp).toLp
        (fun x => p x * f i x)) l
      (𝓝 ((n06_interval_memLp_mul_continuous hg hp).toLp (fun x => p x * g x))) := by
  obtain ⟨C, hC⟩ := isCompact_Icc.bddAbove_image
    (show ContinuousOn (fun x => ‖p x‖) (Icc (0 : ℝ) 1) from hp.norm.continuousOn)
  have hb (x : ℝ) (hx : x ∈ Icc (0 : ℝ) 1) : ‖p x‖ ≤ C :=
    hC ⟨x, hx, rfl⟩
  have hpf (i : ι) : MemLp (fun x => p x * f i x) 2
      (volume.restrict (Ioo (0 : ℝ) 1)) := n06_interval_memLp_mul_continuous (hf i) hp
  have hpg : MemLp (fun x => p x * g x) 2
      (volume.restrict (Ioo (0 : ℝ) 1)) := n06_interval_memLp_mul_continuous hg hp
  have hnorm (i : ι) :
      ‖(hpf i).toLp (fun x => p x * f i x) - hpg.toLp (fun x => p x * g x)‖ ≤
        C * ‖(hf i).toLp (f i) - hg.toLp g‖ := by
    apply Lp.norm_le_mul_norm_of_ae_le_mul
    filter_upwards [Lp.coeFn_sub ((hpf i).toLp (fun x => p x * f i x))
      (hpg.toLp (fun x => p x * g x)),
      Lp.coeFn_sub ((hf i).toLp (f i)) (hg.toLp g),
      (hpf i).coeFn_toLp, hpg.coeFn_toLp, (hf i).coeFn_toLp, hg.coeFn_toLp,
      ae_restrict_mem measurableSet_Ioo] with x hout hin hfx hgx hux hvx hx
    rw [hout, hin]
    simp only [Pi.sub_apply, hfx, hgx, hux, hvx]
    rw [← mul_sub, norm_mul]
    exact mul_le_mul_of_nonneg_right (hb x (mem_Icc_of_Ioo hx)) (norm_nonneg _)
  apply tendsto_iff_norm_sub_tendsto_zero.mpr
  apply squeeze_zero (fun _ => norm_nonneg _) hnorm
  simpa only [mul_zero] using
    (tendsto_iff_norm_sub_tendsto_zero.mp hlim).const_mul C

/-- The weighted square integral is an inner product in the original interval L2. -/
theorem n06_unit_weighted_square_eq_inner {f p : ℝ → ℝ}
    (hf : MemLp f 2 (volume.restrict (Ioo (0 : ℝ) 1))) (hp : Continuous p) :
    (∫ x in (0 : ℝ)..1, p x * f x ^ 2) =
      inner ℝ ((n06_interval_memLp_mul_continuous hf hp).toLp (fun x => p x * f x))
        (hf.toLp f) := by
  rw [ContinuousFlexibility.Radial.r11b_real_inner_toLp_eq_integral,
    n06_unit_intervalIntegral_eq]
  apply integral_congr_ae
  exact Eventually.of_forall fun x => by ring

/-- Every continuous weighted square integral converges under strong L2 convergence. -/
theorem n06_tendsto_unit_weighted_square {ι : Type*} {l : Filter ι}
    {f : ι → ℝ → ℝ} {g p : ℝ → ℝ}
    (hf : ∀ i, MemLp (f i) 2 (volume.restrict (Ioo (0 : ℝ) 1)))
    (hg : MemLp g 2 (volume.restrict (Ioo (0 : ℝ) 1)))
    (hp : Continuous p)
    (hlim : Tendsto (fun i => (hf i).toLp (f i)) l (𝓝 (hg.toLp g))) :
    Tendsto (fun i => ∫ x in (0 : ℝ)..1, p x * f i x ^ 2) l
      (𝓝 (∫ x in (0 : ℝ)..1, p x * g x ^ 2)) := by
  have hmul := n06_tendsto_unit_toLp_mul_continuous hf hg hp hlim
  have hi := hmul.inner hlim (𝕜 := ℝ)
  have hseq :
      (fun i => inner ℝ
        ((n06_interval_memLp_mul_continuous (hf i) hp).toLp (fun x => p x * f i x))
        ((hf i).toLp (f i))) =
        (fun i => ∫ x in (0 : ℝ)..1, p x * f i x ^ 2) :=
    funext fun i => (n06_unit_weighted_square_eq_inner (hf i) hp).symm
  have htarget : inner ℝ
      ((n06_interval_memLp_mul_continuous hg hp).toLp (fun x => p x * g x))
      (hg.toLp g) = ∫ x in (0 : ℝ)..1, p x * g x ^ 2 :=
    (n06_unit_weighted_square_eq_inner hg hp).symm
  rw [hseq, htarget] at hi
  exact hi

/-- The unweighted square integral also converges in strong L2. -/
theorem n06_tendsto_unit_square {ι : Type*} {l : Filter ι}
    {f : ι → ℝ → ℝ} {g : ℝ → ℝ}
    (hf : ∀ i, MemLp (f i) 2 (volume.restrict (Ioo (0 : ℝ) 1)))
    (hg : MemLp g 2 (volume.restrict (Ioo (0 : ℝ) 1)))
    (hlim : Tendsto (fun i => (hf i).toLp (f i)) l (𝓝 (hg.toLp g))) :
    Tendsto (fun i => ∫ x in (0 : ℝ)..1, f i x ^ 2) l
      (𝓝 (∫ x in (0 : ℝ)..1, g x ^ 2)) := by
  simpa only [one_mul] using
    n06_tendsto_unit_weighted_square hf hg
      (p := fun _ => (1 : ℝ)) continuous_const hlim

end ContinuousFlexibility.Analysis
