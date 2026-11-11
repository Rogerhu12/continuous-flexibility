import ContinuousFlexibility.Radial.TailHighEnergyEstimate
import ContinuousFlexibility.Radial.TailTestPairing

/-!
# The high-mode inequality in the actual weighted space

Finite mass--resistance estimates pass to compact tests on the complete tail.
The first mass interval is controlled by the Dirichlet entrance when there is
no initial gap; every other mass interval is controlled by its weighted mean.
-/

noncomputable section

namespace ContinuousFlexibility.Radial

open Set Filter MeasureTheory
open scoped Topology ContDiff InnerProductSpace
open ContinuousFlexibility.Statements

theorem tail_integral_eq_interval_of_support {T : DeepTailData}
    (hT : DeepTailHypotheses T) {c : ℝ} (hc : T.entrance ≤ c) (hc' : c ≤ T.endpoint)
    {f : ℝ → ℝ} (hs : Function.support f ⊆ Ioo T.entrance c) :
    (∫ x, f x ∂deepTailMeasure T) = ∫ x in T.entrance..c, T.p x * f x := by
  have hp : ContDiffOn ℝ ∞ T.p (Ioo T.entrance T.endpoint) :=
    (deepTail_contDiffOn hT).mono Ioo_subset_Ico_self
  have hpos : ∀ x ∈ Ioo T.entrance T.endpoint, 0 < T.p x :=
    fun x hx => deepTail_pos hT x (Ioo_subset_Ico_self hx)
  rw [tail_integral_density hp hpos f, intervalIntegral.integral_of_le hc,
    integral_Ioc_eq_integral_Ioo]
  apply setIntegral_eq_of_subset_of_forall_sdiff_eq_zero measurableSet_Ioo
    (fun x hx => ⟨hx.1, hx.2.trans_le hc'⟩)
  intro x hx
  have hf : f x = 0 := by
    by_contra hf
    exact hx.2 (hs hf)
  rw [hf, mul_zero]

theorem tail_norm_sq_of_ae {T : DeepTailData} (u : DeepTailL2 T) {φ : ℝ → ℝ}
    (hφ : (u : ℝ → ℝ) =ᵐ[deepTailMeasure T] φ) :
    ‖u‖ ^ 2 = ∫ x, φ x ^ 2 ∂deepTailMeasure T := by
  rw [← real_inner_self_eq_norm_sq, L2.inner_def]
  apply integral_congr_ae
  filter_upwards [hφ] with x hx
  simp only [hx, RCLike.inner_apply, conj_trivial, pow_two]

theorem tail_compact_high_energy_bound {T : DeepTailData} (hT : DeepTailHypotheses T)
    {u : ℝ → ℝ} (hu : ContDiff ℝ 1 u) (hcompact : HasCompactSupport u)
    (hs : tsupport u ⊆ Ioo T.entrance T.endpoint)
    (hz : ∀ n, ∃ z ∈ Icc (T.node n) (T.massEnd n), u z = 0) :
    T.Λ * (∫ x, u x ^ 2 ∂deepTailMeasure T) ≤
      5 * T.η * ∫ x, deriv u x ^ 2 ∂deepTailMeasure T := by
  obtain ⟨n, hn⟩ := deepTail_compact_subset_some_cut hT hcompact hs
  have hsq : Function.support (fun x => u x ^ 2) ⊆ Ioo T.entrance (T.node (n + 1)) := by
    intro x hx
    apply hn
    apply subset_tsupport u
    intro hzero
    exact hx (by simp [hzero])
  have hdsq : Function.support (fun x => deriv u x ^ 2) ⊆
      Ioo T.entrance (T.node (n + 1)) := by
    intro x hx
    apply hn
    apply support_deriv_subset
    intro hzero
    exact hx (by simp [hzero])
  rw [tail_integral_eq_interval_of_support hT (deepTail_entrance_le_node hT (n + 1))
      (deepTail_node_lt_endpoint hT (n + 1)).le hsq,
    tail_integral_eq_interval_of_support hT (deepTail_entrance_le_node hT (n + 1))
      (deepTail_node_lt_endpoint hT (n + 1)).le hdsq]
  exact tail_finite_high_energy_bound hT hu (Nat.succ_pos n) (fun k _ => hz k)

/-- All mass intervals have a zero once the active weighted means vanish.
The omitted first mean is replaced by the genuine entrance value. -/
theorem tail_mass_zeros_of_active_means {T : DeepTailData} (hT : DeepTailHypotheses T)
    {u : ℝ → ℝ} (hu : Continuous u) (hentrance : u T.entrance = 0)
    (hmean : ∀ n, tailFirstMassIndex T ≤ n →
      (∫ x in T.node n..T.massEnd n, T.p x * u x) = 0) :
    ∀ n, ∃ z ∈ Icc (T.node n) (T.massEnd n), u z = 0 := by
  intro n
  by_cases hn : tailFirstMassIndex T ≤ n
  · have hs := deepTail_Icc_subset hT (deepTail_entrance_le_node hT n)
      (deepTail_massEnd_lt_endpoint hT n)
    exact tail_exists_zero_of_weighted_mean_zero (deepTail_node_lt_massEnd hT n)
      ((deepTail_contDiffOn hT).continuousOn.mono hs)
      (fun x hx => deepTail_pos hT x (hs hx)) hu.continuousOn (hmean n hn)
  · have hn0 : n = 0 := by have := tailFirstMassIndex_le_one T; omega
    subst n
    have he : T.node 0 = T.entrance := by
      by_contra he
      rw [tailFirstMassIndex_eq_zero he] at hn
      exact hn le_rfl
    refine ⟨T.entrance, ?_, hentrance⟩
    rw [← he]
    exact ⟨le_rfl, (deepTail_node_lt_massEnd hT 0).le⟩

/-- The high-mode estimate for any smooth compact core representative. -/
theorem tail_core_high_norm_bound {T : DeepTailData} (hT : DeepTailHypotheses T)
    {u d : DeepTailL2 T} {φ : ℝ → ℝ} (hφ : ContDiff ℝ ∞ φ)
    (hcφ : HasCompactSupport φ) (hsφ : tsupport φ ⊆ Ioo T.entrance T.endpoint)
    (hu : (u : ℝ → ℝ) =ᵐ[deepTailMeasure T] φ)
    (hd : (d : ℝ → ℝ) =ᵐ[deepTailMeasure T] deriv φ)
    (hmean : ∀ n, tailFirstMassIndex T ≤ n →
      (∫ x in T.node n..T.massEnd n, T.p x * φ x) = 0) :
    T.Λ * ‖u‖ ^ 2 ≤ 5 * T.η * ‖d‖ ^ 2 := by
  have hentrance : φ T.entrance = 0 :=
    image_eq_zero_of_notMem_tsupport (fun h => lt_irrefl _ (hsφ h).1)
  rw [tail_norm_sq_of_ae u hu, tail_norm_sq_of_ae d hd]
  exact tail_compact_high_energy_bound hT (hφ.of_le (by simp)) hcφ hsφ
    (tail_mass_zeros_of_active_means hT hφ.continuous hentrance hmean)

end ContinuousFlexibility.Radial
