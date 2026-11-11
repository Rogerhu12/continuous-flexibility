import ContinuousFlexibility.Radial.TailNaturalInterpolation
import ContinuousFlexibility.Radial.TailRegularIntervalState
import ContinuousFlexibility.Analysis.OneSidedSmoothExtension

/-!
# Joining the actual initial gap to the outward natural state

Value and flux are matched at the first mass node. Smooth extension at the
entrance is performed only after solving the original equation on the
whole one-sided tail.
-/

noncomputable section

namespace ContinuousFlexibility.Radial

open Set Filter
open scoped Topology ContDiff
open ContinuousFlexibility.Statements ContinuousFlexibility.Analysis

theorem tailGlueCut_hasDerivAt {f g : ℝ → ℝ} {c d : ℝ}
    (heq : f c = g c) (hf : HasDerivAt f d c) (hg : HasDerivAt g d c) :
    HasDerivAt (morseGlueCut c f g) d c := by
  have hL : HasDerivWithinAt (morseGlueCut c f g) d (Iic c) c :=
    hf.hasDerivWithinAt.congr_of_mem
      (fun x hx => by simp only [morseGlueCut, ite_eq_left hx]) le_rfl
  have hR : HasDerivWithinAt (morseGlueCut c f g) d (Ici c) c := by
    apply hg.hasDerivWithinAt.congr_of_mem _ le_rfl
    intro x hx
    rcases eq_or_lt_of_le hx with rfl | hlt
    · simpa only [morseGlueCut, le_refl, ite_true] using heq
    · simp only [morseGlueCut, ite_eq_right (not_le_of_gt hlt)]
  simpa only [Iic_union_Ici, hasDerivWithinAt_univ] using hL.union hR

theorem tailFirstOrderSystem_glue {p u v U V : ℝ → ℝ} {Λ a b c : ℝ}
    (hac : a ≤ c) (hcb : c < b)
    (hL : TailFirstOrderSystem p Λ u v (Icc a c))
    (hR : TailFirstOrderSystem p Λ U V (Ico c b))
    (hu : u c = U c) (hv : v c = V c) :
    TailFirstOrderSystem p Λ (morseGlueCut c u U) (morseGlueCut c v V) (Ico a b) := by
  intro x hx
  rcases lt_trichotomy x c with hlt | rfl | hgt
  · have hUg : morseGlueCut c u U =ᶠ[𝓝 x] u := by
      filter_upwards [Iio_mem_nhds hlt] with y hy
      simp only [morseGlueCut, ite_eq_left hy.le]
    have hVg : morseGlueCut c v V =ᶠ[𝓝 x] v := by
      filter_upwards [Iio_mem_nhds hlt] with y hy
      simp only [morseGlueCut, ite_eq_left hy.le]
    simpa only [morseGlueCut, ite_eq_left hlt.le] using
      (show HasDerivAt (morseGlueCut c u U) (v x / p x) x ∧
        HasDerivAt (morseGlueCut c v V) (-Λ * p x * u x) x from
        ⟨((hL x ⟨hx.1, hlt.le⟩).1).congr_of_eventuallyEq hUg,
          ((hL x ⟨hx.1, hlt.le⟩).2).congr_of_eventuallyEq hVg⟩)
  · have h₁ := hL c ⟨hac, le_rfl⟩
    have h₂ := hR c ⟨le_rfl, hcb⟩
    rw [← hv, ← hu] at h₂
    simpa only [morseGlueCut, le_refl, ite_true] using
      (show HasDerivAt (morseGlueCut c u U) (v c / p c) c ∧
        HasDerivAt (morseGlueCut c v V) (-Λ * p c * u c) c from
        ⟨tailGlueCut_hasDerivAt hu h₁.1 h₂.1, tailGlueCut_hasDerivAt hv h₁.2 h₂.2⟩)
  · have hUg : morseGlueCut c u U =ᶠ[𝓝 x] U := by
      filter_upwards [Ioi_mem_nhds hgt] with y hy
      simp only [morseGlueCut, ite_eq_right (not_le_of_gt hy)]
    have hVg : morseGlueCut c v V =ᶠ[𝓝 x] V := by
      filter_upwards [Ioi_mem_nhds hgt] with y hy
      simp only [morseGlueCut, ite_eq_right (not_le_of_gt hy)]
    simpa only [morseGlueCut, ite_eq_right (not_le_of_gt hgt)] using
      (show HasDerivAt (morseGlueCut c u U) (V x / p x) x ∧
        HasDerivAt (morseGlueCut c v V) (-Λ * p x * U x) x from
        ⟨((hR x ⟨hgt.le, hx.2⟩).1).congr_of_eventuallyEq hUg,
          ((hR x ⟨hgt.le, hx.2⟩).2).congr_of_eventuallyEq hVg⟩)

/-- The actual initial gap extends the same outward interpolant through
the entrance, without imposing a Dirichlet condition on the natural line. -/
theorem exists_tailNaturalInitialExtension {T : DeepTailData}
    (hT : DeepTailHypotheses T) {a : ℕ → ℝ}
    (hrec : ∀ n, -tailActualInteriorDiagonal T hT n * a (n + 1) =
      tailActualNodeCoupling T hT n * a n +
        tailActualNodeCoupling T hT (n + 1) * a (n + 2)) :
    ∃ u v : ℝ → ℝ,
      TailFirstOrderSystem T.p T.Λ u v (Ico T.entrance T.endpoint) ∧
      EqOn u (tailPoissonInterpolation T hT a) (Ico (T.node 0) T.endpoint) ∧
      EqOn v (tailPoissonInterpolationFlux T hT a) (Ico (T.node 0) T.endpoint) := by
  let U := tailPoissonInterpolation T hT a
  let V := tailPoissonInterpolationFlux T hT a
  have hR : TailFirstOrderSystem T.p T.Λ U V (Ico (T.node 0) T.endpoint) :=
    tailPoissonInterpolation_system_Ico hT hrec
  rcases hT.2.2.2.1 with heq | hgap
  · refine ⟨U, V, ?_, EqOn.refl _ _, EqOn.refl _ _⟩
    simpa only [heq] using hR
  · have hsub := deepTail_Icc_subset hT le_rfl (deepTail_node_lt_endpoint hT 0)
    have hp := (deepTail_contDiffOn hT).continuousOn.mono hsub
    have hp₀ := fun x hx => deepTail_pos hT x (hsub hx)
    have hsmall : T.Λ * (∫ x in T.entrance..T.node 0, T.p x) *
        (∫ x in T.entrance..T.node 0, (T.p x)⁻¹) < 1 :=
      hgap.2.1.trans_lt hT.2.2.2.2.2.1
    obtain ⟨u, v, hL, hu, hv, _⟩ := exists_tailRegularInterval_state hgap.1 hp hp₀
      hT.2.2.1.le hsmall (U (T.node 0)) (V (T.node 0))
    refine ⟨morseGlueCut (T.node 0) u U, morseGlueCut (T.node 0) v V,
      tailFirstOrderSystem_glue hgap.1.le (deepTail_node_lt_endpoint hT 0) hL hR hu hv, ?_, ?_⟩
    · intro x hx
      rcases eq_or_lt_of_le hx.1 with rfl | hlt
      · simpa only [morseGlueCut, le_refl, ite_true] using hu
      · simp only [morseGlueCut, ite_eq_right (not_le_of_gt hlt)]
    · intro x hx
      rcases eq_or_lt_of_le hx.1 with rfl | hlt
      · simpa only [morseGlueCut, le_refl, ite_true] using hv
      · simp only [morseGlueCut, ite_eq_right (not_le_of_gt hlt)]

/-- A smooth extension preserves a first-order state on the closed entrance
side as well as the open interior. -/
theorem tailFirstOrderSystem_of_smooth_extension_Ico
    {p u v U V : ℝ → ℝ} {Λ a b : ℝ} (hab : a < b)
    (h : TailFirstOrderSystem p Λ u v (Ico a b))
    (hu : EqOn U u (Ico a b)) (hv : EqOn V v (Ico a b))
    (hU : ContDiffAt ℝ ∞ U a) (hV : ContDiffAt ℝ ∞ V a) :
    TailFirstOrderSystem p Λ U V (Ico a b) := by
  intro x hx
  rcases eq_or_lt_of_le hx.1 with rfl | hlt
  · have hd := h a ⟨le_rfl, hab⟩
    rw [hv ⟨le_rfl, hab⟩, hu ⟨le_rfl, hab⟩]
    exact ⟨hasDerivAt_of_smooth_extension_Ico hab hU hu hd.1.hasDerivWithinAt,
      hasDerivAt_of_smooth_extension_Ico hab hV hv hd.2.hasDerivWithinAt⟩
  · have hUg : U =ᶠ[𝓝 x] u :=
      Filter.eventually_of_mem (Ioo_mem_nhds hlt hx.2) (fun y hy => hu ⟨hy.1.le, hy.2⟩)
    have hVg : V =ᶠ[𝓝 x] v :=
      Filter.eventually_of_mem (Ioo_mem_nhds hlt hx.2) (fun y hy => hv ⟨hy.1.le, hy.2⟩)
    rw [hv hx, hu hx]
    exact ⟨(h x hx).1.congr_of_eventuallyEq hUg, (h x hx).2.congr_of_eventuallyEq hVg⟩

/-- The actual state has a single smooth extension at the entrance, with
all node values and all physical fluxes unchanged. -/
theorem exists_tailSmoothNaturalState {T : DeepTailData}
    (hT : DeepTailHypotheses T) {a : ℕ → ℝ}
    (hrec : ∀ n, -tailActualInteriorDiagonal T hT n * a (n + 1) =
      tailActualNodeCoupling T hT n * a n +
        tailActualNodeCoupling T hT (n + 1) * a (n + 2)) :
    ∃ u v : ℝ → ℝ,
      ContDiffOn ℝ ∞ u (Iio T.endpoint) ∧ ContDiffOn ℝ ∞ v (Iio T.endpoint) ∧
      TailFirstOrderSystem T.p T.Λ u v (Ico T.entrance T.endpoint) ∧
      EqOn u (tailPoissonInterpolation T hT a) (Ico (T.node 0) T.endpoint) ∧
      EqOn v (tailPoissonInterpolationFlux T hT a) (Ico (T.node 0) T.endpoint) := by
  obtain ⟨u, v, h, hu, hv⟩ := exists_tailNaturalInitialExtension hT hrec
  have hs := tailFirstOrderSystemWithin_contDiffOn
    (uniqueDiffOn_Ico T.entrance T.endpoint) (deepTail_contDiffOn hT)
    (fun x hx => (deepTail_pos hT x hx).ne') h.within
  obtain ⟨U, hU, hUs⟩ := exists_contDiffOn_Iio_extension_of_Ico hT.1 hs.1
  obtain ⟨V, hV, hVs⟩ := exists_contDiffOn_Iio_extension_of_Ico hT.1 hs.2
  have hsub : Ico (T.node 0) T.endpoint ⊆ Ico T.entrance T.endpoint :=
    fun _ hx => ⟨hT.2.1.trans hx.1, hx.2⟩
  exact ⟨U, V, hUs, hVs,
    tailFirstOrderSystem_of_smooth_extension_Ico hT.1 h hU hV
      (hUs.contDiffAt (isOpen_Iio.mem_nhds hT.1))
      (hVs.contDiffAt (isOpen_Iio.mem_nhds hT.1)),
    (hU.mono hsub).trans hu, (hV.mono hsub).trans hv⟩

end ContinuousFlexibility.Radial
