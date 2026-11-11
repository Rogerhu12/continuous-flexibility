import ContinuousFlexibility.Radial.TailPositiveResolvent
import ContinuousFlexibility.Radial.TailTruncationConvergence

/-!
# Convergence of the actual deep-tail inverses

The positive Friedrichs resolvents converge by exhaustion of the closed form.
The elementary resolvent identity transfers this convergence to the spectral
parameter, using the uniform inverse bound. Restricting a source to a finite
Dirichlet interval preserves its pairings with the entire form domain.
-/

noncomputable section

namespace ContinuousFlexibility.Radial

open Set Filter MeasureTheory
open scoped Topology InnerProductSpace
open ContinuousFlexibility.Statements

/-- The positive resolvent identity expressed using an inverse of the shifted
Friedrichs relation. This includes the Dirichlet boundary conditions. -/
theorem tailInverse_positive_identity (T : DeepTailData) (c : ℝ)
    (G : DeepTailL2 T →L[ℝ] DeepTailL2 T)
    (huniq : ∀ u f, TailFriedrichsGraph T c u (f + T.Λ • u) → G f = u)
    (q : DeepTailL2 T) :
    G (q - (T.Λ + 1) • tailPositiveResolvent T c q) =
      tailPositiveResolvent T c q := by
  apply huniq
  have he : q - (T.Λ + 1) • tailPositiveResolvent T c q +
      T.Λ • tailPositiveResolvent T c q = q - tailPositiveResolvent T c q := by
    module
  rw [he]
  exact tailPositiveResolvent_graph T c q

/-- Uniform spectral inverse bounds and convergence of the positive resolvents
give strong convergence of the spectral inverses on the fixed physical space. -/
theorem tailInverse_truncation_tendsto {T : DeepTailData} (hT : DeepTailHypotheses T)
    (G : DeepTailL2 T →L[ℝ] DeepTailL2 T)
    (Gₙ : ℕ → DeepTailL2 T →L[ℝ] DeepTailL2 T)
    (hG : ∀ f, TailFriedrichsGraph T T.endpoint (G f) (f + T.Λ • G f))
    (huniq : ∀ n u f, TailFriedrichsGraph T (T.node (n + 1)) u
      (f + T.Λ • u) → Gₙ n f = u)
    {M : ℝ} (hbound : ∀ n, ‖Gₙ n‖ ≤ M) (f : DeepTailL2 T) :
    Tendsto (fun n => Gₙ n f) atTop (𝓝 (G f)) := by
  let q : DeepTailL2 T := f + (T.Λ + 1) • G f
  have hq : tailPositiveResolvent T T.endpoint q = G f := by
    have h := (tailFriedrichsGraph_iff_positiveResolvent T T.endpoint _ _).mp (hG f)
    have he : f + T.Λ • G f + G f = q := by dsimp only [q]; module
    rwa [he] at h
  let r : ℕ → DeepTailL2 T :=
    fun n => tailPositiveResolvent T (T.node (n + 1)) q - G f
  have hr : Tendsto r atTop (𝓝 0) := by
    have h := (tailPositiveResolvent_truncation_tendsto hT q).sub
      (tendsto_const_nhds (x := G f))
    simpa only [hq, sub_self] using h
  have hGr : Tendsto (fun n => Gₙ n (r n)) atTop (𝓝 0) :=
    tail_bounded_apply_tendsto_zero Gₙ hbound hr
  have heq (n : ℕ) : Gₙ n f - G f = r n + (T.Λ + 1) • Gₙ n (r n) := by
    have hid := tailInverse_positive_identity T (T.node (n + 1)) (Gₙ n)
      (huniq n) q
    have hsource : q - (T.Λ + 1) • tailPositiveResolvent T (T.node (n + 1)) q =
        f - (T.Λ + 1) • r n := by dsimp only [q, r]; module
    rw [hsource, map_sub, map_smul] at hid
    calc
      Gₙ n f - G f = (Gₙ n f - (T.Λ + 1) • Gₙ n (r n)) +
          (T.Λ + 1) • Gₙ n (r n) - G f := by abel
      _ = r n + (T.Λ + 1) • Gₙ n (r n) := by
        rw [hid]
        dsimp only [r]
        abel
  have hz : Tendsto (fun n => Gₙ n f - G f) atTop (𝓝 0) := by
    have h := hr.add (hGr.const_smul (T.Λ + 1))
    simpa only [← heq, smul_zero, add_zero] using h
  exact tendsto_sub_nhds_zero_iff.mp hz

theorem tailIndicator_inner_form {T : DeepTailData} {c : ℝ}
    (f : DeepTailL2 T) {p : DeepTailL2 T × DeepTailL2 T}
    (hp : p ∈ TailFormLift T c) :
    ⟪tailIndicator T (Iio c) measurableSet_Iio f, p.1⟫_ℝ = ⟪f, p.1⟫_ℝ := by
  rw [L2.inner_def, L2.inner_def]
  apply integral_congr_ae
  filter_upwards [tailIndicator_coeFn T (Iio c) measurableSet_Iio f,
    (tailFormLift_ae_zero_outside hp).1] with x hx hz
  rw [hx]
  by_cases hxc : x < c
  · rw [indicator_of_mem hxc]
  · have hv : p.1 x = 0 := hz (fun h => hxc h.2)
    rw [indicator_of_notMem hxc, hv, inner_zero_right, inner_zero_right]

/-- Source restriction affects no test pairing in the closed Dirichlet form. -/
theorem tailFriedrichsGraph_restrict_source (T : DeepTailData) (c : ℝ)
    (u f : DeepTailL2 T) :
    TailFriedrichsGraph T c u
      (tailIndicator T (Iio c) measurableSet_Iio f + T.Λ • u) ↔
    TailFriedrichsGraph T c u (f + T.Λ • u) := by
  constructor
  · rintro ⟨d, hd, he⟩
    refine ⟨d, hd, fun p hp => ?_⟩
    simpa only [inner_add_left, tailIndicator_inner_form f hp] using he p hp
  · rintro ⟨d, hd, he⟩
    refine ⟨d, hd, fun p hp => ?_⟩
    simpa only [inner_add_left, tailIndicator_inner_form f hp] using he p hp

theorem tailInverse_restrict_source (T : DeepTailData) (c : ℝ)
    (G : DeepTailL2 T →L[ℝ] DeepTailL2 T)
    (hG : ∀ f, TailFriedrichsGraph T c (G f) (f + T.Λ • G f))
    (huniq : ∀ u f, TailFriedrichsGraph T c u (f + T.Λ • u) → G f = u)
    (f : DeepTailL2 T) :
    G (tailIndicator T (Iio c) measurableSet_Iio f) = G f :=
  huniq (G f) _ ((tailFriedrichsGraph_restrict_source T c (G f) f).mpr (hG f))

/-- The source restrictions in the frozen statement can be used without an
extra limiting argument: each finite inverse already ignores the removed source. -/
theorem tailInverse_restricted_truncation_tendsto {T : DeepTailData}
    (hT : DeepTailHypotheses T) (G : DeepTailL2 T →L[ℝ] DeepTailL2 T)
    (Gₙ : ℕ → DeepTailL2 T →L[ℝ] DeepTailL2 T)
    (hG : ∀ f, TailFriedrichsGraph T T.endpoint (G f) (f + T.Λ • G f))
    (hGn : ∀ n f, TailFriedrichsGraph T (T.node (n + 1)) (Gₙ n f)
      (f + T.Λ • Gₙ n f))
    (huniq : ∀ n u f, TailFriedrichsGraph T (T.node (n + 1)) u
      (f + T.Λ • u) → Gₙ n f = u)
    {M : ℝ} (hbound : ∀ n, ‖Gₙ n‖ ≤ M) (f : DeepTailL2 T) :
    Tendsto (fun n => Gₙ n (tailIndicator T (Iio (T.node (n + 1)))
      measurableSet_Iio f)) atTop (𝓝 (G f)) := by
  simpa only [tailInverse_restrict_source T _ _ (hGn _) (huniq _)] using
    tailInverse_truncation_tendsto hT G Gₙ hG huniq hbound f

end ContinuousFlexibility.Radial
