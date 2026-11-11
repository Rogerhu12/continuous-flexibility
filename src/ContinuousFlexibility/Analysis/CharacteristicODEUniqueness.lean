import ContinuousFlexibility.Scalar.Conservation
import Mathlib.Analysis.ODE.ExistUnique
import Mathlib.Analysis.Calculus.MeanValue
import Mathlib.Topology.Order.ProjIcc

/-!
# Uniqueness for ordinary characteristic trajectories

The ordinary-flow specification gives the ODE on an open radial interval
and continuity on its closure.  A continuous right-hand side supplies the
missing endpoint derivative by the fundamental theorem of calculus.  The
angular Lipschitz constant is needed only on the compact range of the two
trajectories being compared.
-/

noncomputable section

namespace ContinuousFlexibility.Analysis

open Set Filter MeasureTheory
open scoped Topology ContDiff NNReal

set_option backward.isDefEq.respectTransparency false

/-- FTC recovers the right derivative at the initial endpoint from the
interior derivative and the continuous closed-interval data. -/
theorem hasDerivWithinAt_right_of_continuousOn_Icc
    {a b : ℝ} {f d : ℝ → ℝ} (hab : a < b)
    (hf : ContinuousOn f (Icc a b)) (hd : ContinuousOn d (Icc a b))
    (hf' : ∀ t ∈ Ioo a b, HasDerivAt f (d t) t) :
    HasDerivWithinAt f (d a) (Ici a) a := by
  let de : ℝ → ℝ := IccExtend hab.le ((Icc a b).domRestrict d)
  have hde : Continuous de := hd.domRestrict.Icc_extend'
  have heq : EqOn de d (Icc a b) := by
    intro t ht
    exact IccExtend_of_mem hab.le _ ht
  have hprimitive (t : ℝ) (ht : t ∈ Icc a b) :
      f t = f a + ∫ r in a..t, de r := by
    have hFTC := intervalIntegral.integral_eq_sub_of_hasDerivAt_of_le (f' := de) ht.1
      (hf.mono (Icc_subset_Icc le_rfl ht.2))
      (fun r hr => by
        have hrab : r ∈ Ioo a b := ⟨hr.1, hr.2.trans_le ht.2⟩
        simpa only [heq ⟨hrab.1.le, hrab.2.le⟩] using hf' r hrab)
      (hde.intervalIntegrable a t)
    linarith only [hFTC]
  have hFTC : HasDerivAt (fun t => f a + ∫ r in a..t, de r) (d a) a := by
    have h := (intervalIntegral.integral_hasDerivAt_right (hde.intervalIntegrable a a)
      hde.aestronglyMeasurable.stronglyMeasurableAtFilter hde.continuousAt).const_add (f a)
    exact (h.congr_deriv (heq (left_mem_Icc.mpr hab.le))).congr_of_eventuallyEq
      (Eventually.of_forall fun t => by simp only [Pi.add_apply])
  apply hFTC.hasDerivWithinAt.congr_of_eventuallyEq
  · filter_upwards [Icc_mem_nhdsGE hab] with t ht
    exact hprimitive t ht
  · simp

/-- Every right derivative required by the closed-interval ODE uniqueness
theorem follows from the endpoint FTC and the ordinary interior ODE. -/
theorem hasDerivWithinAt_Ico_of_continuousOn_Icc
    {a b : ℝ} {f d : ℝ → ℝ} (hab : a < b)
    (hf : ContinuousOn f (Icc a b)) (hd : ContinuousOn d (Icc a b))
    (hf' : ∀ t ∈ Ioo a b, HasDerivAt f (d t) t)
    {t : ℝ} (ht : t ∈ Ico a b) :
    HasDerivWithinAt f (d t) (Ici t) t := by
  rcases eq_or_lt_of_le ht.1 with h | h
  · subst t
    exact hasDerivWithinAt_right_of_continuousOn_Icc hab hf hd hf'
  · exact (hf' t ⟨h, ht.2⟩).hasDerivWithinAt

/-- A continuous angular derivative has a uniform Lipschitz constant on
each closed radial/angular rectangle. -/
theorem exists_lipschitzOnWith_of_continuous_angular_derivative
    {a b l u : ℝ} {v : ℝ → ℝ → ℝ} {d : PolarPoint → ℝ}
    (hderiv : ∀ t ∈ Icc a b, ∀ θ ∈ Icc l u,
      HasDerivAt (v t) (d (t, θ)) θ)
    (hd : ContinuousOn d (Icc a b ×ˢ Icc l u)) :
    ∃ K : ℝ≥0, ∀ t ∈ Icc a b, LipschitzOnWith K (v t) (Icc l u) := by
  obtain ⟨B, hB⟩ := (isCompact_Icc.prod isCompact_Icc).exists_bound_of_continuousOn hd
  refine ⟨⟨max B 0, le_max_right _ _⟩, fun t ht => ?_⟩
  apply (convex_Icc l u).lipschitzOnWith_of_nnnorm_deriv_le
    (fun θ hθ => (hderiv t ht θ hθ).differentiableAt)
  intro θ hθ
  apply NNReal.coe_le_coe.mp
  change ‖deriv (v t) θ‖ ≤ max B 0
  rw [(hderiv t ht θ hθ).deriv]
  exact (hB (t, θ) ⟨ht, hθ⟩).trans (le_max_left _ _)

/-- Ordinary trajectories are unique when the vector field and its actual
angular derivative are continuous on the closed radial strip.  No global
bound in the angular coordinate is required. -/
theorem ode_solution_unique_of_continuous_angular_derivative
    {a b : ℝ} {v : ℝ → ℝ → ℝ} {d : PolarPoint → ℝ} {f g : ℝ → ℝ}
    (hab : a < b)
    (hv : ContinuousOn (fun p : PolarPoint => v p.1 p.2) (Icc a b ×ˢ univ))
    (hderiv : ∀ t ∈ Icc a b, ∀ θ, HasDerivAt (v t) (d (t, θ)) θ)
    (hd : ContinuousOn d (Icc a b ×ˢ univ))
    (hf : ContinuousOn f (Icc a b))
    (hf' : ∀ t ∈ Ioo a b, HasDerivAt f (v t (f t)) t)
    (hg : ContinuousOn g (Icc a b))
    (hg' : ∀ t ∈ Ioo a b, HasDerivAt g (v t (g t)) t)
    (ha : f a = g a) : EqOn f g (Icc a b) := by
  obtain ⟨Bf, hBf⟩ := isCompact_Icc.exists_bound_of_continuousOn hf
  obtain ⟨Bg, hBg⟩ := isCompact_Icc.exists_bound_of_continuousOn hg
  let R : ℝ := |Bf| + |Bg| + 1
  have hfr (t : ℝ) (ht : t ∈ Icc a b) : f t ∈ Icc (-R) R := by
    apply abs_le.mp
    have hb : |f t| ≤ Bf := by simpa only [Real.norm_eq_abs] using hBf t ht
    have habs := le_abs_self Bf
    have hnonneg := abs_nonneg Bg
    dsimp [R]
    linarith
  have hgr (t : ℝ) (ht : t ∈ Icc a b) : g t ∈ Icc (-R) R := by
    apply abs_le.mp
    have hb : |g t| ≤ Bg := by simpa only [Real.norm_eq_abs] using hBg t ht
    have habs := le_abs_self Bg
    have hnonneg := abs_nonneg Bf
    dsimp [R]
    linarith
  obtain ⟨K, hK⟩ := exists_lipschitzOnWith_of_continuous_angular_derivative
    (l := -R) (u := R) (fun t ht θ _ => hderiv t ht θ)
    (hd.mono (fun p hp => ⟨hp.1, mem_univ _⟩))
  have hdf : ContinuousOn (fun t => v t (f t)) (Icc a b) :=
    hv.comp (continuousOn_id.prodMk hf) (fun t ht => ⟨ht, mem_univ _⟩)
  have hdg : ContinuousOn (fun t => v t (g t)) (Icc a b) :=
    hv.comp (continuousOn_id.prodMk hg) (fun t ht => ⟨ht, mem_univ _⟩)
  exact ODE_solution_unique_of_mem_Icc_right
    (s := fun _ => Icc (-R) R)
    (fun t ht => hK t ⟨ht.1, ht.2.le⟩) hf
    (fun t ht => hasDerivWithinAt_Ico_of_continuousOn_Icc hab hf hdf hf' ht)
    (fun t ht => hfr t ⟨ht.1, ht.2.le⟩) hg
    (fun t ht => hasDerivWithinAt_Ico_of_continuousOn_Icc hab hg hdg hg' ht)
    (fun t ht => hgr t ⟨ht.1, ht.2.le⟩) ha

/-- A continuous radial coefficient can multiply a smooth angular field
without losing the angular regularity needed for uniqueness.  This form
allows the square-root coefficient at a turning radius to vanish. -/
theorem ode_solution_unique_of_separated_radial_speed
    {a b : ℝ} {A B : PolarPoint → ℝ} {k f g : ℝ → ℝ}
    (hab : a < b) (hk : ContinuousOn k (Icc a b))
    (hA : ∀ p ∈ Icc a b ×ˢ (univ : Set ℝ), ContDiffAt ℝ ∞ A p)
    (hB : ∀ p ∈ Icc a b ×ˢ (univ : Set ℝ), ContDiffAt ℝ ∞ B p)
    (hf : ContinuousOn f (Icc a b))
    (hf' : ∀ t ∈ Ioo a b,
      HasDerivAt f (A (t, f t) - k t * B (t, f t)) t)
    (hg : ContinuousOn g (Icc a b))
    (hg' : ∀ t ∈ Ioo a b,
      HasDerivAt g (A (t, g t) - k t * B (t, g t)) t)
    (ha : f a = g a) : EqOn f g (Icc a b) := by
  have hcA : ContinuousOn A (Icc a b ×ˢ (univ : Set ℝ)) :=
    fun p hp => (hA p hp).continuousAt.continuousWithinAt
  have hcB : ContinuousOn B (Icc a b ×ˢ (univ : Set ℝ)) :=
    fun p hp => (hB p hp).continuousAt.continuousWithinAt
  have hck : ContinuousOn (fun p : PolarPoint => k p.1) (Icc a b ×ˢ univ) :=
    hk.comp continuousOn_fst (fun p hp => hp.1)
  have hcAθ : ContinuousOn (angularPartial A) (Icc a b ×ˢ (univ : Set ℝ)) :=
    fun p hp => (contDiffAt_angularPartial (hA p hp) (m := ∞) (by simp)).continuousAt.continuousWithinAt
  have hcBθ : ContinuousOn (angularPartial B) (Icc a b ×ˢ (univ : Set ℝ)) :=
    fun p hp => (contDiffAt_angularPartial (hB p hp) (m := ∞) (by simp)).continuousAt.continuousWithinAt
  apply ode_solution_unique_of_continuous_angular_derivative
    (v := fun t x => A (t, x) - k t * B (t, x))
    (d := fun p => angularPartial A p - k p.1 * angularPartial B p)
    hab (hcA.sub (hck.mul hcB)) ?_ (hcAθ.sub (hck.mul hcBθ)) hf hf' hg hg' ha
  intro t ht θ
  have hAp := (hA (t, θ) ⟨ht, mem_univ _⟩).differentiableAt (by simp)
  have hBp := (hB (t, θ) ⟨ht, mem_univ _⟩).differentiableAt (by simp)
  exact ((hasDerivAt_angular_slice hAp).sub
    ((hasDerivAt_angular_slice hBp).const_mul (k t))).congr_of_eventuallyEq
      (Eventually.of_forall fun x => by simp only [Pi.sub_apply, Pi.mul_apply])

end ContinuousFlexibility.Analysis
