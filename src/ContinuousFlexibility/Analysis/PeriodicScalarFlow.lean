import ContinuousFlexibility.Analysis.ScalarFlowExistence
import Mathlib.Analysis.Calculus.MeanValue
import Mathlib.Analysis.Normed.Group.Bounded
import Mathlib.Topology.Instances.Real.Lemmas

/-!
# Actual flows of periodic scalar vector fields

A compact parameter set and one angular period give bounds on every real
angle. Applying this to a vector field and its actual angular derivative
supplies the boundedness and Lipschitz hypotheses of Picard--Lindelof.

The resulting trajectories satisfy the ODE on the full closed time
interval. Uniqueness then proves that a full turn of the initial angle
gives a full turn of the solution, independently of the choices made by
the existence theorem.
-/

noncomputable section

namespace ContinuousFlexibility.Analysis

open Set Filter
open scoped Topology NNReal

/-- A continuous periodic family has a uniform bound over a compact set
of external parameters and all real angles. -/
theorem exists_norm_bound_periodic_compact
    {P E : Type*} [TopologicalSpace P] [NormedAddCommGroup E]
    {S : Set P} {F : P × ℝ → E} {T : ℝ}
    (hS : IsCompact S) (hT : T ≠ 0)
    (hF : ContinuousOn F (S ×ˢ univ))
    (hperiod : ∀ p ∈ S, Function.Periodic (fun θ => F (p, θ)) T) :
    ∃ M : ℝ, 0 ≤ M ∧ ∀ p ∈ S, ∀ θ, ‖F (p, θ)‖ ≤ M := by
  obtain ⟨M, hM⟩ := (hS.prod (isCompact_uIcc : IsCompact (uIcc (0 : ℝ) T))).exists_bound_of_continuousOn
      (hF.mono (fun _ hp => ⟨hp.1, mem_univ _⟩))
  refine ⟨max M 0, le_max_right _ _, ?_⟩
  intro p hp θ
  have hr : F (p, θ) ∈ Set.range (fun φ => F (p, φ)) := ⟨θ, rfl⟩
  rw [← (hperiod p hp).image_uIcc hT 0] at hr
  obtain ⟨φ, hφ, heq⟩ := hr
  have hφ' : φ ∈ uIcc (0 : ℝ) T := by simpa only [zero_add] using hφ
  calc
    ‖F (p, θ)‖ = ‖F (p, φ)‖ := congrArg norm heq.symm
    _ ≤ M := hM (p, φ) ⟨hp, hφ'⟩
    _ ≤ max M 0 := le_max_left _ _

/-- Uniform angular Lipschitz bounds give uniqueness for actual scalar
solutions on the closed interval, including both endpoint values. -/
theorem eqOn_scalarFlow_of_same_initial
    {F : ℝ → ℝ → ℝ} {u v : ℝ → ℝ} {a b : ℝ} {K : ℝ≥0}
    (hF : ∀ t ∈ Icc a b, LipschitzWith K (F t))
    (hdu : ∀ t ∈ Icc a b,
      HasDerivWithinAt u (F t (u t)) (Icc a b) t)
    (hdv : ∀ t ∈ Icc a b,
      HasDerivWithinAt v (F t (v t)) (Icc a b) t)
    (hinit : u a = v a) :
    EqOn u v (Icc a b) := by
  have hd {w : ℝ → ℝ}
      (hw : ∀ t ∈ Icc a b,
        HasDerivWithinAt w (F t (w t)) (Icc a b) t)
      (t : ℝ) (ht : t ∈ Ico a b) :
      HasDerivWithinAt w (F t (w t)) (Ici t) t := by
    have hn : Icc a b ∈ 𝓝[Ici t] t :=
      Filter.mem_of_superset (Icc_mem_nhdsGE ht.2) (Icc_subset_Icc_left ht.1)
    exact (hw t ⟨ht.1, ht.2.le⟩).mono_of_mem_nhdsWithin hn
  exact ODE_solution_unique_of_mem_Icc_right
    (fun t ht => (hF t ⟨ht.1, ht.2.le⟩).lipschitzOnWith)
    (HasDerivWithinAt.continuousOn hdu) (hd hdu) (fun _ _ => mem_univ _)
    (HasDerivWithinAt.continuousOn hdv) (hd hdv) (fun _ _ => mem_univ _) hinit

/-- Periodicity of the speed forces equivariance of every actual solution
family, without assuming regularity of its choice in the initial angle. -/
theorem scalarFlow_period_add
    {F : ℝ → ℝ → ℝ} {Θ : ℝ → ℝ → ℝ}
    {a b T : ℝ} {K : ℝ≥0}
    (hF : ∀ t ∈ Icc a b, LipschitzWith K (F t))
    (hperiod : ∀ t ∈ Icc a b, Function.Periodic (F t) T)
    (hinit : ∀ θ, Θ θ a = θ)
    (hderiv : ∀ θ t, t ∈ Icc a b →
      HasDerivWithinAt (Θ θ) (F t (Θ θ t)) (Icc a b) t)
    (θ : ℝ) {t : ℝ} (ht : t ∈ Icc a b) :
    Θ (θ + T) t = Θ θ t + T := by
  apply eqOn_scalarFlow_of_same_initial hF (hderiv (θ + T)) _ _ ht
  · intro r hr
    simpa only [(hperiod r hr) (Θ θ r)] using (hderiv θ r hr).add_const T
  · rw [hinit (θ + T), hinit θ]

/-- A continuous periodic field with a continuous actual angular
derivative admits genuine circle-flow lifts throughout any prescribed
compact time interval. The bounds needed for existence are derived. -/
theorem exists_periodicScalarFlow_on_Icc
    {F D : ℝ × ℝ → ℝ} {a b T : ℝ} (hab : a ≤ b) (hT : T ≠ 0)
    (hF : ContinuousOn F (Icc a b ×ˢ univ))
    (hD : ContinuousOn D (Icc a b ×ˢ univ))
    (hperiodF : ∀ t ∈ Icc a b, Function.Periodic (fun θ => F (t, θ)) T)
    (hperiodD : ∀ t ∈ Icc a b, Function.Periodic (fun θ => D (t, θ)) T)
    (hderiv : ∀ t ∈ Icc a b, ∀ θ,
      HasDerivAt (fun φ => F (t, φ)) (D (t, θ)) θ) :
    ∃ Θ : ℝ → ℝ → ℝ,
      (∀ θ, Θ θ a = θ) ∧
      (∀ θ t, t ∈ Icc a b →
        HasDerivWithinAt (Θ θ) (F (t, Θ θ t)) (Icc a b) t) ∧
      (∀ θ t, t ∈ Icc a b → Θ (θ + T) t = Θ θ t + T) := by
  obtain ⟨M, hM0, hM⟩ :=
    exists_norm_bound_periodic_compact isCompact_Icc hT hF hperiodF
  obtain ⟨K, hK0, hK⟩ :=
    exists_norm_bound_periodic_compact isCompact_Icc hT hD hperiodD
  have hLip (t : ℝ) (ht : t ∈ Icc a b) :
      LipschitzWith (NNReal.mk K hK0) (fun θ => F (t, θ)) := by
    apply LipschitzWith.of_dist_le_mul
    intro θ φ
    simpa only [dist_eq_norm, NNReal.coe_mk] using
      (convex_univ : Convex ℝ (univ : Set ℝ)).norm_image_sub_le_of_norm_hasDerivWithin_le
        (fun x _ => (hderiv t ht x).hasDerivWithinAt)
        (fun x _ => hK t ht x) (mem_univ φ) (mem_univ θ)
  have hc (θ : ℝ) :
      ContinuousOn (fun t => F (t, θ)) (Icc a b) :=
    hF.comp (continuousOn_id.prodMk continuousOn_const) (fun _ ht => ⟨ht, mem_univ _⟩)
  have hex (θ : ℝ) := exists_scalarFlow_on_Icc
    (M := NNReal.mk M hM0) (show a ∈ Icc a b from ⟨le_rfl, hab⟩)
    hLip hc (fun t ht x => by simpa only [NNReal.coe_mk] using hM t ht x) θ
  choose Θ hΘ using hex
  refine ⟨Θ, fun θ => (hΘ θ).1, fun θ => (hΘ θ).2.2.1, ?_⟩
  intro θ t ht
  exact scalarFlow_period_add hLip hperiodF (fun θ => (hΘ θ).1)
    (fun θ => (hΘ θ).2.2.1) θ ht

end ContinuousFlexibility.Analysis
