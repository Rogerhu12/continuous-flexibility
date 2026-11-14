module

public import ContinuousFlexibility.Radial.OuterNaturalInitialGap
public import ContinuousFlexibility.Radial.TailNaturalUniqueness

/-!
# The normalized natural Poisson solution with its full weighted bound

The solution comes from the actual mass--resistance construction. Its
first outgoing flux follows from the canonical edge coefficients, so
the initial resistance interval and the complete norm estimate require
no additional boundary or integrability hypothesis.
-/

@[expose] public section

noncomputable section

namespace ContinuousFlexibility.Radial

open Set MeasureTheory
open scoped Topology ContDiff
open ContinuousFlexibility.Statements

set_option backward.isDefEq.respectTransparency false

/-- The actual first outgoing flux has the lower bound needed on an
initial resistance interval. It follows from the equation and node
contraction, without assuming equality with an interpolation. -/
theorem tailActualState_firstFlux_lower {T : DeepTailData}
    (hT : DeepTailHypotheses T) (hη : T.η ≤ 1 / 16) (hK : 32 ≤ T.K)
    {u v : ℝ → ℝ}
    (hsys : TailFirstOrderSystem T.p T.Λ u v (Ico T.entrance T.endpoint))
    (hu₀ : u (T.node 0) = 1)
    (hstep : ∀ n, |u (T.node (n + 1))| ≤
      8 / (T.Λ * tailMass T (n + 1) * tailResistance T n) * |u (T.node n)|) :
    T.Λ * tailMass T 0 / 2 ≤ v (T.node 0) := by
  have hu₁ : |u (T.node 1)| ≤ 1 := by
    have h := hstep 0
    rw [hu₀, abs_one, mul_one] at h
    apply h.trans
    apply (div_le_one (mul_pos (mul_pos hT.2.2.1 (tailMass_pos hT 1))
      (tailResistance_pos hT 0))).mpr
    linarith only [hK, (hT.2.2.2.2.2.2.2.2.2.2 0).2.2.2.2.1]
  have hu : ContinuousOn u (Ico T.entrance T.endpoint) :=
    fun x hx => (hsys x hx).1.continuousAt.continuousWithinAt
  have hv : ContinuousOn v (Ico T.entrance T.endpoint) :=
    fun x hx => (hsys x hx).2.continuousAt.continuousWithinAt
  have hedge := tailActualEdge_interval_subset hT 0
  have hflux := (tailActualEdge_solution_flux_endpoints hT 0
    (hu.mono hedge) (hv.mono hedge)
    (hsys.mono (fun _ hx => hedge (Ioo_subset_Icc_self hx)))).1
  have hlower := tailNaturalFirstFlux_lower hT hη hK
    (a := fun n => u (T.node n)) hu₀ hu₁
  rw [tailPoissonInterpolationFlux_first_node] at hlower
  rw [hflux]
  exact hlower

/-- The actual natural solution normalized to one at the tail entrance.
Its complete squared norm is controlled by the first mass, including
the allowed initial resistance interval. -/
theorem exists_tailNaturalPoisson_norm_bound {T : DeepTailData}
    (hT : DeepTailHypotheses T) (hη : T.η ≤ 1 / 16) (hK : 32 ≤ T.K) :
    ∃ P Q : ℝ → ℝ,
      TailNaturalEquation T P ∧
      ContDiffOn ℝ ∞ P (Iio T.endpoint) ∧
      ContDiffOn ℝ ∞ Q (Iio T.endpoint) ∧
      TailFirstOrderSystem T.p T.Λ P Q (Ico T.entrance T.endpoint) ∧
      Integrable P (deepTailMeasure T) ∧
      P T.entrance = 1 ∧
      (∀ n, P (T.node n) ≠ 0) ∧
      (∀ n, |P (T.node (n + 1))| ≤
        8 / (T.Λ * tailMass T (n + 1) * tailResistance T n) * |P (T.node n)|) ∧
      (∫ x, P x ^ 2 ∂deepTailMeasure T) ≤ 33 * tailMass T 0 ∧
      (T.entrance < T.node 0 →
        |P (T.node 0)| ≤ 8 / (T.Λ * tailMass T 0 * tailInitialResistance T)) := by
  obtain ⟨u, v, hu, hus, hvs, hsys, huL1, hu₀, hunode, _, hstep, hune⟩ :=
    exists_tailNaturalSolution hT hη hK
  have hv₀ := tailActualState_firstFlux_lower hT hη hK hsys hu₀ hstep
  let c : ℝ := (u T.entrance)⁻¹
  let P : ℝ → ℝ := fun x => c * u x
  let Q : ℝ → ℝ := fun x => c * v x
  have hcne : c ≠ 0 := inv_ne_zero hune
  have hPsys : TailFirstOrderSystem T.p T.Λ P Q (Ico T.entrance T.endpoint) :=
    hsys.const_mul c
  have hP : TailNaturalEquation T P := by
    refine ⟨contDiffAt_const.mul hu.1, contDiffOn_const.mul hu.2.1,
      hu.2.2.1.const_mul c, ?_⟩
    exact tailFirstOrderSystem_equation isOpen_Ioo
      (fun x hx => (deepTail_pos hT x ⟨hx.1.le, hx.2⟩).ne')
      (hPsys.mono Ioo_subset_Ico_self)
  have hPeq (x : ℝ) : P x = u x / u T.entrance := by
    dsimp only [P, c]
    rw [div_eq_mul_inv, mul_comm]
  refine ⟨P, Q, hP, contDiffOn_const.mul hus, contDiffOn_const.mul hvs,
    hPsys, huL1.const_mul c, ?_, ?_, ?_, ?_, ?_⟩
  · change (u T.entrance)⁻¹ * u T.entrance = 1
    exact inv_mul_cancel₀ hune
  · intro n
    exact mul_ne_zero hcne (hunode n)
  · intro n
    change |c * u (T.node (n + 1))| ≤
      8 / (T.Λ * tailMass T (n + 1) * tailResistance T n) * |c * u (T.node n)|
    calc
      _ = |c| * |u (T.node (n + 1))| := abs_mul _ _
      _ ≤ |c| * (8 / (T.Λ * tailMass T (n + 1) * tailResistance T n) *
          |u (T.node n)|) :=
        mul_le_mul_of_nonneg_left (hstep n) (abs_nonneg c)
      _ = _ := by rw [abs_mul]; ring
  · simp_rw [hPeq]
    exact tailNaturalEquation_normalized_sq_integral_le hT hη hK hu hsys hu₀ hv₀ hstep
  · intro hg
    rw [hPeq]
    exact tailActualState_initialGap_normalized_first_node_le hT hη hK hsys hu₀ hv₀ hg

end ContinuousFlexibility.Radial
