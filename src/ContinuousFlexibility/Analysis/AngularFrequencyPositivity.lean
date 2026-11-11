import ContinuousFlexibility.Analysis.AngularResolventDomains

/-!
# Nonnegativity of the angular frequency operator

The diagonal quadratic form is the sum of the nonnegative terms
`n * ‖v n‖²`.  The coordinate isometry transports this fact to the actual
unbounded operator associated with an angular resolvent.
-/

noncomputable section

namespace ContinuousFlexibility.Analysis

open scoped ENNReal

variable {𝕜 : Type*} [RCLike 𝕜]
variable {E : ℕ → Type*} [∀ n, NormedAddCommGroup (E n)]
  [∀ n, InnerProductSpace 𝕜 (E n)]

/-- The quadratic form of the maximal diagonal frequency operator. -/
theorem angularFrequency_re_inner_eq_tsum
    (v : (angularFrequency (𝕜 := 𝕜) (E := E)).domain) :
    RCLike.re (inner 𝕜 (v : lp E 2) (angularFrequency (𝕜 := 𝕜) v)) =
      ∑' n, (n : ℝ) * ‖(v : lp E 2) n‖ ^ 2 := by
  rw [lp.inner_eq_tsum, RCLike.re_tsum 𝕜
    (lp.summable_inner (𝕜 := 𝕜) (v : lp E 2) (angularFrequency (𝕜 := 𝕜) v))]
  apply tsum_congr
  intro n
  rw [angularFrequency_apply, inner_smul_right, RCLike.re_ofReal_mul,
    inner_self_eq_norm_sq]

theorem angularFrequency_re_inner_nonneg
    (v : (angularFrequency (𝕜 := 𝕜) (E := E)).domain) :
    0 ≤ RCLike.re (inner 𝕜 (v : lp E 2) (angularFrequency (𝕜 := 𝕜) v)) := by
  rw [angularFrequency_re_inner_eq_tsum]
  exact tsum_nonneg (fun n => mul_nonneg (Nat.cast_nonneg n) (sq_nonneg _))

theorem angularDerivative_re_inner_nonneg {v : lp E 2}
    (hv : v ∈ angularFrequencyDomain (𝕜 := 𝕜)) :
    0 ≤ RCLike.re (inner 𝕜 v (angularDerivative (𝕜 := 𝕜) v)) := by
  simpa only [angularDerivative, dif_pos hv] using
    angularFrequency_re_inner_nonneg (𝕜 := 𝕜) ⟨v, hv⟩

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace 𝕜 H]
  [NormedSpace ℝ H] [IsScalarTower ℝ 𝕜 H] [CompleteSpace H]
  [HasAngularSpectralDecomposition 𝕜 H]

namespace AngularResolventData

/-- The original self-adjoint unbounded frequency operator is nonnegative
on its actual domain. -/
theorem frequency_nonneg (A : AngularResolventData 𝕜 H) (v : A.frequency.domain) :
    0 ≤ RCLike.re (inner 𝕜 (v : H) (A.frequency v)) := by
  have hv : A.Sobolev 1 (v : H) :=
    (A.frequency_domain_iff_sobolev_one v).mp v.property
  have h := angularDerivative_re_inner_nonneg (𝕜 := 𝕜)
    (mem_angularFrequencyDomain_of_sobolev (𝕜 := 𝕜) hv)
  rw [← A.coordinates_derivative, A.coordinates.inner_map_map,
    A.derivative_eq_frequency v] at h
  exact h

end AngularResolventData

end ContinuousFlexibility.Analysis
