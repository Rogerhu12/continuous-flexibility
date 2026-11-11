import ContinuousFlexibility.Analysis.AngularHilbertScale
import ContinuousFlexibility.Analysis.AngularResolventOperator
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Module
import Mathlib.Tactic.Ring

/-!
# Identification of the angular Sobolev domain with the original operator

The first Sobolev domain is exactly the range of the bounded resolvent.
On that domain the spectral frequency action equals the actual maximal
self-adjoint partial operator `B⁻¹ - I`.
-/

noncomputable section

namespace ContinuousFlexibility.Analysis

variable {𝕜 : Type*} [RCLike 𝕜]

private theorem angular_frequency_reciprocal (n : ℕ) :
    (n : ℝ) * angularResolventEigenvalue n = 1 - angularResolventEigenvalue n := by
  unfold angularResolventEigenvalue
  have h : (n : ℝ) + 1 ≠ 0 := by positivity
  field_simp
  ring

private theorem angular_reciprocal_succ (n : ℕ) :
    angularResolventEigenvalue n * (1 + (n : ℝ)) = 1 := by
  unfold angularResolventEigenvalue
  have h : (n : ℝ) + 1 ≠ 0 := by positivity
  field_simp
  ring

private theorem angular_frequency_reciprocal_smul {F : Type*}
    [AddCommGroup F] [Module 𝕜 F] (n : ℕ) (x : F) :
    ((n : ℝ) : 𝕜) • ((angularResolventEigenvalue n : 𝕜) • x) =
      x - (angularResolventEigenvalue n : 𝕜) • x := by
  have h := congrArg (fun t : ℝ => (t : 𝕜)) (angular_frequency_reciprocal n)
  simp only [RCLike.ofReal_mul, RCLike.ofReal_sub, RCLike.ofReal_one] at h
  rw [smul_smul, h, sub_smul, one_smul]

private theorem angular_reciprocal_succ_smul {F : Type*}
    [AddCommGroup F] [Module 𝕜 F] (n : ℕ) (x : F) :
    (angularResolventEigenvalue n : 𝕜) • (x + ((n : ℝ) : 𝕜) • x) = x := by
  have h := congrArg (fun t : ℝ => (t : 𝕜)) (angular_reciprocal_succ n)
  simp only [RCLike.ofReal_mul, RCLike.ofReal_add, RCLike.ofReal_one] at h
  calc
    _ = ((angularResolventEigenvalue n : 𝕜) * (1 + ((n : ℝ) : 𝕜))) • x := by module
    _ = x := by rw [h, one_smul]

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace 𝕜 H] [CompleteSpace H]
  [NormedSpace ℝ H] [IsScalarTower ℝ 𝕜 H]
  [HasAngularSpectralDecomposition 𝕜 H]

namespace AngularResolventData

/-- The original maximal angular operator determined by the resolvent. -/
def frequency (A : AngularResolventData 𝕜 H) : H →ₗ.[𝕜] H :=
  angularResolventOperator A.operator A.injective

theorem frequency_selfAdjoint (A : AngularResolventData 𝕜 H) : IsSelfAdjoint A.frequency :=
  angularResolventOperator_isSelfAdjoint A.operator A.injective A.selfAdjoint

@[simp] theorem frequency_domain (A : AngularResolventData 𝕜 H) :
    A.frequency.domain = A.operator.range := angularResolventOperator_domain _ _

theorem sobolev_one_operator (A : AngularResolventData 𝕜 H) (x : H) :
    A.Sobolev 1 (A.operator x) := by
  apply (memAngularSobolev_one_iff_frequency (𝕜 := 𝕜) (A.coordinates (A.operator x))).mpr
  change Memℓp (fun n : ℕ => ((n : ℝ) : 𝕜) • A.coordinates (A.operator x) n) 2
  have hfun : (fun n : ℕ => ((n : ℝ) : 𝕜) • A.coordinates (A.operator x) n) =
      (fun n : ℕ => (A.coordinates x - A.coordinates (A.operator x)) n) := by
    funext n
    rw [lp.coeFn_sub, Pi.sub_apply, A.coordinates_operator,
      angular_frequency_reciprocal_smul]
  rw [hfun]
  exact lp.memℓp _

/-- The shifted spectral frequency action has the given bounded resolvent. -/
theorem operator_add_derivative (A : AngularResolventData 𝕜 H) {v : H}
    (hv : A.Sobolev 1 v) : A.operator (v + A.derivative v) = v := by
  have hdom := mem_angularFrequencyDomain_of_sobolev (𝕜 := 𝕜) hv
  apply A.coordinates.injective
  ext n
  rw [A.coordinates_operator, map_add, lp.coeFn_add, Pi.add_apply,
    A.coordinates_derivative, angularDerivative_apply hdom]
  exact angular_reciprocal_succ_smul n _

/-- No extra first-order regularity is hidden in the spectral definition:
its domain is the actual maximal operator domain. -/
theorem frequency_domain_iff_sobolev_one (A : AngularResolventData 𝕜 H) (v : H) :
    v ∈ A.frequency.domain ↔ A.Sobolev 1 v := by
  rw [frequency_domain]
  constructor
  · rintro ⟨x, rfl⟩
    exact A.sobolev_one_operator x
  · intro hv
    exact ⟨v + A.derivative v, A.operator_add_derivative hv⟩

/-- The frequency action used in the commutator theorem is the given
self-adjoint unbounded operator on every vector in its domain. -/
theorem derivative_eq_frequency (A : AngularResolventData 𝕜 H) (v : A.frequency.domain) :
    A.derivative (v : H) = A.frequency v := by
  have hv : A.Sobolev 1 (v : H) :=
    (A.frequency_domain_iff_sobolev_one v).mp v.property
  have hleft := A.operator_add_derivative hv
  have hright := angularResolventOperator_right_inverse A.operator A.injective v
  have h := A.injective (hleft.trans hright.symm)
  exact add_left_cancel h

end AngularResolventData

end ContinuousFlexibility.Analysis
