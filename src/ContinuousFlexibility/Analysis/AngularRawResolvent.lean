import Mathlib.Analysis.InnerProductSpace.LinearPMap
import Mathlib.Tactic.Linarith

/-!
# Bounded resolvents of a given unbounded operator

`AngularRawResolventData A r` records the bounded inverse of `A - r I`,
including the actual domain of `A` and both inverse identities.  The same
object is used at every real spectral parameter.  In particular, `r=-1`
is the shifted inverse used by the angular-frequency construction.
-/

noncomputable section

namespace ContinuousFlexibility.Analysis

variable {𝕜 H : Type*} [RCLike 𝕜]
  [NormedAddCommGroup H] [InnerProductSpace 𝕜 H]

local notation "⟪" x ", " y "⟫" => inner 𝕜 x y

/-- A bounded two-sided inverse of `A - r I`, with its domain assertions. -/
structure AngularRawResolventData (A : H →ₗ.[𝕜] H) (r : ℝ) where
  operator : H →L[𝕜] H
  mapsDomain : ∀ x, operator x ∈ A.domain
  left : ∀ x, A ⟨operator x, mapsDomain x⟩ - (r : 𝕜) • operator x = x
  right : ∀ v : A.domain, operator (A v - (r : 𝕜) • (v : H)) = v

namespace AngularRawResolventData

variable {A : H →ₗ.[𝕜] H} {r : ℝ}

theorem injective (Q : AngularRawResolventData A r) : Function.Injective Q.operator := by
  intro x y hxy
  have harg : (⟨Q.operator x, Q.mapsDomain x⟩ : A.domain) =
      ⟨Q.operator y, Q.mapsDomain y⟩ := Subtype.ext hxy
  calc
    x = A ⟨Q.operator x, Q.mapsDomain x⟩ - (r : 𝕜) • Q.operator x := (Q.left x).symm
    _ = A ⟨Q.operator y, Q.mapsDomain y⟩ - (r : 𝕜) • Q.operator y :=
      congrArg₂ (fun u v : H => u - v) (congrArg (fun v : A.domain => A v) harg)
        (congrArg (fun v : H => (r : 𝕜) • v) hxy)
    _ = y := Q.left y

theorem range_eq_domain (Q : AngularRawResolventData A r) :
    Q.operator.range = A.domain := by
  ext v
  constructor
  · rintro ⟨x, rfl⟩
    exact Q.mapsDomain x
  · intro hv
    exact ⟨A ⟨v, hv⟩ - (r : 𝕜) • v, Q.right ⟨v, hv⟩⟩

/-- The bounded resolvent is independent of the choice of inverse data. -/
theorem operator_unique (Q P : AngularRawResolventData A r) : Q.operator = P.operator := by
  ext x
  calc
    Q.operator x = P.operator
        (A ⟨Q.operator x, Q.mapsDomain x⟩ - (r : 𝕜) • Q.operator x) :=
      (P.right ⟨Q.operator x, Q.mapsDomain x⟩).symm
    _ = P.operator x := by rw [Q.left x]

theorem left_shifted (Q : AngularRawResolventData A (-1)) (x : H) :
    Q.operator x + A ⟨Q.operator x, Q.mapsDomain x⟩ = x := by
  simpa only [RCLike.ofReal_neg, RCLike.ofReal_one, neg_smul, one_smul,
    sub_neg_eq_add, add_comm] using Q.left x

theorem right_shifted (Q : AngularRawResolventData A (-1)) (v : A.domain) :
    Q.operator ((v : H) + A v) = v := by
  simpa only [RCLike.ofReal_neg, RCLike.ofReal_one, neg_smul, one_smul,
    sub_neg_eq_add, add_comm] using Q.right v

/-- A nonnegative operator has a contractive shifted resolvent whenever
that resolvent exists. -/
theorem norm_le_one (Q : AngularRawResolventData A (-1))
    (hpos : ∀ v : A.domain, 0 ≤ RCLike.re ⟪(v : H), A v⟫) :
    ‖Q.operator‖ ≤ 1 := by
  apply ContinuousLinearMap.opNorm_le_bound _ zero_le_one
  intro x
  have hsq := norm_add_sq (𝕜 := 𝕜) (Q.operator x) (A ⟨Q.operator x, Q.mapsDomain x⟩)
  rw [Q.left_shifted x] at hsq
  have hnonneg := hpos ⟨Q.operator x, Q.mapsDomain x⟩
  have hle : ‖Q.operator x‖ ^ 2 ≤ ‖x‖ ^ 2 := by
    nlinarith only [hsq, hnonneg, sq_nonneg ‖A ⟨Q.operator x, Q.mapsDomain x⟩‖]
  have hnorm := (sq_le_sq₀ (norm_nonneg (Q.operator x)) (norm_nonneg x)).mp hle
  simpa only [one_mul] using hnorm

variable [CompleteSpace H]

/-- Resolvents at real parameters of a self-adjoint unbounded operator
are self-adjoint bounded operators. -/
theorem selfAdjoint (Q : AngularRawResolventData A r) (hA : IsSelfAdjoint A) :
    IsSelfAdjoint Q.operator := by
  have hformal : A.IsFormalAdjoint A := by
    have h := LinearPMap.adjoint_isFormalAdjoint (T := A) hA.dense_domain
    rwa [LinearPMap.isSelfAdjoint_def.mp hA] at h
  apply ContinuousLinearMap.isSelfAdjoint_iff_isSymmetric.mpr
  intro x y
  calc
    ⟪Q.operator x, y⟫ =
        ⟪Q.operator x, A ⟨Q.operator y, Q.mapsDomain y⟩ - (r : 𝕜) • Q.operator y⟫ := by
      rw [Q.left y]
    _ = ⟪A ⟨Q.operator x, Q.mapsDomain x⟩, Q.operator y⟫ -
        (r : 𝕜) * ⟪Q.operator x, Q.operator y⟫ := by
      rw [inner_sub_right, inner_smul_right,
        ← hformal ⟨Q.operator x, Q.mapsDomain x⟩ ⟨Q.operator y, Q.mapsDomain y⟩]
    _ = ⟪A ⟨Q.operator x, Q.mapsDomain x⟩ - (r : 𝕜) • Q.operator x, Q.operator y⟫ := by
      rw [inner_sub_left, inner_smul_left, RCLike.conj_ofReal]
    _ = ⟪x, Q.operator y⟫ := by rw [Q.left x]

end AngularRawResolventData

end ContinuousFlexibility.Analysis
