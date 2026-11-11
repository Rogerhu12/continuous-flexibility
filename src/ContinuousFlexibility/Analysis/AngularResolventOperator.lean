import Mathlib.Analysis.InnerProductSpace.LinearPMap
import Mathlib.Tactic.Abel

/-!
# The unbounded operator determined by an injective self-adjoint resolvent

For an injective bounded operator `B`, the operator `B⁻¹ - I` has domain
`range B`.  Its shifted inverse is exactly `B`.  When `B` is self-adjoint,
the range is dense and this partially defined operator is genuinely
self-adjoint: the domain of its Hilbert-space adjoint is proved to be the
same range, rather than included as a hypothesis.
-/

noncomputable section

namespace ContinuousFlexibility.Analysis

open scoped Topology

variable {𝕜 H : Type*} [RCLike 𝕜]
  [NormedAddCommGroup H] [InnerProductSpace 𝕜 H]

local notation "⟪" x ", " y "⟫" => inner 𝕜 x y

/-- The unbounded operator whose shifted inverse is `B`. -/
def angularResolventOperator (B : H →L[𝕜] H) (hInjective : Function.Injective B) :
    H →ₗ.[𝕜] H where
  domain := B.range
  toFun := (LinearEquiv.ofInjective B.toLinearMap hInjective).symm.toLinearMap -
    B.range.subtype

@[simp] theorem angularResolventOperator_domain (B : H →L[𝕜] H)
    (hInjective : Function.Injective B) :
    (angularResolventOperator B hInjective).domain = B.range := rfl

theorem angularResolventOperator_apply (B : H →L[𝕜] H)
    (hInjective : Function.Injective B) (y : (angularResolventOperator B hInjective).domain) :
    angularResolventOperator B hInjective y =
      (LinearEquiv.ofInjective B.toLinearMap hInjective).symm y - (y : H) := by
  rw [← LinearPMap.toFun_eq_coe (angularResolventOperator B hInjective) y]
  simp only [angularResolventOperator, _root_.sub_apply, LinearMap.sub_apply, Pi.sub_apply,
    LinearEquiv.coe_toLinearMap, Submodule.subtype_apply]

/-- The defining formula on the range of the bounded resolvent. -/
theorem angularResolventOperator_apply_image (B : H →L[𝕜] H)
    (hInjective : Function.Injective B) (x : H) :
    angularResolventOperator B hInjective
      ⟨B x, LinearMap.mem_range_self B.toLinearMap x⟩ = x - B x := by
  have harg : (⟨B x, LinearMap.mem_range_self B.toLinearMap x⟩ : B.range) =
      LinearEquiv.ofInjective B.toLinearMap hInjective x := by
    apply Subtype.ext
    simpa only [ContinuousLinearMap.coe_coe] using
      (LinearEquiv.ofInjective_apply B.toLinearMap (h := hInjective) x).symm
  exact (angularResolventOperator_apply B hInjective _).trans
    (congrArg (fun z : H => z - B x)
      ((congrArg (LinearEquiv.ofInjective B.toLinearMap hInjective).symm harg).trans
        ((LinearEquiv.ofInjective B.toLinearMap hInjective).symm_apply_apply x)))

/-- Applying `I + Λ` after `B` gives the identity. -/
theorem angularResolventOperator_left_inverse (B : H →L[𝕜] H)
    (hInjective : Function.Injective B) (x : H) :
    B x + angularResolventOperator B hInjective
      ⟨B x, LinearMap.mem_range_self B.toLinearMap x⟩ = x := by
  rw [angularResolventOperator_apply_image]
  abel

/-- Applying `B` after `I + Λ` gives the identity on the operator domain. -/
theorem angularResolventOperator_right_inverse (B : H →L[𝕜] H)
    (hInjective : Function.Injective B) (y : (angularResolventOperator B hInjective).domain) :
    B ((y : H) + angularResolventOperator B hInjective y) = y := by
  have heq : (y : H) + angularResolventOperator B hInjective y =
      (LinearEquiv.ofInjective B.toLinearMap hInjective).symm y := by
    rw [angularResolventOperator_apply]
    abel
  rw [heq]
  simpa only [ContinuousLinearMap.coe_coe] using
    LinearEquiv.ofInjective_symm_apply B.toLinearMap (h := hInjective) y

variable [CompleteSpace H]

/-- Injectivity and self-adjointness of the resolvent imply that its range,
and hence the domain of the unbounded operator, is dense. -/
theorem angularResolventOperator_dense (B : H →L[𝕜] H)
    (hInjective : Function.Injective B) (hB : IsSelfAdjoint B) :
    Dense ((angularResolventOperator B hInjective).domain : Set H) := by
  rw [angularResolventOperator_domain]
  apply Submodule.dense_iff_topologicalClosure_eq_top.mpr
  have hperp : B.rangeᗮ = B.ker := hB.isSymmetric.orthogonal_range
  have hker : B.ker = ⊥ := LinearMap.ker_eq_bot.mpr hInjective
  rw [← B.range.orthogonal_orthogonal_eq_closure, hperp, hker,
    Submodule.bot_orthogonal_eq_top]

theorem angularResolventOperator_isFormalAdjoint (B : H →L[𝕜] H)
    (hInjective : Function.Injective B) (hB : IsSelfAdjoint B) :
    (angularResolventOperator B hInjective).IsFormalAdjoint
      (angularResolventOperator B hInjective) := by
  intro x y
  let e := LinearEquiv.ofInjective B.toLinearMap hInjective
  have hx : B (e.symm x) = (x : H) :=
    LinearEquiv.ofInjective_symm_apply B.toLinearMap x
  have hy : B (e.symm y) = (y : H) :=
    LinearEquiv.ofInjective_symm_apply B.toLinearMap y
  rw [angularResolventOperator_apply, angularResolventOperator_apply,
    inner_sub_left, inner_sub_right]
  apply congrArg (fun z : 𝕜 => z - ⟪(x : H), (y : H)⟫)
  calc
    ⟪e.symm x, (y : H)⟫ = ⟪e.symm x, B (e.symm y)⟫ := by rw [hy]
    _ = ⟪B (e.symm x), e.symm y⟫ := (hB.isSymmetric _ _).symm
    _ = ⟪(x : H), e.symm y⟫ := by rw [hx]

/-- Testing the adjoint against `B x` identifies every vector in its domain
as an element of the range of `B`. -/
theorem angularResolventOperator_adjoint_range_identity (B : H →L[𝕜] H)
    (hInjective : Function.Injective B) (hB : IsSelfAdjoint B)
    (y : (angularResolventOperator B hInjective).adjoint.domain) :
    (y : H) = B ((y : H) + (angularResolventOperator B hInjective).adjoint y) := by
  apply ext_inner_right 𝕜
  intro x
  have h := LinearPMap.adjoint_isFormalAdjoint
    (T := angularResolventOperator B hInjective)
    (angularResolventOperator_dense B hInjective hB) y
    ⟨B x, LinearMap.mem_range_self B.toLinearMap x⟩
  rw [angularResolventOperator_apply_image, inner_sub_right] at h
  calc
    ⟪(y : H), x⟫ = ⟪(y : H), B x⟫ +
        ⟪(angularResolventOperator B hInjective).adjoint y, B x⟫ := by
      rw [h]
      abel
    _ = ⟪(y : H) + (angularResolventOperator B hInjective).adjoint y, B x⟫ :=
      (inner_add_left _ _ _).symm
    _ = ⟪B ((y : H) + (angularResolventOperator B hInjective).adjoint y), x⟫ :=
      (hB.isSymmetric _ _).symm

theorem angularResolventOperator_adjoint_domain_le (B : H →L[𝕜] H)
    (hInjective : Function.Injective B) (hB : IsSelfAdjoint B) :
    (angularResolventOperator B hInjective).adjoint.domain ≤
      (angularResolventOperator B hInjective).domain := by
  intro y hy
  change y ∈ B.range
  exact ⟨y + (angularResolventOperator B hInjective).adjoint ⟨y, hy⟩,
    (angularResolventOperator_adjoint_range_identity B hInjective hB ⟨y, hy⟩).symm⟩

/-- `B⁻¹ - I` is self-adjoint on its actual maximal domain `range B`. -/
theorem angularResolventOperator_isSelfAdjoint (B : H →L[𝕜] H)
    (hInjective : Function.Injective B) (hB : IsSelfAdjoint B) :
    IsSelfAdjoint (angularResolventOperator B hInjective) := by
  apply LinearPMap.isSelfAdjoint_def.mpr
  apply LinearPMap.ext
  · apply le_antisymm
    · exact angularResolventOperator_adjoint_domain_le B hInjective hB
    · intro y hy
      apply LinearPMap.mem_adjoint_domain_of_exists (T := angularResolventOperator B hInjective)
      refine ⟨angularResolventOperator B hInjective ⟨y, hy⟩, ?_⟩
      intro x
      exact angularResolventOperator_isFormalAdjoint B hInjective hB ⟨y, hy⟩ x
  · intro y hyadj hy
    apply LinearPMap.adjoint_apply_eq (T := angularResolventOperator B hInjective)
      (angularResolventOperator_dense B hInjective hB)
    intro x
    exact angularResolventOperator_isFormalAdjoint B hInjective hB ⟨y, hy⟩ x

theorem angularResolventOperator_isClosed (B : H →L[𝕜] H)
    (hInjective : Function.Injective B) (hB : IsSelfAdjoint B) :
    (angularResolventOperator B hInjective).IsClosed :=
  (angularResolventOperator_isSelfAdjoint B hInjective hB).isClosed

end ContinuousFlexibility.Analysis
