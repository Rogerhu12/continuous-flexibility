import ContinuousFlexibility.Analysis.N04PositiveGeometryBoundaryFormulaWordBounds
import ContinuousFlexibility.Analysis.N01cSpatialParameterComposition

/-!
# Normed finite kernels on the actual boundary towers

The same ordered-word bound applies to operator-valued boundary jets.
Products, finite tuples and a polynomially bounded smooth kernel retain
the original parameter height and the exact sum of angular orders.
These operations are used in the finite inverse-jet recursion.
-/

noncomputable section

namespace ContinuousFlexibility.Analysis

open Set Function ContinuousFlexibility.Statements
open scoped ContDiff BigOperators

variable {E F G : Type*}
  [TopologicalSpace E] [AddCommGroup E] [Module ℝ E]
  [IsTopologicalAddGroup E] [ContinuousSMul ℝ E]
  [NormedAddCommGroup F] [NormedSpace ℝ F]
  [NormedAddCommGroup G] [NormedSpace ℝ G]

namespace N04BoundaryWordBounds

theorem postcompCLM {U : Set E} {f : E × ℝ → F}
    {J : SmoothDirections (U ×ˢ univ) f}
    {K s d : ℕ} {x : E} {θ : ℝ} {P : E → Prop} {M H t : ℝ} {shift : ℕ}
    (hf : N04BoundaryWordBounds J K s d x θ P M H t shift)
    (A : F →L[ℝ] G) (hA : ‖A‖ ≤ 1) :
    N04BoundaryWordBounds (smoothDirections_postcompCLM J A)
      K s d x θ P M H t shift := by
  intro n w hk ha v hv hp
  rw [smoothDirections_postcompCLM_D_apply]
  exact (A.le_opNorm _).trans
    ((mul_le_mul_of_nonneg_right hA (norm_nonneg _)).trans
      (by simpa only [one_mul] using hf n w hk ha v hv hp))

theorem prod {U : Set E} {f : E × ℝ → F} {g : E × ℝ → G}
    {J : SmoothDirections (U ×ˢ univ) f} {Q : SmoothDirections (U ×ˢ univ) g}
    {K s d : ℕ} {x : E} {θ : ℝ} {P : E → Prop} {M H t : ℝ} {shift : ℕ}
    (hf : N04BoundaryWordBounds J K s d x θ P M H t shift)
    (hg : N04BoundaryWordBounds Q K s d x θ P M H t shift) :
    N04BoundaryWordBounds (smoothDirectionsProd J Q) K s d x θ P M H t shift := by
  intro n w hk ha v hv hp
  change max ‖J.D n (x, θ) v‖ ‖Q.D n (x, θ) v‖ ≤ _
  exact max_le (hf n w hk ha v hv hp) (hg n w hk ha v hv hp)

theorem vectorTuple {m : ℕ} {U : Set E}
    (hU : IsOpen U) {f : Fin m → E × ℝ → F}
    (J : ∀ i, SmoothDirections (U ×ˢ univ) (f i))
    {K s d : ℕ} {x : E} {θ : ℝ} {P : E → Prop} {M H t : ℝ} {shift : ℕ}
    (hM : 0 ≤ M) (hH : 0 ≤ H) (ht : 0 ≤ t)
    (hf : ∀ i, N04BoundaryWordBounds (J i) K s d x θ P M H t shift) :
    N04BoundaryWordBounds (smoothDirections_vectorTuple (hU.prod isOpen_univ) J)
      K s d x θ P M H t shift := by
  intro n w hk ha v hv hp
  have hbound : 0 ≤ M * parameterHeightWeight H w.stateArity *
      t ^ ((w.angleArity - d) + shift * w.stateArity) :=
    mul_nonneg (mul_nonneg hM (parameterHeightWeight_nonneg hH _)) (pow_nonneg ht _)
  apply (pi_norm_le_iff_of_nonneg hbound).mpr
  intro i
  exact hf i n w hk ha v hv hp

theorem finiteSum {ι : Type*} [Fintype ι] {U : Set E}
    (hU : IsOpen U) {f : ι → E × ℝ → F}
    (J : ∀ i, SmoothDirections (U ×ˢ univ) (f i))
    {K s d : ℕ} {x : E} {θ : ℝ} {P : E → Prop} {M H t : ℝ} {shift : ℕ}
    (hf : ∀ i, N04BoundaryWordBounds (J i) K s d x θ P M H t shift) :
    N04BoundaryWordBounds (smoothDirections_finiteSum (hU.prod isOpen_univ) J)
      K s d x θ P ((Fintype.card ι : ℝ) * M) H t shift := by
  intro n w hk ha v hv hp
  rw [smoothDirections_finiteSum_D_apply]
  exact (norm_sum_le _ _).trans ((Finset.sum_le_sum
    (fun i _ => hf i n w hk ha v hv hp)).trans_eq (by
      simp only [Finset.sum_const, Finset.card_univ, nsmul_eq_mul]
      ring))

theorem value {U : Set E} {f : E × ℝ → F}
    {J : SmoothDirections (U ×ˢ univ) f}
    {K s d : ℕ} {x : E} {θ : ℝ} {P : E → Prop} {M H t : ℝ} {shift : ℕ}
    (h : N04BoundaryWordBounds J K s d x θ P M H t shift) (hx : x ∈ U) :
    ‖f (x, θ)‖ ≤ M := by
  have hb := h 0 .nil (Nat.zero_le _) (Nat.zero_le _) Fin.elim0
    ⟨fun i => i.elim0, fun i => i.elim0⟩ (fun i => i.elim0)
  simpa only [J.zero (x, θ) ⟨hx, mem_univ _⟩,
    StateAngleWord.stateArity, StateAngleWord.angleArity, Nat.zero_sub,
    Nat.mul_zero, Nat.add_zero, parameterHeightWeight, ite_true, pow_zero,
    mul_one] using hb

end N04BoundaryWordBounds

/-- A finite kernel whose ordinary jets have polynomial material cost
preserves the actual boundary word budget in any normed codomain. -/
theorem n04PositiveGeometry_boundaryKernel_polynomial_bound
    (N degree : ℕ) (C : ℝ) (hC : 1 ≤ C) :
    ∃ A : ℝ, 1 ≤ A ∧
    ∀ {U : Set E} {V : Set F} {f : E × ℝ → F} {g : F → G},
    ∀ J : SmoothDirections (U ×ˢ univ) f,
    ∀ Q : SmoothDirections (U ×ˢ univ) (g ∘ f),
    IsOpen V → ContDiffOn ℝ ∞ g V → MapsTo f (U ×ˢ univ) V →
    ∀ K s d : ℕ, K + s + d ≤ N → ∀ x ∈ U, ∀ θ P,
    ∀ M H t : ℝ, 1 ≤ M → 0 ≤ H → H ≤ M → 1 ≤ t → ∀ shift,
    N04BoundaryWordBounds J K s d x θ P M H t shift →
    (∀ j : ℕ, j ≤ N → ‖iteratedFDeriv ℝ j g (f (x, θ))‖ ≤ C * M ^ degree) →
    N04BoundaryWordBounds Q K s d x θ P
      (A * M ^ (degree + 2 * N)) H t shift := by
  classical
  let count : ℝ := 1 + ∑ j ∈ Finset.range (N + 1),
    (Fintype.card (OrderedFinpartition j) : ℝ)
  have hc : 1 ≤ count := le_add_of_nonneg_right
    (Finset.sum_nonneg fun _ _ => Nat.cast_nonneg _)
  refine ⟨count * C, one_le_mul_of_one_le_of_one_le hc hC, ?_⟩
  intro U V f g J Q hV hg hmap K s d hN x hx θ P M H t hM hH hHM ht shift hJ houter
  intro n w hk ha v hv hp
  have hn : n ≤ N := by
    have hw := w.arity_sum
    omega
  let κ : ∀ c : OrderedFinpartition n, Fin c.length → ℕ :=
    fun c i => (w.restrict (c.emb i)).stateArity
  let cost : ∀ c : OrderedFinpartition n, Fin c.length → ℕ :=
    fun c i => ((w.restrict (c.emb i)).angleArity - d) + shift * κ c i
  have hsum (c : OrderedFinpartition n) :
      ∑ i, cost c i ≤ (w.angleArity - d) + shift * w.stateArity := by
    dsimp only [cost, κ]
    rw [Finset.sum_add_distrib, ← Finset.mul_sum, w.sum_restrict_stateArity c]
    have hs := n04PositiveGeometry_sum_sub_reserve_le Finset.univ
      (fun i => (w.restrict (c.emb i)).angleArity) d
    rw [w.sum_restrict_angleArity c] at hs
    exact Nat.add_le_add_right hs _
  have hinner (c : OrderedFinpartition n) (i : Fin c.length) :
      ‖J.D (c.partSize i) (x, θ) (v ∘ c.emb i)‖ ≤
        M * parameterHeightWeight H (κ c i) * t ^ cost c i := by
    have hk' : (w.restrict (c.emb i)).stateArity ≤ K :=
      ((Finset.single_le_sum (fun j _ => Nat.zero_le
        (w.restrict (c.emb j)).stateArity) (Finset.mem_univ i)).trans_eq
          (w.sum_restrict_stateArity c)).trans hk
    have ha' : (w.restrict (c.emb i)).angleArity ≤ s + d :=
      ((Finset.single_le_sum (fun j _ => Nat.zero_le
        (w.restrict (c.emb j)).angleArity) (Finset.mem_univ i)).trans_eq
          (w.sum_restrict_angleArity c)).trans ha
    exact hJ (c.partSize i) (w.restrict (c.emb i)) hk' ha'
        (v ∘ c.emb i) (hv.restrict _) (fun j => hp _)
  have hb := n04PositiveGeometry_finiteKernel_weighted_bound J hV hg hmap Q
    n w.stateArity ((w.angleArity - d) + shift * w.stateArity) (x, θ) ⟨hx, mem_univ _⟩ v
    κ cost (fun c => w.sum_restrict_stateArity c) hsum
    (mul_nonneg (zero_le_one.trans hC) (pow_nonneg (zero_le_one.trans hM) _))
    hM hH hHM hM ht (fun j hj => houter j (hj.trans hn)) hinner
  have hcount : (Fintype.card (OrderedFinpartition n) : ℝ) ≤ count :=
    (Finset.single_le_sum (fun j _ => Nat.cast_nonneg
      (Fintype.card (OrderedFinpartition j)))
      (Finset.mem_range.mpr (Nat.lt_succ_of_le hn))).trans
      (le_add_of_nonneg_left zero_le_one)
  have hpoly : (Fintype.card (OrderedFinpartition n) : ℝ) *
      (C * M ^ degree) * M ^ n * M ^ n ≤ (count * C) * M ^ (degree + 2 * N) := by
    calc
      _ = ((Fintype.card (OrderedFinpartition n) : ℝ) * C) * M ^ (degree + 2 * n) := by
        rw [show degree + 2 * n = degree + n + n by omega, pow_add, pow_add]
        ring
      _ ≤ _ := mul_le_mul (mul_le_mul_of_nonneg_right hcount (zero_le_one.trans hC))
        (pow_le_pow_right₀ hM (by omega)) (pow_nonneg (zero_le_one.trans hM) _)
        (mul_nonneg (zero_le_one.trans hc) (zero_le_one.trans hC))
  exact hb.trans (mul_le_mul_of_nonneg_right
    (mul_le_mul_of_nonneg_right hpoly (parameterHeightWeight_nonneg hH _))
    (pow_nonneg (zero_le_one.trans ht) _))

end ContinuousFlexibility.Analysis
