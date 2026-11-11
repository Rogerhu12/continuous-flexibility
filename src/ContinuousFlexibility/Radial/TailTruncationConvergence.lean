import Mathlib.Analysis.InnerProductSpace.Symmetric
import Mathlib.Analysis.InnerProductSpace.Projection.Submodule
import Mathlib.Analysis.Normed.Operator.Banach

/-!
# Strong limits of uniformly bounded inverses

These lemmas isolate the functional-analytic limit in the deep-tail construction.
Pointwise convergence of bounded operators is strong convergence. A uniform bound
on their inverses passes to the limit as a lower bound; symmetry then makes the
closed range dense. The inverse identity proves strong convergence of the inverses.

The compression lemma extends a finite-dimensional compression by the identity on
the complementary coordinates. It therefore applies to genuine two-sided inverses
on one fixed Hilbert space, rather than to an inverse on a moving subspace.
-/

noncomputable section

namespace ContinuousFlexibility.Radial

open Filter
open scoped Topology

section Normed

variable {E F : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [NormedAddCommGroup F] [NormedSpace ℝ F]

/-- A uniformly bounded family sends a sequence converging to zero to zero. -/
theorem tail_bounded_apply_tendsto_zero (A : ℕ → E →L[ℝ] F) {M : ℝ}
    (hbound : ∀ n, ‖A n‖ ≤ M) {u : ℕ → E}
    (hu : Tendsto u atTop (𝓝 0)) :
    Tendsto (fun n => A n (u n)) atTop (𝓝 0) := by
  apply squeeze_zero_norm (fun n =>
    ((A n).le_opNorm (u n)).trans
      (mul_le_mul_of_nonneg_right (hbound n) (norm_nonneg _)))
  simpa only [norm_zero, mul_zero] using hu.norm.const_mul M

/-- Strong convergence and a uniform operator bound allow the input to vary. -/
theorem tail_strong_apply_tendsto (A : ℕ → E →L[ℝ] F) (A∞ : E →L[ℝ] F)
    {M : ℝ} (hbound : ∀ n, ‖A n‖ ≤ M)
    (hstrong : ∀ x, Tendsto (fun n => A n x) atTop (𝓝 (A∞ x)))
    {u : ℕ → E} {u∞ : E} (hu : Tendsto u atTop (𝓝 u∞)) :
    Tendsto (fun n => A n (u n)) atTop (𝓝 (A∞ u∞)) := by
  have hz : Tendsto (fun n => A n (u n - u∞)) atTop (𝓝 0) :=
    tail_bounded_apply_tendsto_zero A hbound
      (by simpa only [sub_self] using hu.sub tendsto_const_nhds)
  have h := hz.add (hstrong u∞)
  simpa only [map_sub, sub_add_cancel, zero_add] using h

end Normed

section Inverses

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]

/-- The inverse identity gives convergence once a right inverse of the limit is
known. Only the left-inverse identity for the approximating operators is needed. -/
theorem tail_inverse_tendsto_apply (A G : ℕ → E →L[ℝ] E)
    (A∞ G∞ : E →L[ℝ] E) {M : ℝ}
    (hleft : ∀ n x, G n (A n x) = x)
    (hright : ∀ x, A∞ (G∞ x) = x)
    (hbound : ∀ n, ‖G n‖ ≤ M)
    (hstrong : ∀ x, Tendsto (fun n => A n x) atTop (𝓝 (A∞ x)))
    (x : E) : Tendsto (fun n => G n x) atTop (𝓝 (G∞ x)) := by
  have herror : Tendsto (fun n => A∞ (G∞ x) - A n (G∞ x)) atTop (𝓝 0) := by
    simpa only [sub_self] using tendsto_const_nhds.sub (hstrong (G∞ x))
  have h := tail_bounded_apply_tendsto_zero G hbound herror
  have heq (n : ℕ) : G n (A∞ (G∞ x) - A n (G∞ x)) = G n x - G∞ x := by
    rw [map_sub, hright, hleft]
  have hz : Tendsto (fun n => G n x - G∞ x) atTop (𝓝 0) := by
    simpa only [heq] using h
  exact (tendsto_sub_nhds_zero_iff).mp hz

/-- Compression to a subspace, extended by the identity on its complement. -/
def tailCompression (P A : E →L[ℝ] E) : E →L[ℝ] E :=
  (P.comp A).comp P + (1 - P)

theorem tailCompression_apply (P A : E →L[ℝ] E) (x : E) :
    tailCompression P A x = P (A (P x)) + (x - P x) := by
  simp only [tailCompression, ContinuousLinearMap.add_apply,
    ContinuousLinearMap.comp_apply, ContinuousLinearMap.sub_apply,
    ContinuousLinearMap.one_apply]

/-- Uniformly bounded projections tending strongly to the identity give strong
convergence of the compressions of every bounded operator. -/
theorem tailCompression_tendsto_apply (P : ℕ → E →L[ℝ] E)
    (A : E →L[ℝ] E) {M : ℝ} (hbound : ∀ n, ‖P n‖ ≤ M)
    (hstrong : ∀ x, Tendsto (fun n => P n x) atTop (𝓝 x)) (x : E) :
    Tendsto (fun n => tailCompression (P n) A x) atTop (𝓝 (A x)) := by
  have hinner : Tendsto (fun n => A (P n x)) atTop (𝓝 (A x)) :=
    A.continuous.tendsto (x) |>.comp (hstrong x)
  have houter : Tendsto (fun n => P n (A (P n x))) atTop (𝓝 (A x)) :=
    tail_strong_apply_tendsto P (1 : E →L[ℝ] E) hbound hstrong hinner
  have hzero : Tendsto (fun n => x - P n x) atTop (𝓝 0) := by
    simpa only [sub_self] using tendsto_const_nhds.sub (hstrong x)
  simpa only [tailCompression_apply, add_zero] using houter.add hzero

end Inverses

section Hilbert

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [CompleteSpace E]

/-- Compression by a symmetric map preserves symmetry. Idempotence is not
needed for this identity. -/
theorem tailCompression_symmetric (P A : E →L[ℝ] E)
    (hP : P.toLinearMap.IsSymmetric) (hA : A.toLinearMap.IsSymmetric) :
    (tailCompression P A).toLinearMap.IsSymmetric := by
  intro x y
  change ⟪tailCompression P A x, y⟫_ℝ = ⟪x, tailCompression P A y⟫_ℝ
  simp only [tailCompression_apply, inner_add_left, inner_add_right,
    inner_sub_left, inner_sub_right, hP.apply_clm, hA.apply_clm]

/-- A strong limit of symmetric bounded operators remains symmetric. -/
theorem tail_strong_limit_symmetric (A : ℕ → E →L[ℝ] E) (A∞ : E →L[ℝ] E)
    (hsym : ∀ n, (A n).toLinearMap.IsSymmetric)
    (hstrong : ∀ x, Tendsto (fun n => A n x) atTop (𝓝 (A∞ x))) :
    A∞.toLinearMap.IsSymmetric := by
  intro x y
  apply tendsto_nhds_unique ((hstrong x).inner tendsto_const_nhds)
  exact (tendsto_const_nhds.inner (hstrong y)).congr'
    (Eventually.of_forall (fun n => (hsym n x y).symm))

/-- A symmetric strong limit with uniformly bounded left inverses has a bounded
two-sided inverse, with the same bound, and the given inverses converge strongly.
This also applies when the approximating maps are already known to have
two-sided inverses; no compactness of the Hilbert space is required. -/
theorem tail_exists_inverse_of_strong_limit (A G : ℕ → E →L[ℝ] E)
    (A∞ : E →L[ℝ] E) {M : ℝ}
    (hsym : ∀ n, (A n).toLinearMap.IsSymmetric)
    (hleft : ∀ n x, G n (A n x) = x)
    (hbound : ∀ n, ‖G n‖ ≤ M)
    (hstrong : ∀ x, Tendsto (fun n => A n x) atTop (𝓝 (A∞ x))) :
    ∃ G∞ : E →L[ℝ] E,
      (∀ x, G∞ (A∞ x) = x) ∧ (∀ x, A∞ (G∞ x) = x) ∧
      ‖G∞‖ ≤ M ∧ ∀ x, Tendsto (fun n => G n x) atTop (𝓝 (G∞ x)) := by
  have hM : 0 ≤ M := (norm_nonneg (G 0)).trans (hbound 0)
  have hlower (x : E) : ‖x‖ ≤ M * ‖A∞ x‖ := by
    apply ge_of_tendsto' ((hstrong x).norm.const_mul M)
    intro n
    calc
      ‖x‖ = ‖G n (A n x)‖ := congrArg norm (hleft n x).symm
      _ ≤ ‖G n‖ * ‖A n x‖ := (G n).le_opNorm (A n x)
      _ ≤ M * ‖A n x‖ := mul_le_mul_of_nonneg_right (hbound n) (norm_nonneg _)
  have hanti : AntilipschitzWith (⟨M, hM⟩ : ℝ≥0) A∞ :=
    A∞.antilipschitz_of_bound hlower
  have hker : A∞.ker = ⊥ := LinearMap.ker_eq_bot.mpr hanti.injective
  have hclosed : A∞.range.topologicalClosure = A∞.range :=
    ContinuousLinearMap.closed_range_of_antilipschitz hanti
  have hs : A∞.toLinearMap.IsSymmetric := tail_strong_limit_symmetric A A∞ hsym hstrong
  have hdense : A∞.range.topologicalClosure = ⊤ :=
    (Submodule.topologicalClosure_eq_top_iff _).mpr (hs.orthogonal_range.trans hker)
  have hrange : A∞.range = ⊤ := hclosed.symm.trans hdense
  let G∞ : E →L[ℝ] E := (ContinuousLinearEquiv.ofBijective A∞ hker hrange).symm
  have hGleft (x : E) : G∞ (A∞ x) = x :=
    ContinuousLinearEquiv.ofBijective_symm_apply_apply A∞ hker hrange x
  have hGright (x : E) : A∞ (G∞ x) = x :=
    ContinuousLinearEquiv.ofBijective_apply_symm_apply A∞ hker hrange x
  refine ⟨G∞, hGleft, hGright, ?_, ?_⟩
  · apply ContinuousLinearMap.opNorm_le_bound _ hM
    intro x
    simpa only [hGright] using hlower (G∞ x)
  · exact tail_inverse_tendsto_apply A G A∞ G∞ hleft hGright hbound hstrong

/-- Finite compressions with uniformly bounded inverses converge to the inverse
of the full symmetric operator. The maps `P n` may be arbitrary uniformly
bounded symmetric approximations of the identity. -/
theorem tail_exists_inverse_of_compressions (P G : ℕ → E →L[ℝ] E)
    (A : E →L[ℝ] E) {M L : ℝ}
    (hP : ∀ n, (P n).toLinearMap.IsSymmetric)
    (hA : A.toLinearMap.IsSymmetric)
    (hPbound : ∀ n, ‖P n‖ ≤ L)
    (hPstrong : ∀ x, Tendsto (fun n => P n x) atTop (𝓝 x))
    (hleft : ∀ n x, G n (tailCompression (P n) A x) = x)
    (hbound : ∀ n, ‖G n‖ ≤ M) :
    ∃ G∞ : E →L[ℝ] E,
      (∀ x, G∞ (A x) = x) ∧ (∀ x, A (G∞ x) = x) ∧
      ‖G∞‖ ≤ M ∧ ∀ x, Tendsto (fun n => G n x) atTop (𝓝 (G∞ x)) := by
  exact tail_exists_inverse_of_strong_limit (fun n => tailCompression (P n) A) G A
    (fun n => tailCompression_symmetric (P n) A (hP n) hA) hleft hbound
    (tailCompression_tendsto_apply P A hPbound hPstrong)

end Hilbert

end ContinuousFlexibility.Radial
