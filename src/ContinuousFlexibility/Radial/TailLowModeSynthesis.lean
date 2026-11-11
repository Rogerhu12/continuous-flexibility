import Mathlib.Analysis.InnerProductSpace.l2Space
import Mathlib.Analysis.Normed.Operator.Extend
import Mathlib.LinearAlgebra.Finsupp.LinearCombination

/-!
# Synthesis and averaging for the low tail modes

The index type can be `ℕ` for the entire tail or `Fin N` for a finite wall.
The vectors supplied to synthesis are the mass-normalized smooth hats in the
energy space. A bound for finite linear combinations constructs the actual
bounded synthesis map on `ℓ²`. Thus no summability assumption for an infinite
combination is left to the caller.

Analysis is built from a finite Bessel bound, with an adapter for normalized
mass indicators forming an orthonormal family in the physical `L²` space.
The Kronecker pairing of indicators with hats gives a genuine bounded
projection on the energy space and zero averages for its complementary part.
-/

noncomputable section

namespace ContinuousFlexibility.Radial

open Filter
open scoped Topology lp ENNReal InnerProductSpace RealInnerProductSpace

variable {ι : Type*} [DecidableEq ι]

/-- The usual embedding of finitely supported coefficients into `ℓ²`. -/
def tailFiniteEmbedding : (ι →₀ ℝ) →ₗ[ℝ] ℓ²(ι, ℝ) :=
  Finsupp.linearCombination ℝ (fun i => lp.single 2 i (1 : ℝ))

theorem tailFiniteEmbedding_single (i : ι) (c : ℝ) :
    tailFiniteEmbedding (Finsupp.single i c) = lp.single 2 i c := by
  rw [tailFiniteEmbedding, Finsupp.linearCombination_single, ← lp.single_smul]
  simp only [smul_eq_mul, mul_one]

theorem tailFiniteEmbedding_eq_sum (a : ι →₀ ℝ) :
    tailFiniteEmbedding a = ∑ i ∈ a.support, lp.single 2 i (a i) := by
  rw [tailFiniteEmbedding,
    Finsupp.linearCombination_apply_of_mem_supported ℝ (Finsupp.mem_supported_support ℝ a)]
  simp only [← lp.single_smul, smul_eq_mul, mul_one]

theorem tailFiniteEmbedding_apply (a : ι →₀ ℝ) (i : ι) :
    tailFiniteEmbedding a i = a i := by
  rw [tailFiniteEmbedding_eq_sum]
  simp only [lp.coeFn_sum, Finset.sum_apply, lp.single_apply]
  calc
    _ = (Pi.single i (a i) : ι → ℝ) i :=
      Finset.sum_eq_single i (fun j _ hji => Pi.single_eq_of_ne hji.symm _)
        (fun hi => by rw [Pi.single_eq_same, Finsupp.notMem_support_iff.mp hi])
    (Pi.single i (a i) : ι → ℝ) i = a i := Pi.single_eq_same _ _

theorem tailFiniteEmbedding_norm_sq (a : ι →₀ ℝ) :
    ‖tailFiniteEmbedding a‖ ^ 2 = ∑ i ∈ a.support, ‖a i‖ ^ 2 := by
  rw [tailFiniteEmbedding_eq_sum]
  simpa [Real.rpow_two] using
    lp.norm_sum_single (p := (2 : ℝ≥0∞)) (by norm_num) (fun i => a i) a.support

theorem tailFiniteEmbedding_denseRange : DenseRange (tailFiniteEmbedding (ι := ι)) := by
  intro x
  apply mem_closure_of_tendsto (lp.hasSum_single (by norm_num : (2 : ℝ≥0∞) ≠ ⊤) x)
  filter_upwards with s
  refine ⟨∑ i ∈ s, Finsupp.single i (x i), ?_⟩
  simp only [map_sum, tailFiniteEmbedding_single]

section Synthesis

variable {E F : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [CompleteSpace E]
  [NormedAddCommGroup F] [NormedSpace ℝ F]

/-- The continuous synthesis determined by a bound on finite combinations.
The accompanying lemmas require that bound and identify this extension. -/
def tailSynthesis (v : ι → E) : ℓ²(ι, ℝ) →L[ℝ] E :=
  (Finsupp.linearCombination ℝ v).extendOfNorm tailFiniteEmbedding

theorem tailSynthesis_on_finite {v : ι → E} {C : ℝ}
    (hbound : ∀ a : ι →₀ ℝ,
      ‖Finsupp.linearCombination ℝ v a‖ ≤ C * ‖tailFiniteEmbedding a‖)
    (a : ι →₀ ℝ) :
    tailSynthesis v (tailFiniteEmbedding a) = Finsupp.linearCombination ℝ v a :=
  LinearMap.extendOfNorm_eq tailFiniteEmbedding_denseRange ⟨C, hbound⟩ a

theorem tailSynthesis_single {v : ι → E} {C : ℝ}
    (hbound : ∀ a : ι →₀ ℝ,
      ‖Finsupp.linearCombination ℝ v a‖ ≤ C * ‖tailFiniteEmbedding a‖)
    (i : ι) (c : ℝ) : tailSynthesis v (lp.single 2 i c) = c • v i := by
  rw [← tailFiniteEmbedding_single, tailSynthesis_on_finite hbound,
    Finsupp.linearCombination_single]

theorem norm_tailSynthesis_le {v : ι → E} {C : ℝ} (hC : 0 ≤ C)
    (hbound : ∀ a : ι →₀ ℝ,
      ‖Finsupp.linearCombination ℝ v a‖ ≤ C * ‖tailFiniteEmbedding a‖) :
    ‖tailSynthesis v‖ ≤ C :=
  LinearMap.opNorm_extendOfNorm_le tailFiniteEmbedding_denseRange hC hbound

theorem tailSynthesis_hasSum {v : ι → E} {C : ℝ}
    (hbound : ∀ a : ι →₀ ℝ,
      ‖Finsupp.linearCombination ℝ v a‖ ≤ C * ‖tailFiniteEmbedding a‖)
    (x : ℓ²(ι, ℝ)) : HasSum (fun i => x i • v i) (tailSynthesis v x) := by
  simpa only [tailSynthesis_single hbound] using
    (lp.hasSum_single (by norm_num : (2 : ℝ≥0∞) ≠ ⊤) x).mapL (tailSynthesis v)

/-- Finite square bounds are sufficient for the synthesis construction. -/
theorem tailSynthesis_bound_of_sq {v : ι → E} {C : ℝ} (hC : 0 ≤ C)
    (hbound : ∀ a : ι →₀ ℝ,
      ‖Finsupp.linearCombination ℝ v a‖ ^ 2 ≤ C ^ 2 * ∑ i ∈ a.support, ‖a i‖ ^ 2)
    (a : ι →₀ ℝ) :
    ‖Finsupp.linearCombination ℝ v a‖ ≤ C * ‖tailFiniteEmbedding a‖ := by
  apply (sq_le_sq₀ (norm_nonneg _) (mul_nonneg hC (norm_nonneg _))).mp
  rw [mul_pow, tailFiniteEmbedding_norm_sq]
  exact hbound a

/-- Any derivative or other bounded coordinate estimate verified on finite
combinations passes to the synthesized vector by density. -/
theorem tailSynthesis_coordinate_bound {v : ι → E} {C ε : ℝ}
    (hbound : ∀ a : ι →₀ ℝ,
      ‖Finsupp.linearCombination ℝ v a‖ ≤ C * ‖tailFiniteEmbedding a‖)
    (D : E →L[ℝ] F)
    (hfinite : ∀ a : ι →₀ ℝ,
      ‖D (Finsupp.linearCombination ℝ v a)‖ ^ 2 ≤ ε * ‖tailFiniteEmbedding a‖ ^ 2)
    (x : ℓ²(ι, ℝ)) : ‖D (tailSynthesis v x)‖ ^ 2 ≤ ε * ‖x‖ ^ 2 := by
  refine tailFiniteEmbedding_denseRange.induction_on
    (p := fun y => ‖D (tailSynthesis v y)‖ ^ 2 ≤ ε * ‖y‖ ^ 2) x ?_ ?_
  · exact isClosed_le ((D.continuous.comp (tailSynthesis v).continuous).norm.pow 2)
      (continuous_const.mul (continuous_norm.pow 2))
  · intro a
    rw [tailSynthesis_on_finite hbound]
    exact hfinite a

/-- A continuous analysis map is a left inverse of synthesis when it has the
Kronecker values on the individual hats. -/
theorem tailSynthesis_analysis_leftInverse {v : ι → E} {C : ℝ}
    (hbound : ∀ a : ι →₀ ℝ,
      ‖Finsupp.linearCombination ℝ v a‖ ≤ C * ‖tailFiniteEmbedding a‖)
    (A : E →L[ℝ] ℓ²(ι, ℝ))
    (hhat : ∀ i, A (v i) = lp.single 2 i (1 : ℝ)) (x : ℓ²(ι, ℝ)) :
    A (tailSynthesis v x) = x := by
  have hmap : A.comp (tailSynthesis v) = (1 : ℓ²(ι, ℝ) →L[ℝ] ℓ²(ι, ℝ)) := by
    apply lp.ext_continuousLinearMap (by norm_num : (2 : ℝ≥0∞) ≠ ⊤)
    intro i
    apply ContinuousLinearMap.ext
    intro c
    simp only [ContinuousLinearMap.comp_apply, lp.singleContinuousLinearMap_apply,
      tailSynthesis_single hbound, map_smul, hhat, ContinuousLinearMap.one_apply,
      ← lp.single_smul, smul_eq_mul, mul_one]
  simpa only [ContinuousLinearMap.comp_apply, ContinuousLinearMap.one_apply] using
    congrArg (fun L : ℓ²(ι, ℝ) →L[ℝ] ℓ²(ι, ℝ) => L x) hmap

end Synthesis

section Analysis

variable {H : Type*} [NormedAddCommGroup H] [NormedSpace ℝ H]

private def tailAnalysisLinear (a : ι → H →L[ℝ] ℝ) (B : ℝ)
    (hbessel : ∀ x (s : Finset ι), ∑ i ∈ s, ‖a i x‖ ^ 2 ≤ B ^ 2 * ‖x‖ ^ 2) :
    H →ₗ[ℝ] ℓ²(ι, ℝ) where
  toFun x := ⟨fun i => a i x, memℓp_gen' (C := B ^ 2 * ‖x‖ ^ 2)
    (fun s => by simpa [Real.rpow_two] using hbessel x s)⟩
  map_add' x y := by
    apply lp.ext
    funext i
    simp only [lp.coeFn_add, Pi.add_apply, map_add]
  map_smul' c x := by
    apply lp.ext
    funext i
    simp only [lp.coeFn_smul, Pi.smul_apply, map_smul, RingHom.id_apply]

private theorem tailAnalysisLinear_apply (a : ι → H →L[ℝ] ℝ) (B : ℝ)
    (hbessel : ∀ x (s : Finset ι), ∑ i ∈ s, ‖a i x‖ ^ 2 ≤ B ^ 2 * ‖x‖ ^ 2)
    (x : H) (i : ι) : tailAnalysisLinear a B hbessel x i = a i x := by
  rfl

private theorem tailAnalysisLinear_bound (a : ι → H →L[ℝ] ℝ) {B : ℝ} (hB : 0 ≤ B)
    (hbessel : ∀ x (s : Finset ι), ∑ i ∈ s, ‖a i x‖ ^ 2 ≤ B ^ 2 * ‖x‖ ^ 2)
    (x : H) : ‖tailAnalysisLinear a B hbessel x‖ ≤ B * ‖x‖ := by
  apply lp.norm_le_of_forall_sum_le (by norm_num : 0 < (2 : ℝ≥0∞).toReal)
    (mul_nonneg hB (norm_nonneg _))
  intro s
  simpa [Real.rpow_two, tailAnalysisLinear_apply, mul_pow]
    using hbessel x s

/-- Bounded coefficient analysis constructed from a finite Bessel inequality. -/
def tailAnalysis (a : ι → H →L[ℝ] ℝ) (B : ℝ) (hB : 0 ≤ B)
    (hbessel : ∀ x (s : Finset ι), ∑ i ∈ s, ‖a i x‖ ^ 2 ≤ B ^ 2 * ‖x‖ ^ 2) :
    H →L[ℝ] ℓ²(ι, ℝ) :=
  (tailAnalysisLinear a B hbessel).mkContinuous B (tailAnalysisLinear_bound a hB hbessel)

theorem tailAnalysis_apply (a : ι → H →L[ℝ] ℝ) (B : ℝ) (hB : 0 ≤ B)
    (hbessel : ∀ x (s : Finset ι), ∑ i ∈ s, ‖a i x‖ ^ 2 ≤ B ^ 2 * ‖x‖ ^ 2)
    (x : H) (i : ι) : tailAnalysis a B hB hbessel x i = a i x := by
  simp only [tailAnalysis, LinearMap.mkContinuous_apply, tailAnalysisLinear_apply]

theorem norm_tailAnalysis_le (a : ι → H →L[ℝ] ℝ) (B : ℝ) (hB : 0 ≤ B)
    (hbessel : ∀ x (s : Finset ι), ∑ i ∈ s, ‖a i x‖ ^ 2 ≤ B ^ 2 * ‖x‖ ^ 2) :
    ‖tailAnalysis a B hB hbessel‖ ≤ B :=
  LinearMap.mkContinuous_norm_le _ hB (tailAnalysisLinear_bound a hB hbessel)

end Analysis

section OrthonormalAnalysis

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℝ H]

private theorem tailOrthonormal_bessel {e : ι → H} (he : Orthonormal ℝ e)
    (x : H) (s : Finset ι) :
    ∑ i ∈ s, ‖innerSL ℝ (e i) x‖ ^ 2 ≤ (1 : ℝ) ^ 2 * ‖x‖ ^ 2 := by
  simpa only [innerSL_apply_apply, one_pow, one_mul] using he.sum_inner_products_le (s := s) x

/-- Analysis against normalized mass indicators, once their orthonormality is
verified, has operator norm at most one. -/
def tailOrthonormalAnalysis (e : ι → H) (he : Orthonormal ℝ e) : H →L[ℝ] ℓ²(ι, ℝ) :=
  tailAnalysis (fun i => innerSL ℝ (e i)) 1 zero_le_one (tailOrthonormal_bessel he)

theorem tailOrthonormalAnalysis_apply (e : ι → H) (he : Orthonormal ℝ e)
    (x : H) (i : ι) : tailOrthonormalAnalysis e he x i = ⟪e i, x⟫_ℝ := by
  rw [tailOrthonormalAnalysis, tailAnalysis_apply, innerSL_apply_apply]

theorem norm_tailOrthonormalAnalysis_le (e : ι → H) (he : Orthonormal ℝ e) :
    ‖tailOrthonormalAnalysis e he‖ ≤ 1 :=
  norm_tailAnalysis_le _ _ _ _

theorem tailOrthonormalAnalysis_of_pairings (e : ι → H) (he : Orthonormal ℝ e)
    {w : ι → H} (hpair : ∀ i j, ⟪e i, w j⟫_ℝ = if i = j then 1 else 0)
    (j : ι) : tailOrthonormalAnalysis e he (w j) = lp.single 2 j (1 : ℝ) := by
  apply lp.ext
  funext i
  rw [tailOrthonormalAnalysis_apply, hpair, lp.single_apply]
  simp only [Pi.single_apply, eq_comm]

end OrthonormalAnalysis

section Projection

variable {E H F : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [CompleteSpace E]
  [NormedAddCommGroup H] [NormedSpace ℝ H] [NormedAddCommGroup F] [NormedSpace ℝ F]

/-- Low-mode projection on the energy space: take mass coefficients and
synthesize the normalized hats. -/
def tailLowProjection (I : E →L[ℝ] H) (A : H →L[ℝ] ℓ²(ι, ℝ)) (v : ι → E) :
    E →L[ℝ] E := (tailSynthesis v).comp (A.comp I)

theorem tailLowProjection_apply (I : E →L[ℝ] H) (A : H →L[ℝ] ℓ²(ι, ℝ)) (v : ι → E)
    (u : E) : tailLowProjection I A v u = tailSynthesis v (A (I u)) := by
  simp only [tailLowProjection, ContinuousLinearMap.comp_apply]

variable {v : ι → E} {C : ℝ}
  (hbound : ∀ a : ι →₀ ℝ,
    ‖Finsupp.linearCombination ℝ v a‖ ≤ C * ‖tailFiniteEmbedding a‖)
  (I : E →L[ℝ] H) (A : H →L[ℝ] ℓ²(ι, ℝ))
  (hhat : ∀ i, A (I (v i)) = lp.single 2 i (1 : ℝ))

include hbound hhat

theorem tailLowProjection_preserves_analysis (u : E) :
    A (I (tailLowProjection I A v u)) = A (I u) := by
  rw [tailLowProjection_apply]
  exact tailSynthesis_analysis_leftInverse hbound (A.comp I) hhat (A (I u))

theorem tailLowProjection_idempotent (u : E) :
    tailLowProjection I A v (tailLowProjection I A v u) = tailLowProjection I A v u := by
  rw [tailLowProjection_apply, tailLowProjection_preserves_analysis hbound I A hhat,
    tailLowProjection_apply]

theorem tailLowProjection_high_analysis_zero (u : E) :
    A (I (u - tailLowProjection I A v u)) = 0 := by
  rw [map_sub, map_sub, tailLowProjection_preserves_analysis hbound I A hhat, sub_self]

/-- A finite derivative bound, normalized by coefficient norm, gives the
required low-mode energy bound in the physical norm. -/
theorem tailLowProjection_energy_bound {ε : ℝ} (hε : 0 ≤ ε)
    (hA : ‖A‖ ≤ 1) (D : E →L[ℝ] F)
    (hfinite : ∀ a : ι →₀ ℝ,
      ‖D (Finsupp.linearCombination ℝ v a)‖ ^ 2 ≤ ε * ‖tailFiniteEmbedding a‖ ^ 2)
    (u : E) :
    ‖D (tailLowProjection I A v u)‖ ^ 2 ≤ ε * ‖I (tailLowProjection I A v u)‖ ^ 2 := by
  have hcoeff : ‖A (I u)‖ ≤ ‖I (tailLowProjection I A v u)‖ := by
    rw [← tailLowProjection_preserves_analysis hbound I A hhat u]
    exact ((A.le_opNorm _).trans
      (mul_le_mul_of_nonneg_right hA (norm_nonneg _))).trans_eq (one_mul _)
  calc
    ‖D (tailLowProjection I A v u)‖ ^ 2 ≤ ε * ‖A (I u)‖ ^ 2 := by
      rw [tailLowProjection_apply]
      exact tailSynthesis_coordinate_bound hbound D hfinite _
    _ ≤ ε * ‖I (tailLowProjection I A v u)‖ ^ 2 := by
      gcongr

end Projection

end ContinuousFlexibility.Radial
