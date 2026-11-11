import ContinuousFlexibility.Statements.Analysis
import Mathlib.Topology.Algebra.Module.Spaces.ContinuousLinearMap

/-!
# Bilinear continuity in the projective grading

A product estimate in each original seminorm gives joint continuity.
The resulting bilinear map can therefore be curried into actual
continuous linear maps, as required by the tame calculus statement.
-/

noncomputable section

namespace ContinuousFlexibility.Analysis

open Filter
open scoped Topology

variable (E : ℕ → Type) [∀ n, NormedAddCommGroup (E n)] [∀ n, NormedSpace ℝ (E n)]
  (bond : ∀ n, E (n + 1) →L[ℝ] E n)

local notation "X" => ProjectiveLimit E bond
local notation "p" => gradedSeminorm E bond

theorem spaces_projective_bilinear_continuous (B : X →ₗ[ℝ] X →ₗ[ℝ] X)
    (hb : ∀ s, ∃ N : ℕ, ∃ C : ℝ, 0 ≤ C ∧ ∀ u v, p s (B u v) ≤ C * p N u * p N v) :
    Continuous (fun z : X × X => B z.1 z.2) := by
  apply continuous_iff_continuousAt.mpr
  intro z₀
  apply (tendsto_projectiveLimit_iff E bond).mpr
  intro s
  obtain ⟨N, C, hC, hb⟩ := hb s
  have hp : Continuous (p N) := continuous_gradedSeminorm E bond N
  have hid (u v : X) : B u v - B z₀.1 z₀.2 =
      B (u - z₀.1) v + B z₀.1 (v - z₀.2) := by
    rw [map_sub, LinearMap.sub_apply, map_sub]
    abel
  have hnorm (z : X × X) : ‖(B z.1 z.2).val s - (B z₀.1 z₀.2).val s‖ ≤
      C * p N (z.1 - z₀.1) * p N z.2 + C * p N z₀.1 * p N (z.2 - z₀.2) := by
    have he := congrArg (projectiveCoordinate E bond s) (hid z.1 z.2)
    simp only [(projectiveCoordinate E bond s).map_sub,
      (projectiveCoordinate E bond s).map_add, projectiveCoordinate_apply] at he
    rw [he]
    apply (norm_add_le _ _).trans
    exact add_le_add
      ((norm_coordinate_le_graded E bond le_rfl _).trans (hb (z.1 - z₀.1) z.2))
      ((norm_coordinate_le_graded E bond le_rfl _).trans (hb z₀.1 (z.2 - z₀.2)))
  have hlim : Tendsto (fun z : X × X =>
      C * p N (z.1 - z₀.1) * p N z.2 + C * p N z₀.1 * p N (z.2 - z₀.2))
      (𝓝 z₀) (𝓝 0) := by
    have hc : Continuous (fun z : X × X =>
        C * p N (z.1 - z₀.1) * p N z.2 + C * p N z₀.1 * p N (z.2 - z₀.2)) :=
      ((continuous_const.mul (hp.comp (continuous_fst.sub continuous_const))).mul
        (hp.comp continuous_snd)).add
        (continuous_const.mul (hp.comp (continuous_snd.sub continuous_const)))
    simpa only [sub_self, map_zero, mul_zero, zero_mul, add_zero] using
      (hc.continuousAt (x := z₀)).tendsto
  exact tendsto_iff_norm_sub_tendsto_zero.mpr (squeeze_zero (fun _ => norm_nonneg _) hnorm hlim)

/-- Bundle a jointly continuous bilinear map into the actual topology of
continuous linear maps. -/
def spaces_projective_bilinear_clm (B : X →ₗ[ℝ] X →ₗ[ℝ] X)
    (hB : Continuous (fun z : X × X => B z.1 z.2)) : X →L[ℝ] X →L[ℝ] X := by
  let L : X →ₗ[ℝ] X →L[ℝ] X :=
    { toFun := fun u => ⟨B u, hB.comp (continuous_const.prodMk continuous_id)⟩
      map_add' := by
        intro u v
        apply ContinuousLinearMap.ext
        intro w
        exact DFunLike.congr_fun (B.map_add u v) w
      map_smul' := by
        intro c u
        apply ContinuousLinearMap.ext
        intro v
        exact DFunLike.congr_fun (B.map_smul c u) v }
  exact ⟨L, ContinuousLinearMap.continuous_of_continuous_uncurry L hB⟩

theorem spaces_projective_bilinear_clm_apply (B : X →ₗ[ℝ] X →ₗ[ℝ] X)
    (hB : Continuous (fun z : X × X => B z.1 z.2)) (u v : X) :
    spaces_projective_bilinear_clm E bond B hB u v = B u v := rfl

theorem spaces_projective_bilinear_smoothTame [∀ n, CompleteSpace (E n)]
    (hH01 : Statements.H01Statement) (B : X →L[ℝ] X →L[ℝ] X)
    (hb : ∃ loss base : ℕ, ∀ s, base ≤ s → ∃ C : ℝ, 0 ≤ C ∧ ∀ u v,
      p s (B u v) ≤ C * (p (s + loss) u * p base v + p base u * p (s + loss) v)) :
    Statements.SmoothTameOn (Statements.pairGrading p p) p Set.univ
      (fun z : X × X => B z.1 z.2) :=
  (hH01.2 E E E bond bond bond).2.2.2.2.2 B hb

/-- Transport a pointwise estimate before exposing the concrete continuous
linear map to the projective tame calculus. -/
theorem spaces_projective_bilinear_smoothTame_of_eq [∀ n, CompleteSpace (E n)]
    (hH01 : Statements.H01Statement) (B : X →L[ℝ] X →L[ℝ] X)
    (f : X → X → X) (heq : ∀ u v, B u v = f u v)
    (hb : ∃ base loss : ℕ, ∀ s, ∃ C : ℝ, 0 ≤ C ∧ ∀ u v,
      p s (f u v) ≤ C * (p (s + loss) u * p base v + p base u * p (s + loss) v)) :
    Statements.SmoothTameOn (Statements.pairGrading p p) p Set.univ
      (fun z : X × X => f z.1 z.2) := by
  have hb' : ∃ loss base : ℕ, ∀ s, base ≤ s → ∃ C : ℝ, 0 ≤ C ∧ ∀ u v,
      p s (B u v) ≤ C * (p (s + loss) u * p base v + p base u * p (s + loss) v) := by
    obtain ⟨base, loss, hb⟩ := hb
    refine ⟨loss, base, fun s _ => ?_⟩
    obtain ⟨C, hC, hb⟩ := hb s
    exact ⟨C, hC, fun u v => by rw [heq]; exact hb u v⟩
  have h := spaces_projective_bilinear_smoothTame E bond hH01 B hb'
  simpa only [heq] using h

end ContinuousFlexibility.Analysis
