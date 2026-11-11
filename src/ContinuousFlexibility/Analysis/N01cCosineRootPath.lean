import ContinuousFlexibility.Analysis.N01cEndpointDivision
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Deriv
import Mathlib.Analysis.SpecialFunctions.Sqrt

/-!
# A smooth compact coordinate for two simple roots

The cosine path stays in the same closed radial component for every real
time. The signed sine factor gives a smooth extension of the transformed
speed; equality with the original speed is used only on the physical
half-period, where the sine has the required sign.
-/

noncomputable section

namespace ContinuousFlexibility.Analysis

open Set
open scoped ContDiff

def rootCosinePath (l h t : ℝ) : ℝ :=
  l + (h - l) / 2 * (1 - Real.cos t)

theorem contDiff_rootCosinePath (l h : ℝ) :
    ContDiff ℝ ∞ (rootCosinePath l h) :=
  contDiff_const.add (contDiff_const.mul (contDiff_const.sub Real.contDiff_cos))

theorem hasDerivAt_rootCosinePath (l h t : ℝ) :
    HasDerivAt (rootCosinePath l h) ((h - l) / 2 * Real.sin t) t := by
  simpa only [rootCosinePath, zero_sub, neg_neg] using
    ((((hasDerivAt_const t (1 : ℝ)).sub (Real.hasDerivAt_cos t)).const_mul
      ((h - l) / 2)).const_add l)

@[simp] theorem rootCosinePath_zero (l h : ℝ) : rootCosinePath l h 0 = l := by
  simp only [rootCosinePath, Real.cos_zero, sub_self, mul_zero, add_zero]

@[simp] theorem rootCosinePath_pi (l h : ℝ) : rootCosinePath l h Real.pi = h := by
  rw [rootCosinePath, Real.cos_pi]
  ring

theorem rootCosinePath_mem_Icc {l h : ℝ} (hlh : l ≤ h) (t : ℝ) :
    rootCosinePath l h t ∈ Icc l h := by
  have hc : 0 ≤ (h - l) / 2 := div_nonneg (sub_nonneg.mpr hlh) (by norm_num)
  have hlo := mul_nonneg hc (sub_nonneg.mpr (Real.cos_le_one t))
  have hup := mul_le_mul_of_nonneg_left
    (show 1 - Real.cos t ≤ 2 by linarith [Real.neg_one_le_cos t]) hc
  dsimp only [rootCosinePath]
  constructor <;> linarith

theorem rootCosinePath_rootFactors (l h t : ℝ) :
    (rootCosinePath l h t - l) * (h - rootCosinePath l h t) =
      ((h - l) / 2) ^ 2 * Real.sin t ^ 2 := by
  calc
    _ = ((h - l) / 2) ^ 2 * (1 - Real.cos t ^ 2) := by
      dsimp only [rootCosinePath]
      ring
    _ = _ := by rw [show 1 - Real.cos t ^ 2 = Real.sin t ^ 2 by
      linarith [Real.sin_sq_add_cos_sq t]]

theorem rootCosinePath_mem_Ioo {l h t : ℝ} (hlh : l < h)
    (ht : t ∈ Ioo (0 : ℝ) Real.pi) : rootCosinePath l h t ∈ Ioo l h := by
  have hs : 0 < Real.sin t := Real.sin_pos_of_pos_of_lt_pi ht.1 ht.2
  have hc : 0 < (h - l) / 2 := div_pos (sub_pos.mpr hlh) (by norm_num)
  have hp : 0 < (rootCosinePath l h t - l) * (h - rootCosinePath l h t) := by
    rw [rootCosinePath_rootFactors]
    exact mul_pos (sq_pos_of_pos hc) (sq_pos_of_pos hs)
  rcases mul_pos_iff.mp hp with hp | hp
  · exact ⟨sub_pos.mp hp.1, sub_pos.mp hp.2⟩
  · exact False.elim ((not_lt_of_ge
      (sub_nonneg.mpr (rootCosinePath_mem_Icc hlh.le t).1)) hp.1)

/-- The exact square-root cancellation on the physical half-period. -/
theorem sqrt_comp_rootCosinePath
    {f : ℝ → ℝ} {l h t : ℝ} (hlh : l < h)
    (hl : f l = 0) (hh : f h = 0)
    (ht : t ∈ Ioo (0 : ℝ) Real.pi) :
    Real.sqrt (f (rootCosinePath l h t)) =
      (h - l) / 2 * Real.sin t *
        Real.sqrt (twoRootDivided f l h (rootCosinePath l h t)) := by
  have hs := Real.sin_pos_of_pos_of_lt_pi ht.1 ht.2
  have hc : 0 < (h - l) / 2 := div_pos (sub_pos.mpr hlh) (by norm_num)
  have he := twoRootDivided_mul_rootFactors hlh hl hh (rootCosinePath l h t)
  rw [rootCosinePath_rootFactors] at he
  have hf : f (rootCosinePath l h t) =
      ((h - l) / 2 * Real.sin t) ^ 2 *
        twoRootDivided f l h (rootCosinePath l h t) := by
    rw [← he]
    ring
  rw [hf, Real.sqrt_mul (sq_nonneg _), Real.sqrt_sq_eq_abs,
    abs_of_nonneg (mul_nonneg hc.le hs.le)]

/-- A single algebraic speed formula. Its sine is signed outside the
physical half-period; no equation for the supplied flow is asserted there. -/
def cosineRegularizedSpeed {E : Type*} (l h : ℝ)
    (A B : E × (ℝ × ℝ) → ℝ) (V : E × ℝ → ℝ)
    (p : E × (ℝ × ℝ)) : ℝ :=
  -((h - l) / 2 * Real.sin p.2.1) *
      A (p.1, (rootCosinePath l h p.2.1, p.2.2)) -
    ((h - l) / 2) ^ 2 * Real.sin p.2.1 ^ 2 *
      B (p.1, (rootCosinePath l h p.2.1, p.2.2)) *
      Real.sqrt (V (p.1, rootCosinePath l h p.2.1))

theorem cosineRegularizedSpeed_eq_transformed
    {E : Type*} {l h : ℝ} (hlh : l < h)
    (A B : E × (ℝ × ℝ) → ℝ) (Q : E × ℝ → ℝ)
    {x : E} {t θ : ℝ} (hl : Q (x, l) = 0) (hh : Q (x, h) = 0)
    (ht : t ∈ Ioo (0 : ℝ) Real.pi) :
    cosineRegularizedSpeed l h A B
        (fun p => twoRootDivided (fun r => Q (p.1, r)) l h p.2) (x, (t, θ)) =
      ((h - l) / 2 * Real.sin t) *
        (-A (x, (rootCosinePath l h t, θ)) -
          B (x, (rootCosinePath l h t, θ)) * Real.sqrt (Q (x, rootCosinePath l h t))) := by
  rw [sqrt_comp_rootCosinePath hlh hl hh ht]
  dsimp only [cosineRegularizedSpeed]
  ring

section Parameters

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]

/-- Joint smoothness follows from the actual radial inputs and strict
positivity of the divided optical square on the whole closed component. -/
theorem contDiffOn_cosineRegularizedSpeed
    {U : Set E} {R : Set ℝ} {l h : ℝ} (hlh : l ≤ h)
    (hclosed : Icc l h ⊆ R)
    {A B : E × (ℝ × ℝ) → ℝ} {V : E × ℝ → ℝ}
    (hA : ContDiffOn ℝ ∞ A (U ×ˢ (R ×ˢ (univ : Set ℝ))))
    (hB : ContDiffOn ℝ ∞ B (U ×ˢ (R ×ˢ (univ : Set ℝ))))
    (hV : ContDiffOn ℝ ∞ V (U ×ˢ R))
    (hpos : ∀ x ∈ U, ∀ r ∈ Icc l h, 0 < V (x, r)) :
    ContDiffOn ℝ ∞ (cosineRegularizedSpeed l h A B V)
      (U ×ˢ (univ : Set (ℝ × ℝ))) := by
  have hpath : ContDiff ℝ ∞ (fun p : E × (ℝ × ℝ) =>
      (p.1, (rootCosinePath l h p.2.1, p.2.2))) :=
    contDiff_fst.prodMk (((contDiff_rootCosinePath l h).comp contDiff_snd.fst).
      prodMk contDiff_snd.snd)
  have hmap : MapsTo (fun p : E × (ℝ × ℝ) =>
      (p.1, (rootCosinePath l h p.2.1, p.2.2)))
      (U ×ˢ (univ : Set (ℝ × ℝ))) (U ×ˢ (R ×ˢ (univ : Set ℝ))) :=
    fun p hp => ⟨hp.1, hclosed (rootCosinePath_mem_Icc hlh p.2.1), mem_univ _⟩
  have hsin : ContDiff ℝ ∞ (fun p : E × (ℝ × ℝ) => Real.sin p.2.1) :=
    Real.contDiff_sin.comp contDiff_snd.fst
  have hroot : ContDiffOn ℝ ∞
      (fun p : E × (ℝ × ℝ) => Real.sqrt (V (p.1, rootCosinePath l h p.2.1)))
      (U ×ˢ (univ : Set (ℝ × ℝ))) :=
    (hV.comp (contDiff_fst.prodMk
      ((contDiff_rootCosinePath l h).comp contDiff_snd.fst)).contDiffOn
      (fun p hp => ⟨hp.1, hclosed (rootCosinePath_mem_Icc hlh p.2.1)⟩)).sqrt
        (fun p hp => (hpos p.1 hp.1 _ (rootCosinePath_mem_Icc hlh p.2.1)).ne')
  exact ((contDiffOn_const.mul hsin.contDiffOn).neg.mul
    (hA.comp hpath.contDiffOn hmap)).sub
      (((contDiffOn_const.mul (hsin.pow 2).contDiffOn).mul
        (hB.comp hpath.contDiffOn hmap)).mul hroot)

end Parameters

end ContinuousFlexibility.Analysis
