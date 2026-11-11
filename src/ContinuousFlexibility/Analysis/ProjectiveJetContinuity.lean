import ContinuousFlexibility.Analysis.CircleMultilinearRealization

/-!
# Joint continuity from actual line derivatives and seminorm bounds

Every target coordinate is a genuine Banach space. The mean value
estimate there controls variation of the base point; the multilinear
telescoping estimate controls variation of the directions. Thus a tower
with actual line derivatives and uniform continuous-seminorm bounds
has the joint continuity required by SmoothDirections.
-/

noncomputable section

namespace ContinuousFlexibility.Analysis

open Set Filter ContinuousFlexibility.Statements
open scoped Topology BigOperators

variable {E : Type*} [TopologicalSpace E] [AddCommGroup E] [Module ℝ E]
  [IsTopologicalAddGroup E] [ContinuousSMul ℝ E]
  {F : ℕ → Type*} [∀ s, NormedAddCommGroup (F s)] [∀ s, NormedSpace ℝ (F s)]
  {bond : ∀ s, F (s + 1) →L[ℝ] F s} {U : Set E}

theorem projectiveJet_hasDerivAt_line
    (A : ∀ n : ℕ, E → E [×n]→L[ℝ] ProjectiveLimit F bond)
    (hline : ∀ n x, x ∈ U → ∀ (v : Fin n → E) (w : E),
      HasProjectiveLineDerivAt (fun y => A n y v) (A (n + 1) x (Fin.cons w v)) x w)
    (n s : ℕ) (x w : E) (v : Fin n → E) {t : ℝ} (ht : x + t • w ∈ U) :
    HasDerivAt (fun u : ℝ => (A n (x + u • w) v).val s)
      ((A (n + 1) (x + t • w) (Fin.cons w v)).val s) t := by
  apply hasDerivAt_iff_tendsto_slope_zero.mpr
  have hd := (hline n (x + t • w) ht v w).clm_comp (projectiveCoordinate F bond s)
  simpa only [HasProjectiveLineDerivAt, HasProjectiveCurveDerivAt,
    projectiveCoordinate_apply, zero_add, zero_smul, add_zero, add_smul, add_assoc] using hd

theorem projectiveJet_base_variation_le
    (A : ∀ n : ℕ, E → E [×n]→L[ℝ] ProjectiveLimit F bond)
    (hline : ∀ n x, x ∈ U → ∀ (v : Fin n → E) (w : E),
      HasProjectiveLineDerivAt (fun y => A n y v) (A (n + 1) x (Fin.cons w v)) x w)
    (hU : Convex ℝ U) (n s : ℕ) (p : Seminorm ℝ E) {B : ℝ} (hB : 0 ≤ B)
    (hbound : ∀ y ∈ U, ∀ v : Fin (n + 1) → E,
      ‖(A (n + 1) y v).val s‖ ≤ B * (1 + p y) * ∏ i, p (v i))
    {x y : E} (hx : x ∈ U) (hy : y ∈ U) (v : Fin n → E) :
    ‖(A n y v).val s - (A n x v).val s‖ ≤
      B * (1 + p x + p (y - x)) * (p (y - x) * ∏ i, p (v i)) := by
  have hmem (t : ℝ) (ht : t ∈ Icc (0 : ℝ) 1) : x + t • (y - x) ∈ U := by
    have hm := hU hx hy (sub_nonneg.mpr ht.2) ht.1 (sub_add_cancel 1 t)
    convert hm using 1 <;> module
  have hderiv (t : ℝ) (ht : t ∈ Icc (0 : ℝ) 1) :
      HasDerivWithinAt (fun u => (A n (x + u • (y - x)) v).val s)
        ((A (n + 1) (x + t • (y - x)) (Fin.cons (y - x) v)).val s)
        (Icc (0 : ℝ) 1) t :=
    (projectiveJet_hasDerivAt_line A hline n s x (y - x) v (hmem t ht)).hasDerivWithinAt
  have hnorm (t : ℝ) (ht : t ∈ Icc (0 : ℝ) 1) :
      ‖(A (n + 1) (x + t • (y - x)) (Fin.cons (y - x) v)).val s‖ ≤
        B * (1 + p x + p (y - x)) * (p (y - x) * ∏ i, p (v i)) := by
    have hb := hbound _ (hmem t ht) (Fin.cons (y - x) v)
    simp only [Fin.prod_univ_succ, Fin.cons_zero, Fin.cons_succ] at hb
    exact hb.trans (mul_le_mul_of_nonneg_right
      (mul_le_mul_of_nonneg_left (by linarith [seminorm_affine_segment_le p x y ht]) hB)
      (mul_nonneg (apply_nonneg p (y - x))
        (Finset.prod_nonneg (fun i _ => apply_nonneg p (v i)))))
  have hm := norm_image_sub_le_of_norm_deriv_le_segment_01' hderiv
    (fun t ht => hnorm t ⟨ht.1, ht.2.le⟩)
  simpa only [zero_smul, add_zero, one_smul, add_sub_cancel] using hm

theorem continuousOn_projectiveJets_of_seminorm_bounds
    (A : ∀ n : ℕ, E → E [×n]→L[ℝ] ProjectiveLimit F bond)
    (hU : IsOpen U) (hc : Convex ℝ U)
    (hline : ∀ n x, x ∈ U → ∀ (v : Fin n → E) (w : E),
      HasProjectiveLineDerivAt (fun y => A n y v) (A (n + 1) x (Fin.cons w v)) x w)
    (hbound : ∀ n s, ∃ p : Seminorm ℝ E, ∃ B : ℝ, Continuous p ∧ 0 ≤ B ∧
      ∀ x ∈ U, ∀ v : Fin n → E,
        ‖(A n x v).val s‖ ≤ B * (1 + p x) * ∏ i, p (v i))
    (n : ℕ) :
    ContinuousOn (fun z : E × (Fin n → E) => A n z.1 z.2) (U ×ˢ univ) := by
  have hcoordinate (s : ℕ) :
      ContinuousOn (fun z : E × (Fin n → E) => (A n z.1 z.2).val s) (U ×ˢ univ) := by
    obtain ⟨p, B, hp, hB, hb⟩ := hbound (n + 1) s
    obtain ⟨q, C, hq, hC, hcq⟩ := hbound n s
    rintro ⟨x, v⟩ hx
    apply ContinuousAt.continuousWithinAt
    apply tendsto_iff_norm_sub_tendsto_zero.mpr
    let err : E × (Fin n → E) → ℝ := fun z =>
      B * (1 + p x + p (z.1 - x)) * (p (z.1 - x) * ∏ j, p (z.2 j)) +
        C * (1 + q x) * seminormMultilinearDifference q v z.2
    have hpbase : Continuous (fun z : E × (Fin n → E) => p (z.1 - x)) :=
      hp.comp (continuous_fst.sub continuous_const)
    have hpdirs : Continuous (fun z : E × (Fin n → E) => ∏ j, p (z.2 j)) :=
      continuous_finsetProd _ (fun j _ => hp.comp ((continuous_apply j).comp continuous_snd))
    have herr : Continuous err :=
      ((continuous_const.mul (continuous_const.add hpbase)).mul (hpbase.mul hpdirs)).add
        (continuous_const.mul ((continuous_seminormMultilinearDifference q hq v).comp continuous_snd))
    have herr0 : err (x, v) = 0 := by
      simp only [err, sub_self, map_zero, mul_zero, zero_mul,
        seminormMultilinearDifference_self, add_zero]
    have hmem : ∀ᶠ z : E × (Fin n → E) in 𝓝 (x, v), z.1 ∈ U :=
      continuous_fst.continuousAt.eventually (hU.mem_nhds hx.1)
    have hupper : ∀ᶠ z : E × (Fin n → E) in 𝓝 (x, v),
        ‖(A n z.1 z.2).val s - (A n x v).val s‖ ≤ err z := by
      filter_upwards [hmem] with z hz
      have hbase := projectiveJet_base_variation_le A hline hc n s p hB hb hx.1 hz z.2
      let Q := projectiveCoordinate F bond s
      let M := Q.toLinearMap.compMultilinearMap (A n x).toMultilinearMap
      have hdirs := norm_multilinear_sub_le_of_seminorm_bound M q (C * (1 + q x))
        (hcq x hx.1) v z.2
      exact (norm_sub_le ((A n z.1 z.2).val s) ((A n x z.2).val s)
        ((A n x v).val s)).trans (add_le_add hbase hdirs)
    exact squeeze_zero' (Eventually.of_forall (fun _ => norm_nonneg _)) hupper
      (by simpa only [herr0] using herr.tendsto (x, v))
  intro z hz
  rw [ContinuousWithinAt, tendsto_projectiveLimit_iff]
  exact fun s => hcoordinate s z hz

def smoothDirectionsOfProjectiveJetBounds
    {f : E → ProjectiveLimit F bond}
    (A : ∀ n : ℕ, E → E [×n]→L[ℝ] ProjectiveLimit F bond)
    (hU : IsOpen U) (hc : Convex ℝ U)
    (hzero : ∀ x ∈ U, A 0 x Fin.elim0 = f x)
    (hline : ∀ n x, x ∈ U → ∀ (v : Fin n → E) (w : E),
      HasProjectiveLineDerivAt (fun y => A n y v) (A (n + 1) x (Fin.cons w v)) x w)
    (hbound : ∀ n s, ∃ p : Seminorm ℝ E, ∃ B : ℝ, Continuous p ∧ 0 ≤ B ∧
      ∀ x ∈ U, ∀ v : Fin n → E,
        ‖(A n x v).val s‖ ≤ B * (1 + p x) * ∏ i, p (v i)) :
    SmoothDirections U f where
  open_domain := hU
  D := A
  zero := hzero
  continuous := continuousOn_projectiveJets_of_seminorm_bounds A hU hc hline hbound
  derivative := hline

end ContinuousFlexibility.Analysis
