import ContinuousFlexibility.Analysis.SpacesBilinearContinuity
import Mathlib.Analysis.Calculus.MeanValue
import Mathlib.LinearAlgebra.Multilinear.Basic

/-!
# Joint continuity of parameterized projective multilinear maps

Finite products of original seminorms give continuity in the multilinear
directions. Genuine line derivatives and local seminorm bounds give a
Banach-level mean-value estimate in the base point. Together these prove
joint continuity in the actual projective topology.
-/

noncomputable section

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

namespace ContinuousFlexibility.Analysis

open Set Filter
open scoped Topology BigOperators

variable (E : ℕ → Type*) [∀ n, NormedAddCommGroup (E n)] [∀ n, NormedSpace ℝ (E n)]
  (bond : ∀ n, E (n + 1) →L[ℝ] E n)

local notation "X" => ProjectiveLimit E bond
local notation "p" => gradedSeminorm E bond

private def spacesMultilinearDifferenceVector {V : Type*} [AddCommGroup V] {k : ℕ}
    (v w : Fin k → V) (i j : Fin k) : V :=
  if j < i then v j else if i = j then v j - w j else w j

private theorem spaces_multilinear_difference {k : ℕ}
    (B : MultilinearMap ℝ (fun _ : Fin k => X) X) (v w : Fin k → X) :
    B v - B w = ∑ i, B (spacesMultilinearDifferenceVector v w i) := by
  unfold spacesMultilinearDifferenceVector
  simpa only [Finset.piecewise_univ,
    Finset.mem_univ, true_implies] using B.map_sub_map_piecewise v w Finset.univ

/-- A product bound in each original seminorm makes an actual multilinear
map continuous on the product of the projective spaces. -/
theorem spaces_projective_multilinear_continuous {k : ℕ}
    (B : MultilinearMap ℝ (fun _ : Fin k => X) X)
    (hb : ∀ s, ∃ N : ℕ, ∃ C : ℝ, 0 ≤ C ∧ ∀ v,
      p s (B v) ≤ C * ∏ i, p N (v i)) :
    Continuous B := by
  apply continuous_iff_continuousAt.mpr
  intro v₀
  apply (tendsto_projectiveLimit_iff E bond).mpr
  intro s
  obtain ⟨N, C, _hC, hb⟩ := hb s
  have hp : Continuous (p N) := continuous_gradedSeminorm E bond N
  have hnorm (v : Fin k → X) : ‖(B v).val s - (B v₀).val s‖ ≤
      ∑ i, C * ∏ j, p N (spacesMultilinearDifferenceVector v v₀ i j) := by
    have he := congrArg (projectiveCoordinate E bond s)
      (spaces_multilinear_difference E bond B v v₀)
    simp only [map_sub, map_sum, projectiveCoordinate_apply] at he
    rw [he]
    apply (norm_sum_le _ _).trans
    exact Finset.sum_le_sum fun i _ =>
      (norm_coordinate_le_graded E bond le_rfl _).trans (hb _)
  have hvec (i j : Fin k) :
      Continuous (fun v : Fin k → X => spacesMultilinearDifferenceVector v v₀ i j) := by
    unfold spacesMultilinearDifferenceVector
    split_ifs
    · exact continuous_apply j
    · exact (continuous_apply j).sub continuous_const
    · exact continuous_const
  have hc : Continuous (fun v : Fin k → X =>
      ∑ i, C * ∏ j, p N (spacesMultilinearDifferenceVector v v₀ i j)) :=
    continuous_finsetSum _ fun i _ => continuous_const.mul
      (continuous_finsetProd _ fun j _ => hp.comp (hvec i j))
  have hz : (∑ i, C * ∏ j, p N (spacesMultilinearDifferenceVector v₀ v₀ i j)) = 0 := by
    apply Finset.sum_eq_zero
    intro i _
    have hprod : (∏ j, p N (spacesMultilinearDifferenceVector v₀ v₀ i j)) = 0 :=
      Finset.prod_eq_zero (Finset.mem_univ i) (by
        simp only [spacesMultilinearDifferenceVector, lt_self_iff_false, ite_false,
          ite_true, sub_self, map_zero])
    rw [hprod, mul_zero]
  have hlim : Tendsto (fun v : Fin k → X =>
      ∑ i, C * ∏ j, p N (spacesMultilinearDifferenceVector v v₀ i j)) (𝓝 v₀) (𝓝 0) := by
    simpa only [hz] using (hc.continuousAt (x := v₀)).tendsto
  exact tendsto_iff_norm_sub_tendsto_zero.mpr
    (squeeze_zero (fun _ => norm_nonneg _) hnorm hlim)

private theorem spaces_seminorm_segment_le {V : Type*} [AddCommGroup V] [Module ℝ V]
    (q : Seminorm ℝ V) (u w : V) (t : ℝ) (ht : t ∈ Icc (0 : ℝ) 1) :
    q (u + t • w) ≤ q u + q w := by
  calc
    q (u + t • w) ≤ q u + q (t • w) := map_add_le_add q _ _
    _ = q u + t * q w := by rw [map_smul_eq_mul, Real.norm_of_nonneg ht.1]
    _ ≤ q u + q w := add_le_add le_rfl
      (by simpa only [one_mul] using mul_le_mul_of_nonneg_right ht.2 (apply_nonneg q w))

private theorem spaces_projective_translated_line_deriv
    (f : X → X) (df : X → X → X)
    (hf : ∀ x w, HasProjectiveLineDerivAt f (df x w) x w)
    (u w : X) (s : ℕ) (t : ℝ) :
    HasDerivAt (fun r : ℝ => (f (u + r • w)).val s) (df (u + t • w) w |>.val s) t := by
  have hh := (hasProjectiveLineDerivAt_iff_levels f
    (df (u + t • w) w) (u + t • w) w).mp (hf (u + t • w) w) s
  apply hasDerivAt_iff_tendsto_slope_zero.mpr
  simpa only [zero_add, zero_smul, add_zero, add_smul, add_assoc] using hh.tendsto_slope_zero

private theorem spaces_coarse_segment_bound {V : Type*} [AddCommGroup V] [Module ℝ V]
    {k : ℕ} (lo high : Seminorm ℝ V) (hmono : ∀ x, lo x ≤ high x)
    (F : V → (Fin (k + 1) → V) → ℝ) {C R : ℝ} (hC : 0 ≤ C)
    (hF : ∀ x v, lo x ≤ R → F x v ≤ C * (1 + high x) * ∏ i, high (v i))
    (u w : V) (v : Fin k → V) (hR : lo u + 1 ≤ R) (hw : high w ≤ 1)
    (t : ℝ) (ht : t ∈ Icc (0 : ℝ) 1) :
    F (u + t • w) (Fin.cons w v) ≤
      C * (2 + high u) * high w * ∏ i, high (v i) := by
  have hlo : lo (u + t • w) ≤ R :=
    (spaces_seminorm_segment_le lo u w t ht).trans
      ((add_le_add le_rfl ((hmono w).trans hw)).trans hR)
  have hhigh : high (u + t • w) ≤ high u + 1 :=
    (spaces_seminorm_segment_le high u w t ht).trans (add_le_add le_rfl hw)
  calc
    F (u + t • w) (Fin.cons w v) ≤
        C * (1 + high (u + t • w)) *
          ∏ i : Fin (k + 1), high ((Fin.cons w v : Fin (k + 1) → V) i) :=
      hF (u + t • w) (Fin.cons w v) hlo
    _ = C * (1 + high (u + t • w)) * (high w * ∏ i, high (v i)) := by
      exact congrArg (fun z : ℝ => C * (1 + high (u + t • w)) * z)
        (Fin.prod_univ_succ
          (fun i : Fin (k + 1) => high ((Fin.cons w v : Fin (k + 1) → V) i)))
    _ ≤ C * (2 + high u) * (high w * ∏ i, high (v i)) :=
      mul_le_mul_of_nonneg_right
        (mul_le_mul_of_nonneg_left (by linarith) hC)
        (mul_nonneg (apply_nonneg high w)
          (Finset.prod_nonneg (fun i _ => apply_nonneg high (v i))))
    _ = _ := by ring

private theorem spaces_projective_base_variation_bound {k : ℕ}
    (B : X → (Fin k → X) → X) (D : X → (Fin (k + 1) → X) → X)
    (hline : ∀ u v w, HasProjectiveLineDerivAt (fun x => B x v)
      (D u (Fin.cons w v)) u w)
    {base s N : ℕ} {C R : ℝ} (hN : base ≤ N) (hC : 0 ≤ C)
    (hD : ∀ u v, p base u ≤ R → p s (D u v) ≤ C * (1 + p N u) * ∏ i, p N (v i))
    (u₀ u : X) (v : Fin k → X) (hR : p base u₀ + 1 ≤ R) (hδ : p N (u - u₀) ≤ 1) :
    ‖(B u v).val s - (B u₀ v).val s‖ ≤
      C * (2 + p N u₀) * p N (u - u₀) * ∏ i, p N (v i) := by
  let du := u - u₀
  let line (t : ℝ) : X := u₀ + t • du
  let df (t : ℝ) : E s := (D (line t) (Fin.cons du v)).val s
  have hd (t : ℝ) : HasDerivAt (fun r => (B (line r) v).val s) (df t) t :=
    spaces_projective_translated_line_deriv E bond (fun x => B x v)
      (fun x w => D x (Fin.cons w v)) (fun x w => hline x v w) u₀ du s t
  have hb (t : ℝ) (ht : t ∈ Icc (0 : ℝ) 1) :
      ‖df t‖ ≤ C * (2 + p N u₀) * p N du * ∏ i, p N (v i) := by
    apply (norm_coordinate_le_graded E bond le_rfl (D (line t) (Fin.cons du v))).trans
    exact spaces_coarse_segment_bound (p base) (p N)
      (fun x => gradedSeminorm_monotone E bond hN x) (fun x z => p s (D x z))
      hC hD u₀ du v hR hδ t ht
  have hm := Convex.norm_image_sub_le_of_norm_hasDerivWithin_le
    (fun t ht => (hd t).hasDerivWithinAt) hb (convex_Icc (0 : ℝ) 1)
    (by simp : (0 : ℝ) ∈ Icc (0 : ℝ) 1) (by simp : (1 : ℝ) ∈ Icc (0 : ℝ) 1)
  have he : u₀ + du = u := by dsimp only [du]; abel
  simpa only [line, one_smul, zero_smul, add_zero, he, sub_zero, norm_one, mul_one] using hm

/-- Genuine projective line derivatives and local seminorm product bounds
give joint continuity of a parameterized multilinear map. -/
theorem spaces_projective_parameter_multilinear_continuous {k : ℕ} (base : ℕ)
    (B : X → MultilinearMap ℝ (fun _ : Fin k => X) X)
    (D : X → (Fin (k + 1) → X) → X)
    (hline : ∀ u v w, HasProjectiveLineDerivAt (fun x => B x v)
      (D u (Fin.cons w v)) u w)
    (hB : ∀ (s : ℕ) (R : ℝ), 1 ≤ R → ∃ N : ℕ, base ≤ N ∧ ∃ C : ℝ, 0 ≤ C ∧
      ∀ u, p base u ≤ R → ∀ v, p s (B u v) ≤ C * (1 + p N u) * ∏ i, p N (v i))
    (hD : ∀ (s : ℕ) (R : ℝ), 1 ≤ R → ∃ N : ℕ, base ≤ N ∧ ∃ C : ℝ, 0 ≤ C ∧
      ∀ u, p base u ≤ R → ∀ v, p s (D u v) ≤ C * (1 + p N u) * ∏ i, p N (v i)) :
    Continuous (fun z : X × (Fin k → X) => B z.1 z.2) := by
  have hfixed (u₀ : X) : Continuous (B u₀) := by
    apply spaces_projective_multilinear_continuous E bond (B u₀)
    intro s
    have hR : 1 ≤ p base u₀ + 1 := by linarith [apply_nonneg (p base) u₀]
    obtain ⟨N, _hN, C, hC, hb⟩ := hB s (p base u₀ + 1) hR
    refine ⟨N, C * (1 + p N u₀), mul_nonneg hC (by positivity), fun v => ?_⟩
    exact hb u₀ (by linarith) v
  apply continuous_iff_continuousAt.mpr
  intro z₀
  apply (tendsto_projectiveLimit_iff E bond).mpr
  intro s
  let R := p base z₀.1 + 1
  have hR : 1 ≤ R := by dsimp only [R]; linarith [apply_nonneg (p base) z₀.1]
  obtain ⟨N, hN, C, hC, hd⟩ := hD s R hR
  have hp : Continuous (p N) := continuous_gradedSeminorm E bond N
  have hcδ : Continuous (fun z : X × (Fin k → X) => p N (z.1 - z₀.1)) :=
    hp.comp (continuous_fst.sub continuous_const)
  have hδlim : Tendsto (fun z : X × (Fin k → X) => p N (z.1 - z₀.1)) (𝓝 z₀) (𝓝 0) := by
    simpa only [sub_self, map_zero] using (hcδ.continuousAt (x := z₀)).tendsto
  have hnear : ∀ᶠ z : X × (Fin k → X) in 𝓝 z₀, p N (z.1 - z₀.1) ≤ 1 := by
    have ht : ∀ᶠ z : X × (Fin k → X) in 𝓝 z₀, p N (z.1 - z₀.1) < 1 :=
      hδlim (Iio_mem_nhds zero_lt_one)
    exact ht.mono (fun _ hz => hz.le)
  have hnorm : ∀ᶠ z : X × (Fin k → X) in 𝓝 z₀,
      ‖(B z.1 z.2).val s - (B z₀.1 z.2).val s‖ ≤
        C * (2 + p N z₀.1) * p N (z.1 - z₀.1) * ∏ i, p N (z.2 i) := by
    filter_upwards [hnear] with z hz
    exact spaces_projective_base_variation_bound E bond (fun u v => B u v) D hline
      hN hC (fun u v hu => hd u hu v) z₀.1 z.1 z.2 le_rfl hz
  have hcbound : Continuous (fun z : X × (Fin k → X) =>
      C * (2 + p N z₀.1) * p N (z.1 - z₀.1) * ∏ i, p N (z.2 i)) :=
    (continuous_const.mul hcδ).mul
      (continuous_finsetProd _ fun i _ => hp.comp ((continuous_apply i).comp continuous_snd))
  have hboundlim : Tendsto (fun z : X × (Fin k → X) =>
      C * (2 + p N z₀.1) * p N (z.1 - z₀.1) * ∏ i, p N (z.2 i)) (𝓝 z₀) (𝓝 0) := by
    simpa only [sub_self, map_zero, mul_zero, zero_mul] using
      (hcbound.continuousAt (x := z₀)).tendsto
  have hbase : Tendsto (fun z : X × (Fin k → X) =>
      (B z.1 z.2).val s - (B z₀.1 z.2).val s) (𝓝 z₀) (𝓝 0) :=
    tendsto_zero_iff_norm_tendsto_zero.mpr
      (squeeze_zero' (Eventually.of_forall (fun _ => norm_nonneg _)) hnorm hboundlim)
  have hcdir : Continuous (fun z : X × (Fin k → X) => (B z₀.1 z.2).val s) :=
    (projectiveCoordinate E bond s).continuous.comp ((hfixed z₀.1).comp continuous_snd)
  have hdir := (hcdir.continuousAt (x := z₀)).tendsto
  simpa only [sub_add_cancel, zero_add] using hbase.add hdir

end ContinuousFlexibility.Analysis
