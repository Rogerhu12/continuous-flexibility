module

public import ContinuousFlexibility.Analysis.N04PositiveGeometryAtomDirections
public import ContinuousFlexibility.Analysis.N01cStateAngleSelections

/-!
# Fixed spatial affine maps preserve the parameter word

Rescaling the transformed directions by one fixed operator bound makes
them admissible for the original joint estimate. The word and its state
arity are unchanged, and the affine map costs only a finite scalar power.
-/

@[expose] public section

noncomputable section

namespace ContinuousFlexibility.Analysis

open Set ContinuousFlexibility.Statements
open scoped BigOperators

variable {E Y : Type*} [TopologicalSpace E] [AddCommGroup E] [Module ℝ E]
  [IsTopologicalAddGroup E] [ContinuousSMul ℝ E]
  [NormedAddCommGroup Y] [NormedSpace ℝ Y]
  {U : Set E} {V W : Set PolarPoint} {f : E × PolarPoint → Y}

theorem n04PositiveGeometry_affineSpatial_word_bound
    (J : SmoothDirections (U ×ˢ V) f) (hU : IsOpen U) (hW : IsOpen W)
    (L : PolarPoint →L[ℝ] PolarPoint) (a : PolarPoint)
    (hmap : MapsTo (fun q => a + L q) W V)
    (Q : SmoothDirections (U ×ˢ W) (fun z : E × PolarPoint => f (z.1, a + L z.2)))
    (p q : Seminorm ℝ E) {C R M : ℝ} (hC : 1 ≤ C) (hL : ‖L‖ ≤ C) (hR : 0 ≤ R)
    (n : ℕ) (w : StateAngleWord n) (x : E) (hx : x ∈ U)
    (y : PolarPoint) (hy : y ∈ W)
    (hbound : ∀ u : Fin n → E × PolarPoint,
      (∀ i, p (u i).1 ≤ 1) → (∀ i, q (u i).1 ≤ R) →
      (∀ i, ‖(u i).2‖ ≤ 1) →
      (∀ i, w.isState i = false → (u i).1 = 0) →
      (∀ i, w.isState i = true → (u i).2 = 0) →
        ‖J.D n (x, a + L y) u‖ ≤ M)
    (v : Fin n → E × PolarPoint)
    (hvL : ∀ i, p (v i).1 ≤ 1) (hvH : ∀ i, q (v i).1 ≤ R)
    (hvS : ∀ i, ‖(v i).2‖ ≤ 1)
    (hv0 : ∀ i, w.isState i = false → (v i).1 = 0)
    (hv1 : ∀ i, w.isState i = true → (v i).2 = 0) :
    ‖Q.D n (x, y) v‖ ≤ C ^ n * M := by
  have hCpos : 0 < C := zero_lt_one.trans_le hC
  have hCi : 0 ≤ C⁻¹ := inv_nonneg.mpr hCpos.le
  have hCi1 : C⁻¹ ≤ 1 := inv_le_one_of_one_le₀ hC
  let A : (E × PolarPoint) →L[ℝ] (E × PolarPoint) :=
    (ContinuousLinearMap.fst ℝ E PolarPoint).prod
      (L.comp (ContinuousLinearMap.snd ℝ E PolarPoint))
  have hA (z : E × PolarPoint) : (0, a) + A z = (z.1, a + L z.2) := by
    simp only [A, ContinuousLinearMap.prod_apply, ContinuousLinearMap.comp_apply,
      ContinuousLinearMap.coe_fst', ContinuousLinearMap.coe_snd', Prod.mk_add_mk, zero_add]
  have hAmap : MapsTo (fun z => (0, a) + A z) (U ×ˢ W) (U ×ˢ V) := by
    intro z hz
    change (0, a) + A z ∈ U ×ˢ V
    rw [hA z]
    exact ⟨hz.1, hmap hz.2⟩
  let K : SmoothDirections (U ×ˢ W)
      (fun z : E × PolarPoint => f (z.1, a + L z.2)) :=
    (J.compAffine A (0, a) (hU.prod hW) hAmap).congrOn
      (fun z _ => congrArg f (hA z))
  have he : Q.D n (x, y) v =
      J.D n (x, a + L y) (fun i => ((v i).1, L (v i).2)) := by
    have h := congrArg (fun B : (E × PolarPoint) [×n]→L[ℝ] Y => B v)
      (Q.unique K n (x, y) ⟨hx, hy⟩)
    simpa only [K, SmoothDirections.congrOn, SmoothDirections.compAffine_apply, hA,
      A, ContinuousLinearMap.prod_apply, ContinuousLinearMap.comp_apply,
      ContinuousLinearMap.coe_fst', ContinuousLinearMap.coe_snd',
      Prod.mk_add_mk, zero_add] using h
  let u : Fin n → E × PolarPoint := fun i => C⁻¹ • ((v i).1, L (v i).2)
  have hscale (s : Seminorm ℝ E) (i : Fin n) :
      s (u i).1 = C⁻¹ * s (v i).1 := by
    change s (C⁻¹ • (v i).1) = _
    rw [map_smul_eq_mul, Real.norm_eq_abs, abs_of_nonneg hCi]
  have huL (i : Fin n) : p (u i).1 ≤ 1 := by
    rw [hscale]
    exact (mul_le_mul_of_nonneg_left (hvL i) hCi).trans
      ((mul_one C⁻¹).le.trans hCi1)
  have huH (i : Fin n) : q (u i).1 ≤ R := by
    rw [hscale]
    exact (mul_le_mul_of_nonneg_left (hvH i) hCi).trans
      (mul_le_of_le_one_left hR hCi1)
  have huS (i : Fin n) : ‖(u i).2‖ ≤ 1 := by
    change ‖C⁻¹ • L (v i).2‖ ≤ 1
    rw [norm_smul, Real.norm_of_nonneg hCi]
    calc
      _ ≤ C⁻¹ * (‖L‖ * ‖(v i).2‖) :=
        mul_le_mul_of_nonneg_left (L.le_opNorm _) hCi
      _ ≤ C⁻¹ * (C * 1) := mul_le_mul_of_nonneg_left
        (mul_le_mul hL (hvS i) (norm_nonneg _) hCpos.le) hCi
      _ = 1 := by rw [mul_one, inv_mul_cancel₀ hCpos.ne']
  have hu0 (i : Fin n) (hi : w.isState i = false) : (u i).1 = 0 := by
    change C⁻¹ • (v i).1 = 0
    rw [hv0 i hi, smul_zero]
  have hu1 (i : Fin n) (hi : w.isState i = true) : (u i).2 = 0 := by
    change C⁻¹ • L (v i).2 = 0
    rw [hv1 i hi, map_zero, smul_zero]
  have hrestore : (fun i => ((v i).1, L (v i).2)) = fun i => C • u i := by
    funext i
    dsimp only [u]
    rw [smul_smul, mul_inv_cancel₀ hCpos.ne', one_smul]
  rw [he, hrestore, ContinuousMultilinearMap.map_smul_univ,
    Finset.prod_const, Finset.card_univ, Fintype.card_fin,
    norm_smul, Real.norm_of_nonneg (pow_nonneg hCpos.le n)]
  exact mul_le_mul_of_nonneg_left (hbound u huL huH huS hu0 hu1)
    (pow_nonneg hCpos.le n)

end ContinuousFlexibility.Analysis
