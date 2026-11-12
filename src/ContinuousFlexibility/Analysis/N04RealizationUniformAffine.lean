import ContinuousFlexibility.Analysis.N07aAffineTower
import ContinuousFlexibility.Scalar.WeightedTowerCalculus

/-!
# Uniform bounds on the actual affine parameter slice

The already constructed affine derivative tower retains the original
base and loss. Translation changes only the numerical constant, and a
grading contraction introduces no additional loss or order-dependent
neighborhood.
-/

noncomputable section

namespace ContinuousFlexibility.Analysis

open Set ContinuousFlexibility.Statements
open scoped BigOperators

private theorem n04Realization_tameJetSize_translate_le
    {Y : Type*} [AddCommGroup Y] [Module ℝ Y]
    (q : ℕ → Seminorm ℝ Y) (k s loss base : ℕ) (c y : Y) (v : Fin k → Y) :
    tameJetSize q k s loss base (c + y) v ≤
      (1 + q (s + loss) c) * tameJetSize q k s loss base y v := by
  have hprod : 0 ≤ ∏ i, q base (v i) :=
    Finset.prod_nonneg (fun _ _ => apply_nonneg _ _)
  have hsum : 0 ≤ ∑ i, q (s + loss) (v i) *
      ∏ j ∈ Finset.univ.erase i, q base (v j) :=
    Finset.sum_nonneg (fun _ _ => mul_nonneg (apply_nonneg _ _)
      (Finset.prod_nonneg (fun _ _ => apply_nonneg _ _)))
  have hq := map_add_le_add (q (s + loss)) c y
  have hqc := apply_nonneg (q (s + loss)) c
  have hqy := apply_nonneg (q (s + loss)) y
  unfold tameJetSize
  nlinarith [mul_le_mul_of_nonneg_right hq hprod,
    mul_nonneg hqc hsum, mul_nonneg hqc (mul_nonneg hqy hprod)]

variable {X Y Z : Type*}
  [TopologicalSpace X] [AddCommGroup X] [Module ℝ X]
  [TopologicalSpace Y] [AddCommGroup Y] [Module ℝ Y] [IsTopologicalAddGroup Y]
  [TopologicalSpace Z] [AddCommGroup Z] [Module ℝ Z]
  {p : ℕ → Seminorm ℝ X} {q : ℕ → Seminorm ℝ Y} {r : ℕ → Seminorm ℝ Z}
  {U : Set Y} {f : Y → Z} {base loss : ℕ}

/-- Restrict the genuine tower along one fixed affine grading
contraction, preserving its fixed base and loss. -/
theorem n04Realization_uniformTower_affine
    (J : SmoothDirections U f)
    (hJ : UniformScalarTowerEstimate q r U base loss f J)
    (c : Y) (L : X →L[ℝ] Y) (hL : ∀ n x, q n (L x) ≤ p n x) :
    UniformScalarTowerEstimate p r ((fun x => c + L x) ⁻¹' U) base loss
      (fun x => f (c + L x)) (n07aSmoothDirectionsAffine J c L) := by
  intro k s hs
  obtain ⟨C, hC, hbound⟩ := hJ k s hs
  refine ⟨C * (1 + q (s + loss) c), mul_nonneg hC (by positivity), ?_⟩
  intro x hx v
  have hlin : tameJetSize q k s loss base (L x) (fun i => L (v i)) ≤
      tameJetSize p k s loss base x v := by
    simpa only [tameJetSize, one_mul, one_pow, ContinuousLinearMap.coe_coe] using
      solve_oneHighWeight_le p q L.toLinearMap 1 le_rfl
        (fun n y => by simpa only [one_mul, ContinuousLinearMap.coe_coe] using hL n y)
        base (s + loss) x v
  rw [n07aSmoothDirectionsAffine_D]
  calc
    _ ≤ C * tameJetSize q k s loss base (c + L x) (fun i => L (v i)) :=
      hbound (c + L x) hx _
    _ ≤ C * ((1 + q (s + loss) c) * tameJetSize p k s loss base x v) :=
      mul_le_mul_of_nonneg_left
        ((n04Realization_tameJetSize_translate_le q k s loss base c (L x)
          (fun i => L (v i))).trans
            (mul_le_mul_of_nonneg_left hlin (by positivity))) hC
    _ = _ := (mul_assoc _ _ _).symm

theorem n04Realization_fixedNeighborhood_affine
    (hf : FixedNeighborhoodSmoothTame q r U base loss f)
    (c : Y) (L : X →L[ℝ] Y) (hL : ∀ n x, q n (L x) ≤ p n x) :
    FixedNeighborhoodSmoothTame p r ((fun x => c + L x) ⁻¹' U) base loss
      (fun x => f (c + L x)) := by
  obtain ⟨J, hJ⟩ := hf.2
  exact fixedNeighborhoodSmoothTame_of_uniform (n07aSmoothDirectionsAffine J c L)
    (n04Realization_uniformTower_affine J hJ c L hL)

end ContinuousFlexibility.Analysis
