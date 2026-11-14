module

public import ContinuousFlexibility.Analysis.N07aAffineTower
public import ContinuousFlexibility.Analysis.TameElementaryCalculus

/-!
# Smooth tame pullback along a fixed affine contraction

The output may be a closed source subspace. The proof pulls back the
actual directional tower, so no representation of that subspace as a
projective limit is required.
-/

@[expose] public section

noncomputable section

namespace ContinuousFlexibility.Analysis

open Set ContinuousFlexibility.Statements
open scoped BigOperators

private theorem n07a_tameJetSize_add_center_le
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

theorem n07a_smoothTameOn_affine_nonexpansive
    {X Y Z : Type*}
    [TopologicalSpace X] [AddCommGroup X] [Module ℝ X]
    [TopologicalSpace Y] [AddCommGroup Y] [Module ℝ Y] [IsTopologicalAddGroup Y]
    [TopologicalSpace Z] [AddCommGroup Z] [Module ℝ Z]
    {p : ℕ → Seminorm ℝ X} {q : ℕ → Seminorm ℝ Y} {r : ℕ → Seminorm ℝ Z}
    {U : Set Y} {f : Y → Z} (hf : SmoothTameOn q r U f)
    (c : Y) (L : X →L[ℝ] Y) (hL : ∀ n x, q n (L x) ≤ p n x) :
    SmoothTameOn p r ((fun x => c + L x) ⁻¹' U) (fun x => f (c + L x)) := by
  obtain ⟨J, hJ⟩ := hf
  refine ⟨n07aSmoothDirectionsAffine J c L, fun k x₀ hx₀ => ?_⟩
  obtain ⟨loss, base, ε, hε, hbound⟩ := hJ k (c + L x₀) hx₀
  refine ⟨loss, base, ε, hε, fun s hs => ?_⟩
  obtain ⟨C, hC, hCs⟩ := hbound s hs
  refine ⟨C * (1 + q (s + loss) c),
    mul_nonneg hC (by positivity), fun x hx hnear v => ?_⟩
  have hnear' : q base ((c + L x) - (c + L x₀)) < ε := by
    rw [add_sub_add_left_eq_sub, ← map_sub]
    exact (hL base (x - x₀)).trans_lt hnear
  have hlin : tameJetSize q k s loss base (L x) (fun i => L (v i)) ≤
      tameJetSize p k s loss base x v := by
    simpa only [tameJetSize, one_mul, one_pow, ContinuousLinearMap.coe_coe] using
      solve_oneHighWeight_le p q L.toLinearMap 1 le_rfl
        (fun n y => by simpa only [one_mul, ContinuousLinearMap.coe_coe] using hL n y)
        base (s + loss) x v
  have hshift := n07a_tameJetSize_add_center_le q k s loss base c (L x)
    (fun i => L (v i))
  change r s (J.D k (c + L x) (fun i => L (v i))) ≤ _
  calc
    _ ≤ C * tameJetSize q k s loss base (c + L x) (fun i => L (v i)) :=
      hCs (c + L x) hx hnear' _
    _ ≤ C * ((1 + q (s + loss) c) * tameJetSize p k s loss base x v) :=
      mul_le_mul_of_nonneg_left
        (hshift.trans (mul_le_mul_of_nonneg_left hlin (by positivity))) hC
    _ = _ := (mul_assoc _ _ _).symm

end ContinuousFlexibility.Analysis
