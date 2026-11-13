import ContinuousFlexibility.Analysis.N04RealizationPositivePrimitiveKernel
import ContinuousFlexibility.Analysis.PositiveReferenceCollarFactory
import ContinuousFlexibility.Scalar.S04CalculusProof

/-!
# The actual radial collar as a smooth finite coefficient kernel

The kernel is the existing collar formula evaluated on its finite
coefficient vector. Its identity with the actual angular data follows
from equality of radial slices before taking their true derivatives.
No new collar or inverse is selected.
-/

noncomputable section

namespace ContinuousFlexibility.Analysis

open Set ContinuousFlexibility.Statements
open scoped ContDiff BigOperators

private def collarCoefficients (n : ℕ) (a : Fin (n + 2) → ℝ)
    (j : ℕ) (_θ : ℝ) : ℝ :=
  if hj : j < n + 2 then a ⟨j, hj⟩ else 0

private theorem collarCoefficients_apply (n : ℕ) (a : Fin (n + 2) → ℝ)
    {j : ℕ} (hj : j < n + 2) (θ : ℝ) :
    collarCoefficients n a j θ = a ⟨j, hj⟩ := by
  simp [collarCoefficients, hj]

private theorem positivePrimitiveRadial_contDiff
    {P : Type} [NormedAddCommGroup P] [NormedSpace ℝ P] [FiniteDimensional ℝ P]
    (F : Bool → P × PolarPoint → ℝ) (hF : ∀ side, ContDiff ℝ ∞ (F side))
    (l r δ v m : ℝ) :
    ContDiff ℝ ∞ (fun p : P × ℝ =>
      parameterizedPositiveReferenceCoordinate l r δ v m
        (fun side q => radialPartial (fun z => F side (p.1, z)) q) (p.2, 0)) := by
  have hPartial (side : Bool) : ContDiff ℝ ∞
      (fun p : P × PolarPoint => radialPartial (fun q => F side (p.1, q)) p.2) := by
    apply contDiff_iff_contDiffAt.mpr
    intro p
    exact contDiffAt_parameter_radialPartial (hF side).contDiffAt
  let B : Bool → P × ℝ → ℝ := fun side p =>
    radialPartial (fun q => F side (p.1, q)) (p.2, 0)
  let Q : P × ℝ → P × PolarPoint := fun p => (p.1, (p.2, 0))
  have hQ : ContDiff ℝ ∞ Q :=
    contDiff_fst.prodMk (contDiff_snd.prodMk contDiff_const)
  have hB (side : Bool) : ContDiff ℝ ∞ (B side) := by
    simpa only [B, Q, Function.comp_apply] using (hPartial side).comp hQ
  exact n04Realization_positivePrimitive_finiteParameter_contDiff B hB l r δ v m

/-- This is the original collar, with fixed finite scalar coefficients. -/
def n04Realization_positiveCollarKernel (n : ℕ) (l r δ v m : ℝ)
    (root : Bool) (p : (Fin (n + 2) → ℝ) × ℝ) : ℝ :=
  positiveReferenceCollarCoordinate n l r δ v m root
    (collarCoefficients n p.1) Prod.fst (p.2, 0)

theorem n04Realization_positiveCollarKernel_contDiff
    (n : ℕ) (l r δ v m : ℝ) (root : Bool) :
    ContDiff ℝ ∞ (n04Realization_positiveCollarKernel n l r δ v m root) := by
  let P : Type := Fin (n + 2) → ℝ
  let F : Bool → P × PolarPoint → ℝ := fun side p =>
    positiveReferenceCollarField n l r root (collarCoefficients n p.1) Prod.fst side p.2
  have hrad : ContDiff ℝ ∞ (fun p : P × PolarPoint => p.2.1) := by
    simpa only [Function.comp_apply] using
      (contDiff_fst : ContDiff ℝ ∞ (Prod.fst : PolarPoint → ℝ)).comp
        (contDiff_snd : ContDiff ℝ ∞ (Prod.snd : P × PolarPoint → PolarPoint))
  have hPoly (c : ℝ) : ContDiff ℝ ∞ (fun p : P × PolarPoint =>
      boundaryTaylorPolynomial (n + 1) c (collarCoefficients n p.1) p.2) := by
    unfold boundaryTaylorPolynomial
    apply ContDiff.sum
    intro j hj
    have hj' : j < n + 2 := Finset.mem_range.mp hj
    have heq : (fun p : P × PolarPoint =>
        collarCoefficients n p.1 j p.2.2 / (j.factorial : ℝ) * (p.2.1 - c) ^ j) =
        (fun p : P × PolarPoint =>
          p.1 ⟨j, hj'⟩ / (j.factorial : ℝ) * (p.2.1 - c) ^ j) := by
      funext p
      rw [collarCoefficients_apply n _ hj' p.2.2]
    rw [heq]
    have hcoord : ContDiff ℝ ∞ (fun p : P × PolarPoint => p.1 ⟨j, hj'⟩) := by
      simpa only [Function.comp_apply] using
        (contDiff_apply ℝ ℝ (⟨j, hj'⟩ : Fin (n + 2))).comp
          (contDiff_fst : ContDiff ℝ ∞ (Prod.fst : P × PolarPoint → P))
    exact (hcoord.div_const _).mul ((hrad.sub contDiff_const).pow j)
  have hF (side : Bool) : ContDiff ℝ ∞ (F side) := by
    by_cases hs : side = root
    · simpa only [F, positiveReferenceCollarField, if_pos hs] using
        hPoly (if side then r else l)
    · simpa only [F, positiveReferenceCollarField, if_neg hs] using hrad
  change ContDiff ℝ ∞ (fun p : P × ℝ =>
    parameterizedPositiveReferenceCoordinate l r δ v m
      (fun side q => radialPartial (fun z => F side (p.1, z)) q) (p.2, 0))
  exact positivePrimitiveRadial_contDiff F hF l r δ v m

private theorem positiveCollar_congr_slice
    {n : ℕ} {A B : ℕ → ℝ → ℝ} (l r δ v m : ℝ) (root : Bool)
    (hA : ∀ j ≤ n + 1, ContDiff ℝ ∞ (A j))
    (hB : ∀ j ≤ n + 1, ContDiff ℝ ∞ (B j))
    (x θ η : ℝ) (hAB : ∀ j ≤ n + 1, A j θ = B j η) :
    positiveReferenceCollarCoordinate n l r δ v m root A Prod.fst (x, θ) =
      positiveReferenceCollarCoordinate n l r δ v m root B Prod.fst (x, η) := by
  let FA : Bool → PolarPoint → ℝ := positiveReferenceCollarField n l r root A Prod.fst
  let FB : Bool → PolarPoint → ℝ := positiveReferenceCollarField n l r root B Prod.fst
  have hFA (side : Bool) : ContDiff ℝ ∞ (FA side) := by
    by_cases hs : side = root
    · simpa only [FA, positiveReferenceCollarField, if_pos hs] using
        contDiff_boundaryTaylorPolynomial hA (if side then r else l)
    · simpa only [FA, positiveReferenceCollarField, if_neg hs] using
        (contDiff_fst : ContDiff ℝ ∞ (Prod.fst : PolarPoint → ℝ))
  have hFB (side : Bool) : ContDiff ℝ ∞ (FB side) := by
    by_cases hs : side = root
    · simpa only [FB, positiveReferenceCollarField, if_pos hs] using
        contDiff_boundaryTaylorPolynomial hB (if side then r else l)
    · simpa only [FB, positiveReferenceCollarField, if_neg hs] using
        (contDiff_fst : ContDiff ℝ ∞ (Prod.fst : PolarPoint → ℝ))
  have hslice (side : Bool) :
      (fun t => FA side (t, θ)) = (fun t => FB side (t, η)) := by
    funext t
    by_cases hs : side = root
    · simp only [FA, FB, positiveReferenceCollarField, if_pos hs,
        boundaryTaylorPolynomial]
      apply Finset.sum_congr rfl
      intro j hj
      rw [hAB j (Nat.le_of_lt_succ (Finset.mem_range.mp hj))]
    · simp only [FA, FB, positiveReferenceCollarField, if_neg hs]
  have hderiv (side : Bool) (t : ℝ) :
      radialPartial (FA side) (t, θ) = radialPartial (FB side) (t, η) := by
    rw [← deriv_cylinder_radial_slice ((hFA side).differentiable (by simp)) t θ,
      ← deriv_cylinder_radial_slice ((hFB side).differentiable (by simp)) t η,
      hslice side]
  have hscaled (side : Bool) :
      (fun t => radialPartial (FA side) (t, θ) / m) =
        (fun t => radialPartial (FB side) (t, η) / m) := by
    funext t
    rw [hderiv side t]
  change v + m * positiveReferenceCoordinate l r δ
      (fun t => radialPartial (FA false) (t, θ) / m)
      (fun t => radialPartial (FA true) (t, θ) / m) x =
    v + m * positiveReferenceCoordinate l r δ
      (fun t => radialPartial (FB false) (t, η) / m)
      (fun t => radialPartial (FB true) (t, η) / m) x
  rw [hscaled false, hscaled true]

/-- Every angular slice uses precisely its original finite boundary
coefficients. The coordinate, width, mass and reference exit are unchanged. -/
theorem n04Realization_positiveCollarKernel_eq
    {n : ℕ} (l r δ v m : ℝ) (root : Bool) (A : ℕ → ℝ → ℝ)
    (hA : ∀ j ≤ n + 1, ContDiff ℝ ∞ (A j)) (x θ : ℝ) :
    positiveReferenceCollarCoordinate n l r δ v m root A Prod.fst (x, θ) =
      n04Realization_positiveCollarKernel n l r δ v m root
        ((fun j : Fin (n + 2) => A j θ), x) := by
  unfold n04Realization_positiveCollarKernel
  apply positiveCollar_congr_slice l r δ v m root hA
    (fun _ _ => contDiff_const) x θ 0
  intro j hj
  have hj' : j < n + 2 := by omega
  change A j θ = collarCoefficients n (fun i : Fin (n + 2) => A i θ) j 0
  rw [collarCoefficients_apply n _ hj' 0]

end ContinuousFlexibility.Analysis
