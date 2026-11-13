import ContinuousFlexibility.Analysis.N04PositiveGeometryBoundaryKernelBounds
import ContinuousFlexibility.Analysis.N06BoundaryRadialJets
import Mathlib.Analysis.Calculus.IteratedDeriv.Lemmas

/-!
# Fixed evaluations and products of actual boundary traces

Evaluating a full spatial jet on fixed unit vectors keeps the original
word budget. The radial product formula then constructs genuine traces,
including their actual constant term.
-/

noncomputable section

namespace ContinuousFlexibility.Analysis

open Set ContinuousFlexibility.Statements
open scoped ContDiff BigOperators

variable {E F V : Type*}
  [TopologicalSpace E] [AddCommGroup E] [Module ℝ E]
  [IsTopologicalAddGroup E] [ContinuousSMul ℝ E]
  [NormedAddCommGroup F] [NormedSpace ℝ F]
  [NormedAddCommGroup V] [NormedSpace ℝ V]

def n04PositiveGeometry_boundaryFixedEvaluation_directions
    {U : Set E} {n : ℕ} {f : E × ℝ → V [×n]→L[ℝ] F}
    (J : SmoothDirections (U ×ˢ univ) f) (v : Fin n → V) :
    SmoothDirections (U ×ˢ univ) (fun y => f y v) :=
  smoothDirections_postcompCLM J (ContinuousMultilinearMap.apply ℝ (fun _ : Fin n => V) F v)

theorem N04BoundaryWordBounds.fixedEvaluation
    {U : Set E} {n : ℕ} {f : E × ℝ → V [×n]→L[ℝ] F}
    {J : SmoothDirections (U ×ˢ univ) f}
    {K s d : ℕ} {x : E} {θ : ℝ} {P : E → Prop} {M H t : ℝ} {shift : ℕ}
    (hb : N04BoundaryWordBounds J K s d x θ P M H t shift)
    (v : Fin n → V) (hv : ∀ i, ‖v i‖ ≤ 1) :
    N04BoundaryWordBounds (n04PositiveGeometry_boundaryFixedEvaluation_directions J v)
      K s d x θ P M H t shift := by
  apply hb.postcompCLM
  apply ContinuousLinearMap.opNorm_le_bound _ zero_le_one
  intro A
  have hprod : (∏ i, ‖v i‖) ≤ 1 :=
    Finset.prod_le_one₀ (fun _ _ => norm_nonneg _) (fun i _ => hv i)
  exact (A.le_opNorm v).trans (by
    simpa only [one_mul, mul_one] using
      mul_le_mul_of_nonneg_left hprod (norm_nonneg A))

theorem n04PositiveGeometry_radialBoundaryJet_mul
    {f g : PolarPoint → ℝ} {c θ : ℝ}
    (hf : ContDiffAt ℝ ∞ f (c, θ)) (hg : ContDiffAt ℝ ∞ g (c, θ)) (n : ℕ) :
    radialBoundaryJet (fun p => f p * g p) c n θ =
      ∑ j : Fin (n + 1), (n.choose j.val : ℝ) *
        (radialBoundaryJet f c j.val θ * radialBoundaryJet g c (n - j.val) θ) := by
  have hline : ContDiffAt ℝ ∞ (fun r : ℝ => (r, θ)) c :=
    contDiffAt_id.prodMk contDiffAt_const
  have hfs := hf.comp c hline
  have hgs := hg.comp c hline
  have he := iteratedDeriv_fun_mul
    (hfs.of_le (show (n : ℕ∞ω) ≤ ∞ by simp))
    (hgs.of_le (show (n : ℕ∞ω) ≤ ∞ by simp))
  simpa only [radialBoundaryJet, Fin.sum_univ_eq_sum_range, mul_assoc] using he

def n04PositiveGeometry_radialProduct_directions
    {U : Set E} (hU : IsOpen U) (c : ℝ) (n : ℕ)
    (f g : E × ℝ → PolarPoint → ℝ)
    (hf : ∀ y ∈ U ×ˢ univ, ContDiffAt ℝ ∞ (f y) (c, y.2))
    (hg : ∀ y ∈ U ×ˢ univ, ContDiffAt ℝ ∞ (g y) (c, y.2))
    (JF : ∀ j, j ≤ n → SmoothDirections (U ×ˢ univ)
      (fun y => radialBoundaryJet (f y) c j y.2))
    (JG : ∀ j, j ≤ n → SmoothDirections (U ×ˢ univ)
      (fun y => radialBoundaryJet (g y) c j y.2)) :
    SmoothDirections (U ×ˢ univ)
      (fun y => radialBoundaryJet (fun p => f y p * g y p) c n y.2) := by
  let JT (j : Fin (n + 1)) := smoothDirections_postcompCLM
    ((JF j.val (Nat.le_of_lt_succ j.isLt)).mul (JG (n - j.val) (Nat.sub_le _ _)))
    ((n.choose j.val : ℝ) • ContinuousLinearMap.id ℝ ℝ)
  exact (smoothDirections_finiteSum (hU.prod isOpen_univ) JT).congr
    (fun y hy => (n04PositiveGeometry_radialBoundaryJet_mul (hf y hy) (hg y hy) n).symm)

theorem n04PositiveGeometry_radialProduct_bound (n N : ℕ) (L : ℝ) (hL : 1 ≤ L) :
    ∃ C : ℝ, 1 ≤ C ∧ ∀ {U : Set E}, IsOpen U → ∀ c : ℝ,
      ∀ f g : E × ℝ → PolarPoint → ℝ,
      (∀ y ∈ U ×ˢ univ, ContDiffAt ℝ ∞ (f y) (c, y.2)) →
      (∀ y ∈ U ×ˢ univ, ContDiffAt ℝ ∞ (g y) (c, y.2)) →
      ∀ JF : ∀ j, j ≤ n → SmoothDirections (U ×ˢ univ)
        (fun y => radialBoundaryJet (f y) c j y.2),
      ∀ JG : ∀ j, j ≤ n → SmoothDirections (U ×ˢ univ)
        (fun y => radialBoundaryJet (g y) c j y.2),
      ∀ Q : SmoothDirections (U ×ˢ univ)
        (fun y => radialBoundaryJet (fun p => f y p * g y p) c n y.2),
      ∀ K s d, K + s + d ≤ N → ∀ x ∈ U, ∀ θ P,
      ∀ M H t : ℝ, 1 ≤ M → 0 ≤ H → H ≤ L → 1 ≤ t → ∀ shift,
      (∀ j hj, N04BoundaryWordBounds (JF j hj) K s d x θ P M H t shift) →
      (∀ j hj, N04BoundaryWordBounds (JG j hj) K s d x θ P M H t shift) →
      N04BoundaryWordBounds Q K s d x θ P (C * M ^ (N + 2)) H t shift := by
  classical
  obtain ⟨B, hB, hb⟩ := n04PositiveGeometry_boundaryWord_mul (E := E) N L hL
  let A : ℝ := 1 + ∑ j : Fin (n + 1), |(n.choose j.val : ℝ)|
  have hA : 1 ≤ A := le_add_of_nonneg_right (Finset.sum_nonneg (fun _ _ => abs_nonneg _))
  have hchoose (j : Fin (n + 1)) : |(n.choose j.val : ℝ)| ≤ A :=
    (Finset.single_le_sum (fun _ _ => abs_nonneg _) (Finset.mem_univ j)).trans
      (le_add_of_nonneg_left zero_le_one)
  let C : ℝ := 1 + (Fintype.card (Fin (n + 1)) : ℝ) * (A * B)
  have hC : 1 ≤ C := le_add_of_nonneg_right
    (mul_nonneg (Nat.cast_nonneg _) (mul_nonneg (zero_le_one.trans hA) (zero_le_one.trans hB)))
  refine ⟨C, hC, ?_⟩
  intro U hU c f g hf hg JF JG Q K s d hN x hx θ P M H t hM hH hHL ht shift hF hG
  let JT (j : Fin (n + 1)) := smoothDirections_postcompCLM
    ((JF j.val (Nat.le_of_lt_succ j.isLt)).mul (JG (n - j.val) (Nat.sub_le _ _)))
    ((n.choose j.val : ℝ) • ContinuousLinearMap.id ℝ ℝ)
  have hT (j : Fin (n + 1)) :
      N04BoundaryWordBounds (JT j) K s d x θ P ((A * B) * M ^ (N + 2)) H t shift := by
    have h := (hb (JF j.val (Nat.le_of_lt_succ j.isLt))
      (JG (n - j.val) (Nat.sub_le _ _)) K s d hN x hx θ P M H t hM hH hHL ht shift
      (hF _ _) (hG _ _)).scale (n.choose j.val)
    apply h.enlarge hH (zero_le_one.trans ht)
    calc
      _ ≤ A * (B * M ^ (N + 2)) := mul_le_mul_of_nonneg_right (hchoose j)
        (mul_nonneg (zero_le_one.trans hB) (pow_nonneg (zero_le_one.trans hM) _))
      _ = _ := by ring
  have hsum := N04BoundaryWordBounds.finiteSum hU JT hT
  have hcost : (Fintype.card (Fin (n + 1)) : ℝ) * ((A * B) * M ^ (N + 2)) ≤
      C * M ^ (N + 2) := by
    dsimp only [C]
    have hp : 0 ≤ M ^ (N + 2) := pow_nonneg (zero_le_one.trans hM) _
    nlinarith
  exact (hsum.enlarge hH (zero_le_one.trans ht) hcost).congr hx
    (fun y hy => (n04PositiveGeometry_radialBoundaryJet_mul (hf y hy) (hg y hy) n).symm)

end ContinuousFlexibility.Analysis
