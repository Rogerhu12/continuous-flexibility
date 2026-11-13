import ContinuousFlexibility.Analysis.N04PositiveGeometryControlledSavedMovingWords
import ContinuousFlexibility.Analysis.CircleSmoothDirectionsOperations
import ContinuousFlexibility.Analysis.TameProductDirections

/-!
# The fixed spatial coordinates in positive joint words

An unwrapped coordinate is used only through positive derivatives. Its
first spatial derivative has cost one, and every parameter derivative
vanishes. Adding or pairing that coordinate therefore preserves the
saved spatial order and the original parameter height factor.
-/

noncomputable section

namespace ContinuousFlexibility.Analysis

open Set ContinuousFlexibility.Statements
open scoped BigOperators

variable {E V F : Type*}
  [TopologicalSpace E] [AddCommGroup E] [Module ℝ E]
  [IsTopologicalAddGroup E] [ContinuousSMul ℝ E]
  [NormedAddCommGroup V] [NormedSpace ℝ V]
  [NormedAddCommGroup F] [NormedSpace ℝ F]

theorem n04PositiveGeometry_spatialLinear_saved_word_bound
    {U : Set (E × V)} (hU : IsOpen U) (L : V →L[ℝ] F)
    (J : SmoothDirections U (fun x : E × V => L x.2))
    {M H t : ℝ} (hM : 1 ≤ M) (hL : ‖L‖ ≤ M) (hH : 0 ≤ H) (ht : 1 ≤ t)
    {n : ℕ} (hn : 0 < n) (w : StateAngleWord n) (C : ℕ)
    (x : E × V) (hx : x ∈ U) (v : Fin n → E × V)
    (hv : ∀ i, ‖(v i).2‖ ≤ 1)
    (hpure : ∀ i, w.isState i = true → (v i).2 = 0) :
    ‖J.D n x v‖ ≤ M * parameterHeightWeight H w.stateArity *
      t ^ (w.angleArity + C * w.stateArity - 1) := by
  let A : (E × V) →L[ℝ] F := L.comp (ContinuousLinearMap.snd ℝ E V)
  let K : SmoothDirections U (fun x : E × V => L x.2) :=
    ((smoothDirectionsLinear A).restrict hU (subset_univ _)).congrOn
      (fun _ _ => rfl)
  have he : J.D n x v = continuousLinearJets A n x v := by
    exact congrArg (fun B : (E × V) [×n]→L[ℝ] F => B v) (J.unique K n x hx)
  have hcost : 0 ≤ M * parameterHeightWeight H w.stateArity *
      t ^ (w.angleArity + C * w.stateArity - 1) :=
    mul_nonneg (mul_nonneg (zero_le_one.trans hM) (parameterHeightWeight_nonneg hH _))
      (pow_nonneg (zero_le_one.trans ht) _)
  rw [he]
  cases n with
  | zero => omega
  | succ n =>
      cases n with
      | zero =>
          change ‖L (v 0).2‖ ≤ _
          by_cases hs : w.isState 0 = true
          · rw [hpure 0 hs, map_zero, norm_zero]
            exact hcost
          · have hs' : w.isState 0 = false := Bool.eq_false_iff.mpr hs
            have hk : w.stateArity = 0 := by
              have hsum := w.stateArity_eq_sum
              simp only [Fin.sum_univ_succ, Fin.sum_univ_zero, add_zero] at hsum
              simpa only [hs', Bool.false_eq_true, ite_false] using hsum
            have hb : w.angleArity = 1 := by have := w.arity_sum; omega
            simp only [hk, hb, parameterHeightWeight, ite_true, mul_one,
              Nat.mul_zero, Nat.add_zero, Nat.sub_self, pow_zero]
            exact (L.le_opNorm _).trans
              ((mul_le_mul hL (hv 0) (norm_nonneg _) (zero_le_one.trans hM)).trans_eq
                (mul_one M))
      | succ n =>
          simpa only [continuousLinearJets, zero_apply, norm_zero] using hcost

/-- Pairing two actual towers with the same word bound costs no extra
factor for the max norm on the product. -/
theorem n04PositiveGeometry_jointPair_word_bound
    {G : Type*} [NormedAddCommGroup G] [NormedSpace ℝ G]
    {U : Set (E × V)} {f : E × V → F} {g : E × V → G}
    (JF : SmoothDirections U f) (JG : SmoothDirections U g)
    (J : SmoothDirections U (fun x => (f x, g x)))
    (n : ℕ) (x : E × V) (hx : x ∈ U) (v : Fin n → E × V)
    {B : ℝ} (hf : ‖JF.D n x v‖ ≤ B) (hg : ‖JG.D n x v‖ ≤ B) :
    ‖J.D n x v‖ ≤ B := by
  let K := smoothDirectionsProd JF JG
  have he : J.D n x v = (JF.D n x v, JG.D n x v) :=
    congrArg (fun A : (E × V) [×n]→L[ℝ] (F × G) => A v) (J.unique K n x hx)
  rw [he, Prod.norm_def]
  exact max_le hf hg

theorem n04PositiveGeometry_jointAdd_word_bound
    {U : Set (E × V)} {f g h : E × V → F}
    (JF : SmoothDirections U f) (JG : SmoothDirections U g)
    (J : SmoothDirections U h) (he : EqOn h (fun x => f x + g x) U)
    (n : ℕ) (x : E × V) (hx : x ∈ U) (v : Fin n → E × V)
    {B C : ℝ} (hf : ‖JF.D n x v‖ ≤ B) (hg : ‖JG.D n x v‖ ≤ C) :
    ‖J.D n x v‖ ≤ B + C := by
  have hvalue : J.D n x v = JF.D n x v + JG.D n x v :=
    congrArg (fun A : (E × V) [×n]→L[ℝ] F => A v)
      ((J.congr he).unique (smoothDirectionsAdd JF JG) n x hx)
  rw [hvalue]
  exact (norm_add_le _ _).trans (add_le_add hf hg)

end ContinuousFlexibility.Analysis
