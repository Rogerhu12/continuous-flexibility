import ContinuousFlexibility.Analysis.N04PositiveGeometryJointLinearWords
import ContinuousFlexibility.Analysis.N04PositiveGeometryAngularInverseWords

/-!
# Finite saved-word bounds on a physical plane region

This predicate records only positive genuine joint orders. Its parameter
arity, two seminorm boxes and single height factor are unchanged by
pairing, angular inversion and moving-point composition.
-/

noncomputable section

namespace ContinuousFlexibility.Analysis

open Set Function ContinuousFlexibility.Statements
open scoped BigOperators ContDiff

variable {E F : Type*}
  [TopologicalSpace E] [AddCommGroup E] [Module ℝ E]
  [IsTopologicalAddGroup E] [ContinuousSMul ℝ E]
  [NormedAddCommGroup F] [NormedSpace ℝ F]

def n04PositiveGeometry_spatialLinearDirections {U : Set E} (hU : IsOpen U)
    (L : PolarPoint →L[ℝ] F) :
    SmoothDirections (U ×ˢ univ) (fun z : E × PolarPoint => L z.2) :=
  (smoothDirectionsLinearOn (L.comp (ContinuousLinearMap.snd ℝ E PolarPoint))
    (hU.prod isOpen_univ)).congrOn (fun z _ => by
      simp only [ContinuousLinearMap.comp_apply, ContinuousLinearMap.coe_snd'])

def N04PlaneSavedWordBounds {U : Set E} {f : E × PolarPoint → F}
    (J : SmoothDirections (U ×ˢ univ) f) (N K C : ℕ) (x : E) (Ω : Set PolarPoint)
    (p q : Seminorm ℝ E) (R M H t : ℝ) : Prop :=
  ∀ y ∈ Ω, ∀ j : ℕ, 0 < j → j ≤ N →
    ∀ w : StateAngleWord j, w.stateArity ≤ K → ∀ v : Fin j → E × PolarPoint,
    (∀ k, if w.isState k then (v k).2 = 0 else (v k).1 = 0) →
    (∀ k, p (v k).1 ≤ 1 ∧ q (v k).1 ≤ R ∧ ‖(v k).2‖ ≤ 1) →
      ‖J.D j (x, y) v‖ ≤ M * parameterHeightWeight H w.stateArity *
        t ^ (w.angleArity + C * w.stateArity - 1)

namespace N04PlaneSavedWordBounds

variable {U : Set E} {f : E × PolarPoint → F}
  {J : SmoothDirections (U ×ˢ univ) f} {N K C : ℕ} {x : E} {Ω : Set PolarPoint}
  {p q : Seminorm ℝ E} {R M M' H t : ℝ}

theorem enlarge (h : N04PlaneSavedWordBounds J N K C x Ω p q R M H t)
    (hH : 0 ≤ H) (ht : 1 ≤ t) (hMM : M ≤ M') :
    N04PlaneSavedWordBounds J N K C x Ω p q R M' H t := by
  intro y hy j hj hjN w hw v hpure hbox
  exact (h y hy j hj hjN w hw v hpure hbox).trans
    (mul_le_mul_of_nonneg_right
      (mul_le_mul_of_nonneg_right hMM (parameterHeightWeight_nonneg hH _))
      (pow_nonneg (zero_le_one.trans ht) _))

theorem congr {g : E × PolarPoint → F}
    (h : N04PlaneSavedWordBounds J N K C x Ω p q R M H t)
    (hx : x ∈ U) (Q : SmoothDirections (U ×ˢ univ) g)
    (he : EqOn f g (U ×ˢ univ)) :
    N04PlaneSavedWordBounds Q N K C x Ω p q R M H t := by
  intro y hy j hj hjN w hw v hpure hbox
  have hvalue : Q.D j (x, y) v = J.D j (x, y) v :=
    congrArg (fun A : (E × PolarPoint) [×j]→L[ℝ] F => A v)
      ((J.congr he).unique Q j (x, y) ⟨hx, mem_univ _⟩).symm
  rw [hvalue]
  exact h y hy j hj hjN w hw v hpure hbox

theorem postcompCLM {Z : Type*} [NormedAddCommGroup Z] [NormedSpace ℝ Z]
    (h : N04PlaneSavedWordBounds J N K C x Ω p q R M H t)
    (L : F →L[ℝ] Z) (hL : ‖L‖ ≤ 1) :
    N04PlaneSavedWordBounds (smoothDirections_postcompCLM J L)
      N K C x Ω p q R M H t := by
  intro y hy j hj hjN w hw v hpure hbox
  rw [smoothDirections_postcompCLM_D_apply]
  exact ((L.le_opNorm _).trans ((mul_le_mul_of_nonneg_right hL (norm_nonneg _)).trans_eq
    (one_mul _))).trans (h y hy j hj hjN w hw v hpure hbox)

theorem pair {Z : Type*} [NormedAddCommGroup Z] [NormedSpace ℝ Z]
    {g : E × PolarPoint → Z} (JG : SmoothDirections (U ×ˢ univ) g)
    (Q : SmoothDirections (U ×ˢ univ) (fun z => (f z, g z)))
    (hx : x ∈ U) (hf : N04PlaneSavedWordBounds J N K C x Ω p q R M H t)
    (hg : N04PlaneSavedWordBounds JG N K C x Ω p q R M H t) :
    N04PlaneSavedWordBounds Q N K C x Ω p q R M H t := by
  intro y hy j hj hjN w hw v hpure hbox
  exact n04PositiveGeometry_jointPair_word_bound J JG Q j (x, y) ⟨hx, mem_univ _⟩ v
    (hf y hy j hj hjN w hw v hpure hbox) (hg y hy j hj hjN w hw v hpure hbox)

theorem spatialLinear (hU : IsOpen U) (L : PolarPoint →L[ℝ] F)
    (Q : SmoothDirections (U ×ˢ univ) (fun z : E × PolarPoint => L z.2))
    (hx : x ∈ U) (hM : 1 ≤ M) (hL : ‖L‖ ≤ M) (hH : 0 ≤ H) (ht : 1 ≤ t) :
    N04PlaneSavedWordBounds Q N K C x Ω p q R M H t := by
  intro y hy j hj hjN w hw v hpure hbox
  exact n04PositiveGeometry_spatialLinear_saved_word_bound (hU.prod isOpen_univ)
    L Q hM hL hH ht hj w C (x, y) ⟨hx, mem_univ _⟩ v (fun k => (hbox k).2.2)
    (fun k hk => by simpa only [hk, ite_true] using hpure k)

end N04PlaneSavedWordBounds

theorem n04PositiveGeometry_finite_nat_power_majorant
    (N : ℕ) (a : ℕ → ℝ) (d : ℕ → ℕ) (ha : ∀ j, 1 ≤ a j) :
    ∃ A : ℝ, 1 ≤ A ∧ ∃ D : ℕ, ∀ j, j ≤ N → ∀ M : ℝ, 1 ≤ M →
      a j * M ^ d j ≤ A * M ^ D := by
  classical
  let A : ℝ := 1 + ∑ j : Fin (N + 1), a j
  let D : ℕ := ∑ j : Fin (N + 1), d j
  have hA : 1 ≤ A := le_add_of_nonneg_right
    (Finset.sum_nonneg (fun (j : Fin (N + 1)) _ => zero_le_one.trans (ha j.val)))
  refine ⟨A, hA, D, ?_⟩
  intro j hj M hM
  let k : Fin (N + 1) := ⟨j, by omega⟩
  have hcoef₀ : a k ≤ ∑ l : Fin (N + 1), a l :=
    Finset.single_le_sum (f := fun l : Fin (N + 1) => a l.val)
      (fun l _ => zero_le_one.trans (ha l.val)) (Finset.mem_univ k)
  have hcoef : a j ≤ A := hcoef₀.trans (by
    dsimp only [A]
    exact le_add_of_nonneg_left zero_le_one)
  have hdegree : d j ≤ D := by
    change d k ≤ ∑ l : Fin (N + 1), d l
    exact Finset.single_le_sum (f := fun l : Fin (N + 1) => d l.val)
      (fun l _ => Nat.zero_le (d l.val)) (Finset.mem_univ k)
  exact mul_le_mul hcoef (pow_le_pow_right₀ hM hdegree)
    (pow_nonneg (zero_le_one.trans hM) _) (zero_le_one.trans hA)

end ContinuousFlexibility.Analysis
