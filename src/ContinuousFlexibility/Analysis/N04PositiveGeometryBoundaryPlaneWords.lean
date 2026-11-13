import ContinuousFlexibility.Analysis.N04PositiveGeometryBoundaryMoving
import ContinuousFlexibility.Analysis.N04PositiveGeometryJointLinearWords

/-!
# Boundary coefficients as functions on the physical plane

The finite coefficient fields depend on state and angle. Pulling them
back by the angle projection preserves their original state slots and
both parameter seminorm boxes. A reserve of one gives the saved spatial
cost needed by the actual whole-component kernels.
-/

noncomputable section

namespace ContinuousFlexibility.Analysis

open Set Function ContinuousFlexibility.Statements

variable {E F : Type*}
  [TopologicalSpace E] [AddCommGroup E] [Module ℝ E]
  [IsTopologicalAddGroup E] [ContinuousSMul ℝ E]
  [NormedAddCommGroup F] [NormedSpace ℝ F]

theorem n04PositiveGeometry_boundaryPlane_saved_word_bound
    {U : Set E} {f : E × ℝ → F} (hU : IsOpen U)
    (J : SmoothDirections (U ×ˢ univ) f)
    (Q : SmoothDirections (U ×ˢ univ) (fun z : E × PolarPoint => f (z.1, z.2.2)))
    (p q : Seminorm ℝ E) {R M H t : ℝ} (hR : 0 ≤ R)
    (hM : 0 ≤ M) (hH : 0 ≤ H) (ht : 1 ≤ t)
    (K s shift : ℕ) (x : E) (hx : x ∈ U) (y : PolarPoint)
    (hbound : N04BoundaryWordBounds J K s 1 x y.2
      (fun a => p a ≤ 1 ∧ q a ≤ R) M H t shift)
    {n : ℕ} (hn : 0 < n) (w : StateAngleWord n)
    (hk : w.stateArity ≤ K) (ha : w.angleArity ≤ s + 1)
    (v : Fin n → E × PolarPoint)
    (hpure : ∀ i, if w.isState i then (v i).2 = 0 else (v i).1 = 0)
    (hbox : ∀ i, p (v i).1 ≤ 1 ∧ q (v i).1 ≤ R ∧ ‖(v i).2‖ ≤ 1) :
    ‖Q.D n (x, y) v‖ ≤ M * parameterHeightWeight H w.stateArity *
      t ^ (w.angleArity + (shift + 1) * w.stateArity - 1) := by
  let L : (E × PolarPoint) →L[ℝ] E × ℝ :=
    (ContinuousLinearMap.fst ℝ E PolarPoint).prod
      ((ContinuousLinearMap.snd ℝ ℝ ℝ).comp (ContinuousLinearMap.snd ℝ E PolarPoint))
  have hL (z : E × PolarPoint) : L z = (z.1, z.2.2) := by
    simp only [L, ContinuousLinearMap.prod_apply, ContinuousLinearMap.comp_apply,
      ContinuousLinearMap.coe_fst', ContinuousLinearMap.coe_snd']
  have hmap : MapsTo L (U ×ˢ (univ : Set PolarPoint)) (U ×ˢ (univ : Set ℝ)) := by
    intro z hz
    rw [hL]
    exact ⟨hz.1, mem_univ _⟩
  let Q' := (J.compLinear L (hU.prod isOpen_univ) hmap).congrOn
    (fun z _ => congrArg f (hL z))
  have he : Q.D n (x, y) v =
      J.D n (x, y.2) (fun i => ((v i).1, (v i).2.2)) := by
    have hh := congrArg (fun A : (E × PolarPoint) [×n]→L[ℝ] F => A v)
      (Q.unique Q' n (x, y) ⟨hx, mem_univ _⟩)
    change Q.D n (x, y) v = J.D n (0 + L (x, y)) (fun i => L (v i)) at hh
    simpa only [zero_add, hL] using hh
  have hpure' (i : Fin n) : if w.isState i then (v i).2.2 = 0 else (v i).1 = 0 := by
    cases hi : w.isState i
    · simpa only [hi, Bool.false_eq_true, if_false] using hpure i
    · have hh : (v i).2 = 0 := by simpa only [hi, if_true] using hpure i
      simp only [hi, if_true, hh, Prod.snd_zero]
  have hbox' (i : Fin n) :
      p (v i).1 ≤ 1 ∧ q (v i).1 ≤ R ∧ ‖(v i).2.2‖ ≤ 1 :=
    ⟨(hbox i).1, (hbox i).2.1, (norm_snd_le (v i).2).trans (hbox i).2.2⟩
  have hb := n04PositiveGeometry_boundary_pure_unit_bound w (J.D n (x, y.2)) p q hR
    (fun u hu hbu => hbound n w hk ha u hu hbu)
    (fun i => ((v i).1, (v i).2.2)) hpure' hbox'
  have hcost : (w.angleArity - 1) + shift * w.stateArity ≤
      w.angleArity + (shift + 1) * w.stateArity - 1 := by
    have hs := w.arity_sum
    rw [Nat.add_mul, one_mul]
    omega
  rw [he]
  exact hb.trans (mul_le_mul_of_nonneg_left (pow_le_pow_right₀ ht hcost)
    (mul_nonneg hM (parameterHeightWeight_nonneg hH _)))

end ContinuousFlexibility.Analysis
