import ContinuousFlexibility.Analysis.ProjectiveJetEvaluation
import ContinuousFlexibility.Scalar.WeightedHomogeneousFamilies

/-!
# The actual control column of a uniform directional tower

The column is the continuous linear map obtained from the genuine first
jet in the control direction, at zero control. The uniform first-jet
estimate supplies one fixed loss for every output order. Monotonicity
extends that estimate below the original base order, and translation of
the state seminorm gives the centered bound used in the nonlinear task.
-/

noncomputable section

namespace ContinuousFlexibility.Statements

open Set ContinuousFlexibility.Analysis
open scoped Topology

section Column

variable {X B Y : Type*}
  [TopologicalSpace X] [AddCommGroup X] [Module ℝ X]
  [TopologicalSpace B] [AddCommGroup B] [Module ℝ B]
  [TopologicalSpace Y] [AddCommGroup Y] [Module ℝ Y]
  {U : Set (X × B)} {F : X × B → Y}

/-- The actual first control derivative is a continuous linear map. -/
def n08ControlColumn (J : SmoothDirections U F) (x : X) : B →L[ℝ] Y :=
  (projectiveJetHeadLinear J.D 0 (x, 0) Fin.elim0).comp
    (ContinuousLinearMap.inr ℝ X B)

theorem n08ControlColumn_apply (J : SmoothDirections U F) (x : X) (b : B) :
    n08ControlColumn J x b = J.D 1 (x, 0) (Fin.cons (0, b) Fin.elim0) := by
  rw [n08ControlColumn, ContinuousLinearMap.comp_apply,
    ContinuousLinearMap.inr_apply, projectiveJetHeadLinear_apply]

theorem n08ControlColumn_hasLineDerivAt
    [IsTopologicalAddGroup X] [ContinuousSMul ℝ X]
    [IsTopologicalAddGroup B] [ContinuousSMul ℝ B] (J : SmoothDirections U F)
    {x : X} (hx : (x, (0 : B)) ∈ U) (b : B) :
    HasProjectiveLineDerivAt (fun a : B => F (x, a)) (n08ControlColumn J x b) 0 b := by
  have h := J.hasProjectiveJetsOn.hasLineDerivAt J.open_domain hx ((0 : X), b)
  simpa only [HasProjectiveLineDerivAt, projectiveFirstJetValue,
    n08ControlColumn_apply, Prod.smul_mk, Prod.mk_add_mk,
    smul_zero, add_zero, zero_add] using h

theorem n08ControlColumn_continuousOn (J : SmoothDirections U F) :
    ContinuousOn (fun z : X × B => n08ControlColumn J z.1 z.2)
      ({x | (x, (0 : B)) ∈ U} ×ˢ univ) := by
  have hinput : Continuous (fun z : X × B =>
      Fin.cons (α := fun _ : Fin 1 => X × B) (0, z.2) Fin.elim0) := by
    apply continuous_pi
    intro i
    refine Fin.cases ?_ (fun j => j.elim0) i
    simpa only [Fin.cons_zero] using continuous_const.prodMk continuous_snd
  have hmap : Continuous (fun z : X × B =>
      ((z.1, (0 : B)), Fin.cons (α := fun _ : Fin 1 => X × B) (0, z.2) Fin.elim0)) :=
    (continuous_fst.prodMk continuous_const).prodMk hinput
  apply ((J.continuous 1).comp hmap.continuousOn
    (fun z hz => ⟨hz.1, mem_univ _⟩)).congr
  intro z _
  exact n08ControlColumn_apply J z.1 z.2

end Column

section Estimates

variable {X B Y : Type*}
  [TopologicalSpace X] [AddCommGroup X] [Module ℝ X]
  [NormedAddCommGroup B] [NormedSpace ℝ B]
  [TopologicalSpace Y] [AddCommGroup Y] [Module ℝ Y]
  {p : ℕ → Seminorm ℝ X} {q : ℕ → Seminorm ℝ Y}
  {U : Set (X × B)} {F : X × B → Y} {base loss : ℕ}

/-- The Banach-control bound holds at every output order, including
orders below the original base, with one enlarged loss and one center. -/
theorem n08ControlColumn_bound_all_orders (hp : Monotone p) (hq : Monotone q)
    (J : SmoothDirections U F)
    (hJ : UniformScalarTowerEstimate (pairGrading p (fun _ => normSeminorm ℝ B))
      q U base loss F J) (x0 : X) :
    ∀ s : ℕ, ∃ C : ℝ, 0 ≤ C ∧ ∀ x, (x, (0 : B)) ∈ U → ∀ b : B,
      q s (n08ControlColumn J x b) ≤
        C * (1 + p (s + (base + loss)) (x - x0)) * ‖b‖ := by
  intro s
  obtain ⟨C, hC, hbound⟩ := hJ 1 (max s base) (le_max_right _ _)
  let t : ℕ := s + (base + loss)
  refine ⟨C * (2 + p t x0), mul_nonneg hC (by positivity), ?_⟩
  intro x hx b
  have htuple : (Fin.cons ((0 : X), b) Fin.elim0 : Fin 1 → X × B) =
      (fun _ => (0, b)) := by
    funext i
    fin_cases i
    exact Fin.cons_zero _ _
  have hb := hbound (x, 0) hx (fun _ : Fin 1 => (0, b))
  change q (max s base) (J.D 1 (x, 0) (fun _ : Fin 1 => (0, b))) ≤
    C * tameJetSize (pairGrading p (fun _ => normSeminorm ℝ B))
      1 (max s base) loss base (x, 0) (fun _ : Fin 1 => (0, b)) at hb
  rw [tameJetSize_pure_linear] at hb
  have horder : max s base + loss ≤ t := by dsimp [t]; omega
  have hxbound : p (max s base + loss) x ≤ p t (x - x0) + p t x0 :=
    (hp horder x).trans (by
      simpa only [sub_add_cancel] using map_add_le_add (p t) (x - x0) x0)
  have hcost : ‖b‖ + (1 + p (max s base + loss) x) * ‖b‖ ≤
      (2 + p t x0) * (1 + p t (x - x0)) * ‖b‖ := by
    have ha : 0 ≤ p t (x - x0) := apply_nonneg _ _
    have hc : 0 ≤ p t x0 := apply_nonneg _ _
    have hh : 2 + p (max s base + loss) x ≤
        (2 + p t x0) * (1 + p t (x - x0)) := by
      nlinarith [mul_nonneg hc ha]
    calc
      _ = (2 + p (max s base + loss) x) * ‖b‖ := by ring
      _ ≤ _ := mul_le_mul_of_nonneg_right hh (norm_nonneg _)
  calc
    q s (n08ControlColumn J x b) ≤ q (max s base) (n08ControlColumn J x b) :=
      hq (le_max_left _ _) _
    _ ≤ C * (‖b‖ + (1 + p (max s base + loss) x) * ‖b‖) := by
      simpa only [n08ControlColumn_apply, htuple, coe_normSeminorm] using hb
    _ ≤ C * ((2 + p t x0) * (1 + p t (x - x0)) * ‖b‖) :=
      mul_le_mul_of_nonneg_left hcost hC
    _ = _ := by ring

end Estimates

end ContinuousFlexibility.Statements
