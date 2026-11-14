import ContinuousFlexibility.Analysis.N04PositiveGeometryBoundaryFormulaAlgebra
import ContinuousFlexibility.Analysis.N01cPhysicalGraphJets

/-!
# The eight literal boundary formulas with one spatial order coefficient

Input and output towers are genuine derivatives of the displayed
functions. The finite intrinsic reserve is three; the variable angular
order and the original parameter order remain separate throughout.
-/

noncomputable section

namespace ContinuousFlexibility.Analysis

open Set Function ContinuousFlexibility.Statements
open scoped ContDiff BigOperators

variable {E : Type*} [TopologicalSpace E] [AddCommGroup E] [Module ℝ E]
  [IsTopologicalAddGroup E] [ContinuousSMul ℝ E]
  {U : Set E} {f : E × ℝ → ℝ}

theorem n04PositiveGeometry_boundaryWord_of_angular
    (J : SmoothDirections (U ×ˢ (univ : Set ℝ)) f)
    (JA : ∀ b θ, SmoothDirections U (fun x => iteratedDeriv b (fun η => f (x, η)) θ))
    (K s d : ℕ) (x : E) (hx : x ∈ U) (θ : ℝ) (P : E → Prop)
    (M H t : ℝ) (shift : ℕ)
    (hb : ∀ k, k ≤ K → ∀ b, b ≤ s → ∀ a, a ≤ d →
      ∀ v : Fin k → E, (∀ i, P (v i)) →
        ‖(JA (b + a) θ).D k x v‖ ≤
          M * parameterHeightWeight H k * t ^ (b + shift * k)) :
    N04BoundaryWordBounds J K s d x θ P M H t shift := by
  intro n w hk ha v hv hp
  let u := w.stateDirections v
  have hu (i : Fin w.stateArity) : P (u i) := by
    obtain ⟨j, hj, he⟩ := w.stateDirections_mem_range v i
    change P (w.stateDirections v i)
    rw [he]
    exact hp j
  have hsplit : (w.angleArity - d) + min d w.angleArity = w.angleArity := by omega
  have hbound := hb w.stateArity hk (w.angleArity - d) (by omega)
    (min d w.angleArity) (min_le_left _ _) u hu
  rw [hsplit] at hbound
  have he := smoothDirections_joint_pureSlots J JA w hx θ u
  have he' : w.pureSlots u = v := w.pureSlots_stateDirections _ hv
  rw [he'] at he
  exact (congrArg norm he).trans_le hbound

private theorem boundary_pureSlots_predicate {n : ℕ} (w : StateAngleWord n)
    (P : E → Prop) (hP : P 0) (v : Fin w.stateArity → E) (hv : ∀ i, P (v i)) :
    ∀ i, P (w.pureSlots v i).1 := by
  induction w with
  | nil => intro i; exact i.elim0
  | state w ih =>
      intro j
      refine Fin.cases ?_ (fun i => ?_) j
      · exact hv (0 : Fin (w.stateArity + 1))
      · exact ih (Fin.tail v) (fun i => hv i.succ) i
  | angle w ih =>
      intro j
      refine Fin.cases ?_ (fun i => ?_) j
      · exact hP
      · exact ih v hv i

theorem n04PositiveGeometry_boundaryWord_to_angular_reserve
    (J : SmoothDirections (U ×ˢ (univ : Set ℝ)) f)
    (JA : ∀ b θ, SmoothDirections U (fun x => iteratedDeriv b (fun η => f (x, η)) θ))
    {K s d : ℕ} {x : E} (hx : x ∈ U) (θ : ℝ) (P : E → Prop) (hP : P 0)
    {M H t : ℝ} {shift : ℕ}
    (h : N04BoundaryWordBounds J K s d x θ P M H t shift)
    (k b : ℕ) (hk : k ≤ K) (hb : b ≤ s + d) (v : Fin k → E) (hv : ∀ i, P (v i)) :
    ‖(JA b θ).D k x v‖ ≤ M * parameterHeightWeight H k * t ^ ((b - d) + shift * k) := by
  have hword (n : ℕ) (w : StateAngleWord n) (hk : w.stateArity ≤ K)
      (hb : w.angleArity ≤ s + d) (v : Fin w.stateArity → E) (hv : ∀ i, P (v i)) :
      ‖(JA w.angleArity θ).D w.stateArity x v‖ ≤
        M * parameterHeightWeight H w.stateArity * t ^ ((w.angleArity - d) + shift * w.stateArity) := by
    have hw := h n w hk hb (w.pureSlots v)
      (w.isPure_pureSlots v) (boundary_pureSlots_predicate w P hP v hv)
    rw [smoothDirections_joint_pureSlots J JA w hx θ v] at hw
    exact hw
  let w := StateAngleWord.stateThenAngle k b
  have htower := hword (b + k) w
  have hstate : w.stateArity = k := StateAngleWord.stateThenAngle_stateArity k b
  have hangle : w.angleArity = b := StateAngleWord.stateThenAngle_angleArity k b
  rw [hstate, hangle] at htower
  exact htower hk hb v hv

theorem n04PositiveGeometry_boundaryWord_to_angular
    (J : SmoothDirections (U ×ˢ (univ : Set ℝ)) f)
    (JA : ∀ b θ, SmoothDirections U (fun x => iteratedDeriv b (fun η => f (x, η)) θ))
    {K s : ℕ} {x : E} (hx : x ∈ U) (θ : ℝ) (P : E → Prop) (hP : P 0)
    {M H t : ℝ} {shift : ℕ}
    (h : N04BoundaryWordBounds J K s 0 x θ P M H t shift)
    (k b : ℕ) (hk : k ≤ K) (hb : b ≤ s) (v : Fin k → E) (hv : ∀ i, P (v i)) :
    ‖(JA b θ).D k x v‖ ≤ M * parameterHeightWeight H k * t ^ (b + shift * k) := by
  simpa only [Nat.sub_zero] using
    n04PositiveGeometry_boundaryWord_to_angular_reserve J JA hx θ P hP h k b hk
      (by simpa only [Nat.add_zero] using hb) v hv

def n04PositiveGeometry_boundaryFormula_directions
    {v : Fin 9 → E × ℝ → ℝ}
    (J : ∀ i, SmoothDirections (U ×ˢ (univ : Set ℝ)) (v i)) (i : Fin 8) :
    SmoothDirections (U ×ˢ univ)
      (fun z => n04PositiveGeometry_boundaryFormula i (fun j θ => v j (z.1, θ)) z.2) :=
  ((n04PositiveGeometry_boundaryExpressions i).directions J).congr
    (fun z _ => congrFun (n04PositiveGeometry_boundaryExpression_eval i
      (fun j θ => v j (z.1, θ))) z.2)

/-- A common polynomial cost for all eight existing formulas. The
coefficient is chosen before the original domain, fields or material
sample. No high seminorm is raised to the number of product factors. -/
theorem n04PositiveGeometry_boundaryFormulas_weighted_reserve
    (K s reserve : ℕ) (L : ℝ) (hL : 1 ≤ L) :
    ∃ C : ℝ, 1 ≤ C ∧ ∃ degree : ℕ,
      ∀ {U : Set E}, Convex ℝ U →
      ∀ {v : Fin 9 → E × ℝ → ℝ},
      ∀ J : ∀ i, SmoothDirections (U ×ˢ univ) (v i),
      ∀ x ∈ U, ∀ θ (P : E → Prop), P 0 →
      ∀ M H t : ℝ, 1 ≤ M → 0 ≤ H → H ≤ L → 1 ≤ t → ∀ shift,
      (∀ i k, k ≤ K → ∀ b, b ≤ s → ∀ a, a ≤ reserve + 3 →
        ∀ JA : SmoothDirections U
          (fun y => iteratedDeriv (b + a) (fun η => v i (y, η)) θ),
        ∀ u : Fin k → E, (∀ j, P (u j)) →
          ‖JA.D k x u‖ ≤ M * parameterHeightWeight H k * t ^ (b + shift * k)) →
      ∀ i : Fin 8, ∀ k, k ≤ K → ∀ b, b ≤ s → ∀ a, a ≤ reserve →
      ∀ Q : SmoothDirections U (fun y => iteratedDeriv (b + a)
        (n04PositiveGeometry_boundaryFormula i (fun j θ => v j (y, θ))) θ),
      ∀ u : Fin k → E, (∀ j, P (u j)) →
        ‖Q.D k x u‖ ≤ C * M ^ degree * parameterHeightWeight H k *
          t ^ (b + shift * k) := by
  classical
  choose c hc degree hb using fun i : Fin 8 =>
    (n04PositiveGeometry_boundaryExpressions i).polynomial_bound (E := E) K s reserve L hL
  let C : ℝ := 1 + ∑ i, c i
  let d : ℕ := ∑ i, degree i
  have hC : 1 ≤ C := le_add_of_nonneg_right
    (Finset.sum_nonneg fun i _ => zero_le_one.trans (hc i))
  have hcC (i : Fin 8) : c i ≤ C :=
    (Finset.single_le_sum (fun j _ => zero_le_one.trans (hc j)) (Finset.mem_univ i)).trans
      (le_add_of_nonneg_left zero_le_one)
  have hdd (i : Fin 8) : degree i ≤ d :=
    Finset.single_le_sum (fun j _ => Nat.zero_le (degree j)) (Finset.mem_univ i)
  refine ⟨C, hC, d, ?_⟩
  intro U hU v J x hx θ P hP M H t hM hH hHL ht shift hsource i k hk b hbs a ha Q u hu
  have hinputs (j : Fin 9) : N04BoundaryWordBounds (J j) K s (reserve + 3) x θ P M H t shift :=
    n04PositiveGeometry_boundaryWord_of_angular (J j)
      (smoothDirections_angularStateSlice (J j)) K s (reserve + 3) x hx θ P M H t shift
      (fun k hk b hb a ha u hu => hsource j k hk b hb a ha _ u hu)
  have hformula := hb i hU J x hx θ P hP M H t hM hH hHL ht shift
    (fun j => (hinputs j).reserve (zero_le_one.trans hM) hH ht (by
      exact Nat.add_le_add_left (n04PositiveGeometry_boundaryExpression_depth i) reserve))
  have hcost : c i * M ^ degree i ≤ C * M ^ d :=
    mul_le_mul (hcC i) (pow_le_pow_right₀ hM (hdd i))
      (pow_nonneg (zero_le_one.trans hM) _) (zero_le_one.trans hC)
  let JF := n04PositiveGeometry_boundaryFormula_directions J i
  have hf : N04BoundaryWordBounds JF K s reserve x θ P (C * M ^ d) H t shift :=
    hformula.enlarge hH (zero_le_one.trans ht) hcost
  have hbound := n04PositiveGeometry_boundaryWord_to_angular_reserve JF
    (smoothDirections_angularStateSlice JF) hx θ P hP hf k (b + a) hk (by omega) u hu
  have hbound' := hbound.trans (mul_le_mul_of_nonneg_left
    (pow_le_pow_right₀ ht (by omega : (b + a - reserve) + shift * k ≤ b + shift * k))
    (mul_nonneg (mul_nonneg (zero_le_one.trans hC)
      (pow_nonneg (zero_le_one.trans hM) _)) (parameterHeightWeight_nonneg hH _)))
  have he := Q.unique (smoothDirections_angularStateSlice JF (b + a) θ) k x hx
  exact (congrArg norm (congrArg (fun A : E [×k]→L[ℝ] ℝ => A u) he)).trans_le hbound'

theorem n04PositiveGeometry_boundaryFormulas_weighted_prefix
    (K s : ℕ) (L : ℝ) (hL : 1 ≤ L) :
    ∃ C : ℝ, 1 ≤ C ∧ ∃ degree : ℕ,
      ∀ {U : Set E}, Convex ℝ U →
      ∀ {v : Fin 9 → E × ℝ → ℝ},
      ∀ J : ∀ i, SmoothDirections (U ×ˢ univ) (v i),
      ∀ x ∈ U, ∀ θ (P : E → Prop), P 0 →
      ∀ M H t : ℝ, 1 ≤ M → 0 ≤ H → H ≤ L → 1 ≤ t → ∀ shift,
      (∀ i k, k ≤ K → ∀ b, b ≤ s → ∀ a, a ≤ 3 →
        ∀ JA : SmoothDirections U
          (fun y => iteratedDeriv (b + a) (fun η => v i (y, η)) θ),
        ∀ u : Fin k → E, (∀ j, P (u j)) →
          ‖JA.D k x u‖ ≤ M * parameterHeightWeight H k * t ^ (b + shift * k)) →
      ∀ i : Fin 8, ∀ k, k ≤ K → ∀ b, b ≤ s →
      ∀ Q : SmoothDirections U (fun y => iteratedDeriv b
        (n04PositiveGeometry_boundaryFormula i (fun j θ => v j (y, θ))) θ),
      ∀ u : Fin k → E, (∀ j, P (u j)) →
        ‖Q.D k x u‖ ≤ C * M ^ degree * parameterHeightWeight H k *
          t ^ (b + shift * k) := by
  obtain ⟨C, hC, degree, hb⟩ :=
    n04PositiveGeometry_boundaryFormulas_weighted_reserve (E := E) K s 0 L hL
  refine ⟨C, hC, degree, ?_⟩
  intro U hU v J x hx θ P hP M H t hM hH hHL ht shift hsource i k hk b hbs Q u hu
  simpa only [Nat.add_zero] using hb hU J x hx θ P hP M H t hM hH hHL ht shift
    (by simpa only [Nat.zero_add] using hsource) i k hk b hbs 0 (Nat.zero_le _) Q u hu

end ContinuousFlexibility.Analysis
