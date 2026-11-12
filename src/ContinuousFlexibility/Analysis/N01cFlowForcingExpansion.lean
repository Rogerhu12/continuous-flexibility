import ContinuousFlexibility.Analysis.N01cVolterraStateJets

/-!
# Exact state/angle expansion of the actual variational forcing

Every graph slot is its state identity contribution plus a scalar
lower-order variation in the angle direction. Multilinearity expands
these two choices in every slot. The resulting coefficients are actual
mixed state/angle evaluations of the given genuine speed tower; the
remaining factors are exactly the lower Volterra variations.

No size bound or derivative of the flow is added as a hypothesis.
-/

noncomputable section

namespace ContinuousFlexibility.Analysis

open Set Function
open ContinuousFlexibility.Statements
open scoped BigOperators

variable {E : Type*} [TopologicalSpace E] [AddCommGroup E] [Module ℝ E]
  [IsTopologicalAddGroup E] [ContinuousSMul ℝ E]

/-- Multilinearity separates fixed state directions from scalar angle
components. The finite set records the slots using a state direction. -/
theorem stateAngle_multilinear_expansion {n : ℕ}
    (A : (E × ℝ) [×n]→L[ℝ] ℝ) (v : Fin n → E) (y : Fin n → ℝ) :
    A (fun i => (v i, y i)) =
      ∑ s : Finset (Fin n),
        A (fun i => if i ∈ s then (v i, 0) else (0, 1)) *
          ∏ i, if i ∈ s then 1 else y i := by
  classical
  have hsum := A.map_add_univ
    (fun i => (v i, (0 : ℝ))) (fun i => ((0 : E), y i))
  have hinput : (fun i => (v i, (0 : ℝ))) +
      (fun i => ((0 : E), y i)) = fun i => (v i, y i) := by
    funext i
    simp only [Pi.add_apply, Prod.mk_add_mk, add_zero, zero_add]
  rw [hinput] at hsum
  rw [hsum]
  apply Finset.sum_congr rfl
  intro s _
  have he :
      s.piecewise (fun i => (v i, (0 : ℝ))) (fun i => ((0 : E), y i)) =
      fun i => (if i ∈ s then (1 : ℝ) else y i) •
        (if i ∈ s then (v i, (0 : ℝ)) else ((0 : E), 1)) := by
    funext i
    by_cases hi : i ∈ s <;> simp [Finset.piecewise, hi]
  rw [he]
  have hs := A.map_smul_univ
    (fun i => if i ∈ s then (1 : ℝ) else y i)
    (fun i => if i ∈ s then (v i, (0 : ℝ)) else ((0 : E), 1))
  simpa only [smul_eq_mul, mul_comm] using hs

theorem flowParameterIdentityJet_snd (n : ℕ) (v : Fin n → E) :
    (flowParameterIdentityJet n v).2 = 0 := by
  cases n with
  | zero => rfl
  | succ n =>
    cases n with
    | zero => rfl
    | succ n => rfl

theorem flowParameterIdentityJet_eq_zero {n : ℕ} (hn : n ≠ 1) (v : Fin n → E) :
    flowParameterIdentityJet n v = 0 := by
  cases n with
  | zero => rfl
  | succ n =>
    cases n with
    | zero => exact (hn rfl).elim
    | succ n => rfl

theorem flowGraphVariationSlot_eq_pair (n : ℕ) (B : E [×n]→L[ℝ] ℝ)
    (v : Fin n → E) :
    flowGraphVariationSlot n B v = ((flowParameterIdentityJet n v).1, B v) := by
  rw [flowGraphVariationSlot_apply]
  apply Prod.ext
  · simp only [Prod.fst_add, add_zero]
  · simp only [Prod.snd_add, flowParameterIdentityJet_snd, zero_add]

/-- The actual speed derivative after choosing state and unit-angle
slots. In a state slot, only singleton parameter blocks can survive. -/
def flowSelectedSpeedCoefficient {U : Set E} {G : E × PolarPoint → ℝ}
    (J : ContinuousTimeSpeedTower U G) (Θ : E × ℝ → ℝ) {N : ℕ}
    (c : _root_.OrderedFinpartition N) (s : Finset (Fin c.length))
    (p : E × ℝ) (v : Fin N → E) : ℝ :=
  J.D c.length (flowTrajectoryGraph Θ p)
    (fun i => if i ∈ s then
      ((flowParameterIdentityJet (c.partSize i) (v ∘ c.emb i)).1, 0) else (0, 1))

/-- The actual lower variation at an angle slot, and the multiplicative
identity at a state slot. The cutoff is the one used in Volterra recursion. -/
def flowSelectedLowerFactor {U : Set E} {N : ℕ}
    (B : ∀ k : ℕ, k < N → ContinuousStateVariation U k)
    (c : _root_.OrderedFinpartition N) (s : Finset (Fin c.length))
    (p : E × ℝ) (v : Fin N → E) (i : Fin c.length) : ℝ :=
  if i ∈ s then 1 else
    (lowerStateVariation B (c.partSize i)).value p (v ∘ c.emb i)

/-- Exact finite expansion of the genuine truncated forcing. -/
theorem truncatedFlowForcing_eq_selected_products
    {U : Set E} {G : E × PolarPoint → ℝ}
    (J : ContinuousTimeSpeedTower U G) (Θ : E × ℝ → ℝ) {N : ℕ}
    (B : ∀ k : ℕ, k < N → ContinuousStateVariation U k)
    (p : E × ℝ) (v : Fin N → E) :
    truncatedFlowForcing J Θ B p v =
      ∑ c : _root_.OrderedFinpartition N, ∑ s : Finset (Fin c.length),
        flowSelectedSpeedCoefficient J Θ c s p v *
          ∏ i, flowSelectedLowerFactor B c s p v i := by
  classical
  rw [truncatedFlowForcing_apply]
  apply Finset.sum_congr rfl
  intro c _
  simpa only [flowGraphVariationSlot_eq_pair,
    flowSelectedSpeedCoefficient, flowSelectedLowerFactor] using
    stateAngle_multilinear_expansion (J.D c.length (flowTrajectoryGraph Θ p))
      (fun i => (flowParameterIdentityJet (c.partSize i) (v ∘ c.emb i)).1)
      (fun i => (lowerStateVariation B (c.partSize i)).value p (v ∘ c.emb i))

/-- A selected state slot of a nonsingleton block vanishes, because the
parameter graph is affine in its state component. -/
theorem flowSelectedSpeedCoefficient_eq_zero
    {U : Set E} {G : E × PolarPoint → ℝ}
    (J : ContinuousTimeSpeedTower U G) (Θ : E × ℝ → ℝ) {N : ℕ}
    (c : _root_.OrderedFinpartition N) (s : Finset (Fin c.length))
    (p : E × ℝ) (v : Fin N → E) (i : Fin c.length)
    (hi : i ∈ s) (hsize : c.partSize i ≠ 1) :
    flowSelectedSpeedCoefficient J Θ c s p v = 0 := by
  classical
  apply (J.D c.length (flowTrajectoryGraph Θ p)).map_coord_zero i
  simp only [if_pos hi, flowParameterIdentityJet_eq_zero hsize, Prod.fst_zero]
  exact Prod.ext rfl rfl

/-- An unselected block at the current or higher order also vanishes,
so every surviving angle factor has strictly lower parameter order. -/
theorem flowSelectedLowerFactor_eq_zero_of_large
    {U : Set E} {N : ℕ}
    (B : ∀ k : ℕ, k < N → ContinuousStateVariation U k)
    (c : _root_.OrderedFinpartition N) (s : Finset (Fin c.length))
    (p : E × ℝ) (v : Fin N → E) (i : Fin c.length)
    (hi : i ∉ s) (hsize : N ≤ c.partSize i) :
    flowSelectedLowerFactor B c s p v i = 0 := by
  classical
  simp only [flowSelectedLowerFactor, if_neg hi, lowerStateVariation,
    dif_neg (Nat.not_lt.mpr hsize), zeroStateVariation,
    ContinuousMultilinearMap.zero_apply]

theorem flowSelectedLowerProduct_eq_zero_of_large
    {U : Set E} {N : ℕ}
    (B : ∀ k : ℕ, k < N → ContinuousStateVariation U k)
    (c : _root_.OrderedFinpartition N) (s : Finset (Fin c.length))
    (p : E × ℝ) (v : Fin N → E) (i : Fin c.length)
    (hi : i ∉ s) (hsize : N ≤ c.partSize i) :
    (∏ j, flowSelectedLowerFactor B c s p v j) = 0 := by
  classical
  exact Finset.prod_eq_zero (Finset.mem_univ i)
    (flowSelectedLowerFactor_eq_zero_of_large B c s p v i hi hsize)

/-- The expansion applied to the recursively constructed variations.
There is no independent family of candidate lower derivatives here. -/
theorem volterra_truncatedFlowForcing_eq_selected_products
    {U : Set E} {G : E × PolarPoint → ℝ}
    (J : ContinuousTimeSpeedTower U G) {Θ : E × ℝ → ℝ}
    (hΘ : ContinuousOn Θ (U ×ˢ univ)) (N : ℕ)
    (p : E × ℝ) (v : Fin N → E) :
    truncatedFlowForcing J Θ (fun k (_ : k < N) => volterraStateVariation J hΘ k) p v =
      ∑ c : _root_.OrderedFinpartition N, ∑ s : Finset (Fin c.length),
        flowSelectedSpeedCoefficient J Θ c s p v *
          ∏ i, flowSelectedLowerFactor
            (fun k (_ : k < N) => volterraStateVariation J hΘ k) c s p v i :=
  truncatedFlowForcing_eq_selected_products J Θ _ p v

end ContinuousFlexibility.Analysis
