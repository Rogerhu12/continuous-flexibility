module

public import ContinuousFlexibility.Analysis.N01cFlowJetIdentification

/-!
# Naturality of the genuine Volterra variations at one parameter value

Only the actual speed jets and the actual trajectory at the selected
parameter values are compared. The finite parameter map may therefore
be compressed away from the base point. No global affine relation
between the two trajectory families is needed.
-/

@[expose] public section

noncomputable section

namespace ContinuousFlexibility.Analysis

open Set Function
open scoped Topology BigOperators

variable {E F : Type*}
  [TopologicalSpace E] [AddCommGroup E] [Module ℝ E]
  [IsTopologicalAddGroup E] [ContinuousSMul ℝ E]
  [TopologicalSpace F] [AddCommGroup F] [Module ℝ F]
  [IsTopologicalAddGroup F] [ContinuousSMul ℝ F]

def flowStateAngleMap (L : F →L[ℝ] E) : (F × ℝ) →L[ℝ] (E × ℝ) :=
  L.prodMap (ContinuousLinearMap.id ℝ ℝ)

@[simp] theorem flowStateAngleMap_apply (L : F →L[ℝ] E) (p : F × ℝ) :
    flowStateAngleMap L p = (L p.1, p.2) := rfl

theorem flowStateAngleMap_graphSlot (L : F →L[ℝ] E) (n : ℕ)
    (A : F [×n]→L[ℝ] ℝ) (B : E [×n]→L[ℝ] ℝ) (v : Fin n → F)
    (h : A v = B (fun i => L (v i))) :
    flowStateAngleMap L (flowGraphVariationSlot n A v) =
      flowGraphVariationSlot n B (fun i => L (v i)) := by
  have hi : flowStateAngleMap L (flowParameterIdentityJet n v) =
      flowParameterIdentityJet n (fun i => L (v i)) := by
    cases n with
    | zero => exact map_zero _
    | succ n =>
      cases n with
      | zero => rfl
      | succ n => exact map_zero _
  rw [flowGraphVariationSlot_apply, map_add, hi, flowGraphVariationSlot_apply]
  have ha : flowStateAngleMap L (0, A v) = (0, B (fun i => L (v i))) := by
    change (L 0, A v) = _
    rw [map_zero, h]
  rw [ha]

/-- Equality of the actual speed jets along one trajectory forces
equality of all recursively constructed variations at that trajectory. -/
theorem volterraStateVariation_natural_at
    {U : Set E} {V : Set F}
    {G : E × PolarPoint → ℝ} {H : F × PolarPoint → ℝ}
    {Θ : E × ℝ → ℝ} {Φ : F × ℝ → ℝ}
    (J : ContinuousTimeSpeedTower U G) (K : ContinuousTimeSpeedTower V H)
    (hΘ : ContinuousOn Θ (U ×ˢ (univ : Set ℝ)))
    (hΦ : ContinuousOn Φ (V ×ˢ (univ : Set ℝ)))
    (L : F →L[ℝ] E) {x : E} (hx : x ∈ U) {q : F} (hq : q ∈ V)
    (hbase : ∀ t : ℝ, Φ (q, t) = Θ (x, t))
    (hjets : ∀ t θ : ℝ, ∀ n : ℕ, ∀ v : Fin n → F × ℝ,
      K.D n (q, (t, θ)) v =
        J.D n (x, (t, θ)) (fun i => flowStateAngleMap L (v i)))
    (n : ℕ) (v : Fin n → F) (t : ℝ) :
    (volterraStateVariation K hΦ n).value (q, t) v =
      (volterraStateVariation J hΘ n).value (x, t) (fun i => L (v i)) := by
  have hlinear (r : ℝ) :
      speedAlongFlowAngularJet K Φ (q, r) =
        speedAlongFlowAngularJet J Θ (x, r) := by
    unfold speedAlongFlowAngularJet flowTrajectoryGraph
    rw [hbase r, hjets]
    congr 1
    funext i
    exact congrArg (fun z : E => (z, (1 : ℝ))) (map_zero L)
  induction n using Nat.strong_induction_on generalizing t with
  | h n ih =>
    cases n with
    | zero =>
      have hv : v = Fin.elim0 := Subsingleton.elim _ _
      have hw : (fun i => L (v i)) = (Fin.elim0 : Fin 0 → E) :=
        Subsingleton.elim _ _
      rw [hw, hv, volterraStateVariation_zero_apply, volterraStateVariation_zero_apply]
      exact hbase t
    | succ n =>
      have hforcing (r : ℝ) :
          truncatedFlowForcing K Φ
            (fun k (_ : k < n + 1) => volterraStateVariation K hΦ k) (q, r) v =
          truncatedFlowForcing J Θ
            (fun k (_ : k < n + 1) => volterraStateVariation J hΘ k)
              (x, r) (fun i => L (v i)) := by
        simp only [truncatedFlowForcing_apply, flowTrajectoryGraph]
        apply Finset.sum_congr rfl
        intro c _
        rw [hbase r, hjets]
        congr 1
        funext i
        apply flowStateAngleMap_graphSlot
        by_cases hi : c.partSize i < n + 1
        · rw [lowerStateVariation_of_lt _ hi, lowerStateVariation_of_lt _ hi]
          exact ih (c.partSize i) hi (v ∘ c.emb i) r
        · simp only [lowerStateVariation, dif_neg hi, zeroStateVariation, zero_apply]
      have hy0 :
          (volterraStateVariation K hΦ (n + 1)).value (q, 0) v = 0 := by
        rw [volterraStateVariation_succ_initial K hΦ n hq]
        rfl
      have hy (r : ℝ) :
          HasDerivAt (fun s => (volterraStateVariation K hΦ (n + 1)).value (q, s) v)
            (speedAlongFlowAngularJet J Θ (x, r) *
                (volterraStateVariation K hΦ (n + 1)).value (q, r) v +
              truncatedFlowForcing J Θ
                (fun k (_ : k < n + 1) => volterraStateVariation J hΘ k)
                  (x, r) (fun i => L (v i))) r := by
        simpa only [hlinear r, hforcing r] using
          volterraStateVariation_hasDerivAt_time K hΦ n hq v r
      exact volterraStateVariation_succ_unique J hΘ n hx
        (fun i => L (v i)) hy0 hy t

end ContinuousFlexibility.Analysis
