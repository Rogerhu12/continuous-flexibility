import ContinuousFlexibility.Analysis.N04PulledFieldsCompositionBudget
import ContinuousFlexibility.Analysis.N04PulledFieldsCompositionCost

/-!
# Uniform positive jets of genuine moving-point families

Physical and inverse raw prefixes are assembled on the same parameter
domain and the same low grading. For each positive parameter order the
high loss is selected before the spatial order. Exact mixed expansions,
the masked composition and one final normalization give the sampled
height factor with a single high seminorm.
-/

noncomputable section

namespace ContinuousFlexibility.Analysis

open Set ContinuousFlexibility.Statements

variable {X ι : Type*} [TopologicalSpace X] [AddCommGroup X] [Module ℝ X]
  [IsTopologicalAddGroup X] [ContinuousSMul ℝ X] [LocallyConvexSpace ℝ X]
  {U : Set X} {V Ω : Set PolarPoint}

/-- Raw estimates for the physical field and actual inverse graph imply
the complete positive-parameter estimate of their genuine composition.
Neither a bound for the composed family nor its current-data interface
is assumed. All numerical coefficients precede the piece and point. -/
theorem n04PulledFields_movingFamily_positiveJets
    {f : ι → X × PolarPoint → ℝ} (F : ∀ i, SmoothDirections (U ×ˢ V) (f i))
    {φ : ι → X × PolarPoint → PolarPoint}
    (Jφ : ∀ i, SmoothDirections (U ×ˢ Ω) (φ i))
    (hφ : ∀ i, MapsTo (φ i) (U ×ˢ Ω) V)
    (hU : IsOpen U) (hΩ : IsOpen Ω) (hc : Convex ℝ (U ×ˢ Ω))
    (p : ℕ → Seminorm ℝ X) (hp : Monotone p) (base : ℕ)
    (E H : ι → ℝ) (hE : ∀ i, 1 ≤ E i) (hH : ∀ i, 0 ≤ H i)
    {L : ℝ} (hL : 1 ≤ L) (hHL : ∀ i, H i ≤ L)
    (A : ι → X → PolarPoint → ∀ a b j : ℕ, X [×j]→L[ℝ] ℝ)
    (hexpansion : ∀ i x, x ∈ U → ∀ q ∈ Ω, ∀ n : ℕ,
      ∀ u : Fin n → X × PolarPoint,
      (F i).D n (x, φ i (x, q)) u =
        scalarAngularExpansion n
          (fun b j => scalarAngularExpansion j
            (fun a k => (A i x q a b k).toMultilinearMap))
          (fun d => (((u d).1, (u d).2.1), (u d).2.2)))
    (physicalLoss : ℕ → ℕ)
    (hphysical : ∀ K top : ℕ, ∃ C P : ℝ, 1 ≤ C ∧ 0 ≤ P ∧
      ∀ i x, x ∈ U → ∀ q ∈ Ω, ∀ a b j : ℕ, j ≤ K → a + b ≤ top →
      ∀ u : Fin j → X, (∀ d, p base (u d) ≤ 1) →
      ∀ R : ℝ, 1 ≤ R → p (top + physicalLoss K) x ≤ R →
        (∀ d, p (top + physicalLoss K) (u d) ≤ R) →
        |A i x q a b j u| ≤ C * E i ^ P * parameterHeightWeight (H i) j *
          (R ^ (1 / ((top : ℝ) + 1))) ^ (a + b))
    (hinverse : ∀ K : ℕ, ∃ offset : ℕ, ∀ N : ℕ,
      ∃ M P : ℝ, 1 ≤ M ∧ 0 ≤ P ∧
      ∀ i x, x ∈ U → ∀ q ∈ Ω, ∀ R : ℝ, 1 ≤ R →
      p (base + N + offset + 1) x ≤ R →
      ∀ n : ℕ, 0 < n → n ≤ N → ∀ w : StateAngleWord n, w.stateArity ≤ K →
      ∀ u : Fin n → X × PolarPoint,
      (∀ d, p base (u d).1 ≤ 1) →
      (∀ d, p (base + N + offset + 1) (u d).1 ≤ R) →
      (∀ d, ‖(u d).2‖ ≤ 1) →
      (∀ d, w.isState d = false → (u d).1 = 0) →
      (∀ d, w.isState d = true → (u d).2 = 0) →
      ‖(Jφ i).D n (x, q) u‖ ≤ M * E i ^ P * parameterHeightWeight (H i) w.stateArity *
        (R ^ (1 / (((N + offset : ℕ) : ℝ) + 1))) ^
          (if w.stateArity = 0 then w.angleArity - 1 else w.angleArity + offset)) :
    ∀ k : ℕ, 0 < k → ∃ loss : ℕ, ∀ s : ℕ, ∃ B : ℝ, 0 < B ∧
      ∀ i x, x ∈ U → ∀ q ∈ Ω, ∀ a b : ℕ, a + b ≤ s →
      ∀ Q : SmoothDirections U
        (fun z => mixedDerivative a b (fun y => f i (z, φ i (z, y))) q),
      ∀ v : Fin k → X,
        |Q.D k x v| ≤ B * E i ^ B * H i *
          oneHighVariationWeight p base (s + loss) x v := by
  intro k hkpos
  refine (hinverse k).elim fun offset hinverseK => ?_
  let loss : ℕ := n04PulledFieldsCompositionLoss base k offset (physicalLoss k)
  refine ⟨loss, fun s => ?_⟩
  let N : ℕ := n04PulledFieldsCompositionPrefix s k offset
  let top : ℕ := n04PulledFieldsCompositionTop s k offset
  have htotal : k + s ≤ N := n04PulledFieldsCompositionPrefix_total_le s k offset
  have hbudget : s + (offset + 1) * k ≤ top :=
    n04PulledFieldsCompositionPrefix_le_top s k offset
  have htotalTop : k + s ≤ top := htotal.trans (Nat.le_add_right N offset)
  have hphysicalIndex : top + physicalLoss k ≤ s + loss :=
    n04PulledFieldsCompositionLoss_physicalHigh_le base s k offset (physicalLoss k)
  have hinverseIndex : base + N + offset + 1 ≤ s + loss := by
    simpa only [N, loss, n04PulledFieldsCompositionTop, Nat.add_assoc] using
      n04PulledFieldsCompositionLoss_inverseHigh_le base s k offset (physicalLoss k)
  refine (hphysical k top).elim fun C hphysicalC => ?_
  refine hphysicalC.elim fun P hphysicalCP => ?_
  refine (hinverseK N).elim fun M hinverseM => ?_
  refine hinverseM.elim fun T hinverseMT => ?_
  have hC : 1 ≤ C := hphysicalCP.1
  have hP : 0 ≤ P := hphysicalCP.2.1
  have hphys := hphysicalCP.2.2
  have hM : 1 ≤ M := hinverseMT.1
  have hT : 0 ≤ T := hinverseMT.2.1
  have hinv := hinverseMT.2.2
  refine (n04PulledFields_movingPoint_materialOneHigh k s C P M T L
    p base (s + loss)).elim fun B hB => ?_
  refine ⟨B, hB.1, fun i x hx q hq a b hab Q v => ?_⟩
  have hCE : 0 ≤ C * E i ^ P :=
    mul_nonneg (zero_le_one.trans hC) (Real.rpow_nonneg (zero_le_one.trans (hE i)) _)
  have hME : 1 ≤ M * E i ^ T := by
    have hpow : 1 ≤ E i ^ T := Real.one_le_rpow (hE i) hT
    simpa only [one_mul] using
      mul_le_mul hM hpow zero_le_one (zero_le_one.trans hM)
  have hnormalized := n04PulledFields_movingPoint_masked_positive_oneHigh
    (F i) (Jφ i) (hφ i) hU hΩ hc p base (s + loss)
    hCE hME (hH i) (hHL i) hL k s offset top hbudget x hx q hq (A i x q)
    (fun n _ u => hexpansion i x hx q hq n u)
    (fun R hR hxR a' b' j horder hj u hu huR =>
      hphys i x hx q hq a' b' j hj (by omega) u hu R hR
        ((hp hphysicalIndex x).trans hxR)
        (fun d => (hp hphysicalIndex (u d)).trans (huR d)))
    (fun R hR hxR n hn hnOrder w hw u hu huR hspatial hstate hangle =>
      hinv i x hx q hq R hR ((hp hinverseIndex x).trans hxR)
        n hn (hnOrder.trans htotal) w hw u hu
        (fun d => (hp hinverseIndex (u d).1).trans (huR d))
        hspatial hstate hangle)
    k a b le_rfl hkpos hab Q
  exact hB.2 (E i) (H i) (hE i) (hH i) k x v (Q.D k x v) (hnormalized v)

end ContinuousFlexibility.Analysis
