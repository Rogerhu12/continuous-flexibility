module

public import ContinuousFlexibility.Analysis.N01cPhysicalFlowPointJets
public import ContinuousFlexibility.Analysis.N01cPhysicalGraphNormalization

/-!
# The complete positive-radial flow jet at one physical point

The physical ODE supplies the actual tower. The pure-slot identity
identifies that tower with the full ordered-partition graph derivative,
whose raw bound is normalized once after all spatial orders are added.
-/

@[expose] public section

noncomputable section

namespace ContinuousFlexibility.Analysis

open Set
open ContinuousFlexibility.Statements
open scoped ContDiff BigOperators

variable {X : Type*} [TopologicalSpace X] [AddCommGroup X] [Module ℝ X]
  [IsTopologicalAddGroup X] [ContinuousSMul ℝ X] [LocallyConvexSpace ℝ X]

theorem physicalFlowPositiveMixed_point_oneHigh_bound
    {U : Set X} {I : Set ℝ} {lam Θ : X → PolarPoint → ℝ}
    (hU : IsOpen U) (hI : IsOpen I)
    (hlam : ∀ x ∈ U, ContDiffOn ℝ ∞ (lam x) (I ×ˢ (univ : Set ℝ)))
    (hΘ : ∀ x ∈ U, ContDiffOn ℝ ∞ (Θ x) (I ×ˢ (univ : Set ℝ)))
    (hODE : ∀ x ∈ U, ∀ r ∈ I, ∀ θ : ℝ,
      HasDerivAt (fun t => Θ x (t, θ)) (lam x (r, Θ x (r, θ))) r)
    {r : ℝ} (hr : r ∈ I)
    (Jlam : ∀ a : ℕ, SmoothDirections (U ×ˢ (univ : Set ℝ))
      (fun p => mixedDerivative a 0 (lam p.1) (r, p.2)))
    (JΘ : SmoothDirections (U ×ˢ (univ : Set ℝ)) (fun p => Θ p.1 (r, p.2)))
    (p : ℕ → Seminorm ℝ X) (center : X) (base high n b k S offset : ℕ)
    (hk : 0 < k) (horder : n + b + (offset + 1) * k ≤ S)
    {x : X} (hx : x ∈ U) (θ : ℝ)
    {δ C₀ C₁ E A₀ A₁ H L : ℝ} (hδ : 0 ≤ δ)
    (hC₀ : 0 ≤ C₀) (hC₁ : 1 ≤ C₁) (hE : 1 ≤ E) (hA₁ : 0 ≤ A₁)
    (hH : 0 ≤ H) (hHL : H ≤ L) (hL : 1 ≤ L)
    (houter : ∀ R : ℝ, 1 ≤ R → p high (x - center) ≤ R →
      ∀ j l, j + l ≤ b + k → ∀ η,
      ∀ J : SmoothDirections U
        (fun y => mixedDerivative 0 l (physicalFlowLieJet (lam y) n) (r, η)),
      ∀ u : Fin j → X, (∀ i, p base (u i) ≤ 1) →
        (∀ i, p high (u i) ≤ R) →
        δ ^ (n + 1) * |J.D j x u| ≤
          C₀ * E ^ A₀ * parameterHeightWeight H j *
            R ^ (((n + l : ℕ) : ℝ) / ((S : ℝ) + 1)))
    (hflow : ∀ R : ℝ, 1 ≤ R → p high (x - center) ≤ R →
      ∀ j l, 0 < j + l → j + l ≤ b + k → j ≤ k →
      ∀ J : SmoothDirections U
        (fun y => iteratedDeriv l (fun η => Θ y (r, η)) θ),
      ∀ u : Fin j → X, (∀ i, p base (u i) ≤ 1) →
        (∀ i, p high (u i) ≤ R) →
        |J.D j x u| ≤ C₁ * E ^ A₁ * parameterHeightWeight H j *
          R ^ (((if j = 0 then l - 1 else l + offset : ℕ) : ℝ) /
            ((S : ℝ) + 1)))
    (J : SmoothDirections U (fun y => mixedDerivative (n + 1) b (Θ y) (r, θ))) :
    ∀ v : Fin k → X,
      δ ^ (n + 1) * |J.D k x v| ≤
        (n01c_graphPartitionWordCount (b + k) * (C₀ * C₁ ^ (b + k) * L ^ (b + k)) *
          E ^ (A₀ + A₁ * ((b + k : ℕ) : ℝ)) * H) *
            oneHighVariationWeight p base high (x - center) v := by
  let JO := physicalLieJointSmoothDirections hU hI hlam hr Jlam n
  let JC := smoothDirections_realCompTVS (smoothDirections_stateFlowGraph JΘ) JO
    (fun q hq => ⟨hq.1, mem_univ _⟩)
  let Ja : ∀ l : ℕ, ∀ η : ℝ, SmoothDirections U
      (fun y => iteratedDeriv l (fun ζ => Θ y (r, ζ)) η) :=
    fun l η => smoothDirections_angularStateSlice JΘ l η
  let Ka : ∀ l : ℕ, ∀ η : ℝ, SmoothDirections U
      (fun y => iteratedDeriv l (fun ζ => physicalFlowLieJet (lam y) n (r, ζ)) η) :=
    fun l η => smoothDirections_angularStateSlice JO l η
  have hcount : 0 ≤ n01c_graphPartitionWordCount (b + k) :=
    Finset.sum_nonneg (fun _ _ => Nat.cast_nonneg _)
  have hweight : 0 ≤
      n01c_graphPartitionWordCount (b + k) * (C₀ * C₁ ^ (b + k) * L ^ (b + k)) *
        E ^ (A₀ + A₁ * ((b + k : ℕ) : ℝ)) * H := by
    exact mul_nonneg (mul_nonneg
      (mul_nonneg hcount (mul_nonneg (mul_nonneg hC₀
        (pow_nonneg (zero_le_one.trans hC₁) _))
        (pow_nonneg (zero_le_one.trans hL) _)))
      (Real.rpow_nonneg (zero_le_one.trans hE) _)) hH
  apply weightedMultilinear_oneHigh_of_unitPower p base high (x - center) (J.D k x)
    (pow_nonneg hδ _) hweight (spatialOrder_fraction_le_one horder)
  intro v hv R hR hxR hvR
  rw [physicalFlowPositiveMixed_D_eq_canonical hU hI hlam hΘ hODE hr Jlam JΘ
    n b k θ J hx v]
  rw [physicalFlowPositiveMixed_D_eq_angularComposition hU hI hlam hΘ hODE hr Jlam JΘ
    n b k θ x v]
  let w := StateAngleWord.stateThenAngle k b
  have hw : 0 < w.stateArity := by
    simpa only [w, StateAngleWord.stateThenAngle_stateArity] using hk
  have hs :
      ∀ u : Fin w.stateArity → X, (∀ i, p base (u i) ≤ 1) →
      (∀ i, p high (u i) ≤ R) →
      δ ^ (n + 1) *
          |(smoothDirections_angularStateSlice JC w.angleArity θ).D w.stateArity x u| ≤
        n01c_graphPartitionWordCount (b + k) *
          (C₀ * C₁ ^ (b + k) * L ^ (b + k)) *
          E ^ (A₀ + A₁ * ((b + k : ℕ) : ℝ)) * H *
            R ^ (((n + w.angleArity + (offset + 1) * w.stateArity : ℕ) : ℝ) /
              ((S : ℝ) + 1)) := by
    intro u hu huR
    rw [stateFlow_angularSlice_D_pureSlots JΘ JO w hx θ u]
    apply stateFlow_composition_raw_bound JΘ Ja JO Ka w hw
      (p base) (p high) n S offset hx θ u hu hR huR
      (pow_nonneg hδ _) hC₀ hC₁ hE hA₁ hH hHL hL
    · intro j l hjl η q hq hqR
      let KJ : SmoothDirections U
          (fun y => mixedDerivative 0 l (physicalFlowLieJet (lam y) n) (r, η)) :=
        (Ka l η).congr (fun _ _ => by
          simp only [mixedDerivative, iteratedDeriv_zero])
      have hh := houter R hR hxR j l hjl η KJ q hq hqR
      simpa only [KJ, SmoothDirections.congr] using hh
    · intro j l hjl hjlN hj u hu huR
      exact hflow R hR hxR j l hjl hjlN
        (by simpa only [w, StateAngleWord.stateThenAngle_stateArity] using hj)
        (Ja l θ) u hu huR
  have hwstate : w.stateArity = k := StateAngleWord.stateThenAngle_stateArity k b
  have hwangle : w.angleArity = b := StateAngleWord.stateThenAngle_angleArity k b
  rw [hwstate, hwangle] at hs
  exact hs v hv hvR

end ContinuousFlexibility.Analysis
