module

public import ContinuousFlexibility.Analysis.N01cStateAngleSmoothDirections

/-!
# Exact word identification for any genuine joint tower

A supplied joint tower supplies its own finite affine smoothness. The
actual angular state towers therefore identify every joint multilinear
slot in its original order. No symmetry or joint-continuity assumption
is added to those already genuine towers.
-/

@[expose] public section

noncomputable section

namespace ContinuousFlexibility.Analysis

open Set Filter
open ContinuousFlexibility.Statements
open scoped Topology ContDiff BigOperators

variable {E : Type*} [TopologicalSpace E] [AddCommGroup E] [Module ℝ E]
  [IsTopologicalAddGroup E] [ContinuousSMul ℝ E]

/-- A joint state-angle tower gives the required finite affine
smoothness with an unused external time coordinate. -/
theorem isFiniteAffineTimeSmooth_of_jointSmoothDirections
    {U : Set E} {g : E × ℝ → ℝ}
    (J : SmoothDirections (U ×ˢ (univ : Set ℝ)) g) :
    IsFiniteAffineTimeSmooth U (fun p : E × PolarPoint => g (p.1, p.2.2)) := by
  intro d x₀ L
  let Q : ((Fin d → ℝ) × PolarPoint) →L[ℝ] (E × ℝ) :=
    (L.comp (ContinuousLinearMap.fst ℝ (Fin d → ℝ) PolarPoint)).prod
      ((ContinuousLinearMap.snd ℝ ℝ ℝ).comp
        (ContinuousLinearMap.snd ℝ (Fin d → ℝ) PolarPoint))
  have hQ (p : (Fin d → ℝ) × PolarPoint) : Q p = (L p.1, p.2.2) := rfl
  have hsubset :
      ((fun y => x₀ + L y) ⁻¹' U) ×ˢ (univ : Set PolarPoint) ⊆
        (fun p : (Fin d → ℝ) × PolarPoint => (x₀, (0 : ℝ)) + Q p) ⁻¹'
          (U ×ˢ (univ : Set ℝ)) := by
    intro p hp
    change (x₀ + L p.1 ∈ U) ∧ ((0 : ℝ) + p.2.2 ∈ (univ : Set ℝ))
    exact ⟨hp.1, mem_univ _⟩
  apply ((smoothDirections_contDiffOn_finiteAffine J (x₀, (0 : ℝ)) Q).mono hsubset).congr
  intro p hp
  simp only [hQ, Prod.mk_add_mk, zero_add]

/-- Every genuine joint jet is the full ordered state-angle word sum.
The candidate word sum need not be assumed jointly continuous for this
identification: the actual line derivatives and openness suffice. -/
theorem smoothDirections_joint_D_eq_stateAngleJet
    {U : Set E} {g : E × ℝ → ℝ}
    (J : SmoothDirections (U ×ˢ (univ : Set ℝ)) g)
    (Ja : ∀ b : ℕ, ∀ θ : ℝ, SmoothDirections U
      (fun x => iteratedDeriv b (fun η => g (x, η)) θ))
    (n : ℕ) : ∀ x : E, x ∈ U → ∀ (θ : ℝ) (v : Fin n → E × ℝ),
      J.D n (x, θ) v =
        stateAngleJet (fun b k => (Ja b θ).D k x) n v := by
  have hU : IsOpen U := (Ja 0 0).open_domain
  have hf := isFiniteAffineTimeSmooth_of_jointSmoothDirections J
  induction n with
  | zero =>
      intro x hx θ v
      rw [smoothDirections_D_zero_apply J ⟨hx, mem_univ _⟩ v, stateAngleJet_zero]
      simpa only [iteratedDeriv_zero] using
        (smoothDirections_D_zero_apply (Ja 0 θ) hx Fin.elim0).symm
  | succ n ih =>
      intro x hx θ v
      let line : ℝ → E × ℝ := fun τ => (x, θ) + τ • v 0
      have hline : Continuous line := continuous_const.add (continuous_id.smul continuous_const)
      have ht : Tendsto line (𝓝 (0 : ℝ)) (𝓝 (x, θ)) := by
        simpa only [ContinuousAt, line, zero_smul, add_zero] using
          (hline.continuousAt : ContinuousAt line (0 : ℝ))
      have hnear := ht.eventually ((hU.prod isOpen_univ).mem_nhds
        (show (x, θ) ∈ U ×ˢ (univ : Set ℝ) from ⟨hx, mem_univ _⟩))
      have heq :
          (fun τ : ℝ => J.D n (line τ) (Fin.tail v)) =ᶠ[𝓝 (0 : ℝ)]
          (fun τ : ℝ => stateAngleJet
            (fun b k => (Ja b (line τ).2).D k (line τ).1) n (Fin.tail v)) := by
        filter_upwards [hnear] with τ hτ
        exact ih (line τ).1 hτ.1 (line τ).2 (Fin.tail v)
      have hfull : HasDerivAt (fun τ : ℝ => J.D n (line τ) (Fin.tail v))
          (J.D (n + 1) (x, θ) (Fin.cons (v 0) (Fin.tail v))) 0 :=
        hasDerivAt_iff_tendsto_slope_zero.mpr
          (J.derivative n (x, θ) ⟨hx, mem_univ _⟩ (Fin.tail v) (v 0))
      have hc := stateAngleJet_hasProjectiveLineDerivAt hU hf
        (fun b q => Ja b q.2) n hx (0 : ℝ) θ (Fin.tail v) (v 0)
      have hcan : HasDerivAt
          (fun τ : ℝ => stateAngleJet
            (fun b k => (Ja b (line τ).2).D k (line τ).1) n (Fin.tail v))
          (stateAngleJet (fun b k => (Ja b θ).D k x) (n + 1)
            (Fin.cons (v 0) (Fin.tail v))) 0 :=
        hasDerivAt_iff_tendsto_slope_zero.mpr hc
      simpa only [Fin.cons_self_tail] using
        (hfull.congr_of_eventuallyEq heq.symm).unique hcan

/-- Pure slots may be interleaved in any prescribed order; the surviving
state directions are read in that same order. -/
theorem smoothDirections_joint_pureSlots
    {U : Set E} {g : E × ℝ → ℝ}
    (J : SmoothDirections (U ×ˢ (univ : Set ℝ)) g)
    (Ja : ∀ b : ℕ, ∀ θ : ℝ, SmoothDirections U
      (fun x => iteratedDeriv b (fun η => g (x, η)) θ))
    {n : ℕ} (w : StateAngleWord n) {x : E} (hx : x ∈ U)
    (θ : ℝ) (v : Fin w.stateArity → E) :
    J.D n (x, θ) (w.pureSlots v) = (Ja w.angleArity θ).D w.stateArity x v := by
  rw [smoothDirections_joint_D_eq_stateAngleJet J Ja n x hx θ (w.pureSlots v),
    stateAngleJet_pureSlots]

end ContinuousFlexibility.Analysis
