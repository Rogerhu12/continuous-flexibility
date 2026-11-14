module

public import ContinuousFlexibility.Analysis.N04RealizationTwoEndpointCubicJets

/-!
# The exact affine cost in divided coefficient jets

On the unit cylinder, the physical cubic factor contributes the sixth
power of the fixed component width. Its reciprocal is retained in the
quantitative conclusion; it does not depend on the requested spatial or
parameter order. A material estimate for that fixed factor can therefore
be supplied separately by the actual atlas.
-/

@[expose] public section

noncomputable section

namespace ContinuousFlexibility.Analysis

open Set
open ContinuousFlexibility.Statements
open scoped ContDiff

variable {E : Type*} [TopologicalSpace E] [AddCommGroup E] [Module ℝ E]
  [IsTopologicalAddGroup E] [ContinuousSMul ℝ E]
  {U : Set E} {N e : E → PolarPoint → ℝ} {width : ℝ}

/-- The actual unit-coordinate quotient carries precisely the inverse
sixth width power, before that fixed cost is absorbed into material data. -/
theorem n04Realization_unitCubic_parameterJets
    (hU : IsOpen U) (hwidth : 0 < width)
    (RN : MixedJetRegularity U (Ioo (0 : ℝ) 1 ×ˢ (univ : Set ℝ)) N)
    (hrep : ∀ x ∈ U, ∃ F : PolarPoint → ℝ, ContDiff ℝ ∞ F ∧
      EqOn F (N x) (Ioo (0 : ℝ) 1 ×ˢ (univ : Set ℝ)) ∧
      ∀ c : Bool, ∀ θ i, i ≤ 2 →
        iteratedDeriv i (fun t : ℝ => F (t, θ)) (if c then 1 else 0) = 0)
    (hfactor : ∀ x ∈ U, ∀ q ∈ Ioo (0 : ℝ) 1 ×ˢ (univ : Set ℝ),
      N x q = width ^ 6 * (q.1 * (1 - q.1)) ^ 3 * e x q)
    (G : ∀ k : ℕ, ℕ → ℕ → E × (Fin k → E) → ℝ)
    (hG : ∀ k a b, Continuous (G k a b))
    (hbound : ∀ k a b q (hq : q ∈ Ioo (0 : ℝ) 1 ×ˢ (univ : Set ℝ)),
      ∀ x ∈ U, ∀ v : Fin k → E,
        |(RN.parameter a b q hq).D k x v| ≤ G k a b (x, v)) :
    ∃ RE : MixedJetRegularity U (Ioo (0 : ℝ) 1 ×ˢ (univ : Set ℝ)) e,
      ∀ k a b p (hp : p ∈ Ioo (0 : ℝ) 1 ×ˢ (univ : Set ℝ)),
        ∀ x ∈ U, ∀ v : Fin k → E,
          |(RE.parameter a b p hp).D k x v| ≤
            (width ^ 6)⁻¹ * G k (a + 6) b (x, v) / 4 := by
  let v : E → PolarPoint → ℝ := fun x q => width ^ 6 * e x q
  have hf : ∀ x ∈ U, ∀ q ∈ Ioo (0 : ℝ) 1 ×ˢ (univ : Set ℝ),
      N x q = (q.1 * (1 - q.1)) ^ 3 * v x q := by
    intro x hx q hq
    rw [hfactor x hx q hq]
    dsimp only [v]
    ring
  obtain ⟨RV, hV⟩ := n04Realization_twoEndpointCubic_parameterJets
    hU zero_lt_one RN hrep hf G hG hbound
  have hpow : 0 < width ^ 6 := pow_pos hwidth 6
  let RE : MixedJetRegularity U (Ioo (0 : ℝ) 1 ×ˢ (univ : Set ℝ)) e :=
    n04Realization_mixedJetRegularity_of_staticFactorization RV hU
      (isOpen_Ioo.prod isOpen_univ) contDiffOn_const (fun _ _ => hpow.ne')
      (fun _ _ _ _ => rfl)
  refine ⟨RE, ?_⟩
  intro k a b p hp x hx dirs
  have he := n04Realization_smoothDirections_D_const_mul
    (RE.parameter a b p hp) (RV.parameter a b p hp) (width ^ 6)
    (fun y _ => by simp only [v, mixedDerivative, iteratedDeriv_const_mul_field]) k hx dirs
  have hb := hV k a b p hp x hx dirs
  rw [he, abs_mul, abs_of_pos hpow] at hb
  calc
    |(RE.parameter a b p hp).D k x dirs| =
        (width ^ 6)⁻¹ * (width ^ 6 * |(RE.parameter a b p hp).D k x dirs|) := by
      rw [← mul_assoc, inv_mul_cancel₀ hpow.ne', one_mul]
    _ ≤ (width ^ 6)⁻¹ * (G k (a + 6) b (x, dirs) / 4) :=
      mul_le_mul_of_nonneg_left hb (inv_nonneg.mpr hpow.le)
    _ = _ := by ring

end ContinuousFlexibility.Analysis
