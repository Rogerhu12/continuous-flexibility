import ContinuousFlexibility.Analysis.N08StateLinearOperations
import ContinuousFlexibility.Analysis.ProjectiveJetEvaluation

/-! # Scalar first-jet bounds on a fixed-parameter affine line -/

noncomputable section

namespace ContinuousFlexibility.Statements

open Set ContinuousFlexibility.Analysis
open scoped BigOperators

set_option backward.isDefEq.respectTransparency false

variable {E : Type*} [TopologicalSpace E] [AddCommGroup E] [Module ℝ E]
  [IsTopologicalAddGroup E] [ContinuousSMul ℝ E]

theorem n08_seminorm_center_lt (p : Seminorm ℝ E) (x : E) {ε : ℝ} (hε : 0 < ε) :
    p (x - x) < ε := by
  simpa only [sub_self, map_zero] using hε

def N08RealCoefficientTowers {I P : Type*} (p : ℕ → Seminorm ℝ E)
    (U : Set (E × ℝ)) (f : I → ℕ → ℕ → P → E × ℝ → ℝ)
    (region : ℕ → P → Prop) (weight : ℝ → ℕ → ℝ) (base loss : ℕ) (x0 : E) : Prop :=
  ∀ k s : ℕ, ∃ B : ℝ, 0 < B ∧ ∀ m i a b y,
    a + b ≤ s → region m y → ∃ J : SmoothDirections U (f i a b y),
      ∀ z ∈ U, ∀ vs : Fin k → E × ℝ,
        |J.D k z vs| ≤ weight B m * oneHighVariationWeight (pairGrading p realGrading)
          base (s + loss) (z - (x0, 0)) vs

/-- A scalar tower's first jet equals the derivative of its actual affine
line with the final real parameter fixed. -/
theorem n08_realFirstJet_fixedParameter
    {U : Set (E × ℝ)} {f : E × ℝ → ℝ} (J : SmoothDirections U f)
    {x v : E} {q df : ℝ} (hx : (x, q) ∈ U)
    (hd : HasDerivAt (fun t : ℝ => f (x + n08RealSMul t v, q)) df 0) :
    J.D 1 (x, q) (Fin.cons (v, 0) Fin.elim0) = df := by
  have hJ : HasProjectiveJetsOn f J.D U :=
    ⟨J.zero, J.continuous, fun n y hy w vs => J.derivative n y hy vs w⟩
  have hline := hJ.hasLineDerivAt J.open_domain hx (v, 0)
  have h : HasDerivAt (fun t : ℝ => f ((x, q) + t • (v, 0)))
      (J.D 1 (x, q) (Fin.cons (v, 0) Fin.elim0)) 0 :=
    hasDerivAt_iff_tendsto_slope_zero.mpr hline
  have hfixed : HasDerivAt (fun t : ℝ => f (x + n08RealSMul t v, q))
      (J.D 1 (x, q) (Fin.cons (v, 0) Fin.elim0)) 0 := by
    simpa only [n08RealSMul, Prod.smul_mk, Prod.mk_add_mk, smul_zero, add_zero] using h
  exact hfixed.unique hd

theorem n08_oneHigh_first_product_zero
    (p : ℕ → Seminorm ℝ E) (base high : ℕ) (v : E) :
    oneHighVariationWeight (pairGrading p realGrading) base high
      (0 : E × ℝ) (Fin.cons (v, 0) Fin.elim0) = p base v + p high v := by
  simp [oneHighVariationWeight, pairGrading, realGrading]

/-- Extract a first-order one-high estimate before instantiating the large
physical state space. All derivative identification is on the actual line. -/
theorem n08_realFirstJet_reference_bound
    {U : Set (E × ℝ)} {f : E × ℝ → ℝ} (J : SmoothDirections U f)
    (p : ℕ → Seminorm ℝ E) (base high : ℕ) (x0 : E) (K : ℝ) (df : E → ℝ)
    (hx : (x0, 0) ∈ U)
    (hd : ∀ v : E, HasDerivAt (fun t : ℝ => f (x0 + n08RealSMul t v, 0)) (df v) 0)
    (hbound : ∀ z ∈ U, ∀ vs : Fin 1 → E × ℝ,
      |J.D 1 z vs| ≤ K * oneHighVariationWeight (pairGrading p realGrading)
        base high (z - (x0, 0)) vs) :
    ∀ v : E, |df v| ≤ K * (p base v + p high v) := by
  intro v
  have hvalue := n08_realFirstJet_fixedParameter J hx (hd v)
  have h := hbound (x0, 0) hx (Fin.cons (v, 0) Fin.elim0)
  simpa only [hvalue, sub_self, n08_oneHigh_first_product_zero] using h

/-- Eliminate the entire quantified coefficient tower while the state
space is still abstract. This keeps its concrete realization opaque. -/
theorem n08_realFirstJet_tower_reference_bound
    {I P R : Type*} (p : ℕ → Seminorm ℝ E) (U : Set (E × ℝ))
    (f : I → ℕ → ℕ → P → E × ℝ → ℝ) (region : ℕ → P → Prop)
    (weight : ℝ → ℕ → ℝ) (base loss : ℕ) (x0 : E)
    (s a b : ℕ) (i : I) (point : R → P) (df : R → E → ℝ)
    (horder : a + b ≤ s) (hx : (x0, 0) ∈ U)
    (hd : ∀ r v, HasDerivAt
      (fun t : ℝ => f i a b (point r) (x0 + n08RealSMul t v, 0)) (df r v) 0)
    (h : N08RealCoefficientTowers p U f region weight base loss x0) :
    ∃ B : ℝ, 0 < B ∧ ∀ m r, region m (point r) → ∀ v : E,
      |df r v| ≤ weight B m * (p base v + p (s + loss) v) := by
  obtain ⟨B, hB, hBj⟩ := h 1 s
  refine ⟨B, hB, fun m r hr => ?_⟩
  obtain ⟨J, hJ⟩ := hBj m i a b (point r) horder hr
  exact n08_realFirstJet_reference_bound J p base (s + loss) x0
    (weight B m) (df r) hx (hd r) hJ

theorem n08_realFirstJet_zero_tower_reference_bound
    {I P R : Type*} (p : ℕ → Seminorm ℝ E) (U : Set (E × ℝ))
    (f : I → ℕ → ℕ → P → E × ℝ → ℝ) (region : ℕ → P → Prop)
    (weight : ℝ → ℕ → ℝ) (base loss : ℕ) (x0 : E)
    (i : I) (point : R → P) (df : R → E → ℝ) (hx : (x0, 0) ∈ U)
    (hd : ∀ r v, HasDerivAt
      (fun t : ℝ => f i 0 0 (point r) (x0 + n08RealSMul t v, 0)) (df r v) 0)
    (h : N08RealCoefficientTowers p U f region weight base loss x0) :
    ∃ B : ℝ, 0 < B ∧ ∀ m r, region m (point r) → ∀ v : E,
      |df r v| ≤ weight B m * (p base v + p loss v) := by
  simpa only [Nat.zero_add] using
    n08_realFirstJet_tower_reference_bound p U f region weight base loss x0
      0 0 0 i point df (by decide) hx hd h

end ContinuousFlexibility.Statements
