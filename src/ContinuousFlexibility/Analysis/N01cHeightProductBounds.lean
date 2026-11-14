module

public import ContinuousFlexibility.Analysis.N01cLinearProductJets
public import ContinuousFlexibility.Analysis.N01cPolarJetBounds

/-!
# One-high bounds for the genuine q times height parameter towers

The real parameter multiplies a continuous-linear state-height input.
Its actual tower has only three possibly nonzero orders. Each of those
orders satisfies the same one-high variation bound on the entire region
where the real parameter has absolute value at most one. No interpolation
or restriction of the high state seminorm is required.

The actual joint-state specializations retain H^(3/4) and the original
E0 power. A fixed reference state contributes only its fixed-order
seminorm to the constant.
-/

@[expose] public section

noncomputable section

namespace ContinuousFlexibility.Analysis

open Set
open ContinuousFlexibility.Statements
open scoped BigOperators

variable {E : Type*} [TopologicalSpace E] [AddCommGroup E] [Module ℝ E]

/-- The actual quadratic tower for a real parameter times a linear input. -/
def smoothDirections_qLinear (L : E →L[ℝ] ℝ) :
    SmoothDirections univ (fun z : E × ℝ => z.2 * L z.1) :=
  (smoothDirections_linearProduct (ContinuousLinearMap.snd ℝ E ℝ)
    (L.comp (ContinuousLinearMap.fst ℝ E ℝ))).congr
      (fun z _ => by
        simp only [ContinuousLinearMap.coe_snd', ContinuousLinearMap.comp_apply,
          ContinuousLinearMap.coe_fst'])

section Bounds

variable [IsTopologicalAddGroup E] [ContinuousSMul ℝ E]

/-- The explicit two-slot weight, stated with a literal finite index type. -/
private theorem oneHighVariationWeight_two
    (p : ℕ → Seminorm ℝ E) (base high : ℕ) (x : E) (v : Fin 2 → E) :
    oneHighVariationWeight p base high x v =
      (1 + p high x) * (p base (v 0) * p base (v 1)) +
        (p high (v 0) * p base (v 1) + p high (v 1) * p base (v 0)) := by
  have h0 : (Finset.univ : Finset (Fin 2)).erase 0 = {1} := by decide
  have h1 : (Finset.univ : Finset (Fin 2)).erase 1 = {0} := by decide
  simp only [oneHighVariationWeight, Fin.prod_univ_two, Fin.sum_univ_two,
    h0, h1, Finset.prod_singleton]

/-- The exact quadratic parameter tower obeys one fixed high-order bound.
The low order is arbitrary; only the real parameter is bounded by one. -/
theorem qLinear_oneHigh_bound
    (p : ℕ → Seminorm ℝ E) (L : E →L[ℝ] ℝ) (base high : ℕ)
    {W : ℝ} (hW : 0 ≤ W) (hL : ∀ x : E, |L x| ≤ W * p high x)
    {U : Set (E × ℝ)} {f : E × ℝ → ℝ}
    (J : SmoothDirections U f) (hformula : ∀ z ∈ U, f z = z.2 * L z.1)
    (k : ℕ) (x0 : E) (z : E × ℝ) (hz : z ∈ U) (hq : |z.2| ≤ 1)
    (v : Fin k → (E × ℝ)) :
    |J.D k z v| ≤ W * (1 + p high x0) *
      oneHighVariationWeight (pairGrading p realGrading) base high (z - (x0, 0)) v := by
  let P := pairGrading p realGrading
  let M : ℝ := 1 + p high x0
  let H : ℝ := P high (z - (x0, 0))
  have hM : 1 ≤ M := le_add_of_nonneg_right (apply_nonneg _ _)
  have hM0 : 0 ≤ M := zero_le_one.trans hM
  have hH : 0 ≤ H := apply_nonneg _ _
  have hP (n : ℕ) (y : E × ℝ) : P n y = p n y.1 + |y.2| := by
    simp only [P, tamePairGrading_apply, realGrading, coe_normSeminorm, Real.norm_eq_abs]
  have hfst (n : ℕ) (y : E × ℝ) : p n y.1 ≤ P n y := by
    rw [hP]
    exact le_add_of_nonneg_right (abs_nonneg _)
  have hsnd (n : ℕ) (y : E × ℝ) : |y.2| ≤ P n y := by
    rw [hP]
    exact le_add_of_nonneg_left (apply_nonneg _ _)
  have hdelta : p high (z.1 - x0) ≤ H := hfst high (z - (x0, 0))
  have hzstate : p high z.1 ≤ H + p high x0 := by
    have ht : p high z.1 ≤ p high (z.1 - x0) + p high x0 := by
      simpa only [sub_add_cancel] using map_add_le_add (p high) (z.1 - x0) x0
    exact ht.trans (add_le_add hdelta le_rfl)
  have hamp : p high z.1 ≤ M * (1 + H) := by
    dsimp only [M]
    nlinarith [mul_nonneg hH (apply_nonneg (p high) x0)]
  have hxL : |L z.1| ≤ W * M * (1 + H) := by
    simpa only [mul_assoc] using
      (hL z.1).trans (mul_le_mul_of_nonneg_left hamp hW)
  have hWM : 0 ≤ W * M := mul_nonneg hW hM0
  have hvL (y : E × ℝ) : |L y.1| ≤ W * M * P high y := by
    calc
      _ ≤ W * p high y.1 := hL y.1
      _ ≤ W * P high y := mul_le_mul_of_nonneg_left (hfst high y) hW
      _ ≤ (W * M) * P high y :=
        mul_le_mul_of_nonneg_right (le_mul_of_one_le_right hW hM) (apply_nonneg _ _)
  let Q : E × ℝ →L[ℝ] ℝ := ContinuousLinearMap.snd ℝ E ℝ
  let A : E × ℝ →L[ℝ] ℝ := L.comp (ContinuousLinearMap.fst ℝ E ℝ)
  have hQ (y : E × ℝ) : Q y = y.2 := by
    simp only [Q, ContinuousLinearMap.coe_snd']
  have hA (y : E × ℝ) : A y = L y.1 := by
    simp only [A, ContinuousLinearMap.comp_apply, ContinuousLinearMap.coe_fst']
  have hproduct : ∀ y ∈ U, f y = Q y * A y := by
    intro y hy
    simpa only [hQ, hA] using hformula y hy
  cases k with
  | zero =>
      have hd : J.D 0 z v = z.2 * L z.1 := by
        simpa only [hQ, hA] using scalarLinearProduct_D_zero Q A J hproduct z hz v
      calc
        |J.D 0 z v| = |z.2 * L z.1| := congrArg abs hd
        _ ≤ W * M * (1 + H) := by
          simpa only [abs_mul, one_mul] using
            mul_le_mul hq hxL (abs_nonneg _) zero_le_one
        _ = W * M * oneHighVariationWeight P base high (z - (x0, 0)) v := by
          simp [oneHighVariationWeight, H]
  | succ k =>
      cases k with
      | zero =>
          have hd : J.D 1 z v = (v 0).2 * L z.1 + z.2 * L (v 0).1 := by
            simpa only [hQ, hA] using scalarLinearProduct_D_one Q A J hproduct z hz v
          have hsize : oneHighVariationWeight P base high (z - (x0, 0)) v =
              (1 + H) * P base (v 0) + P high (v 0) := by
            simp [oneHighVariationWeight, H]
          calc
            |J.D 1 z v| = |(v 0).2 * L z.1 + z.2 * L (v 0).1| := congrArg abs hd
            _ ≤ |(v 0).2| * |L z.1| + |z.2| * |L (v 0).1| := by
              simpa only [abs_mul] using
                abs_add_le ((v 0).2 * L z.1) (z.2 * L (v 0).1)
            _ ≤ P base (v 0) * (W * M * (1 + H)) +
                1 * (W * M * P high (v 0)) :=
              add_le_add
                (mul_le_mul (hsnd base (v 0)) hxL (abs_nonneg _) (apply_nonneg _ _))
                (mul_le_mul hq (hvL (v 0)) (abs_nonneg _) zero_le_one)
            _ = W * M * oneHighVariationWeight P base high (z - (x0, 0)) v := by
              rw [hsize]
              ring
      | succ k =>
          cases k with
          | zero =>
              have hd : J.D 2 z v =
                  (v 0).2 * L (v 1).1 + (v 1).2 * L (v 0).1 := by
                simpa only [hQ, hA] using scalarLinearProduct_D_two Q A J hproduct z hz v
              have hsize : oneHighVariationWeight P base high (z - (x0, 0)) v =
                  (1 + H) * (P base (v 0) * P base (v 1)) +
                    (P high (v 0) * P base (v 1) + P high (v 1) * P base (v 0)) := by
                exact oneHighVariationWeight_two P base high (z - (x0, 0)) v
              have hrest : 0 ≤ (1 + H) * (P base (v 0) * P base (v 1)) :=
                mul_nonneg (add_nonneg zero_le_one hH)
                  (mul_nonneg (apply_nonneg _ _) (apply_nonneg _ _))
              calc
                |J.D 2 z v| =
                    |(v 0).2 * L (v 1).1 + (v 1).2 * L (v 0).1| := congrArg abs hd
                _ ≤ |(v 0).2| * |L (v 1).1| + |(v 1).2| * |L (v 0).1| := by
                  simpa only [abs_mul] using
                    abs_add_le ((v 0).2 * L (v 1).1) ((v 1).2 * L (v 0).1)
                _ ≤ P base (v 0) * (W * M * P high (v 1)) +
                    P base (v 1) * (W * M * P high (v 0)) :=
                  add_le_add
                    (mul_le_mul (hsnd base (v 0)) (hvL (v 1))
                      (abs_nonneg _) (apply_nonneg _ _))
                    (mul_le_mul (hsnd base (v 1)) (hvL (v 0))
                      (abs_nonneg _) (apply_nonneg _ _))
                _ = W * M *
                    (P high (v 0) * P base (v 1) + P high (v 1) * P base (v 0)) := by ring
                _ ≤ W * M * oneHighVariationWeight P base high (z - (x0, 0)) v := by
                  rw [hsize]
                  exact mul_le_mul_of_nonneg_left (le_add_of_nonneg_left hrest) hWM
          | succ n =>
              have hd : J.D (n + 3) z v = 0 :=
                scalarLinearProduct_D_ge_three Q A J hproduct n z hz v
              have hsize : 0 ≤ oneHighVariationWeight P base high (z - (x0, 0)) v := by
                unfold oneHighVariationWeight
                positivity
              simpa only [hd, abs_zero] using mul_nonneg hWM hsize


/-- The weighted scalar-jet estimate passes to every genuine q-linear
tower. The whole existential and quantifier calculation takes place over
an abstract state space, before any concrete physical model is supplied. -/
theorem family_qMixedJets_oneHigh_bound
    (p : ℕ → Seminorm ℝ E) (f : E → PolarPoint → ℝ)
    (E0 H : ℝ → ℝ) (γ : ℝ) (Ω : Set PolarPoint) (s high : ℕ)
    (L : ∀ a b : ℕ, ∀ q : PolarPoint, q ∈ Ω → E →L[ℝ] ℝ)
    (heval : ∀ a b q hq x, L a b q hq x = mixedDerivative a b (f x) q)
    (hweights : ∀ q ∈ Ω, 0 ≤ E0 q.1 ∧ 0 ≤ H q.1)
    (hraw : ∃ C A : ℝ, 0 ≤ C ∧ 0 ≤ A ∧ ∀ x : E, ∀ a b : ℕ,
      0 < a + b → a + b ≤ s → ∀ q ∈ Ω,
        |mixedDerivative a b (f x) q| ≤ C * E0 q.1 ^ A * H q.1 ^ γ * p high x) :
    ∃ C A : ℝ, 0 ≤ C ∧ 0 ≤ A ∧ ∀ a b : ℕ,
      0 < a + b → a + b ≤ s → ∀ q ∈ Ω,
      ∀ U : Set (E × ℝ),
      ∀ J : SmoothDirections U (fun z => z.2 * mixedDerivative a b (f z.1) q),
      ∀ k base : ℕ, ∀ x0 : E, ∀ z ∈ U, |z.2| ≤ 1 →
      ∀ v : Fin k → (E × ℝ),
        |J.D k z v| ≤ C * E0 q.1 ^ A * H q.1 ^ γ *
          (1 + p high x0) *
          oneHighVariationWeight (pairGrading p realGrading)
            base high (z - (x0, 0)) v := by
  obtain ⟨C, A, hC, hA, hb⟩ := hraw
  refine ⟨C, A, hC, hA, fun a b hpos horder q hq U J k base x0 z hz hzq v => ?_⟩
  have hW : 0 ≤ C * E0 q.1 ^ A * H q.1 ^ γ :=
    mul_nonneg (mul_nonneg hC (Real.rpow_nonneg (hweights q hq).1 _))
      (Real.rpow_nonneg (hweights q hq).2 _)
  have hL (x : E) :
      |L a b q hq x| ≤ (C * E0 q.1 ^ A * H q.1 ^ γ) * p high x := by
    rw [heval]
    exact hb x a b hpos horder q hq
  have hformula (y : E × ℝ) (_hy : y ∈ U) :
      y.2 * mixedDerivative a b (f y.1) q = y.2 * L a b q hq y.1 :=
    congrArg (fun t : ℝ => y.2 * t) (heval a b q hq y.1).symm
  exact qLinear_oneHigh_bound p (L a b q hq) base high hW hL
    J hformula k x0 z hz hzq v

/-- The five polar input functions can share constants before selecting
an input. This zero-spatial-order specialization uses the full raw jet
estimate without inspecting a concrete state model. -/
theorem family_qFiveInputs_oneHigh_bound
    (p : ℕ → Seminorm ℝ E) (f : Fin 5 → E → PolarPoint → ℝ)
    (E0 H : ℝ → ℝ) (γ : ℝ) (Ω : Set PolarPoint) (s high : ℕ)
    (L : ∀ q : PolarPoint, q ∈ Ω → Fin 5 → E →L[ℝ] ℝ)
    (heval : ∀ q hq i x, L q hq i x = f i x q)
    (hweights : ∀ q ∈ Ω, 0 ≤ E0 q.1 ∧ 0 ≤ H q.1)
    (hraw : ∃ C A : ℝ, 0 ≤ C ∧ 0 ≤ A ∧ ∀ x : E, ∀ a b : ℕ,
      a + b ≤ s → ∀ q ∈ Ω,
      (|mixedDerivative a b (f 0 x) q| ≤ C * E0 q.1 ^ A * H q.1 ^ γ * p high x) ∧
      (|mixedDerivative a b (f 1 x) q| ≤ C * E0 q.1 ^ A * H q.1 ^ γ * p high x) ∧
      (|mixedDerivative a b (f 2 x) q| ≤ C * E0 q.1 ^ A * H q.1 ^ γ * p high x) ∧
      (|mixedDerivative a b (f 3 x) q| ≤ C * E0 q.1 ^ A * H q.1 ^ γ * p high x) ∧
      (|mixedDerivative a b (f 4 x) q| ≤ C * E0 q.1 ^ A * H q.1 ^ γ * p high x)) :
    ∃ C A : ℝ, 0 ≤ C ∧ 0 ≤ A ∧ ∀ i : Fin 5, ∀ q ∈ Ω,
      ∀ U : Set (E × ℝ),
      ∀ J : SmoothDirections U (fun z => z.2 * f i z.1 q),
      ∀ k base : ℕ, ∀ x0 : E, ∀ z ∈ U, |z.2| ≤ 1 →
      ∀ v : Fin k → (E × ℝ),
        |J.D k z v| ≤ C * E0 q.1 ^ A * H q.1 ^ γ *
          (1 + p high x0) *
          oneHighVariationWeight (pairGrading p realGrading)
            base high (z - (x0, 0)) v := by
  obtain ⟨C, A, hC, hA, hb⟩ := hraw
  refine ⟨C, A, hC, hA, fun i q hq U J k base x0 z hz hzq v => ?_⟩
  have hW : 0 ≤ C * E0 q.1 ^ A * H q.1 ^ γ :=
    mul_nonneg (mul_nonneg hC (Real.rpow_nonneg (hweights q hq).1 _))
      (Real.rpow_nonneg (hweights q hq).2 _)
  have hinput (x : E) : |f i x q| ≤ C * E0 q.1 ^ A * H q.1 ^ γ * p high x := by
    have hfive := hb x 0 0 (Nat.zero_le s) q hq
    simp only [mixedDerivative, iteratedDeriv_zero] at hfive
    refine Fin.cases hfive.1 ?_ i
    refine Fin.cases hfive.2.1 ?_
    refine Fin.cases hfive.2.2.1 ?_
    refine Fin.cases hfive.2.2.2.1 ?_
    refine Fin.cases hfive.2.2.2.2 ?_
    exact fun j => Fin.elim0 j
  have hL (x : E) : |L q hq i x| ≤
      (C * E0 q.1 ^ A * H q.1 ^ γ) * p high x := by
    rw [heval]
    exact hinput x
  have hformula (y : E × ℝ) (_hy : y ∈ U) :
      y.2 * f i y.1 q = y.2 * L q hq i y.1 :=
    congrArg (fun t : ℝ => y.2 * t) (heval q hq i y.1).symm
  exact qLinear_oneHigh_bound p (L q hq i) base high hW hL
    J hformula k x0 z hz hzq v

/-- The same full-quantifier bridge preserves every actual mixed spatial
jet of the five inputs and one fixed high grading index. -/
theorem family_qFiveMixedJets_oneHigh_bound
    (p : ℕ → Seminorm ℝ E) (f : Fin 5 → E → PolarPoint → ℝ)
    (E0 H : ℝ → ℝ) (γ : ℝ) (Ω : Set PolarPoint) (s high : ℕ)
    (L : ∀ a b : ℕ, ∀ q : PolarPoint, q ∈ Ω → Fin 5 → E →L[ℝ] ℝ)
    (heval : ∀ a b q hq i x, L a b q hq i x = mixedDerivative a b (f i x) q)
    (hweights : ∀ q ∈ Ω, 0 ≤ E0 q.1 ∧ 0 ≤ H q.1)
    (hraw : ∃ C A : ℝ, 0 ≤ C ∧ 0 ≤ A ∧ ∀ x : E, ∀ a b : ℕ,
      a + b ≤ s → ∀ q ∈ Ω,
      (|mixedDerivative a b (f 0 x) q| ≤ C * E0 q.1 ^ A * H q.1 ^ γ * p high x) ∧
      (|mixedDerivative a b (f 1 x) q| ≤ C * E0 q.1 ^ A * H q.1 ^ γ * p high x) ∧
      (|mixedDerivative a b (f 2 x) q| ≤ C * E0 q.1 ^ A * H q.1 ^ γ * p high x) ∧
      (|mixedDerivative a b (f 3 x) q| ≤ C * E0 q.1 ^ A * H q.1 ^ γ * p high x) ∧
      (|mixedDerivative a b (f 4 x) q| ≤ C * E0 q.1 ^ A * H q.1 ^ γ * p high x)) :
    ∃ C A : ℝ, 0 ≤ C ∧ 0 ≤ A ∧ ∀ i : Fin 5, ∀ a b : ℕ, a + b ≤ s →
      ∀ q ∈ Ω, ∀ U : Set (E × ℝ),
      ∀ J : SmoothDirections U (fun z => z.2 * mixedDerivative a b (f i z.1) q),
      ∀ k base : ℕ, ∀ x0 : E, ∀ z ∈ U, |z.2| ≤ 1 →
      ∀ v : Fin k → (E × ℝ),
        |J.D k z v| ≤ C * E0 q.1 ^ A * H q.1 ^ γ *
          (1 + p high x0) *
          oneHighVariationWeight (pairGrading p realGrading)
            base high (z - (x0, 0)) v := by
  obtain ⟨C, A, hC, hA, hb⟩ := hraw
  refine ⟨C, A, hC, hA, fun i a b hab q hq U J k base x0 z hz hzq v => ?_⟩
  have hW : 0 ≤ C * E0 q.1 ^ A * H q.1 ^ γ :=
    mul_nonneg (mul_nonneg hC (Real.rpow_nonneg (hweights q hq).1 _))
      (Real.rpow_nonneg (hweights q hq).2 _)
  have hinput (x : E) :
      |mixedDerivative a b (f i x) q| ≤ C * E0 q.1 ^ A * H q.1 ^ γ * p high x := by
    have hfive := hb x a b hab q hq
    refine Fin.cases hfive.1 ?_ i
    refine Fin.cases hfive.2.1 ?_
    refine Fin.cases hfive.2.2.1 ?_
    refine Fin.cases hfive.2.2.2.1 ?_
    refine Fin.cases hfive.2.2.2.2 ?_
    exact fun j => Fin.elim0 j
  have hL (x : E) : |L a b q hq i x| ≤
      (C * E0 q.1 ^ A * H q.1 ^ γ) * p high x := by
    rw [heval]
    exact hinput x
  have hformula (y : E × ℝ) (_hy : y ∈ U) :
      y.2 * mixedDerivative a b (f i y.1) q = y.2 * L a b q hq i y.1 :=
    congrArg (fun t : ℝ => y.2 * t) (heval a b q hq i y.1).symm
  exact qLinear_oneHigh_bound p (L a b q hq i) base high hW hL
    J hformula k x0 z hz hzq v

end Bounds

end ContinuousFlexibility.Analysis

namespace ContinuousFlexibility.Statements

open Set ContinuousFlexibility.Analysis

/-- The five actual polar height inputs, in the coefficient formula's order. -/
def stateUPolarInput (S : PhysicalSpacesData) :
    Fin 5 → AnnularState S → PolarPoint → ℝ :=
  Fin.cases (fun x => heightRadial (stateU S x))
    (Fin.cases (fun x => heightAngular (stateU S x))
      (Fin.cases (fun x => radialPartial (heightRadial (stateU S x)))
        (Fin.cases (fun x => radialPartial (heightAngular (stateU S x)))
          (Fin.cases (fun x => angularPartial (heightAngular (stateU S x)))
            (fun i => Fin.elim0 i)))))

/-- Their previously proved physical jet functionals, with the same order. -/
def stateUPolarInputCLM
    {D : ReferenceData} {T : MaterialData} {S : PhysicalSpacesData}
    (hT : IsMaterialData D T) (hS : IsPhysicalSpaces D T S)
    (p : PolarPoint) (hp : p ∈ annularOpen D) :
    Fin 5 → AnnularState S →L[ℝ] ℝ :=
  Fin.cases (stateUHeightRadialCLM hT hS p hp)
    (Fin.cases (stateUHeightAngularCLM hT hS p hp)
      (Fin.cases (stateURadialHeightRadialCLM hT hS p hp)
        (Fin.cases (stateURadialHeightAngularCLM hT hS p hp)
          (Fin.cases (stateUAngularHeightAngularCLM hT hS p hp)
            (fun i => Fin.elim0 i)))))

set_option backward.isDefEq.respectTransparency true in
theorem stateUPolarInputCLM_apply
    {D : ReferenceData} {T : MaterialData} {S : PhysicalSpacesData}
    (hT : IsMaterialData D T) (hS : IsPhysicalSpaces D T S)
    (p : PolarPoint) (hp : p ∈ annularOpen D) (hr : p.1 ≠ 0)
    (i : Fin 5) (x : AnnularState S) :
    stateUPolarInputCLM hT hS p hp i x = stateUPolarInput S i x p := by
  refine Fin.cases (stateUHeightRadialCLM_apply hT hS p hp x) ?_ i
  refine Fin.cases (stateUHeightAngularCLM_apply hT hS p hp x) ?_
  refine Fin.cases (stateURadialHeightRadialCLM_apply hT hS p hp x) ?_
  refine Fin.cases (stateURadialHeightAngularCLM_apply hT hS p hp hr x) ?_
  refine Fin.cases (stateUAngularHeightAngularCLM_apply hT hS p hp hr x) ?_
  exact fun j => Fin.elim0 j

set_option backward.isDefEq.respectTransparency true in
/-- The genuine joint-parameter tower for q times an ordinary state-height jet. -/
def qStateUJetSmoothDirections
    {D : ReferenceData} {T : MaterialData} {S : PhysicalSpacesData}
    (hT : IsMaterialData D T) (hS : IsPhysicalSpaces D T S)
    (a b : ℕ) (p : PolarPoint) (hp : p ∈ annularOpen D) :
    SmoothDirections univ (fun z : AnnularState S × ℝ =>
      z.2 * mixedDerivative a b (stateU S z.1) p) :=
  (smoothDirections_qLinear (E := AnnularState S) (stateUJetCLM hT hS a b p hp)).congr
    (fun z _ => congrArg (fun t : ℝ => z.2 * t)
      (stateUJetCLM_apply (D := D) (T := T) (S := S) hT hS a b p hp z.1))

set_option backward.isDefEq.respectTransparency true in
/-- The five q-dependent polar height contributions have actual quadratic towers. -/
def qStateUPolarInputSmoothDirections
    {D : ReferenceData} {T : MaterialData} {S : PhysicalSpacesData}
    (hT : IsMaterialData D T) (hS : IsPhysicalSpaces D T S)
    (p : PolarPoint) (hp : p ∈ annularOpen D) (hr : p.1 ≠ 0) (i : Fin 5) :
    SmoothDirections univ (fun z : AnnularState S × ℝ =>
      z.2 * stateUPolarInput S i z.1 p) :=
  (smoothDirections_qLinear (E := AnnularState S) (stateUPolarInputCLM hT hS p hp i)).congr
    (fun z _ => congrArg (fun t : ℝ => z.2 * t)
      (stateUPolarInputCLM_apply hT hS p hp hr i z.1))

set_option backward.isDefEq.respectTransparency true in
/-- Every genuine tower of a positive-order q times state-height jet
obeys the raw weighted one-high estimate. The spatial loss is two,
independently of the parameter order or the low input order. -/
theorem stateU_qMixedJets_oneHigh_bound
    {D : ReferenceData} {T : MaterialData} {S : PhysicalSpacesData}
    (hT : IsMaterialData D T) (hS : IsPhysicalSpaces D T S) (s : ℕ) :
    ∃ C A : ℝ, 0 ≤ C ∧ 0 ≤ A ∧ ∀ a b : ℕ,
      0 < a + b → a + b ≤ s → ∀ p ∈ annularOpen D,
      ∀ U : Set (AnnularState S × ℝ),
      ∀ J : SmoothDirections U (fun z => z.2 * mixedDerivative a b (stateU S z.1) p),
      ∀ k base : ℕ, ∀ x0 : AnnularState S, ∀ z ∈ U, |z.2| ≤ 1 →
      ∀ v : Fin k → (AnnularState S × ℝ),
        |J.D k z v| ≤ C * T.E0 p.1 ^ A * T.H p.1 ^ (3 / 4 : ℝ) *
          (1 + stateGrading S (s + 2) x0) *
          oneHighVariationWeight (pairGrading (stateGrading S) realGrading)
            base (s + 2) (z - (x0, 0)) v := by
  exact family_qMixedJets_oneHigh_bound (E := AnnularState S)
    (stateGrading S) (stateU S) T.E0 T.H (3 / 4 : ℝ) (annularOpen D) s (s + 2)
    (stateUJetCLM (D := D) (T := T) (S := S) hT hS)
    (stateUJetCLM_apply (D := D) (T := T) (S := S) hT hS)
    (fun q hq => ⟨(hT.2.1 q.1 hq.1).2.2.1.le, (hT.2.1 q.1 hq.1).2.1.le⟩)
    (stateU_positiveMixedJets_le_E0_stateGrading (D := D) (T := T) (S := S) hT hS s)

set_option backward.isDefEq.respectTransparency true in
/-- The same weighted bound applies to all five actual polar height
contributions on the joint parameter space, including any previously
constructed tower for them. Its constants are uniform in the input index,
spatial point, parameter order, state and increments. -/
theorem stateU_qPolarInputs_oneHigh_bound
    {D : ReferenceData} {T : MaterialData} {S : PhysicalSpacesData}
    (hT : IsMaterialData D T) (hS : IsPhysicalSpaces D T S)
    (hD : 0 < D.a) (s : ℕ) :
    ∃ C A : ℝ, 0 ≤ C ∧ 0 ≤ A ∧ ∀ i : Fin 5, ∀ p ∈ annularOpen D,
      ∀ U : Set (AnnularState S × ℝ),
      ∀ J : SmoothDirections U (fun z => z.2 * stateUPolarInput S i z.1 p),
      ∀ k base : ℕ, ∀ x0 : AnnularState S, ∀ z ∈ U, |z.2| ≤ 1 →
      ∀ v : Fin k → (AnnularState S × ℝ),
        |J.D k z v| ≤ C * T.E0 p.1 ^ A * T.H p.1 ^ (3 / 4 : ℝ) *
          (1 + stateGrading S (s + 4) x0) *
          oneHighVariationWeight (pairGrading (stateGrading S) realGrading)
            base (s + 4) (z - (x0, 0)) v := by
  exact family_qFiveInputs_oneHigh_bound (E := AnnularState S)
    (stateGrading S) (stateUPolarInput S) T.E0 T.H (3 / 4 : ℝ)
    (annularOpen D) s (s + 4)
    (stateUPolarInputCLM (D := D) (T := T) (S := S) hT hS)
    (fun q hq i x => stateUPolarInputCLM_apply
      (D := D) (T := T) (S := S) hT hS q hq (hD.trans hq.1.1).ne' i x)
    (fun q hq => ⟨(hT.2.1 q.1 hq.1).2.2.1.le, (hT.2.1 q.1 hq.1).2.1.le⟩)
    (stateU_polarMixedJets_le_E0_stateGrading (D := D) (T := T) (S := S) hT hS hD s)

end ContinuousFlexibility.Statements
