module

public import ContinuousFlexibility.Analysis.N07bMaterialDirection
public import ContinuousFlexibility.Analysis.N07bAngularChainExpansion

/-!
# Finite chains of arbitrary geometric derivatives

The initial coefficient and every direction are selected independently of
the scalar being differentiated. Paths retain all three Leibniz terms,
including the coefficient derivative. The same finite expansion applies
to any initial material jet, so a second-order reference expression can
be followed by the required number of current angular derivatives.
-/

@[expose] public section

noncomputable section

namespace ContinuousFlexibility.Analysis

open Set Filter
open ContinuousFlexibility.Statements
open scoped ContDiff Topology BigOperators

set_option backward.isDefEq.respectTransparency false

/-- A word of actual geometric directional derivatives. -/
def n07bDirectionIterate (X : ℕ → PolarPoint → PolarPoint)
    (f : PolarPoint → ℝ) : ℕ → PolarPoint → ℝ
  | 0 => f
  | j + 1 => n07bDirectionalDerivative (X j) (n07bDirectionIterate X f j)

/-- Its material coefficients, starting from an arbitrary geometric
coefficient. They have no scalar field or source as an argument. -/
def n07bDirectionChainCoefficient (T : MaterialData) (β : ℝ)
    (X : ℕ → PolarPoint → PolarPoint) (c : PolarPoint → ℝ) :
    (j : ℕ) → n07bAngularChainIndex j → PolarPoint → ℝ
  | 0, _ => c
  | j + 1, i =>
      if i.2 = 0 then
        n07bDirectionCoeffStay T β (X j) (n07bDirectionChainCoefficient T β X c j i.1)
      else if i.2 = 1 then
        n07bDirectionCoeffRadial T (X j) (n07bDirectionChainCoefficient T β X c j i.1)
      else
        n07bDirectionCoeffAngular (X j) (n07bDirectionChainCoefficient T β X c j i.1)

theorem n07bDirectionIterate_congr
    (X : ℕ → PolarPoint → PolarPoint) {U : Set PolarPoint} (hU : IsOpen U)
    {f g : PolarPoint → ℝ} (hfg : EqOn f g U) (j : ℕ) :
    EqOn (n07bDirectionIterate X f j) (n07bDirectionIterate X g j) U := by
  induction j with
  | zero => exact hfg
  | succ j ih =>
      intro x hx
      apply n07bDirectionalDerivative_congr
      filter_upwards [hU.mem_nhds hx] with y hy
      exact ih hy

theorem n07bDirectionIterate_contDiffAt
    {X : ℕ → PolarPoint → PolarPoint} {f : PolarPoint → ℝ} {x : PolarPoint}
    (hX : ∀ j, ContDiffAt ℝ ∞ (X j) x) (hf : ContDiffAt ℝ ∞ f x) (j : ℕ) :
    ContDiffAt ℝ ∞ (n07bDirectionIterate X f j) x := by
  induction j with
  | zero => exact hf
  | succ j ih => exact n07b_contDiffAt_directionalDerivative (hX j) ih

theorem n07bDirectionIterate_finset_sum {ι : Type*}
    (X : ℕ → PolarPoint → PolarPoint) {U : Set PolarPoint} (hU : IsOpen U)
    (hX : ∀ j, ContDiffOn ℝ ∞ (X j) U) (s : Finset ι)
    {f : ι → PolarPoint → ℝ} (hf : ∀ i ∈ s, ContDiffOn ℝ ∞ (f i) U)
    (j : ℕ) {x : PolarPoint} (hx : x ∈ U) :
    n07bDirectionIterate X (fun y => ∑ i ∈ s, f i y) j x =
      ∑ i ∈ s, n07bDirectionIterate X (f i) j x := by
  classical
  induction j generalizing x with
  | zero => rfl
  | succ j ih =>
      have heq : n07bDirectionIterate X (fun y => ∑ i ∈ s, f i y) j =ᶠ[𝓝 x]
          (fun y => ∑ i ∈ s, n07bDirectionIterate X (f i) j y) := by
        filter_upwards [hU.mem_nhds hx] with y hy
        exact ih hy
      have hterm (i : ι) (hi : i ∈ s) :
          DifferentiableAt ℝ (n07bDirectionIterate X (f i) j) x :=
        (n07bDirectionIterate_contDiffAt
          (fun k => (hX k x hx).contDiffAt (hU.mem_nhds hx))
          ((hf i hi x hx).contDiffAt (hU.mem_nhds hx)) j).differentiableAt (by simp)
      exact (n07bDirectionalDerivative_congr (X j) heq).trans
        (n07bDirectionalDerivative_finset_sum (X j) s hterm)

theorem n07b_directionChain_sum_succ
    (T : MaterialData) (β : ℝ) (X : ℕ → PolarPoint → PolarPoint)
    (c : PolarPoint → ℝ) (j ar aθ : ℕ) (u : PolarPoint → ℝ) (x : PolarPoint) :
    (∑ i : n07bAngularChainIndex (j + 1),
      n07bDirectionChainCoefficient T β X c (j + 1) i x *
        mixedDerivative (ar + n07bAngularChainRadial (j + 1) i)
          (aθ + n07bAngularChainAngular (j + 1) i) u (n07bMaterialChart T x)) =
      ∑ i : n07bAngularChainIndex j,
        (n07bDirectionCoeffStay T β (X j)
            (n07bDirectionChainCoefficient T β X c j i) x *
          mixedDerivative (ar + n07bAngularChainRadial j i)
            (aθ + n07bAngularChainAngular j i) u (n07bMaterialChart T x) +
        n07bDirectionCoeffRadial T (X j)
            (n07bDirectionChainCoefficient T β X c j i) x *
          mixedDerivative (ar + n07bAngularChainRadial j i + 1)
            (aθ + n07bAngularChainAngular j i) u (n07bMaterialChart T x) +
        n07bDirectionCoeffAngular (X j)
            (n07bDirectionChainCoefficient T β X c j i) x *
          mixedDerivative (ar + n07bAngularChainRadial j i)
            (aθ + n07bAngularChainAngular j i + 1) u (n07bMaterialChart T x)) := by
  classical
  change (∑ i : n07bAngularChainIndex j × Fin 3, _) = _
  rw [Fintype.sum_prod_type]
  apply Finset.sum_congr rfl
  intro i _
  simp [Fin.sum_univ_three, n07bDirectionChainCoefficient,
    n07bAngularChainRadial, n07bAngularChainAngular, Nat.add_assoc]

variable {D : ReferenceData} {T : MaterialData}

/-- All coefficients are genuinely smooth on the actual open set when
the initial coefficient and the actual directions are smooth there. -/
theorem n07bDirectionChainCoefficient_contDiffAt (hT : IsMaterialData D T)
    {X : ℕ → PolarPoint → PolarPoint} {c : PolarPoint → ℝ} {x : PolarPoint}
    (hx : x.1 ∈ Ioo D.a D.b) (β : ℝ)
    (hX : ∀ j, ContDiffAt ℝ ∞ (X j) x) (hc : ContDiffAt ℝ ∞ c x)
    (j : ℕ) (i : n07bAngularChainIndex j) :
    ContDiffAt ℝ ∞ (n07bDirectionChainCoefficient T β X c j i) x := by
  induction j with
  | zero => exact hc
  | succ j ih =>
      rcases i with ⟨i, k⟩
      have hnew := n07b_contDiffAt_directionChainCoefficients hT hx β (hX j) (ih i)
      fin_cases k
      · simpa [n07bDirectionChainCoefficient] using hnew.1
      · simpa [n07bDirectionChainCoefficient] using hnew.2.1
      · simpa [n07bDirectionChainCoefficient] using hnew.2.2

/-- An exact finite expansion for any initial material jet. The coefficient
family is the same for all initial orders and all material functions. -/
theorem n07b_directionChain_materialJet_expansion
    (hT : IsMaterialData D T) {U : Set PolarPoint}
    (hU : IsOpen U) (hcore : U ⊆ annularOpen D)
    (X : ℕ → PolarPoint → PolarPoint) (hX : ∀ j, ContDiffOn ℝ ∞ (X j) U)
    (β : ℝ) {c u : PolarPoint → ℝ}
    (hc : ContDiffOn ℝ ∞ c U) (hu : ContDiff ℝ ∞ u)
    (ar aθ j : ℕ) {x : PolarPoint} (hx : x ∈ U) :
    n07bDirectionIterate X
        (fun y => T.H y.1 ^ β * c y *
          mixedDerivative ar aθ u (n07bMaterialChart T y)) j x =
      T.H x.1 ^ β * ∑ i : n07bAngularChainIndex j,
        n07bDirectionChainCoefficient T β X c j i x *
          mixedDerivative (ar + n07bAngularChainRadial j i)
            (aθ + n07bAngularChainAngular j i) u (n07bMaterialChart T x) := by
  induction j generalizing x with
  | zero =>
      simp [n07bDirectionIterate, n07bDirectionChainCoefficient, n07bAngularChainIndex,
        n07bAngularChainRadial, n07bAngularChainAngular, mul_assoc]
  | succ j ih =>
      have hxcore : x.1 ∈ Ioo D.a D.b := (hcore hx).1
      have heq : n07bDirectionIterate X
          (fun y => T.H y.1 ^ β * c y * mixedDerivative ar aθ u (n07bMaterialChart T y)) j
          =ᶠ[𝓝 x] (fun y => T.H y.1 ^ β * ∑ i : n07bAngularChainIndex j,
            n07bDirectionChainCoefficient T β X c j i y *
              mixedDerivative (ar + n07bAngularChainRadial j i)
                (aθ + n07bAngularChainAngular j i) u (n07bMaterialChart T y)) := by
        filter_upwards [hU.mem_nhds hx] with y hy
        exact ih hy
      have hcoeff (i : n07bAngularChainIndex j) (_ : i ∈ Finset.univ) :
          ContDiffAt ℝ ∞ (n07bDirectionChainCoefficient T β X c j i) x :=
        n07bDirectionChainCoefficient_contDiffAt hT hxcore β
          (fun k => (hX k x hx).contDiffAt (hU.mem_nhds hx))
          ((hc x hx).contDiffAt (hU.mem_nhds hx)) j i
      calc
        _ = n07bDirectionalDerivative (X j)
            (fun y => T.H y.1 ^ β * ∑ i : n07bAngularChainIndex j,
              n07bDirectionChainCoefficient T β X c j i y *
                mixedDerivative (ar + n07bAngularChainRadial j i)
                  (aθ + n07bAngularChainAngular j i) u (n07bMaterialChart T y)) x :=
          n07bDirectionalDerivative_congr (X j) heq
        _ = T.H x.1 ^ β * ∑ i : n07bAngularChainIndex j,
            (n07bDirectionCoeffStay T β (X j)
                (n07bDirectionChainCoefficient T β X c j i) x *
              mixedDerivative (ar + n07bAngularChainRadial j i)
                (aθ + n07bAngularChainAngular j i) u (n07bMaterialChart T x) +
            n07bDirectionCoeffRadial T (X j)
                (n07bDirectionChainCoefficient T β X c j i) x *
              mixedDerivative (ar + n07bAngularChainRadial j i + 1)
                (aθ + n07bAngularChainAngular j i) u (n07bMaterialChart T x) +
            n07bDirectionCoeffAngular (X j)
                (n07bDirectionChainCoefficient T β X c j i) x *
              mixedDerivative (ar + n07bAngularChainRadial j i)
                (aθ + n07bAngularChainAngular j i + 1) u (n07bMaterialChart T x)) :=
          n07b_directional_weighted_material_sum hT (X j) β Finset.univ
            (fun i => ar + n07bAngularChainRadial j i)
            (fun i => aθ + n07bAngularChainAngular j i)
            (n07bDirectionChainCoefficient T β X c j) hu hxcore hcoeff
        _ = _ := by rw [n07b_directionChain_sum_succ]

/-- In particular the initial material function is the actual pullback
of an arbitrary physical scalar. The equality is local on the open set. -/
theorem n07b_directionChain_physical_expansion
    (hT : IsMaterialData D T) {U : Set PolarPoint}
    (hU : IsOpen U) (hcore : U ⊆ annularOpen D)
    (X : ℕ → PolarPoint → PolarPoint) (hX : ∀ j, ContDiffOn ℝ ∞ (X j) U)
    (β : ℝ) {c f : PolarPoint → ℝ}
    (hc : ContDiffOn ℝ ∞ c U) (hf : ContDiffOn ℝ ∞ f (annularOpen D))
    (j : ℕ) {x : PolarPoint} (hx : x ∈ U) :
    n07bDirectionIterate X (fun y => c y * f y) j x =
      T.H x.1 ^ β * ∑ i : n07bAngularChainIndex j,
        n07bDirectionChainCoefficient T β X c j i x *
          mixedDerivative (n07bAngularChainRadial j i) (n07bAngularChainAngular j i)
            (materialPullback T β f) (n07bMaterialChart T x) := by
  have heq : EqOn (fun y => c y * f y)
      (fun y => T.H y.1 ^ β * c y *
        mixedDerivative 0 0 (materialPullback T β f) (n07bMaterialChart T y)) U := by
    intro y hy
    simp only [mixedDerivative, iteratedDeriv_zero, Prod.eta]
    calc
      c y * f y = c y * (T.H y.1 ^ β *
          materialPullback T β f (n07bMaterialChart T y)) :=
        congrArg (c y * ·) (n07b_materialPullback_restore hT β f (hcore hy).1).symm
      _ = _ := by ring
  exact (n07bDirectionIterate_congr X hU heq j hx).trans (by
    simpa only [zero_add] using n07b_directionChain_materialJet_expansion hT hU hcore
      X hX β hc (contDiff_materialPullback hT hf) 0 0 j hx)

end ContinuousFlexibility.Analysis
