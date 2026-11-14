module

public import ContinuousFlexibility.Analysis.N07bReferenceMaterialSeeds

/-!
# Continuing a finite material expansion by actual directional derivatives

This is a finite-sum calculus identity on an arbitrary open physical set.
It retains the initial material orders and all coefficient derivatives.
Applied to the reference seeds, the resulting jets have order at most
the number of new derivatives plus two.
-/

@[expose] public section

noncomputable section

namespace ContinuousFlexibility.Analysis

open Set
open ContinuousFlexibility.Statements
open scoped ContDiff BigOperators

set_option backward.isDefEq.respectTransparency false

variable {D : ReferenceData} {T : MaterialData}

/-- The actual derivative word of a finite material sum, with one chain
for each initial summand. -/
theorem n07b_directionChain_finite_material_expansion {ι : Type*} [Fintype ι]
    (hT : IsMaterialData D T) {U : Set PolarPoint}
    (hU : IsOpen U) (hcore : U ⊆ annularOpen D)
    (X : ℕ → PolarPoint → PolarPoint) (hX : ∀ k, ContDiffOn ℝ ∞ (X k) U)
    (β : ℝ) (a b : ι → ℕ) {c : ι → PolarPoint → ℝ}
    (hc : ∀ i, ContDiffOn ℝ ∞ (c i) U)
    {u : PolarPoint → ℝ} (hu : ContDiff ℝ ∞ u)
    (j : ℕ) {x : PolarPoint} (hx : x ∈ U) :
    n07bDirectionIterate X
      (fun y => T.H y.1 ^ β * ∑ i : ι,
        c i y * mixedDerivative (a i) (b i) u (n07bMaterialChart T y)) j x =
      T.H x.1 ^ β * ∑ k : ι × n07bAngularChainIndex j,
        n07bDirectionChainCoefficient T β X (c k.1) j k.2 x *
          mixedDerivative (a k.1 + n07bAngularChainRadial j k.2)
            (b k.1 + n07bAngularChainAngular j k.2) u (n07bMaterialChart T x) := by
  classical
  let F : ι → PolarPoint → ℝ := fun i y =>
    T.H y.1 ^ β * c i y * mixedDerivative (a i) (b i) u (n07bMaterialChart T y)
  have hF : ∀ i, ContDiffOn ℝ ∞ (F i) U := by
    intro i y hy
    have hycore : y.1 ∈ Ioo D.a D.b := (hcore hy).1
    exact (((n07b_contDiffAt_physicalMaterialWeight hT hycore β).mul
      ((hc i y hy).contDiffAt (hU.mem_nhds hy))).mul
        ((contDiff_mixedDerivative hu (a i) (b i)).contDiffAt.comp y
          (n07b_contDiffAt_materialChart hT hycore))).contDiffWithinAt
  have hsplit : (fun y : PolarPoint => T.H y.1 ^ β * ∑ i : ι,
      c i y * mixedDerivative (a i) (b i) u (n07bMaterialChart T y)) =
      (fun y => ∑ i : ι, F i y) := by
    funext y
    simp only [F, Finset.mul_sum, mul_assoc]
  rw [hsplit]
  calc
    _ = ∑ i : ι, n07bDirectionIterate X (F i) j x :=
      n07bDirectionIterate_finset_sum X hU hX Finset.univ (fun i _ => hF i) j hx
    _ = ∑ i : ι, T.H x.1 ^ β * ∑ k : n07bAngularChainIndex j,
        n07bDirectionChainCoefficient T β X (c i) j k x *
          mixedDerivative (a i + n07bAngularChainRadial j k)
            (b i + n07bAngularChainAngular j k) u (n07bMaterialChart T x) := by
      apply Finset.sum_congr rfl
      intro i _
      exact n07b_directionChain_materialJet_expansion hT hU hcore X hX β (hc i) hu
        (a i) (b i) j hx
    _ = T.H x.1 ^ β * ∑ i : ι, ∑ k : n07bAngularChainIndex j,
        n07bDirectionChainCoefficient T β X (c i) j k x *
          mixedDerivative (a i + n07bAngularChainRadial j k)
            (b i + n07bAngularChainAngular j k) u (n07bMaterialChart T x) := by
      rw [Finset.mul_sum]
    _ = _ := by rw [Fintype.sum_prod_type]

/-- The same formula applies to any actual function which agrees with
the finite material sum on the whole open set. -/
theorem n07b_directionChain_of_finite_material_expansion {ι : Type*} [Fintype ι]
    (hT : IsMaterialData D T) {U : Set PolarPoint}
    (hU : IsOpen U) (hcore : U ⊆ annularOpen D)
    (X : ℕ → PolarPoint → PolarPoint) (hX : ∀ k, ContDiffOn ℝ ∞ (X k) U)
    (β : ℝ) (a b : ι → ℕ) {c : ι → PolarPoint → ℝ}
    (hc : ∀ i, ContDiffOn ℝ ∞ (c i) U)
    {u : PolarPoint → ℝ} (hu : ContDiff ℝ ∞ u) {f : PolarPoint → ℝ}
    (hformula : EqOn f (fun y => T.H y.1 ^ β * ∑ i : ι,
      c i y * mixedDerivative (a i) (b i) u (n07bMaterialChart T y)) U)
    (j : ℕ) {x : PolarPoint} (hx : x ∈ U) :
    n07bDirectionIterate X f j x =
      T.H x.1 ^ β * ∑ k : ι × n07bAngularChainIndex j,
        n07bDirectionChainCoefficient T β X (c k.1) j k.2 x *
          mixedDerivative (a k.1 + n07bAngularChainRadial j k.2)
            (b k.1 + n07bAngularChainAngular j k.2) u (n07bMaterialChart T x) :=
  (n07bDirectionIterate_congr X hU hformula j hx).trans
    (n07b_directionChain_finite_material_expansion hT hU hcore X hX β a b hc hu j hx)

/-- Every initial jet loses at most one further derivative per step. -/
theorem n07b_finite_material_expansion_order {ι : Type*} (a b : ι → ℕ)
    {s : ℕ} (horder : ∀ i, a i + b i ≤ s)
    (j : ℕ) (k : ι × n07bAngularChainIndex j) :
    (a k.1 + n07bAngularChainRadial j k.2) +
      (b k.1 + n07bAngularChainAngular j k.2) ≤ s + j := by
  have hi := horder k.1
  have hj := n07b_angularChain_order j k.2
  omega

/-- In the actual reference expression the starting order is two. -/
theorem n07b_reference_material_expansion_order (j : ℕ)
    (k : n07bReferenceMaterialSeed × n07bAngularChainIndex j) :
    (n07bReferenceSeedRadial k.1 + n07bAngularChainRadial j k.2) +
      (n07bReferenceSeedAngular k.1 + n07bAngularChainAngular j k.2) ≤ 2 + j :=
  n07b_finite_material_expansion_order n07bReferenceSeedRadial n07bReferenceSeedAngular
    n07b_referenceSeed_order j k

end ContinuousFlexibility.Analysis
