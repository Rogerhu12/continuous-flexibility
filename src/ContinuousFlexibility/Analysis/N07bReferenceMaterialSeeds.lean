import ContinuousFlexibility.Analysis.N07bReferencePDEPullback

/-!
# The finite material seeds of the actual reference expression

The reference radial expression has one word of length one and two words
of length two. Their three-branch expansions give twenty-one terms. Every
coefficient is determined by the geometry before the scalar is supplied,
and the material jet in each term has order at most two. Further current
angular derivatives can therefore use the same general chain expansion.
-/

noncomputable section

namespace ContinuousFlexibility.Analysis

open Set
open ContinuousFlexibility.Statements ContinuousFlexibility.Radial
open scoped ContDiff BigOperators

set_option backward.isDefEq.respectTransparency false

/-- The three paths of the first-order word and the two sets of nine
paths of the second-order words. -/
abbrev n07bReferenceMaterialSeed :=
  n07bAngularChainIndex 1 ⊕ (n07bAngularChainIndex 2 ⊕ n07bAngularChainIndex 2)

def n07bReferenceSeedRadial : n07bReferenceMaterialSeed → ℕ
  | .inl i => n07bAngularChainRadial 1 i
  | .inr (.inl i) => n07bAngularChainRadial 2 i
  | .inr (.inr i) => n07bAngularChainRadial 2 i

def n07bReferenceSeedAngular : n07bReferenceMaterialSeed → ℕ
  | .inl i => n07bAngularChainAngular 1 i
  | .inr (.inl i) => n07bAngularChainAngular 2 i
  | .inr (.inr i) => n07bAngularChainAngular 2 i

/-- The actual direction-word coefficients multiplied by their respective
reference operator coefficient. There is no unknown or source argument. -/
def n07bReferenceSeedCoefficient (T : MaterialData) (β : ℝ)
    (Xr Xθ : PolarPoint → PolarPoint) (c : PolarPoint → ℝ)
    (A : Fin 3 → PolarPoint → ℝ) : n07bReferenceMaterialSeed → PolarPoint → ℝ
  | .inl i => fun x => A 0 x *
      n07bDirectionChainCoefficient T β (fun _ => Xr) c 1 i x
  | .inr (.inl i) => fun x => A 1 x *
      n07bDirectionChainCoefficient T β (fun _ => Xr) c 2 i x
  | .inr (.inr i) => fun x => A 2 x *
      n07bDirectionChainCoefficient T β (fun _ => Xθ) c 2 i x

theorem n07b_referenceMaterialSeed_card :
    Fintype.card n07bReferenceMaterialSeed = 21 := by
  simp only [n07bReferenceMaterialSeed, Fintype.card_sum, n07b_angularChain_card]
  norm_num

theorem n07b_referenceSeed_order (i : n07bReferenceMaterialSeed) :
    n07bReferenceSeedRadial i + n07bReferenceSeedAngular i ≤ 2 := by
  rcases i with i | (i | i)
  · exact (n07b_angularChain_order 1 i).trans (by decide)
  · exact n07b_angularChain_order 2 i
  · exact n07b_angularChain_order 2 i

variable {D : ReferenceData} {T : MaterialData}

theorem n07bReferenceSeedCoefficient_contDiffAt
    (hT : IsMaterialData D T) {x : PolarPoint}
    (hx : x.1 ∈ Ioo D.a D.b) (β : ℝ)
    {Xr Xθ : PolarPoint → PolarPoint} {c : PolarPoint → ℝ}
    {A : Fin 3 → PolarPoint → ℝ}
    (hXr : ContDiffAt ℝ ∞ Xr x) (hXθ : ContDiffAt ℝ ∞ Xθ x)
    (hc : ContDiffAt ℝ ∞ c x) (hA : ∀ k, ContDiffAt ℝ ∞ (A k) x)
    (i : n07bReferenceMaterialSeed) :
    ContDiffAt ℝ ∞ (n07bReferenceSeedCoefficient T β Xr Xθ c A i) x := by
  rcases i with i | (i | i)
  · exact (hA 0).mul
      (n07bDirectionChainCoefficient_contDiffAt hT hx β (fun _ => hXr) hc 1 i)
  · exact (hA 1).mul
      (n07bDirectionChainCoefficient_contDiffAt hT hx β (fun _ => hXr) hc 2 i)
  · exact (hA 2).mul
      (n07bDirectionChainCoefficient_contDiffAt hT hx β (fun _ => hXθ) hc 2 i)

/-- The exact finite expansion of the three actual direction words. -/
theorem n07b_referenceWords_material_expansion
    (hT : IsMaterialData D T) {U : Set PolarPoint}
    (hU : IsOpen U) (hcore : U ⊆ annularOpen D)
    {Xr Xθ : PolarPoint → PolarPoint}
    (hXr : ContDiffOn ℝ ∞ Xr U) (hXθ : ContDiffOn ℝ ∞ Xθ U)
    (β : ℝ) {c f : PolarPoint → ℝ}
    (hc : ContDiffOn ℝ ∞ c U) (hf : ContDiffOn ℝ ∞ f (annularOpen D))
    (A : Fin 3 → PolarPoint → ℝ) {x : PolarPoint} (hx : x ∈ U) :
    A 0 x * n07bDirectionIterate (fun _ => Xr) (fun y => c y * f y) 1 x +
      A 1 x * n07bDirectionIterate (fun _ => Xr) (fun y => c y * f y) 2 x +
      A 2 x * n07bDirectionIterate (fun _ => Xθ) (fun y => c y * f y) 2 x =
        T.H x.1 ^ β * ∑ i : n07bReferenceMaterialSeed,
          n07bReferenceSeedCoefficient T β Xr Xθ c A i x *
            mixedDerivative (n07bReferenceSeedRadial i) (n07bReferenceSeedAngular i)
              (materialPullback T β f) (n07bMaterialChart T x) := by
  classical
  rw [n07b_directionChain_physical_expansion hT hU hcore
      (fun _ => Xr) (fun _ => hXr) β hc hf 1 hx,
    n07b_directionChain_physical_expansion hT hU hcore
      (fun _ => Xr) (fun _ => hXr) β hc hf 2 hx,
    n07b_directionChain_physical_expansion hT hU hcore
      (fun _ => Xθ) (fun _ => hXθ) β hc hf 2 hx]
  simp only [n07bReferenceMaterialSeed, Fintype.sum_sum_type,
    n07bReferenceSeedCoefficient, n07bReferenceSeedRadial, n07bReferenceSeedAngular]
  simp_rw [mul_assoc, ← Finset.mul_sum]
  ring

/-- The three actual multipliers in the reference radial expression after
pullback. `B` is the actual reference source density in applications. -/
def n07bReferenceSeedMultiplier (w : ℝ → ℝ)
    (Θ : PolarPoint → PolarPoint) (B : PolarPoint → ℝ)
    (k : Fin 3) (x : PolarPoint) : ℝ :=
  if k = 0 then B x * deriv w (Θ x).1
  else if k = 1 then B x * w (Θ x).1
  else B x * (deriv w (Θ x).1 / (Θ x).1)

/-- The finite material formula is obtained from the actual reference PDE
and actual inverse transitions; it is not an assumed transport identity. -/
theorem n07b_referencePDE_material_seed_expansion
    (hT : IsMaterialData D T) {U V : Set PolarPoint}
    (hU : IsOpen U) (hV : IsOpen V) (hcore : U ⊆ annularOpen D)
    {τ Θ : PolarPoint → PolarPoint}
    (hτ : ContDiffOn ℝ ∞ τ V) (hΘ : ContDiffOn ℝ ∞ Θ U)
    (hτmap : MapsTo τ V U) (hΘmap : MapsTo Θ U V)
    (hinv : ∀ y ∈ V, Θ (τ y) = y) (hleft : ∀ x ∈ U, τ (Θ x) = x)
    (β : ℝ) {c f : PolarPoint → ℝ}
    (hc : ContDiffOn ℝ ∞ c U) (hf : ContDiffOn ℝ ∞ f (annularOpen D))
    (B : PolarPoint → ℝ) {w : ℝ → ℝ} {x : PolarPoint} (hx : x ∈ U)
    (hw : DifferentiableAt ℝ w (Θ x).1) :
    B x * radialPDE w (fun r θ => c (τ (r, θ)) * f (τ (r, θ))) (Θ x).1 (Θ x).2 =
      T.H x.1 ^ β * ∑ i : n07bReferenceMaterialSeed,
        n07bReferenceSeedCoefficient T β
          (n07bReferenceDirection τ Θ (1, 0)) (n07bReferenceDirection τ Θ (0, 1))
          c (n07bReferenceSeedMultiplier w Θ B) i x *
          mixedDerivative (n07bReferenceSeedRadial i) (n07bReferenceSeedAngular i)
            (materialPullback T β f) (n07bMaterialChart T x) := by
  have hXr := n07bReferenceDirection_contDiffOn hU hV hτ hΘ hΘmap (1, 0)
  have hXθ := n07bReferenceDirection_contDiffOn hU hV hτ hΘ hΘmap (0, 1)
  have hpde := n07b_referencePDE_pullback hU hV hτ hΘ hτmap hΘmap hinv hleft
    (hc.mul (hf.mono hcore)) hx hw
  change radialPDE w (fun r θ => c (τ (r, θ)) * f (τ (r, θ))) (Θ x).1 (Θ x).2 = _ at hpde
  rw [hpde]
  have hseed := n07b_referenceWords_material_expansion hT hU hcore hXr hXθ β hc hf
    (n07bReferenceSeedMultiplier w Θ B) hx
  have hA₀ : n07bReferenceSeedMultiplier w Θ B 0 x = B x * deriv w (Θ x).1 := by
    simp [n07bReferenceSeedMultiplier]
  have hA₁ : n07bReferenceSeedMultiplier w Θ B 1 x = B x * w (Θ x).1 := by
    norm_num [n07bReferenceSeedMultiplier]
  have hA₂ : n07bReferenceSeedMultiplier w Θ B 2 x =
      B x * (deriv w (Θ x).1 / (Θ x).1) := by
    norm_num [n07bReferenceSeedMultiplier]
  rw [hA₀, hA₁, hA₂] at hseed
  calc
    _ = (B x * deriv w (Θ x).1) *
          n07bDirectionIterate (fun _ => n07bReferenceDirection τ Θ (1, 0))
            (fun y => c y * f y) 1 x +
        (B x * w (Θ x).1) *
          n07bDirectionIterate (fun _ => n07bReferenceDirection τ Θ (1, 0))
            (fun y => c y * f y) 2 x +
        (B x * (deriv w (Θ x).1 / (Θ x).1)) *
          n07bDirectionIterate (fun _ => n07bReferenceDirection τ Θ (0, 1))
            (fun y => c y * f y) 2 x := by ring
    _ = _ := hseed

end ContinuousFlexibility.Analysis
