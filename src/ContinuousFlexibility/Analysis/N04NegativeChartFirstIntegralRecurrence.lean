module

public import ContinuousFlexibility.Analysis.N04bCharacteristicFirstIntegralsTransport
public import ContinuousFlexibility.Analysis.JointMixedTransportCalculus
public import ContinuousFlexibility.Analysis.ScalarTransportSystemBounds
public import ContinuousFlexibility.Analysis.N01cSpatialParameterComposition

/-!
# The actual transport equation for a centered first integral

Subtracting the reference affine-angle integral leaves a forcing term
equal to the speed difference. Differentiating the genuine joint tower
gives the exact radial recurrence, with its original state, radial and
angular Leibniz indices.
-/

@[expose] public section

noncomputable section

namespace ContinuousFlexibility.Analysis

open Set ContinuousFlexibility.Statements
open scoped ContDiff BigOperators

/-- Centering by an affine-angle reference retains precisely the
difference of the two characteristic speeds. -/
theorem n04NegativeChart_firstIntegral_defect_transport
    {f : PolarPoint → ℝ} {τ : ℝ → ℝ} {p : PolarPoint} {c τ' : ℝ}
    (hf : DifferentiableAt ℝ f p) (hτ : HasDerivAt τ τ' p.1)
    (htransport : radialPartial f p = -c * angularPartial f p) :
    radialPartial (fun q => f q - (q.2 + τ q.1)) p =
      -(c * angularPartial (fun q => f q - (q.2 + τ q.1)) p) - (c + τ') := by
  have ht : HasFDerivAt (fun q : PolarPoint => τ q.1)
      (τ' • ContinuousLinearMap.fst ℝ ℝ ℝ) p := by
    simpa only [Function.comp_def] using hτ.comp_hasFDerivAt p hasFDerivAt_fst
  have hr : HasFDerivAt (fun q : PolarPoint => q.2 + τ q.1)
      (ContinuousLinearMap.snd ℝ ℝ ℝ + τ' • ContinuousLinearMap.fst ℝ ℝ ℝ) p :=
    hasFDerivAt_snd.add ht
  have hrad : radialPartial (fun q : PolarPoint => q.2 + τ q.1) p = τ' := by
    simp only [radialPartial, hr.fderiv, ContinuousLinearMap.add_apply,
      ContinuousLinearMap.smul_apply, ContinuousLinearMap.coe_fst',
      ContinuousLinearMap.coe_snd', smul_eq_mul, mul_one, zero_add]
  have hang : angularPartial (fun q : PolarPoint => q.2 + τ q.1) p = 1 := by
    simp only [angularPartial, hr.fderiv, ContinuousLinearMap.add_apply,
      ContinuousLinearMap.smul_apply, ContinuousLinearMap.coe_fst',
      ContinuousLinearMap.coe_snd', smul_eq_mul, mul_zero, add_zero]
  rw [radialPartial_sub hf hr.differentiableAt,
    angularPartial_sub hf hr.differentiableAt, htransport, hrad, hang]
  ring

/-- The literal inverse-flow first integral satisfies the centered
equation; its transport identity is proved by the existing inverse-flow
theorem, rather than assumed for a formal jet array. -/
theorem n04NegativeChart_minusFirstIntegral_defect_transport
    {Φ d v : PolarPoint → ℝ} {hL τ : ℝ → ℝ} {a b P τ' : ℝ}
    (hΦ : N04bCircleFlowRegularity Φ a b P) (hP : P ≠ 0)
    (hhL : ContDiff ℝ ∞ hL)
    (hflow : ∀ r ∈ Ioo a b, ∀ θ : ℝ,
      HasDerivAt (fun s => Φ (s, θ))
        (d (r, Φ (r, θ)) - v (r, Φ (r, θ))) r)
    {p : PolarPoint} (hp : p ∈ Ioo a b ×ˢ univ) (hτ : HasDerivAt τ τ' p.1) :
    radialPartial (fun q => n04bMinusFirstIntegral Φ hL q - (q.2 + τ q.1)) p =
      -((d p - v p) * angularPartial
        (fun q => n04bMinusFirstIntegral Φ hL q - (q.2 + τ q.1)) p) -
          ((d p - v p) + τ') :=
  n04NegativeChart_firstIntegral_defect_transport
    (((n04b_minusFirstIntegral_smooth hΦ hP hhL).contDiffAt
      ((isOpen_Ioo.prod isOpen_univ).mem_nhds hp)).differentiableAt (by simp)) hτ
    (n04b_minusFirstIntegral_transport hΦ hP hhL hflow hp)

variable {E : Type*} [TopologicalSpace E] [AddCommGroup E] [Module ℝ E]
  [IsTopologicalAddGroup E] [ContinuousSMul ℝ E]
  {U : Set E} {V : Set PolarPoint} {f c e : E × PolarPoint → ℝ}

/-- Every factor of the unknown first integral on the right has strictly
smaller radial order. The forcing is the actual speed difference. -/
theorem n04NegativeChart_jointMixedDiagonal_inhomogeneous_transport
    (JF : SmoothDirections (U ×ˢ V) f) (JC : SmoothDirections (U ×ˢ V) c)
    (JE : SmoothDirections (U ×ˢ V) e)
    (hU : IsOpen U) (hV : IsOpen V) (hc : Convex ℝ (U ×ˢ V))
    (htransport : ∀ x ∈ U, ∀ p ∈ V,
      radialPartial (fun q => f (x, q)) p =
        -(c (x, p) * angularPartial (fun q => f (x, q)) p) - e (x, p))
    (n a b : ℕ) (x w : E) (hx : x ∈ U) {p : PolarPoint} (hp : p ∈ V) :
    jointMixedDiagonal JF n (a + 1) b x w p =
      -diagonalJetProduct
        (fun k i j (_ : Unit) => jointMixedDiagonal JC k i j x w p)
        (fun k i j (_ : Unit) => jointMixedDiagonal JF k i (j + 1) x w p) n a b () -
          jointMixedDiagonal JE n a b x w p := by
  let Jθ := JF.spatialAngularTower hV hc
  let Jr := JF.spatialRadialTower hV hc
  let L := JC.mul Jθ
  let M := (smoothDirections_constant (hU.prod hV) (-1 : ℝ)).mul L
  have heq : ∀ y ∈ U, ∀ q ∈ V,
      radialPartial (fun z => f (y, z)) q =
        (-1 : ℝ) * (c (y, q) * angularPartial (fun z => f (y, z)) q) - e (y, q) := by
    intro y hy q hq
    rw [htransport y hy q hq]
    ring
  have hsub := jointMixedDiagonal_sub M JE Jr hU hV hc heq n a b x w hx hp
  have hneg := jointMixedDiagonal_const_mul L M hU hV hc (-1)
    (fun _ _ _ _ => rfl) n a b x w hx hp
  have hprod : jointMixedDiagonal L n a b x w p =
      diagonalJetProduct
        (fun k i j (_ : Unit) => jointMixedDiagonal JC k i j x w p)
        (fun k i j (_ : Unit) => jointMixedDiagonal JF k i (j + 1) x w p) n a b () := by
    rw [jointMixedDiagonal_mul JC Jθ L hU hV hc
      (fun _ _ _ _ => rfl) n a b x w hx hp]
    unfold diagonalJetProduct
    apply Finset.sum_congr rfl
    intro j hj
    apply Finset.sum_congr rfl
    intro i hi
    apply Finset.sum_congr rfl
    intro k hk
    rw [jointMixedDiagonal_spatialAngular JF hV hc (n - k) (a - i) (b - j) x w hx hp]
  have hs := jointMixedDiagonal_spatialRadial JF hV hc n a b x w hx hp
  rw [← hs, hsub, hneg, hprod, neg_one_mul]

end ContinuousFlexibility.Analysis

/-- info: 'ContinuousFlexibility.Analysis.n04NegativeChart_jointMixedDiagonal_inhomogeneous_transport'
depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms ContinuousFlexibility.Analysis.n04NegativeChart_jointMixedDiagonal_inhomogeneous_transport
