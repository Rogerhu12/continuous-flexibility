import ContinuousFlexibility.Analysis.N06NuPhysicalSmooth

/-!
# Symmetry of the actual current nu column

The finite smooth representation and its scalar symmetry calculus are
proved in N06NuPhysicalSmooth. This module identifies the actual coordinate
reflection packet and transports it to the genuine nu column.
-/

noncomputable section

namespace ContinuousFlexibility.Statements

open Set Filter
open ContinuousFlexibility.Analysis
open scoped ContDiff Topology

set_option backward.isDefEq.respectTransparency false

variable {D : ReferenceData} {T : MaterialData} {S : PhysicalSpacesData}
  {C : NonlinearGeometryData S} {base loss : ℕ} {ε : ℝ}

/-- The reflection algebra is performed on an arbitrary scalar field,
so no physical-space decoder participates in finite-array reduction. -/
private theorem n06_mixed_coordinate_reflection
    (u : PolarPoint → ℝ) (r θ w w' χ χ' q ν : ℝ)
    (hu : ∀ a b η, mixedDerivative a b u (r, -η) =
      (-1 : ℝ) ^ b * mixedDerivative a b u (r, η)) :
    ![r, w, w', χ, χ', mixedDerivative 1 0 u (r, -θ),
      mixedDerivative 2 0 u (r, -θ),
      (1 / r) * mixedDerivative 0 1 u (r, -θ),
      (1 / r) * mixedDerivative 1 1 u (r, -θ) -
        (1 / r ^ 2) * mixedDerivative 0 1 u (r, -θ),
      (1 / r) * mixedDerivative 0 2 u (r, -θ), q, ν] =
    n06NuCoordinateReflect
      ![r, w, w', χ, χ', mixedDerivative 1 0 u (r, θ),
        mixedDerivative 2 0 u (r, θ),
        (1 / r) * mixedDerivative 0 1 u (r, θ),
        (1 / r) * mixedDerivative 1 1 u (r, θ) -
          (1 / r ^ 2) * mixedDerivative 0 1 u (r, θ),
        (1 / r) * mixedDerivative 0 2 u (r, θ), q, ν] := by
  have h₀ : mixedDerivative 1 0 u (r, -θ) = mixedDerivative 1 0 u (r, θ) :=
    (hu 1 0 θ).trans (by simp only [pow_zero, one_mul])
  have h₁ : mixedDerivative 2 0 u (r, -θ) = mixedDerivative 2 0 u (r, θ) :=
    (hu 2 0 θ).trans (by simp only [pow_zero, one_mul])
  have h₂ : mixedDerivative 0 1 u (r, -θ) = -(mixedDerivative 0 1 u (r, θ)) :=
    (hu 0 1 θ).trans (by simp only [pow_one, neg_one_mul])
  have h₃ : mixedDerivative 1 1 u (r, -θ) = -(mixedDerivative 1 1 u (r, θ)) :=
    (hu 1 1 θ).trans (by simp only [pow_one, neg_one_mul])
  have h₄ : mixedDerivative 0 2 u (r, -θ) = mixedDerivative 0 2 u (r, θ) :=
    (hu 0 2 θ).trans (by simp only [neg_one_sq, one_mul])
  funext i
  fin_cases i
  · change r = r
    rfl
  · change w = w
    rfl
  · change w' = w'
    rfl
  · change χ = χ
    rfl
  · change χ' = χ'
    rfl
  · change mixedDerivative 1 0 u (r, -θ) = mixedDerivative 1 0 u (r, θ)
    exact h₀
  · change mixedDerivative 2 0 u (r, -θ) = mixedDerivative 2 0 u (r, θ)
    exact h₁
  · change (1 / r) * mixedDerivative 0 1 u (r, -θ) =
      -((1 / r) * mixedDerivative 0 1 u (r, θ))
    exact (congrArg (fun x : ℝ => (1 / r) * x) h₂).trans
      (mul_neg (1 / r) (mixedDerivative 0 1 u (r, θ)))
  · change (1 / r) * mixedDerivative 1 1 u (r, -θ) -
        (1 / r ^ 2) * mixedDerivative 0 1 u (r, -θ) =
      -((1 / r) * mixedDerivative 1 1 u (r, θ) -
        (1 / r ^ 2) * mixedDerivative 0 1 u (r, θ))
    exact (congrArg₂ (fun x y : ℝ => (1 / r) * x - (1 / r ^ 2) * y) h₃ h₂).trans
      (by ring)
  · change (1 / r) * mixedDerivative 0 2 u (r, -θ) =
      (1 / r) * mixedDerivative 0 2 u (r, θ)
    exact congrArg (fun x : ℝ => (1 / r) * x) h₄
  · change q = q
    rfl
  · change ν = ν
    rfl

theorem n06_actualNuJetCoordinates_reflection
    (hT : IsMaterialData D T) (hS : IsPhysicalSpaces D T S)
    (z : AnnularState S × ℝ) {p : PolarPoint} (hr : p.1 ≠ 0) :
    n06ActualNuJetCoordinates D S z (p.1, -p.2) =
      n06NuCoordinateReflect (n06ActualNuJetCoordinates D S z p) := by
  have hraw (θ : ℝ) : n06ActualNuJetCoordinates D S z (p.1, θ) =
      n06NuCoordinateAngularJet D S z p.1 θ 0 := by
    simpa only [iteratedDeriv_zero] using
      n06_actualNuJetCoordinates_angularJet_eq (D := D) (T := T) (S := S)
        hT hS z (r := p.1) hr 0 θ
  have hjet : n06NuCoordinateAngularJet D S z p.1 (-p.2) 0 =
      n06NuCoordinateReflect (n06NuCoordinateAngularJet D S z p.1 p.2 0) :=
    n06_mixed_coordinate_reflection (stateU S z.1) p.1 p.2
      (D.w p.1) (deriv D.w p.1) (D.chi p.1) (deriv D.chi p.1) z.2 z.1.2.1
      (fun a b θ => n06_stateU_mixedDerivative_reflection
        (D := D) (T := T) (S := S) hS z.1 a b (p.1, θ))
  exact (hraw (-p.2)).trans
    (hjet.trans (congrArg n06NuCoordinateReflect (hraw p.2).symm))

theorem n06_nuColumn_periodic
    (hT : IsMaterialData D T) (hS : IsPhysicalSpaces D T S)
    (hN01 : N01Properties D T S C base loss ε) (z : AnnularState S × ℝ) :
    Function.Periodic (nuColumnField D S C z) (0, Real.pi) := by
  intro p
  by_cases hborder : p.1 ∈ tsupport D.chi
  · have hp : p ∈ annularOpen D := ⟨(hN01.1.2.2.2.1.2.2.1 hborder).1, mem_univ _⟩
    have hp' : p + (0, Real.pi) ∈ annularOpen D :=
      ⟨by simpa only [Prod.fst_add, add_zero] using hp.1, mem_univ _⟩
    rw [n06_nuColumn_eq_finiteJetMap hT hS hN01 z hp',
      n06_nuColumn_eq_finiteJetMap hT hS hN01 z hp,
      n06_actualNuJetCoordinates_periodic hS z p]
  · have hborder' : (p + (0, Real.pi)).1 ∉ tsupport D.chi := by
      simpa only [Prod.fst_add, add_zero] using hborder
    rw [n06_nuColumn_zero_off_tsupport hT hS hN01 z hborder',
      n06_nuColumn_zero_off_tsupport hT hS hN01 z hborder]

theorem n06_nuColumn_even
    (hT : IsMaterialData D T) (hS : IsPhysicalSpaces D T S)
    (hN01 : N01Properties D T S C base loss ε) (z : AnnularState S × ℝ)
    (p : PolarPoint) : nuColumnField D S C z (p.1, -p.2) = nuColumnField D S C z p := by
  by_cases hborder : p.1 ∈ tsupport D.chi
  · have hp : p ∈ annularOpen D := ⟨(hN01.1.2.2.2.1.2.2.1 hborder).1, mem_univ _⟩
    have hp' : (p.1, -p.2) ∈ annularOpen D := ⟨hp.1, mem_univ _⟩
    have hr : p.1 ≠ 0 := (hN01.1.1.choose_spec.1.1.trans hp.1.1).ne'
    rw [n06_nuColumn_eq_finiteJetMap hT hS hN01 z hp',
      n06_nuColumn_eq_finiteJetMap hT hS hN01 z hp,
      n06_actualNuJetCoordinates_reflection hT hS z hr, n06NuFiniteJetMap_reflect]
  · rw [n06_nuColumn_zero_off_tsupport hT hS hN01 z (p := (p.1, -p.2)) hborder,
      n06_nuColumn_zero_off_tsupport hT hS hN01 z hborder]

end ContinuousFlexibility.Statements
