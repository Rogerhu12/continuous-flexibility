import ContinuousFlexibility.Radial.InnerRadialWeightedInverse

/-!
# The unlocalized bound for the same actual inner inverse

The original interface theorem already supplies the weighted correction
with a contractive output loss. Choosing the identity loss gives the
coarse estimate below for the very same physical inverse.
-/

noncomputable section

namespace ContinuousFlexibility.Radial

open ContinuousFlexibility.Statements
open scoped ContDiff Matrix.Norms.L2Operator

namespace InnerRadialActualChain

variable {D : ReferenceData} {n : ℕ} {G : InnerRadialChainGeometry D n}
  {bordered : Bool} {j : ℝ} {central : Fin (n + 1)} {column : RadialModeL2 D}
  (C : InnerRadialActualChain D G bordered j central column)

local notation "H" => InnerRadialPhysicalSource D G bordered

theorem inverse_eq_innerGluedInverse (hw : ContDiff ℝ ∞ D.w)
    (hS : IsUnit C.fluxMatrix) :
    C.inverse hw hS = innerGluedInverse (C.dirichlet hw) (C.poisson hw)
      (Matrix.toEuclideanCLM (n := Fin n) (𝕜 := ℝ) C.fluxMatrix⁻¹) :=
  C.inverse_eq_glued hw hS

/-- The original localized theorem with identity output loss. All
operators and local errors remain those of the same actual chain. -/
theorem inverse_weighted_bound
    (hw : ContDiff ℝ ∞ D.w) (hS : IsUnit C.fluxMatrix)
    (hκ : ∀ i, 0 < C.kappa i) (w : Fin n → ℝ) (hwpos : ∀ i, 0 < w i)
    (hgaps : ∀ p (Q : InnerRadialGapChart D G j central p), C.piece p = .inr Q →
      ∃ c : ℝ,
        (0 < p.val → innerChainScalarRestriction n p w 1 0 = c) ∧
        (p.val < n → innerChainScalarRestriction n p w 1 1 = c))
    (hsep : ∀ i : Fin n,
      (C.piece i.castSucc).kappa 1 = 0 ∨ (C.piece i.succ).kappa 0 = 0)
    (hmodels : ∀ p (M : InnerRadialModelChart D G bordered j central column p),
      C.piece p = .inl M → 0 < p.val ∧ p.val < n ∧ ∀ i, 0 < M.kappa i)
    {η : ℝ} (hη : 0 ≤ η) (hηsmall : η < 1 / 4)
    (herror : ∀ p (M : InnerRadialModelChart D G bordered j central column p),
      C.piece p = .inl M → ∀ sign : Bool,
        ‖innerTwoCutWeightedError M.kappa (innerChainScalarRestriction n p w 1)
          M.errorMatrix sign‖ ≤ η)
    (W : H ≃L[ℝ] H) (hW : IsSelfAdjoint (W : H →L[ℝ] H))
    {CP d : ℝ} (hCP : 0 ≤ CP) (hj : 0 < j)
    (hP : ∀ sign : Bool,
      ‖innerWeightedPoisson W
        (innerMatrixEquiv (Matrix.diagonal w) (Matrix.posDef_diagonal_iff.mpr hwpos).isUnit)
        (C.poisson hw) (Matrix.toEuclideanCLM (n := Fin n) (𝕜 := ℝ)
          (innerInterfaceInverseSqrt C.referenceMatrix)) sign‖ ≤ CP / j)
    (sign : Bool)
    (hD : ‖(innerHilbertWeight W sign : H →L[ℝ] H) ∘L
      C.dirichlet hw ∘L (innerHilbertWeight W (!sign) : H →L[ℝ] H)‖ ≤ d) :
    ‖(innerHilbertWeight W sign : H →L[ℝ] H) ∘L
      C.inverse hw hS ∘L (innerHilbertWeight W (!sign) : H →L[ℝ] H)‖ ≤
        d + 2 * CP ^ 2 / j ^ 2 := by
  have hh := C.inverse_localized_weighted_bound hw hκ w hwpos hgaps hsep hmodels
    hη hηsmall herror hS W hW (ContinuousLinearMap.id ℝ H)
    (ContinuousLinearMap.opNorm_le_bound _ zero_le_one
      (fun x => by simpa only [ContinuousLinearMap.id_apply, one_mul] using (le_refl ‖x‖)))
    hCP hj hP sign (by simpa only [ContinuousLinearMap.id_comp] using hD)
  simpa only [ContinuousLinearMap.id_comp] using hh

end InnerRadialActualChain

end ContinuousFlexibility.Radial
