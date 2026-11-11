import ContinuousFlexibility.Radial.InnerRadialDirichletPoisson
import Mathlib.Analysis.InnerProductSpace.Adjoint

/-!
# Actual weak Green identity and forced Poisson flux

The physical signed-potential relation makes the energy symmetric.
Local zero-endpoint equations allow the canonical affine trace lifts to
be replaced by the same actual Poisson fields. These facts prove the
finite-domain Green identity, including the single central scalar.

Consequently the actual Dirichlet forced flux is minus the pairing with
the very same actual Poisson realization, for arbitrary L² sources.
No global Green or adjoint-flux identity is assumed.
-/

noncomputable section

namespace ContinuousFlexibility.Radial

open Set MeasureTheory Filter ContinuousFlexibility.Statements
open scoped ContDiff InnerProductSpace BigOperators

section PhysicalGreen

variable (D : ReferenceData) (hw : Continuous D.w) {n : ℕ}
  (G : InnerRadialChainGeometry D n) {H : Type*}
  [AddCommGroup H] [Module ℝ H]
  (forcing : H →ₗ[ℝ] (Fin (n + 1) → RadialModeL2 D))
  (rowSource : H →ₗ[ℝ] ℝ) (bordered : Bool) (j : ℝ)
  (central : Fin (n + 1)) (column : RadialModeL2 D)

local notation "B" => EuclideanSpace ℝ (Fin n)
local notation "W" =>
  ↥(innerRadialBrokenSpace D hw G forcing rowSource bordered j central column)
local notation "Src" =>
  innerRadialDomainSource D hw G forcing rowSource bordered j central column
local notation "Tr" =>
  innerRadialDomainTrace D hw G forcing rowSource bordered j central column
local notation "Flux" =>
  innerRadialDomainFlux D hw G forcing rowSource bordered j central column

/-- The actual physical source-field pairing, with one scalar term. -/
def innerRadialSourcePairing (F : H) (x : W) : ℝ :=
  (∑ p, ⟪forcing F p, (x.val.1.1 p).1⟫_ℝ) + rowSource F * x.val.1.2.2

theorem innerRadialSourcePairing_zero (x : W) :
    innerRadialSourcePairing D hw G forcing rowSource bordered j central column 0 x = 0 := by
  simp only [innerRadialSourcePairing, map_zero, Pi.zero_apply, inner_zero_left,
    Finset.sum_const_zero, zero_mul, add_zero]

/-- A zero-endpoint weak solution has the same conormal functional on
every actual matched field with the prescribed internal trace. -/
theorem innerRadialBrokenFlux_test (x y : W) :
    Flux x (Tr y) =
      ∑ p, innerRadialChainResidual D central column x.val.1.1 x.val.1.2.1
        (forcing x.val.2) x.val.1.2.2 p (y.val.1.1 p) := by
  have hx := (mem_innerRadialBrokenSpace D hw G forcing rowSource bordered j
    central column x.val).mp x.property
  have hy := (mem_innerRadialBrokenSpace D hw G forcing rowSource bordered j
    central column y.val).mp y.property
  have hsub := innerRadialChainDomain_sub_lift D hw G hy.1
  rw [innerRadialDomainFlux_apply, innerRadialDomainTrace_apply,
    innerRadialBrokenFlux_eq, innerRadialChainFlux, innerMatchedWeakFlux_apply]
  apply Finset.sum_congr rfl
  intro p _
  have he := hx.2.2.2 p
    (y.val.1.1 p - innerRadialAffineLift D hw (G.left_pos p) (G.in_core p) (G.weight_pos p)
      (innerChainBoundaryRestriction n p (innerRadialChainTrace D hw G y.val.1.1)))
    (hsub p)
  rw [map_sub] at he
  simpa only [innerRadialChainLift, LinearMap.comp_apply] using (sub_eq_zero.mp he).symm

/-- Expanding the true local weak residual retains exactly one column
pairing in the finite sum. -/
theorem innerRadialChainResidual_sum
    (q r : Fin (n + 1) → InnerRadialH1Pair D)
    (v f : Fin (n + 1) → RadialModeL2 D) (borderScalar : ℝ) :
    (∑ p, innerRadialChainResidual D central column q v f borderScalar p (r p)) =
      (∑ p, (⟪(q p).2, (r p).2⟫_ℝ + ⟪v p, (r p).1⟫_ℝ)) +
        borderScalar * ⟪column, (r central).1⟫_ℝ -
        ∑ p, ⟪f p, (r p).1⟫_ℝ := by
  have hc : (∑ p : Fin (n + 1),
      borderScalar * ⟪(if p = central then column else 0), (r p).1⟫_ℝ) =
      borderScalar * ⟪column, (r central).1⟫_ℝ := by
    rw [Finset.sum_eq_single central]
    · simp only [if_pos rfl, ite_true]
    · intro p _ hp
      simp only [if_neg hp, inner_zero_left, mul_zero]
    · intro hc
      exact (hc (Finset.mem_univ central)).elim
  simp only [innerRadialChainResidual, innerRadialWeakResidual,
    Finset.sum_sub_distrib, Finset.sum_add_distrib]
  rw [hc]

/-- The finite physical energy is symmetric for the actual signed
potential products. No abstract symmetric-form assumption is used. -/
theorem innerRadialEnergy_sum_symm
    (q r : Fin (n + 1) → InnerRadialH1Pair D)
    (v w : Fin (n + 1) → RadialModeL2 D)
    (hv : ∀ p, InnerRadialPotentialClass D j (G.left p) (G.right p) (q p).1 (v p))
    (hw' : ∀ p, InnerRadialPotentialClass D j (G.left p) (G.right p) (r p).1 (w p)) :
    (∑ p, (⟪(q p).2, (r p).2⟫_ℝ + ⟪v p, (r p).1⟫_ℝ)) =
      ∑ p, (⟪(r p).2, (q p).2⟫_ℝ + ⟪w p, (q p).1⟫_ℝ) := by
  apply Finset.sum_congr rfl
  intro p _
  exact congrArg₂ (fun a b : ℝ => a + b) (real_inner_comm _ _)
    ((hv p).inner_symm (hw' p))

/-- Green reciprocity on the true broken weak graph. Boundary flux is
the only obstruction to symmetry of the actual source-field pairing. -/
theorem innerRadialBroken_green (x y : W) :
    Flux x (Tr y) - Flux y (Tr x) =
      innerRadialSourcePairing D hw G forcing rowSource bordered j central column (Src y) x -
        innerRadialSourcePairing D hw G forcing rowSource bordered j central column (Src x) y := by
  have hx := (mem_innerRadialBrokenSpace D hw G forcing rowSource bordered j
    central column x.val).mp x.property
  have hy := (mem_innerRadialBrokenSpace D hw G forcing rowSource bordered j
    central column y.val).mp y.property
  have hsym := innerRadialEnergy_sum_symm D G j x.val.1.1 y.val.1.1
    x.val.1.2.1 y.val.1.2.1 hx.2.1 hy.2.1
  rw [innerRadialBrokenFlux_test D hw G forcing rowSource bordered j central column x y,
    innerRadialBrokenFlux_test D hw G forcing rowSource bordered j central column y x,
    innerRadialChainResidual_sum, innerRadialChainResidual_sum, hsym]
  simp only [innerRadialSourcePairing, innerRadialDomainSource_apply]
  have hxrow := hx.2.2.1
  have hyrow := hy.2.2.1
  cases bordered with
  | false =>
    simp only [Bool.false_eq_true, if_false] at hxrow hyrow
    rw [hxrow.1, hxrow.2, hyrow.1, hyrow.2]
    ring
  | true =>
    simp only [eq_self_iff_true, ite_true] at hxrow hyrow
    rw [hxrow, hyrow]
    ring

/-- Green symmetry on the actual zero-total-flux domain. -/
theorem innerRadialBroken_green_zero_flux (x y : W)
    (hx : Flux x = 0) (hy : Flux y = 0) :
    innerRadialSourcePairing D hw G forcing rowSource bordered j central column (Src x) y =
      innerRadialSourcePairing D hw G forcing rowSource bordered j central column (Src y) x := by
  have h := innerRadialBroken_green D hw G forcing rowSource bordered j central column x y
  rw [hx, hy, LinearMap.zero_apply, LinearMap.zero_apply, sub_self] at h
  exact (sub_eq_zero.mp h.symm).symm

/-- The same actual Dirichlet and Poisson realizations satisfy the
forced-flux identity for every L² source, including the central scalar. -/
theorem innerRadialDirichletRealization_forced_flux
    (hunique : ∀ p, InnerRadialPieceKernelUnique D G bordered j central column p)
    (hex : ∀ F ξ p, Nonempty
      (InnerRadialPieceSolution D hw G forcing rowSource bordered j central column F ξ p))
    (F : H) (ξ : B) :
    Flux (innerRadialDirichletRealization D hw G forcing rowSource bordered j central column
      hunique hex F) ξ =
      -innerRadialSourcePairing D hw G forcing rowSource bordered j central column F
        (innerRadialPoissonRealization D hw G forcing rowSource bordered j central column
          hunique hex ξ) := by
  let d := innerRadialDirichletRealization D hw G forcing rowSource bordered j central column
    hunique hex F
  let p := innerRadialPoissonRealization D hw G forcing rowSource bordered j central column
    hunique hex ξ
  have hd : Src d = F ∧ Tr d = 0 :=
    innerRadialDirichletRealization_source_trace D hw G forcing rowSource
      bordered j central column hunique hex F
  have hp : Src p = 0 ∧ Tr p = ξ :=
    innerRadialPoissonRealization_source_trace D hw G forcing rowSource
      bordered j central column hunique hex ξ
  have h := innerRadialBroken_green D hw G forcing rowSource bordered j central column d p
  rw [hp.2, hd.2, map_zero, sub_zero, hp.1, hd.1,
    innerRadialSourcePairing_zero, zero_sub] at h
  exact h

end PhysicalGreen

section HilbertAdjoint

variable (D : ReferenceData) (hw : Continuous D.w) {n : ℕ}
  (G : InnerRadialChainGeometry D n) {H : Type*}
  [NormedAddCommGroup H] [InnerProductSpace ℝ H] [CompleteSpace H]
  (forcing : H →ₗ[ℝ] (Fin (n + 1) → RadialModeL2 D))
  (rowSource : H →ₗ[ℝ] ℝ) (bordered : Bool) (j : ℝ)
  (central : Fin (n + 1)) (column : RadialModeL2 D)
  (hunique : ∀ p, InnerRadialPieceKernelUnique D G bordered j central column p)
  (hex : ∀ F ξ p, Nonempty
    (InnerRadialPieceSolution D hw G forcing rowSource bordered j central column F ξ p))

/-- Identifying the realized Poisson field in the same Hilbert source
measure turns the proved physical Green formula into minus its actual
adjoint. The only identification input is the physical L²/scalar
pairing of that same Poisson field. -/
theorem innerRadialDirichletRealization_forced_adjoint
    (T : EuclideanSpace ℝ (Fin n) →L[ℝ] H)
    (hT : ∀ F ξ, ⟪F, T ξ⟫_ℝ =
      innerRadialSourcePairing D hw G forcing rowSource bordered j central column F
        (innerRadialPoissonRealization D hw G forcing rowSource bordered j central column
          hunique hex ξ))
    (F : H) (ξ : EuclideanSpace ℝ (Fin n)) :
    innerRadialDomainFlux D hw G forcing rowSource bordered j central column
      (innerRadialDirichletRealization D hw G forcing rowSource bordered j central column
        hunique hex F) ξ = -⟪T.adjoint F, ξ⟫_ℝ := by
  rw [innerRadialDirichletRealization_forced_flux D hw G forcing rowSource
    bordered j central column hunique hex F ξ, ← hT F ξ,
    ContinuousLinearMap.adjoint_inner_left]

end HilbertAdjoint

end ContinuousFlexibility.Radial
