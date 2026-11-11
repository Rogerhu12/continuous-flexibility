import ContinuousFlexibility.Radial.InnerInterfaceInverse
import Mathlib.Analysis.InnerProductSpace.Adjoint
import Mathlib.Analysis.InnerProductSpace.Symmetric
import Mathlib.Tactic.Ring

/-!
# The inner Poisson correction and its Green identities

The two weight signs act on one correction `T K T†` and one inverse
`D + T K T†`. The second factor in the weighted estimate is the adjoint
of the Poisson map with the opposite sign. All norms in this module are
actual Hilbert norms; a scalar border is therefore represented by a Hilbert
sum, not by the ordinary product with its maximum norm.

The final section derives both inverse identities from the local
Dirichlet, homogeneous Poisson, trace and flux identities. Its domain is
the space of broken fields with matching values; the global domain is
selected by vanishing total outward flux. No inverse property of the
assembled operator is assumed.
-/

noncomputable section

namespace ContinuousFlexibility.Radial

open scoped InnerProductSpace

variable {H B : Type*}
  [NormedAddCommGroup H] [InnerProductSpace ℝ H] [CompleteSpace H]
  [NormedAddCommGroup B] [InnerProductSpace ℝ B] [CompleteSpace B]

/-- A weight and its inverse, indexed by the two signs. -/
def innerHilbertWeight (W : H ≃L[ℝ] H) : Bool → H ≃L[ℝ] H
  | true => W
  | false => W.symm

theorem innerHilbertWeight_apply_not_apply (W : H ≃L[ℝ] H)
    (forward : Bool) (x : H) :
    innerHilbertWeight W forward (innerHilbertWeight W (!forward) x) = x := by
  cases forward with
  | false => exact W.symm_apply_apply x
  | true => exact W.apply_symm_apply x

theorem innerHilbertWeight_not_apply_apply (W : H ≃L[ℝ] H)
    (forward : Bool) (x : H) :
    innerHilbertWeight W (!forward) (innerHilbertWeight W forward x) = x := by
  cases forward with
  | false => exact W.apply_symm_apply x
  | true => exact W.symm_apply_apply x

/-- Inverse multiplication by a real weight remains self-adjoint. -/
theorem innerHilbertWeight_symm_selfAdjoint (W : H ≃L[ℝ] H)
    (hW : IsSelfAdjoint (W : H →L[ℝ] H)) :
    IsSelfAdjoint (W.symm : H →L[ℝ] H) := by
  apply ContinuousLinearMap.isSelfAdjoint_iff_isSymmetric.mpr
  exact LinearMap.IsSymmetric.toLinearMap_symm (T := W.toLinearEquiv) hW.isSymmetric

theorem innerHilbertWeight_selfAdjoint (W : H ≃L[ℝ] H)
    (hW : IsSelfAdjoint (W : H →L[ℝ] H)) (forward : Bool) :
    IsSelfAdjoint (innerHilbertWeight W forward : H →L[ℝ] H) := by
  cases forward with
  | false => exact innerHilbertWeight_symm_selfAdjoint W hW
  | true => exact hW

/-- The exact Poisson correction, using one interface inverse `K`. -/
def innerCouplingCorrection (T : B →L[ℝ] H) (K : B →L[ℝ] B) : H →L[ℝ] H :=
  T ∘L K ∘L T.adjoint

theorem innerCouplingCorrection_apply (T : B →L[ℝ] H) (K : B →L[ℝ] B) (F : H) :
    innerCouplingCorrection T K F = T (K (T.adjoint F)) := by
  simp only [innerCouplingCorrection, ContinuousLinearMap.comp_apply]

/-- The same inner inverse for all weight estimates. -/
def innerGluedInverse (D : H →L[ℝ] H) (T : B →L[ℝ] H)
    (K : B →L[ℝ] B) : H →L[ℝ] H :=
  D + innerCouplingCorrection T K

theorem innerGluedInverse_apply (D : H →L[ℝ] H) (T : B →L[ℝ] H)
    (K : B →L[ℝ] B) (F : H) :
    innerGluedInverse D T K F = D F + T (K (T.adjoint F)) := by
  simp only [innerGluedInverse, ContinuousLinearMap.add_apply,
    innerCouplingCorrection_apply]

/-- A normalized weighted Poisson map. Here `J` is the inverse square root
of the full positive interface matrix. -/
def innerWeightedPoisson (W : H ≃L[ℝ] H) (Ω : B ≃L[ℝ] B)
    (T : B →L[ℝ] H) (J : B →L[ℝ] B) (forward : Bool) : B →L[ℝ] H :=
  (innerHilbertWeight W forward : H →L[ℝ] H) ∘L T ∘L
    (innerHilbertWeight Ω (!forward) : B →L[ℝ] B) ∘L J

theorem innerWeightedPoisson_adjoint (W : H ≃L[ℝ] H) (Ω : B ≃L[ℝ] B)
    (T : B →L[ℝ] H) (J : B →L[ℝ] B)
    (hW : IsSelfAdjoint (W : H →L[ℝ] H))
    (hΩ : IsSelfAdjoint (Ω : B →L[ℝ] B)) (hJ : IsSelfAdjoint J)
    (forward : Bool) :
    (innerWeightedPoisson W Ω T J forward).adjoint =
      J ∘L (innerHilbertWeight Ω (!forward) : B →L[ℝ] B) ∘L
        T.adjoint ∘L (innerHilbertWeight W forward : H →L[ℝ] H) := by
  simp only [innerWeightedPoisson, ContinuousLinearMap.adjoint_comp,
    (innerHilbertWeight_selfAdjoint W hW forward).adjoint_eq,
    (innerHilbertWeight_selfAdjoint Ω hΩ (!forward)).adjoint_eq,
    hJ.adjoint_eq, ContinuousLinearMap.comp_assoc]

/-- Removing the boundary weights from the already established interface
factorization uses only their two inverse identities. -/
theorem innerCoupling_remove_boundary_weights (Ω : B ≃L[ℝ] B)
    (J K N : B →L[ℝ] B) (forward : Bool)
    (hfactor : (innerHilbertWeight Ω forward : B →L[ℝ] B) ∘L K ∘L
      (innerHilbertWeight Ω (!forward) : B →L[ℝ] B) = J ∘L N ∘L J) :
    K = (innerHilbertWeight Ω (!forward) : B →L[ℝ] B) ∘L J ∘L N ∘L J ∘L
      (innerHilbertWeight Ω forward : B →L[ℝ] B) := by
  ext x
  have h := congrArg (fun A : B →L[ℝ] B =>
    innerHilbertWeight Ω (!forward) (A (innerHilbertWeight Ω forward x))) hfactor
  simpa only [ContinuousLinearMap.comp_apply, ContinuousLinearEquiv.coe_coe,
    innerHilbertWeight_not_apply_apply] using h

/-- The right factor is the adjoint of the Poisson map with the opposite sign. -/
theorem innerCoupling_weighted_factorization (W : H ≃L[ℝ] H) (Ω : B ≃L[ℝ] B)
    (T : B →L[ℝ] H) (J K : B →L[ℝ] B) (N : Bool → B →L[ℝ] B)
    (hW : IsSelfAdjoint (W : H →L[ℝ] H))
    (hΩ : IsSelfAdjoint (Ω : B →L[ℝ] B)) (hJ : IsSelfAdjoint J)
    (hfactor : ∀ forward : Bool,
      (innerHilbertWeight Ω forward : B →L[ℝ] B) ∘L K ∘L
        (innerHilbertWeight Ω (!forward) : B →L[ℝ] B) = J ∘L N forward ∘L J)
    (forward : Bool) :
    (innerHilbertWeight W forward : H →L[ℝ] H) ∘L innerCouplingCorrection T K ∘L
      (innerHilbertWeight W (!forward) : H →L[ℝ] H) =
      innerWeightedPoisson W Ω T J forward ∘L N forward ∘L
        (innerWeightedPoisson W Ω T J (!forward)).adjoint := by
  have hK := innerCoupling_remove_boundary_weights Ω J K (N forward) forward
    (hfactor forward)
  rw [innerCouplingCorrection, hK,
    innerWeightedPoisson_adjoint W Ω T J hW hΩ hJ (!forward)]
  simp only [innerWeightedPoisson, Bool.not_not, ContinuousLinearMap.comp_assoc]

/-- The correction loses no cell coefficient power. The explicit constant
`2 * C^2` can be absorbed into the manuscript's fixed `C`. -/
theorem innerCoupling_weighted_bound (W : H ≃L[ℝ] H) (Ω : B ≃L[ℝ] B)
    (T : B →L[ℝ] H) (J K : B →L[ℝ] B) (N : Bool → B →L[ℝ] B)
    (hW : IsSelfAdjoint (W : H →L[ℝ] H))
    (hΩ : IsSelfAdjoint (Ω : B →L[ℝ] B)) (hJ : IsSelfAdjoint J)
    (hfactor : ∀ forward : Bool,
      (innerHilbertWeight Ω forward : B →L[ℝ] B) ∘L K ∘L
        (innerHilbertWeight Ω (!forward) : B →L[ℝ] B) = J ∘L N forward ∘L J)
    {C j : ℝ} (hC : 0 ≤ C) (hj : 0 < j)
    (hP : ∀ forward : Bool, ‖innerWeightedPoisson W Ω T J forward‖ ≤ C / j)
    (hN : ∀ forward : Bool, ‖N forward‖ ≤ 2) (forward : Bool) :
    ‖(innerHilbertWeight W forward : H →L[ℝ] H) ∘L innerCouplingCorrection T K ∘L
      (innerHilbertWeight W (!forward) : H →L[ℝ] H)‖ ≤ 2 * C ^ 2 / j ^ 2 := by
  rw [innerCoupling_weighted_factorization W Ω T J K N hW hΩ hJ hfactor forward]
  have hPopp : ‖(innerWeightedPoisson W Ω T J (!forward)).adjoint‖ ≤ C / j := by
    simpa only [LinearIsometryEquiv.norm_map] using hP (!forward)
  have hright : ‖N forward‖ * ‖(innerWeightedPoisson W Ω T J (!forward)).adjoint‖ ≤
      2 * (C / j) :=
    mul_le_mul (hN forward) hPopp (norm_nonneg _) (by norm_num)
  calc
    ‖innerWeightedPoisson W Ω T J forward ∘L N forward ∘L
        (innerWeightedPoisson W Ω T J (!forward)).adjoint‖ ≤
      ‖innerWeightedPoisson W Ω T J forward‖ *
        (‖N forward‖ * ‖(innerWeightedPoisson W Ω T J (!forward)).adjoint‖) :=
      (ContinuousLinearMap.opNorm_comp_le _ _).trans
        (mul_le_mul_of_nonneg_left (ContinuousLinearMap.opNorm_comp_le _ _) (norm_nonneg _))
    _ ≤ (C / j) * (2 * (C / j)) :=
      mul_le_mul (hP forward) hright
        (mul_nonneg (norm_nonneg _) (norm_nonneg _)) (div_nonneg hC hj.le)
    _ = 2 * C ^ 2 / j ^ 2 := by
      simp only [div_eq_mul_inv, inv_pow]
      ring

/-- The weighted estimate for the full inverse separates the local
Dirichlet cost from the uniformly controlled Poisson correction. -/
theorem innerGluedInverse_weighted_bound (W : H ≃L[ℝ] H) (Ω : B ≃L[ℝ] B)
    (D : H →L[ℝ] H) (T : B →L[ℝ] H) (J K : B →L[ℝ] B)
    (N : Bool → B →L[ℝ] B)
    (hW : IsSelfAdjoint (W : H →L[ℝ] H))
    (hΩ : IsSelfAdjoint (Ω : B →L[ℝ] B)) (hJ : IsSelfAdjoint J)
    (hfactor : ∀ forward : Bool,
      (innerHilbertWeight Ω forward : B →L[ℝ] B) ∘L K ∘L
        (innerHilbertWeight Ω (!forward) : B →L[ℝ] B) = J ∘L N forward ∘L J)
    {C j d : ℝ} (hC : 0 ≤ C) (hj : 0 < j)
    (hP : ∀ forward : Bool, ‖innerWeightedPoisson W Ω T J forward‖ ≤ C / j)
    (hN : ∀ forward : Bool, ‖N forward‖ ≤ 2) (forward : Bool)
    (hD : ‖(innerHilbertWeight W forward : H →L[ℝ] H) ∘L D ∘L
      (innerHilbertWeight W (!forward) : H →L[ℝ] H)‖ ≤ d) :
    ‖(innerHilbertWeight W forward : H →L[ℝ] H) ∘L innerGluedInverse D T K ∘L
      (innerHilbertWeight W (!forward) : H →L[ℝ] H)‖ ≤ d + 2 * C ^ 2 / j ^ 2 := by
  have hcorrection := innerCoupling_weighted_bound W Ω T J K N hW hΩ hJ hfactor
    hC hj hP hN forward
  rw [innerGluedInverse, ContinuousLinearMap.add_comp, ContinuousLinearMap.comp_add]
  exact (norm_add_le _ _).trans (add_le_add hD hcorrection)

/-- Green symmetry of an inverse follows from the symmetry of the actual
interface operator and its right inverse identity. -/
theorem innerInverse_selfAdjoint (S K : B →L[ℝ] B) (hS : IsSelfAdjoint S)
    (hSK : ∀ x, S (K x) = x) : IsSelfAdjoint K := by
  apply ContinuousLinearMap.isSelfAdjoint_iff_isSymmetric.mpr
  intro x y
  simpa only [ContinuousLinearMap.coe_coe, hSK] using (hS.isSymmetric (K x) (K y)).symm

theorem innerGluedInverse_selfAdjoint (D : H →L[ℝ] H) (T : B →L[ℝ] H)
    (S K : B →L[ℝ] B) (hD : IsSelfAdjoint D) (hS : IsSelfAdjoint S)
    (hSK : ∀ x, S (K x) = x) : IsSelfAdjoint (innerGluedInverse D T K) :=
  hD.add ((innerInverse_selfAdjoint S K hS hSK).conj_adjoint T)

theorem innerGluedInverse_green (D : H →L[ℝ] H) (T : B →L[ℝ] H)
    (S K : B →L[ℝ] B) (hD : IsSelfAdjoint D) (hS : IsSelfAdjoint S)
    (hSK : ∀ x, S (K x) = x) (x y : H) :
    ⟪innerGluedInverse D T K x, y⟫_ℝ = ⟪x, innerGluedInverse D T K y⟫_ℝ :=
  (innerGluedInverse_selfAdjoint D T S K hD hS hSK).isSymmetric x y

section DomainGluing

variable {V : Type*} [AddCommGroup V] [Module ℝ V]

/-- The solution in the broken domain, before taking its ambient realization. -/
def innerDomainSolution (d : H →ₗ[ℝ] V) (p : B →ₗ[ℝ] V)
    (T : B →L[ℝ] H) (K : B →L[ℝ] B) : H →ₗ[ℝ] V :=
  d + p.comp (K.toLinearMap.comp T.adjoint.toLinearMap)

theorem innerDomainSolution_apply (d : H →ₗ[ℝ] V) (p : B →ₗ[ℝ] V)
    (T : B →L[ℝ] H) (K : B →L[ℝ] B) (F : H) :
    innerDomainSolution d p T K F = d F + p (K (T.adjoint F)) := by
  simp only [innerDomainSolution, LinearMap.add_apply, LinearMap.comp_apply,
    ContinuousLinearMap.coe_coe]

/-- Local Dirichlet uniqueness gives the decomposition into a zero-trace
part and the homogeneous Poisson lift of the actual trace. -/
theorem innerDirichletPoisson_decomposition (L : V →ₗ[ℝ] H) (trace : V →ₗ[ℝ] B)
    (d : H →ₗ[ℝ] V) (p : B →ₗ[ℝ] V)
    (hLd : ∀ F, L (d F) = F) (htraceD : ∀ F, trace (d F) = 0)
    (hLp : ∀ a, L (p a) = 0) (htraceP : ∀ a, trace (p a) = a)
    (hunique : ∀ u, L u = 0 → trace u = 0 → u = 0) (u : V) :
    u = d (L u) + p (trace u) := by
  apply sub_eq_zero.mp
  apply hunique
  · simp only [map_sub, map_add, hLd, hLp, add_zero, sub_self]
  · simp only [map_sub, map_add, htraceD, htraceP, zero_add, sub_self]

/-- The source equation and exact cancellation of total outward flux. -/
theorem innerDomainSolution_solves (L : V →ₗ[ℝ] H) (flux : V →ₗ[ℝ] B)
    (d : H →ₗ[ℝ] V) (p : B →ₗ[ℝ] V) (T : B →L[ℝ] H) (S K : B →L[ℝ] B)
    (hLd : ∀ F, L (d F) = F) (hLp : ∀ a, L (p a) = 0)
    (hfluxD : ∀ F, flux (d F) = -T.adjoint F)
    (hfluxP : ∀ a, flux (p a) = S a) (hSK : ∀ a, S (K a) = a) (F : H) :
    L (innerDomainSolution d p T K F) = F ∧
      flux (innerDomainSolution d p T K F) = 0 := by
  constructor
  · simp only [innerDomainSolution_apply, map_add, hLd, hLp, add_zero]
  · simp only [innerDomainSolution_apply, map_add, hfluxD, hfluxP, hSK,
      neg_add_cancel]

theorem innerDomainSolution_trace (trace : V →ₗ[ℝ] B)
    (d : H →ₗ[ℝ] V) (p : B →ₗ[ℝ] V) (T : B →L[ℝ] H) (K : B →L[ℝ] B)
    (htraceD : ∀ F, trace (d F) = 0) (htraceP : ∀ a, trace (p a) = a) (F : H) :
    trace (innerDomainSolution d p T K F) = K (T.adjoint F) := by
  simp only [innerDomainSolution_apply, map_add, htraceD, htraceP, zero_add]

/-- The left inverse identity on the actual matched-flux domain follows
from local uniqueness and the interface's left inverse identity. -/
theorem innerDomainSolution_left_inverse (L : V →ₗ[ℝ] H) (trace flux : V →ₗ[ℝ] B)
    (d : H →ₗ[ℝ] V) (p : B →ₗ[ℝ] V) (T : B →L[ℝ] H) (S K : B →L[ℝ] B)
    (hLd : ∀ F, L (d F) = F) (htraceD : ∀ F, trace (d F) = 0)
    (hLp : ∀ a, L (p a) = 0) (htraceP : ∀ a, trace (p a) = a)
    (hunique : ∀ u, L u = 0 → trace u = 0 → u = 0)
    (hfluxD : ∀ F, flux (d F) = -T.adjoint F)
    (hfluxP : ∀ a, flux (p a) = S a) (hKS : ∀ a, K (S a) = a)
    (u : V) (hu : flux u = 0) : innerDomainSolution d p T K (L u) = u := by
  have hdecomp := innerDirichletPoisson_decomposition L trace d p hLd htraceD hLp
    htraceP hunique u
  have hflux : S (trace u) = T.adjoint (L u) := by
    have h := congrArg flux hdecomp
    rw [hu, map_add, hfluxD, hfluxP] at h
    apply sub_eq_zero.mp
    simpa only [sub_eq_add_neg, add_comm] using h.symm
  have htrace : K (T.adjoint (L u)) = trace u := by
    rw [← hflux, hKS]
  rw [innerDomainSolution_apply, htrace]
  exact hdecomp.symm

/-- The broken-domain solution realizes exactly the same bounded operator
whose weighted norm and Green symmetry were proved above. -/
theorem innerDomainSolution_realize (realize : V →ₗ[ℝ] H)
    (d : H →ₗ[ℝ] V) (p : B →ₗ[ℝ] V) (D : H →L[ℝ] H)
    (T : B →L[ℝ] H) (K : B →L[ℝ] B)
    (hD : ∀ F, realize (d F) = D F) (hP : ∀ a, realize (p a) = T a) (F : H) :
    realize (innerDomainSolution d p T K F) = innerGluedInverse D T K F := by
  simp only [innerDomainSolution_apply, map_add, hD, hP, innerGluedInverse_apply]

end DomainGluing

end ContinuousFlexibility.Radial
