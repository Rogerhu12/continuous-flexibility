import ContinuousFlexibility.Radial.InnerRadialPhysicalDirichlet
import ContinuousFlexibility.Radial.InnerRadialSchurInverse

/-!
# The actual physical Schur inverse and Green self-adjointness

The Hilbert correction uses the very same physical Dirichlet and Poisson
fields. Its interface source is the proved Poisson adjoint. The two
inverse identities hold on the image of the actual finite weak graph,
with its real H¹ fields, signed potential and one central scalar.

The interface identification is with the actual Poisson conormal flux.
Its invertibility is supplied by the finite normalized interface proof.
Global Green reciprocity proves self-adjointness of this same operator.
-/

noncomputable section

namespace ContinuousFlexibility.Radial

open Set MeasureTheory ContinuousFlexibility.Statements
open scoped InnerProductSpace BigOperators

/-- Finite-dimensional Riesz identification, retaining the Euclidean
cut norm used by the interface matrices. -/
def innerRadialBoundaryRiesz (n : ℕ) :
    EuclideanSpace ℝ (Fin n) ≃ₗ[ℝ] (EuclideanSpace ℝ (Fin n) →ₗ[ℝ] ℝ) :=
  (InnerProductSpace.toDual ℝ (EuclideanSpace ℝ (Fin n))).toLinearEquiv.trans
    LinearMap.toContinuousLinearMap.symm

@[simp] theorem innerRadialBoundaryRiesz_apply (n : ℕ)
    (ξ η : EuclideanSpace ℝ (Fin n)) :
    innerRadialBoundaryRiesz n ξ η = ⟪ξ, η⟫_ℝ := by
  simp only [innerRadialBoundaryRiesz, LinearEquiv.trans_apply,
    LinearMap.coe_toContinuousLinearMap_symm, ContinuousLinearMap.coe_coe,
    LinearIsometryEquiv.coe_toLinearEquiv, InnerProductSpace.toDual_apply_apply]

section PhysicalGraph

variable (D : ReferenceData) (hw : Continuous D.w) {n : ℕ}
  (G : InnerRadialChainGeometry D n) (bordered : Bool) (j : ℝ)
  (central : Fin (n + 1)) (column : RadialModeL2 D)

local notation "B" => EuclideanSpace ℝ (Fin n)
local notation "H" => InnerRadialPhysicalSource D G bordered
local notation "forcing" => innerRadialPhysicalForcing D G bordered
local notation "rowSource" => (innerRadialPhysicalRow D G bordered).toLinearMap
local notation "W" =>
  InnerRadialDomain D hw G forcing rowSource bordered j central column
local notation "realize" =>
  innerRadialPhysicalRealization D G hw bordered j central column
local notation "Src" =>
  innerRadialDomainSource D hw G forcing rowSource bordered j central column
local notation "Flux" =>
  innerRadialDomainFlux D hw G forcing rowSource bordered j central column

/-- The actual weak inner graph on the physical L²/scalar space. Its
witness is the genuine finite H¹ graph with total conormal flux zero. -/
def InnerRadialPhysicalWeakGraph (u F : H) : Prop :=
  ∃ x : W, realize x = u ∧ Src x = F ∧ Flux x = 0

/-- The Hilbert graph is precisely the original matched physical weak
equation; the derivative and potential coordinates are actual witnesses. -/
theorem innerRadialPhysicalWeakGraph_iff (u F : H) :
    InnerRadialPhysicalWeakGraph D hw G bordered j central column u F ↔
      ∃ q : Fin (n + 1) → InnerRadialH1Pair D,
      ∃ v : Fin (n + 1) → RadialModeL2 D, ∃ borderScalar : ℝ,
        u.val = WithLp.toLp 2 (∑ p, (q p).1, borderScalar) ∧
          InnerRadialChainWeakGraph D hw G bordered j central column
            q v (forcing F) borderScalar (rowSource F) := by
  constructor
  · rintro ⟨x, hu, hF, hflux⟩
    refine ⟨x.val.1.1, x.val.1.2.1, x.val.1.2.2, ?_, ?_⟩
    · rw [← hu, innerRadialPhysicalRealization_apply]
    · have hraw : innerRadialBrokenFlux D hw G forcing central column x.val = 0 := by
        simpa only [innerRadialDomainFlux_apply] using hflux
      have hg := (innerRadialBrokenSpace_global_iff D hw G forcing rowSource
        bordered j central column x.val).mpr ⟨x.property, hraw⟩
      have hs : x.val.2 = F := by
        simpa only [innerRadialDomainSource_apply] using hF
      simpa only [hs] using hg
  · rintro ⟨q, v, borderScalar, hu, hg⟩
    let raw : InnerRadialBrokenData D n H := ((q, (v, borderScalar)), F)
    have hraw := (innerRadialBrokenSpace_global_iff D hw G forcing rowSource
      bordered j central column raw).mp hg
    let x : W := ⟨raw, hraw.1⟩
    refine ⟨x, ?_, ?_, ?_⟩
    · apply Subtype.ext
      rw [innerRadialPhysicalRealization_apply]
      exact hu.symm
    · rw [innerRadialDomainSource_apply]
      rfl
    · rw [innerRadialDomainFlux_apply]
      exact hraw.2

/-- Green reciprocity on the actual physical weak graph. -/
theorem innerRadialPhysicalWeakGraph_green {u v F K : H}
    (hu : InnerRadialPhysicalWeakGraph D hw G bordered j central column u F)
    (hv : InnerRadialPhysicalWeakGraph D hw G bordered j central column v K) :
    ⟪F, v⟫_ℝ = ⟪K, u⟫_ℝ := by
  obtain ⟨x, hx, hF, hfx⟩ := hu
  obtain ⟨y, hy, hK, hfy⟩ := hv
  have h := innerRadialBroken_green_zero_flux D hw G forcing rowSource
    bordered j central column x y hfx hfy
  rw [hF, hK,
    ← innerRadialPhysicalRealization_pairing D hw G bordered j central column F y,
    ← innerRadialPhysicalRealization_pairing D hw G bordered j central column K x,
    hx, hy] at h
  exact h

variable
  (hunique : ∀ p, InnerRadialPieceKernelUnique D G bordered j central column p)
  (hex : ∀ F ξ p, Nonempty
    (InnerRadialPieceSolution D hw G forcing rowSource bordered j central column F ξ p))

local notation "Dir" =>
  innerRadialDirichletRealization D hw G forcing rowSource bordered j central column
    hunique hex
local notation "Pois" =>
  innerRadialPoissonRealization D hw G forcing rowSource bordered j central column
    hunique hex
local notation "P" =>
  innerRadialPhysicalPoisson D hw G bordered j central column hunique hex
local notation "Riesz" => innerRadialBoundaryRiesz n

/-- The actual interface pairing, expressed in the finite weak dual. -/
theorem innerRadialPhysicalInterface_identification
    (S : B ≃ₗ[ℝ] B)
    (hS : ∀ ξ η, Flux (Pois ξ) η = ⟪S ξ, η⟫_ℝ) :
    ∀ ξ, Flux (Pois ξ) = S.trans Riesz ξ := by
  intro ξ
  apply LinearMap.ext
  intro η
  rw [LinearEquiv.trans_apply, innerRadialBoundaryRiesz_apply]
  exact hS ξ η

/-- The same physical Schur formula. The Dirichlet CLM is identified
with the already constructed canonical local Dirichlet realization. -/
def innerRadialPhysicalSchur (D0 : H →L[ℝ] H) (S : B ≃ₗ[ℝ] B) : H →L[ℝ] H :=
  D0 + (P).comp ((LinearMap.toContinuousLinearMap S.symm.toLinearMap).comp (P).adjoint)

@[simp] theorem innerRadialPhysicalSchur_apply (D0 : H →L[ℝ] H)
    (S : B ≃ₗ[ℝ] B) (F : H) :
    innerRadialPhysicalSchur D hw G bordered j central column hunique hex D0 S F =
      D0 F + P (S.symm ((P).adjoint F)) := by
  simp only [innerRadialPhysicalSchur, ContinuousLinearMap.add_apply,
    ContinuousLinearMap.comp_apply, LinearMap.coe_toContinuousLinearMap',
    LinearEquiv.coe_coe]

/-- The Hilbert formula realizes the very same constructed weak Schur
solution. Its plus sign follows from the proved negative forced flux. -/
theorem innerRadialPhysicalSchur_eq_realization (D0 : H →L[ℝ] H)
    (hD0 : ∀ F, D0 F =
      innerRadialPhysicalDirichlet D hw G bordered j central column hunique hex F)
    (S : B ≃ₗ[ℝ] B) (F : H) :
    innerRadialPhysicalSchur D hw G bordered j central column hunique hex D0 S F =
      realize (innerRadialSchurInverse D hw G forcing rowSource bordered j central column
        hunique hex (S.trans Riesz) F) := by
  have hf : Flux (Dir F) = -(Riesz ((P).adjoint F)) := by
    apply LinearMap.ext
    intro η
    rw [LinearMap.neg_apply, innerRadialBoundaryRiesz_apply]
    exact innerRadialPhysicalDirichlet_forced_adjoint D hw G bordered j central column
      hunique hex F η
  have hb : (S.trans Riesz).symm (Riesz ((P).adjoint F)) = S.symm ((P).adjoint F) := by
    apply (S.trans Riesz).injective
    rw [LinearEquiv.apply_symm_apply, LinearEquiv.trans_apply, S.apply_symm_apply]
  have hc : innerRadialSchurInverse D hw G forcing rowSource bordered j central column
      hunique hex (S.trans Riesz) F =
      Dir F + Pois (S.symm ((P).adjoint F)) := by
    rw [innerRadialSchurInverse, innerWeakSchurSolution_apply, hf, neg_neg, hb]
  rw [hc, map_add, innerRadialPhysicalSchur_apply, hD0,
    innerRadialPhysicalPoisson_apply, innerRadialPhysicalDirichlet, LinearMap.comp_apply]

/-- The actual operator is a right inverse of the complete physical
weak graph, including the central border row and interface matching. -/
theorem innerRadialPhysicalSchur_right_inverse (D0 : H →L[ℝ] H)
    (hD0 : ∀ F, D0 F =
      innerRadialPhysicalDirichlet D hw G bordered j central column hunique hex F)
    (S : B ≃ₗ[ℝ] B)
    (hS : ∀ ξ η, Flux (Pois ξ) η = ⟪S ξ, η⟫_ℝ) (F : H) :
    InnerRadialPhysicalWeakGraph D hw G bordered j central column
      (innerRadialPhysicalSchur D hw G bordered j central column hunique hex D0 S F) F := by
  refine ⟨innerRadialSchurInverse D hw G forcing rowSource bordered j central column
    hunique hex (S.trans Riesz) F, ?_, ?_, ?_⟩
  · exact (innerRadialPhysicalSchur_eq_realization D hw G bordered j central column
      hunique hex D0 hD0 S F).symm
  · exact innerRadialSchurInverse_source D hw G forcing rowSource bordered j central column
      hunique hex (S.trans Riesz) F
  · exact innerRadialSchurInverse_flux D hw G forcing rowSource bordered j central column
      hunique hex (S.trans Riesz)
      (innerRadialPhysicalInterface_identification D hw G bordered j central column
        hunique hex S hS) F

/-- The same operator is the left inverse on every actual physical
weak-domain element, including nonsmooth L² forcing. -/
theorem innerRadialPhysicalSchur_left_inverse (D0 : H →L[ℝ] H)
    (hD0 : ∀ F, D0 F =
      innerRadialPhysicalDirichlet D hw G bordered j central column hunique hex F)
    (S : B ≃ₗ[ℝ] B)
    (hS : ∀ ξ η, Flux (Pois ξ) η = ⟪S ξ, η⟫_ℝ)
    {u F : H}
    (hu : InnerRadialPhysicalWeakGraph D hw G bordered j central column u F) :
    innerRadialPhysicalSchur D hw G bordered j central column hunique hex D0 S F = u := by
  obtain ⟨x, hx, hF, hflux⟩ := hu
  have hraw : innerRadialBrokenFlux D hw G forcing central column x.val = 0 := by
    simpa only [innerRadialDomainFlux_apply] using hflux
  have hg := (innerRadialBrokenSpace_global_iff D hw G forcing rowSource
    bordered j central column x.val).mpr ⟨x.property, hraw⟩
  have hl := innerRadialSchurInverse_left_inverse D hw G forcing rowSource
    bordered j central column hunique hex (S.trans Riesz)
    (innerRadialPhysicalInterface_identification D hw G bordered j central column
      hunique hex S hS) x hg
  calc
    _ = realize (innerRadialSchurInverse D hw G forcing rowSource bordered j central column
        hunique hex (S.trans Riesz) (Src x)) := by
      rw [hF, innerRadialPhysicalSchur_eq_realization D hw G bordered j central column
        hunique hex D0 hD0 S F]
    _ = realize x := congrArg realize hl
    _ = u := hx

/-- Exact graph characterization of the one physical inverse. -/
theorem innerRadialPhysicalSchur_graph_iff (D0 : H →L[ℝ] H)
    (hD0 : ∀ F, D0 F =
      innerRadialPhysicalDirichlet D hw G bordered j central column hunique hex F)
    (S : B ≃ₗ[ℝ] B)
    (hS : ∀ ξ η, Flux (Pois ξ) η = ⟪S ξ, η⟫_ℝ) (u F : H) :
    InnerRadialPhysicalWeakGraph D hw G bordered j central column u F ↔
      innerRadialPhysicalSchur D hw G bordered j central column hunique hex D0 S F = u := by
  constructor
  · exact innerRadialPhysicalSchur_left_inverse D hw G bordered j central column
      hunique hex D0 hD0 S hS
  · intro hu
    rw [← hu]
    exact innerRadialPhysicalSchur_right_inverse D hw G bordered j central column
      hunique hex D0 hD0 S hS F

/-- Self-adjointness follows from the actual weak Green identity.
No independent symmetry assumption on an assembled inverse is used. -/
theorem innerRadialPhysicalSchur_selfAdjoint (D0 : H →L[ℝ] H)
    (hD0 : ∀ F, D0 F =
      innerRadialPhysicalDirichlet D hw G bordered j central column hunique hex F)
    (S : B ≃ₗ[ℝ] B)
    (hS : ∀ ξ η, Flux (Pois ξ) η = ⟪S ξ, η⟫_ℝ) :
    IsSelfAdjoint (innerRadialPhysicalSchur D hw G bordered j central column
      hunique hex D0 S) := by
  apply ContinuousLinearMap.isSelfAdjoint_iff_isSymmetric.mpr
  intro F K
  have h := innerRadialPhysicalWeakGraph_green D hw G bordered j central column
    (innerRadialPhysicalSchur_right_inverse D hw G bordered j central column
      hunique hex D0 hD0 S hS F)
    (innerRadialPhysicalSchur_right_inverse D hw G bordered j central column
      hunique hex D0 hD0 S hS K)
  exact (real_inner_comm _ _).trans h.symm

end PhysicalGraph

end ContinuousFlexibility.Radial
