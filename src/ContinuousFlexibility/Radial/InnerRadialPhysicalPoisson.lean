import ContinuousFlexibility.Radial.InnerRadialPhysicalSource
import ContinuousFlexibility.Radial.InnerRadialWeakGreen
import ContinuousFlexibility.Radial.InnerBorderWeights
import Mathlib.Analysis.Normed.Module.FiniteDimension

/-!
# The same physical Poisson operator and its actual adjoint

The canonical broken-domain Poisson solution is realized in the genuine
supported Hilbert source space. Its boundary domain is finite dimensional,
so this actual linear map is continuous. Orthogonal piece restriction and
the proved H¹ support identify the physical inner product exactly.

The arbitrary-L² Dirichlet conormal flux is therefore minus the adjoint
of this same physical Poisson operator. No pairing or flux identity is
an additional hypothesis.
-/

noncomputable section

namespace ContinuousFlexibility.Radial

open Set MeasureTheory Filter ContinuousFlexibility.Statements
open scoped InnerProductSpace BigOperators

/-- The physical product pairing counts the scalar once. Restriction
moves onto the source because each actual field lies in its piece. -/
theorem innerBorderL2_inner_piece_sum {α ι : Type*} [MeasurableSpace α]
    [Fintype ι] (μ : Measure α) (sets : ι → Set α)
    (F : InnerBorderL2 μ) (u : ι → Lp ℝ 2 μ) (c : ℝ)
    (hu : ∀ i, innerL2PieceProjection μ (sets i) (u i) = u i) :
    ⟪F, (WithLp.toLp 2 (∑ i, u i, c) : InnerBorderL2 μ)⟫_ℝ =
      (∑ i, ⟪innerL2PieceProjection μ (sets i) F.fst, u i⟫_ℝ) + F.snd * c := by
  rw [innerBorderL2_inner_coordinates,
    WithLp.toLp_fst (p := 2) (∑ i, u i, c),
    WithLp.toLp_snd (p := 2) (∑ i, u i, c), inner_sum]
  apply congrArg (fun z : ℝ => z + F.snd * c)
  exact Finset.sum_congr rfl (fun i _ =>
    (innerL2PieceProjection_inner_fixed μ (sets i) F.fst (u i) (hu i)).symm)

section PhysicalPoisson

variable (D : ReferenceData) (hw : Continuous D.w) {n : ℕ}
  (G : InnerRadialChainGeometry D n) (bordered : Bool) (j : ℝ)
  (central : Fin (n + 1)) (column : RadialModeL2 D)

local notation "B" => EuclideanSpace ℝ (Fin n)
local notation "H" => InnerRadialPhysicalSource D G bordered
local notation "forcing" => innerRadialPhysicalForcing D G bordered
local notation "rowSource" => innerRadialPhysicalRowLinear D G bordered
local notation "W" =>
  InnerRadialDomain D hw G forcing rowSource bordered j central column
local notation "realize" =>
  innerRadialPhysicalRealization D G hw bordered j central column

/-- Actual physical L²/scalar pairing on every broken weak field. -/
theorem innerRadialPhysicalRealization_pairing (F : H) (x : W) :
    ⟪F, realize x⟫_ℝ =
      innerRadialSourcePairing D hw G forcing rowSource bordered j central column F x := by
  have hx := (mem_innerRadialBrokenSpace D hw G forcing rowSource bordered j
    central column x.val).mp x.property
  obtain ⟨ξ, hξ⟩ := (innerRadialChainDomain_trace_iff D hw G x.val.1.1).mp hx.1
  have hfix (p : Fin (n + 1)) :
      innerL2PieceProjection (radialHilbertMeasure D) (Ioo (G.left p) (G.right p))
        (x.val.1.1 p).1 = (x.val.1.1 p).1 :=
    innerRadialH1Domain_piece_projection D hw (G.left_pos p) (G.in_core p)
      (G.weight_pos p) (hξ p).1
  rw [← (innerRadialPhysicalInclusion D G bordered).inner_map_map,
    innerRadialPhysicalInclusion_apply, innerRadialPhysicalInclusion_apply,
    innerRadialPhysicalRealization_apply]
  rw [innerBorderL2_inner_piece_sum (radialHilbertMeasure D)
    (fun p => Ioo (G.left p) (G.right p)) F.val
    (fun p => (x.val.1.1 p).1) x.val.1.2.2 hfix]
  simp only [innerRadialSourcePairing, innerRadialPhysicalForcing_apply,
    innerRadialPhysicalRowLinear_apply]

variable
  (hunique : ∀ p, InnerRadialPieceKernelUnique D G bordered j central column p)
  (hex : ∀ (F : InnerRadialPhysicalSource D G bordered)
    (ξ : EuclideanSpace ℝ (Fin n)) (p : Fin (n + 1)), Nonempty
      (InnerRadialPieceSolution D hw G
        (innerRadialPhysicalForcing D G bordered) (innerRadialPhysicalRowLinear D G bordered)
        bordered j central column F ξ p))

/-- The actual Dirichlet field map. Its quantitative continuity is
supplied by the local Dirichlet bounds when the finite inverse is estimated. -/
def innerRadialPhysicalDirichlet : H →ₗ[ℝ] H :=
  (realize).comp
    (innerRadialDirichletRealization D hw G forcing rowSource bordered j central column
      hunique hex)

/-- The same actual Poisson fields, as a continuous map from internal
cut data to the physical supported Hilbert source. -/
def innerRadialPhysicalPoisson : B →L[ℝ] H :=
  LinearMap.toContinuousLinearMap
    ((realize).comp
      (innerRadialPoissonRealization D hw G forcing rowSource bordered j central column
        hunique hex))

theorem innerRadialPhysicalDirichlet_eq_assembled (F : H)
    (s : ∀ p, InnerRadialPieceSolution D hw G forcing rowSource bordered j central column
      F 0 p) :
    innerRadialPhysicalDirichlet D hw G bordered j central column hunique hex F =
      realize (innerRadialAssemblePieces D hw G forcing rowSource bordered j central column
        F 0 s) := by
  rw [innerRadialPhysicalDirichlet, LinearMap.comp_apply,
    innerRadialDirichletRealization_eq_assembled D hw G forcing rowSource
      bordered j central column hunique hex F s]

theorem innerRadialPhysicalDirichlet_value_eq_assembled (F : H)
    (s : ∀ p, InnerRadialPieceSolution D hw G forcing rowSource bordered j central column
      F 0 p) :
    (innerRadialPhysicalDirichlet D hw G bordered j central column hunique hex F).val =
      WithLp.toLp 2 (∑ p, (s p).q.1, (s central).borderScalar) := by
  rw [innerRadialPhysicalDirichlet_eq_assembled D hw G bordered j central column
    hunique hex F s, innerRadialPhysicalRealization_apply]
  rfl

@[simp] theorem innerRadialPhysicalPoisson_apply (ξ : B) :
    innerRadialPhysicalPoisson D hw G bordered j central column hunique hex ξ =
      realize
        (innerRadialPoissonRealization D hw G forcing rowSource bordered j central column
          hunique hex ξ) := by
  simp only [innerRadialPhysicalPoisson, LinearMap.coe_toContinuousLinearMap',
    LinearMap.comp_apply]

/-- This is the physical field of every actual local Poisson witness,
so later local estimates and DtN formulas refer to this very operator. -/
theorem innerRadialPhysicalPoisson_eq_assembled (ξ : B)
    (s : ∀ p, InnerRadialPieceSolution D hw G forcing rowSource bordered j central column
      0 ξ p) :
    innerRadialPhysicalPoisson D hw G bordered j central column hunique hex ξ =
      realize (innerRadialAssemblePieces D hw G forcing rowSource bordered j central column
        0 ξ s) := by
  rw [innerRadialPhysicalPoisson_apply,
    innerRadialPoissonRealization_eq_assembled D hw G forcing rowSource
      bordered j central column hunique hex ξ s]

theorem innerRadialPhysicalPoisson_value_eq_assembled (ξ : B)
    (s : ∀ p, InnerRadialPieceSolution D hw G forcing rowSource bordered j central column
      0 ξ p) :
    (innerRadialPhysicalPoisson D hw G bordered j central column hunique hex ξ).val =
      WithLp.toLp 2 (∑ p, (s p).q.1, (s central).borderScalar) := by
  rw [innerRadialPhysicalPoisson_eq_assembled D hw G bordered j central column
    hunique hex ξ s, innerRadialPhysicalRealization_apply]
  rfl

/-- Forced outgoing flux equals minus the actual adjoint of the same
physical Poisson operator, for every source in the true Hilbert domain. -/
theorem innerRadialPhysicalDirichlet_forced_adjoint (F : H) (ξ : B) :
    innerRadialDomainFlux D hw G forcing rowSource bordered j central column
      (innerRadialDirichletRealization D hw G forcing rowSource bordered j central column
        hunique hex F) ξ =
      -⟪(innerRadialPhysicalPoisson D hw G bordered j central column
        hunique hex).adjoint F, ξ⟫_ℝ := by
  apply innerRadialDirichletRealization_forced_adjoint D hw G forcing rowSource
    bordered j central column hunique hex
    (innerRadialPhysicalPoisson D hw G bordered j central column hunique hex)
  intro F' ξ'
  rw [innerRadialPhysicalPoisson_apply]
  exact innerRadialPhysicalRealization_pairing D hw G bordered j central column F' _

end PhysicalPoisson

end ContinuousFlexibility.Radial
