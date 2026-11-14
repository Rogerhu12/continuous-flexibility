module

public import ContinuousFlexibility.Radial.InnerSupportedScalarSign
public import ContinuousFlexibility.Radial.InnerRadialPhysicalSchur

/-!
# The manuscript scalar sign on the actual inner problem

The local compression models use the positive Riesz column. For
`B = -varpi⁻¹ L`, the manuscript uses its negative, together with the
negative scalar row. The same supported Hilbert space carries the
isometric involution `J(u,c) = (u,-c)`.

This file identifies the two genuine physical weak graphs. It then
transports the same inverse by `J G J`, retaining both inverse
identities, the Schur formula, and Green self-adjointness. No local
model, interface matrix, or cut geometry is chosen again.
-/

@[expose] public section

noncomputable section

namespace ContinuousFlexibility.Radial

open Set MeasureTheory ContinuousFlexibility.Statements
open scoped InnerProductSpace BigOperators

section WeakEquation

variable (D : ReferenceData) (hw : Continuous D.w) {n : ℕ}
  (G : InnerRadialChainGeometry D n) (bordered : Bool) (j : ℝ)
  (central : Fin (n + 1)) (column : RadialModeL2 D)

/-- Negating the column and its scalar coefficient leaves every actual
local energy residual unchanged. -/
theorem innerRadialChainResidual_scalarSign
    (q : Fin (n + 1) → InnerRadialH1Pair D)
    (v f : Fin (n + 1) → RadialModeL2 D) (c : ℝ) (p : Fin (n + 1)) :
    innerRadialChainResidual D central (-column) q v f (-c) p =
      innerRadialChainResidual D central column q v f c p := by
  apply LinearMap.ext
  intro r
  by_cases hp : p = central
  · simp only [innerRadialChainResidual, if_pos hp, innerRadialWeakResidual_apply,
      inner_neg_left]
    ring
  · simp only [innerRadialChainResidual, if_neg hp, innerRadialWeakResidual_apply,
      inner_zero_left, mul_zero]

/-- The physical outgoing flux is unchanged as well: each summand is
the same energy residual paired with the same actual affine lift. -/
theorem innerRadialChainFlux_scalarSign
    (q : Fin (n + 1) → InnerRadialH1Pair D)
    (v f : Fin (n + 1) → RadialModeL2 D) (c : ℝ) :
    innerRadialChainFlux D hw G central (-column) q v f (-c) =
      innerRadialChainFlux D hw G central column q v f c := by
  have hres :
      innerRadialChainResidual D central (-column) q v f (-c) =
        innerRadialChainResidual D central column q v f c :=
    funext (fun p => innerRadialChainResidual_scalarSign D central column q v f c p)
  unfold innerRadialChainFlux
  rw [hres]

/-- Both the central scalar and its source row change sign. All
physical value, gradient, potential, and boundary coordinates stay the
same. This includes the scalar-zero unbordered modes. -/
theorem innerRadialChainWeakGraph_scalarSign_iff
    (q : Fin (n + 1) → InnerRadialH1Pair D)
    (v f : Fin (n + 1) → RadialModeL2 D) (c d : ℝ) :
    InnerRadialChainWeakGraph D hw G bordered j central (-column) q v f (-c) (-d) ↔
      InnerRadialChainWeakGraph D hw G bordered j central column q v f c d := by
  cases bordered <;>
    simp only [InnerRadialChainWeakGraph, innerRadialChainResidual_scalarSign,
      Bool.false_eq_true, ite_false, ite_true, inner_neg_left, neg_inj, neg_eq_zero]

end WeakEquation

section SupportedCoordinates

variable (D : ReferenceData) {n : ℕ} (G : InnerRadialChainGeometry D n)
  (bordered : Bool)

local notation "H" => InnerRadialPhysicalSource D G bordered
local notation "J" =>
  innerSupportedScalarSign (radialHilbertMeasure D) (innerRadialChainRegion D G) bordered

/-- Physical forcing is the actual field projection, so it is
unchanged by reflection of the sole scalar coordinate. -/
theorem innerRadialPhysicalForcing_scalarSign (F : H) :
    innerRadialPhysicalForcing D G bordered (J F) =
      innerRadialPhysicalForcing D G bordered F := by
  funext p
  simp only [innerRadialPhysicalForcing_apply, innerSupportedScalarSign_fst]

theorem innerRadialPhysicalRow_scalarSign (F : H) :
    innerRadialPhysicalRowLinear D G bordered (J F) =
      -innerRadialPhysicalRowLinear D G bordered F := by
  simp only [innerRadialPhysicalRowLinear_apply, innerSupportedScalarSign_snd]

end SupportedCoordinates

section PhysicalGraph

variable (D : ReferenceData) (hw : Continuous D.w) {n : ℕ}
  (G : InnerRadialChainGeometry D n) (bordered : Bool) (j : ℝ)
  (central : Fin (n + 1)) (column : RadialModeL2 D)

local notation "H" => InnerRadialPhysicalSource D G bordered
local notation "J" =>
  innerSupportedScalarSign (radialHilbertMeasure D) (innerRadialChainRegion D G) bordered

/-- The sign change acts on an actual weak solution, including its
closed physical domain, scalar row, and all matched tests. -/
theorem innerRadialPhysicalWeakGraph_scalarSign {u F : H}
    (h : InnerRadialPhysicalWeakGraph D hw G bordered j central column u F) :
    InnerRadialPhysicalWeakGraph D hw G bordered j central (-column) (J u) (J F) := by
  obtain ⟨q, v, c, hu, hg⟩ :=
    (innerRadialPhysicalWeakGraph_iff D hw G bordered j central column u F).mp h
  apply (innerRadialPhysicalWeakGraph_iff D hw G bordered j central (-column)
    (J u) (J F)).mpr
  refine ⟨q, v, -c, ?_, ?_⟩
  · have hf := congrArg (fun z : InnerBorderL2 (radialHilbertMeasure D) => z.fst) hu
    have hc := congrArg (fun z : InnerBorderL2 (radialHilbertMeasure D) => z.snd) hu
    simp only [WithLp.toLp_fst] at hf
    simp only [WithLp.toLp_snd] at hc
    rw [innerSupportedScalarSign_apply_val, hf, hc]
  · rw [innerRadialPhysicalForcing_scalarSign, innerRadialPhysicalRow_scalarSign]
    exact (innerRadialChainWeakGraph_scalarSign_iff D hw G bordered j central column
      q v (innerRadialPhysicalForcing D G bordered F) c
      (innerRadialPhysicalRowLinear D G bordered F)).mpr hg

/-- The two sign conventions define exactly isometrically conjugate
physical graphs, in both directions. -/
theorem innerRadialPhysicalWeakGraph_scalarSign_iff (u F : H) :
    InnerRadialPhysicalWeakGraph D hw G bordered j central (-column) (J u) (J F) ↔
      InnerRadialPhysicalWeakGraph D hw G bordered j central column u F := by
  constructor
  · intro h
    have h' := innerRadialPhysicalWeakGraph_scalarSign D hw G bordered j central
      (-column) h
    simpa only [neg_neg,
      innerSupportedScalarSign_involutive (radialHilbertMeasure D)
        (innerRadialChainRegion D G) bordered u,
      innerSupportedScalarSign_involutive (radialHilbertMeasure D)
        (innerRadialChainRegion D G) bordered F] using h'
  · exact innerRadialPhysicalWeakGraph_scalarSign D hw G bordered j central column

/-- Equivalently, a solution in the manuscript convention is obtained
by applying the same involution to the original source and solution. -/
theorem innerRadialPhysicalWeakGraph_negColumn_iff (u F : H) :
    InnerRadialPhysicalWeakGraph D hw G bordered j central (-column) u F ↔
      InnerRadialPhysicalWeakGraph D hw G bordered j central column (J u) (J F) := by
  simpa only [
    innerSupportedScalarSign_involutive (radialHilbertMeasure D)
      (innerRadialChainRegion D G) bordered u,
    innerSupportedScalarSign_involutive (radialHilbertMeasure D)
      (innerRadialChainRegion D G) bordered F] using
    innerRadialPhysicalWeakGraph_scalarSign_iff D hw G bordered j central column (J u) (J F)

end PhysicalGraph

/-- The one inner inverse in the manuscript's negative-column and
negative-row convention. -/
def innerRadialScalarSignInverse (D : ReferenceData) {n : ℕ}
    (G : InnerRadialChainGeometry D n) (bordered : Bool)
    (A : InnerRadialPhysicalSource D G bordered →L[ℝ]
      InnerRadialPhysicalSource D G bordered) :
    InnerRadialPhysicalSource D G bordered →L[ℝ]
      InnerRadialPhysicalSource D G bordered :=
  let J := innerSupportedScalarSign (radialHilbertMeasure D) (innerRadialChainRegion D G) bordered
  (J : InnerRadialPhysicalSource D G bordered →L[ℝ]
    InnerRadialPhysicalSource D G bordered) ∘L A ∘L
    (J : InnerRadialPhysicalSource D G bordered →L[ℝ]
      InnerRadialPhysicalSource D G bordered)

section Inverse

variable (D : ReferenceData) (hw : Continuous D.w) {n : ℕ}
  (G : InnerRadialChainGeometry D n) (bordered : Bool) (j : ℝ)
  (central : Fin (n + 1)) (column : RadialModeL2 D)

local notation "H" => InnerRadialPhysicalSource D G bordered
local notation "J" =>
  innerSupportedScalarSign (radialHilbertMeasure D) (innerRadialChainRegion D G) bordered

theorem innerRadialScalarSignInverse_apply (A : H →L[ℝ] H) (F : H) :
    innerRadialScalarSignInverse D G bordered A F = J (A (J F)) := by
  simp only [innerRadialScalarSignInverse, ContinuousLinearMap.comp_apply,
    LinearIsometryEquiv.coe_coe'']

/-- An exact graph characterization gives both inverse identities
after the scalar reflection. There is no new inverse choice. -/
theorem innerRadialScalarSignInverse_graph_iff (A : H →L[ℝ] H)
    (hA : ∀ u F : H,
      InnerRadialPhysicalWeakGraph D hw G bordered j central column u F ↔ A F = u)
    (u F : H) :
    InnerRadialPhysicalWeakGraph D hw G bordered j central (-column) u F ↔
      innerRadialScalarSignInverse D G bordered A F = u := by
  rw [innerRadialPhysicalWeakGraph_negColumn_iff D hw G bordered j central column,
    hA, innerRadialScalarSignInverse_apply]
  constructor
  · intro h
    rw [h, innerSupportedScalarSign_involutive]
  · intro h
    have h' := congrArg J h
    simpa only [
      innerSupportedScalarSign_involutive (radialHilbertMeasure D)
        (innerRadialChainRegion D G) bordered (A (J F))] using h'

theorem innerRadialScalarSignInverse_right_inverse (A : H →L[ℝ] H)
    (hA : ∀ u F : H,
      InnerRadialPhysicalWeakGraph D hw G bordered j central column u F ↔ A F = u)
    (F : H) :
    InnerRadialPhysicalWeakGraph D hw G bordered j central (-column)
      (innerRadialScalarSignInverse D G bordered A F) F :=
  (innerRadialScalarSignInverse_graph_iff D hw G bordered j central column A hA _ F).mpr rfl

theorem innerRadialScalarSignInverse_left_inverse (A : H →L[ℝ] H)
    (hA : ∀ u F : H,
      InnerRadialPhysicalWeakGraph D hw G bordered j central column u F ↔ A F = u)
    {u F : H}
    (hu : InnerRadialPhysicalWeakGraph D hw G bordered j central (-column) u F) :
    innerRadialScalarSignInverse D G bordered A F = u :=
  (innerRadialScalarSignInverse_graph_iff D hw G bordered j central column A hA u F).mp hu

/-- Green symmetry is retained in the actual physical weak graph,
with the negative column and negative row prescribed by the paper. -/
theorem innerRadialScalarSignInverse_selfAdjoint (A : H →L[ℝ] H)
    (hA : ∀ u F : H,
      InnerRadialPhysicalWeakGraph D hw G bordered j central column u F ↔ A F = u) :
    IsSelfAdjoint (innerRadialScalarSignInverse D G bordered A) := by
  apply ContinuousLinearMap.isSelfAdjoint_iff_isSymmetric.mpr
  intro F K
  have h := innerRadialPhysicalWeakGraph_green D hw G bordered j central (-column)
    (innerRadialScalarSignInverse_right_inverse D hw G bordered j central column A hA F)
    (innerRadialScalarSignInverse_right_inverse D hw G bordered j central column A hA K)
  exact (real_inner_comm _ _).trans h.symm

end Inverse

section SchurFormula

variable (D : ReferenceData) {n : ℕ} (G : InnerRadialChainGeometry D n)
  (bordered : Bool)

local notation "H" => InnerRadialPhysicalSource D G bordered
local notation "J" =>
  innerSupportedScalarSign (radialHilbertMeasure D) (innerRadialChainRegion D G) bordered

/-- The exact Schur formula keeps the same interface inverse. Only
the scalar coordinates of the local Dirichlet and Poisson fields are
reflected; the physical fields and all cut values stay unchanged. -/
theorem innerRadialScalarSignInverse_schur
    {B : Type*} [NormedAddCommGroup B] [InnerProductSpace ℝ B] [CompleteSpace B]
    (A D0 : H →L[ℝ] H) (T : B →L[ℝ] H) (R : B →L[ℝ] B)
    (hA : A = D0 + T ∘L R ∘L T.adjoint) :
    innerRadialScalarSignInverse D G bordered A =
      innerRadialScalarSignInverse D G bordered D0 +
        ((J : H →L[ℝ] H) ∘L T) ∘L R ∘L ((J : H →L[ℝ] H) ∘L T).adjoint := by
  rw [hA]
  simp only [innerRadialScalarSignInverse, ContinuousLinearMap.comp_add,
    ContinuousLinearMap.add_comp, ContinuousLinearMap.adjoint_comp,
    (innerSupportedScalarSign_selfAdjoint (radialHilbertMeasure D)
      (innerRadialChainRegion D G) bordered).adjoint_eq,
    ContinuousLinearMap.comp_assoc]

end SchurFormula

end ContinuousFlexibility.Radial
