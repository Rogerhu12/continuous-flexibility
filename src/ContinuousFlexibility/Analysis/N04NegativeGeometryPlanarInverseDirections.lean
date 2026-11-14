module

public import ContinuousFlexibility.Analysis.N04NegativeGeometryPlanarParameterInverse
public import ContinuousFlexibility.Analysis.N04NegativeGeometryImplicitDirections
public import ContinuousFlexibility.Analysis.CircleSmoothDirectionsOperations
public import Mathlib.Analysis.Calculus.ContDiff.Operations

/-!
# The genuine joint tower of a parameterized planar inverse

The forward tower supplies the actual spatial differential and its joint
operator continuity. Nonzero Jacobian gives its continuous inverse.
The ordinary implicit theorem on finite affine slices and the actual
right-inverse equation then identify all implicit jet candidates.
The parameter space retains its given topology throughout.
-/

@[expose] public section

noncomputable section

namespace ContinuousFlexibility.Analysis

open Set Filter ContinuousFlexibility.Statements
open scoped Topology ContDiff

section SpatialDifferential

variable {E Y : Type*}
  [TopologicalSpace E] [AddCommGroup E] [Module ℝ E]
  [IsTopologicalAddGroup E] [ContinuousSMul ℝ E]
  [NormedAddCommGroup Y] [NormedSpace ℝ Y] [FiniteDimensional ℝ Y]
  {U : Set E} {V : Set Y} {F : E × Y → Y}

/-- The actual first tower jet restricted to the finite spatial factor. -/
def n04NegativeGeometry_spatialDifferential
    (J : SmoothDirections (U ×ˢ V) F) (z : E × Y) : Y →L[ℝ] Y :=
  ((ContinuousMultilinearMap.ofSubsingleton ℝ (E × Y) Y (0 : Fin 1)).symm
    (J.D 1 z)).comp (ContinuousLinearMap.inr ℝ E Y)

@[simp] theorem n04NegativeGeometry_spatialDifferential_apply
    (J : SmoothDirections (U ×ˢ V) F) (z : E × Y) (y : Y) :
    n04NegativeGeometry_spatialDifferential J z y =
      J.D 1 z (fun _ : Fin 1 => (0, y)) := by
  simp only [n04NegativeGeometry_spatialDifferential, ContinuousLinearMap.comp_apply,
    ContinuousLinearMap.inr_apply, ContinuousMultilinearMap.ofSubsingleton_symm_apply_apply]

/-- Finite spatial restriction identifies the tower differential with
the literal ordinary Fréchet differential. -/
theorem n04NegativeGeometry_spatialDifferential_eq_fderiv
    (J : SmoothDirections (U ×ˢ V) F) {z : E × Y} (hz : z ∈ U ×ˢ V) :
    n04NegativeGeometry_spatialDifferential J z =
      fderiv ℝ (fun y => F (z.1, y)) z.2 := by
  apply ContinuousLinearMap.ext
  intro y
  have hpoint : (z.1, (0 : Y)) + (ContinuousLinearMap.inr ℝ E Y) z.2 ∈ U ×ˢ V := by
    simpa only [ContinuousLinearMap.inr_apply, Prod.mk_add_mk, add_zero, zero_add] using hz
  have h := smoothDirections_iteratedFDeriv_finiteAffine
    J (z.1, (0 : Y)) (ContinuousLinearMap.inr ℝ E Y) 1 hpoint (fun _ : Fin 1 => y)
  simpa only [n04NegativeGeometry_spatialDifferential_apply,
    ContinuousLinearMap.inr_apply, Prod.mk_add_mk, add_zero, zero_add,
    Prod.eta, iteratedFDeriv_one_apply] using h.symm

/-- Finite-dimensionality is used only for the spatial operator norm;
the parameter space need not be normable. -/
theorem n04NegativeGeometry_spatialDifferential_continuousOn
    (J : SmoothDirections (U ×ˢ V) F) :
    ContinuousOn (n04NegativeGeometry_spatialDifferential J) (U ×ˢ V) := by
  apply continuousOn_clm_apply.mpr
  intro y
  simpa only [n04NegativeGeometry_spatialDifferential_apply, Function.comp_def, id_eq] using
    (J.continuous 1).comp
      (continuous_id.prodMk continuous_const).continuousOn
      (fun _ hz => ⟨hz, mem_univ (fun _ : Fin 1 => ((0 : E), y))⟩)

end SpatialDifferential

section PlanarInverse

variable {E : Type*}
  [TopologicalSpace E] [AddCommGroup E] [Module ℝ E]
  [IsTopologicalAddGroup E] [ContinuousSMul ℝ E]
  {U : Set E} {V W : Set PolarPoint} {F G : E × PolarPoint → PolarPoint}

private theorem spatialDifferential_isInvertible
    (J : SmoothDirections (U ×ˢ V) F) {z : E × PolarPoint} (hz : z ∈ U ×ˢ V)
    (hJac : planeJacobian (fun y => F (z.1, y)) z.2 ≠ 0) :
    (n04NegativeGeometry_spatialDifferential J z).IsInvertible := by
  rw [n04NegativeGeometry_spatialDifferential_eq_fderiv J hz]
  let A := fderiv ℝ (fun y => F (z.1, y)) z.2
  have hd : A.det ≠ 0 := by
    simpa only [A, planeJacobian_eq_fderiv_det] using hJac
  refine ⟨A.toContinuousLinearEquivOfDetNeZero hd, ?_⟩
  simp only [ContinuousLinearMap.coe_toContinuousLinearEquivOfDetNeZero, A]

private theorem inverse_contDiffAt_jointAffine
    (J : SmoothDirections (U ×ˢ V) F)
    (hU : IsOpen U) (hV : IsOpen V) (hW : IsOpen W)
    (hJac : ∀ z ∈ U ×ˢ V, planeJacobian (fun y => F (z.1, y)) z.2 ≠ 0)
    (hInj : ∀ x ∈ U, InjOn (fun y => F (x, y)) V)
    (hMaps : MapsTo G (U ×ˢ W) V)
    (hRight : ∀ z ∈ U ×ˢ W, F (z.1, G z) = z.2)
    (m : ℕ) (z : E × PolarPoint) (hz : z ∈ U ×ˢ W)
    (L : (Fin m → ℝ) →L[ℝ] E × PolarPoint) :
    ContDiffAt ℝ ∞ (fun q => G (z + L q)) 0 := by
  let Lp := (ContinuousLinearMap.fst ℝ E PolarPoint).comp L
  let Ly := (ContinuousLinearMap.snd ℝ E PolarPoint).comp L
  have hs := n04NegativeGeometry_inverse_contDiffOn_finiteAffine
    J hU hV hW hJac hInj hMaps hRight z.1 Lp
  have h0 : ((0 : Fin m → ℝ), z.2) ∈
      (((fun p => z.1 + Lp p) ⁻¹' U) ×ˢ W) := by
    simpa only [mem_prod, mem_preimage, map_zero, add_zero] using hz
  have hO : IsOpen (((fun p => z.1 + Lp p) ⁻¹' U) ×ˢ W) :=
    (hU.preimage (continuous_const.add Lp.continuous)).prod hW
  have hpath : ContDiffAt ℝ ∞ (fun q : Fin m → ℝ => (q, z.2 + Ly q)) 0 :=
    contDiffAt_id.prodMk (contDiffAt_const.add Ly.contDiff.contDiffAt)
  have hp0 : (fun q : Fin m → ℝ => (q, z.2 + Ly q)) 0 = (0, z.2) := by
    simp only [map_zero, add_zero]
  have hlocal : ContDiffAt ℝ ∞
      (fun p : (Fin m → ℝ) × PolarPoint => G (z.1 + Lp p.1, p.2))
      ((fun q : Fin m → ℝ => (q, z.2 + Ly q)) 0) :=
    hp0.symm ▸ hs.contDiffAt (hO.mem_nhds h0)
  have hcomposed := hlocal.comp (0 : Fin m → ℝ) hpath
  have hc : ContDiffAt ℝ ∞
      (fun q : Fin m → ℝ => G (z.1 + Lp q, z.2 + Ly q)) 0 := by
    simpa only [Function.comp_def] using hcomposed
  have heq : (fun q : Fin m → ℝ => G (z.1 + Lp q, z.2 + Ly q)) =
      (fun q => G (z + L q)) := by
    funext q
    rfl
  exact heq ▸ hc

/-- The actual two-dimensional inverse has one joint parameter and
spatial tower. Its only continuity input is the actual inverse value;
all parameter derivatives are consequences. -/
def n04NegativeGeometry_parameterized_planar_inverse_jointTower
    (J : SmoothDirections (U ×ˢ V) F)
    (hU : IsOpen U) (hV : IsOpen V) (hW : IsOpen W)
    (hJac : ∀ z ∈ U ×ˢ V, planeJacobian (fun y => F (z.1, y)) z.2 ≠ 0)
    (hInj : ∀ x ∈ U, InjOn (fun y => F (x, y)) V)
    (hMaps : MapsTo G (U ×ˢ W) V)
    (hRight : ∀ z ∈ U ×ˢ W, F (z.1, G z) = z.2)
    (hG : ContinuousOn G (U ×ˢ W)) : SmoothDirections (U ×ˢ W) G := by
  let Z := E × PolarPoint
  let H : Z × PolarPoint → PolarPoint := fun q => F (q.1.1, q.2) - q.1.2
  let L₁ : (Z × PolarPoint) →L[ℝ] (E × PolarPoint) :=
    ((ContinuousLinearMap.fst ℝ E PolarPoint).comp
      (ContinuousLinearMap.fst ℝ Z PolarPoint)).prod
      (ContinuousLinearMap.snd ℝ Z PolarPoint)
  let L₂ : (Z × PolarPoint) →L[ℝ] PolarPoint :=
    (ContinuousLinearMap.snd ℝ E PolarPoint).comp
      (ContinuousLinearMap.fst ℝ Z PolarPoint)
  have hO : IsOpen ((U ×ˢ W) ×ˢ V) := (hU.prod hW).prod hV
  let Jpair := smoothDirectionsProd
    (J.compLinear L₁ hO (fun q hq => ⟨hq.1.1, hq.2⟩))
    (smoothDirectionsLinearOn L₂ hO)
  let JH : SmoothDirections ((U ×ˢ W) ×ˢ V) H :=
    smoothDirections_contDiff_comp Jpair isOpen_univ
      (contDiff_fst.sub contDiff_snd).contDiffOn (fun _ _ => mem_univ _)
  let D : Z → PolarPoint →L[ℝ] PolarPoint :=
    fun z => n04NegativeGeometry_spatialDifferential J (z.1, G z)
  let A : Z → PolarPoint →L[ℝ] PolarPoint := fun z => (D z).inverse
  have hD : ContinuousOn D (U ×ˢ W) :=
    (n04NegativeGeometry_spatialDifferential_continuousOn J).comp
      (continuous_fst.continuousOn.prodMk hG) (fun z hz => ⟨hz.1, hMaps hz⟩)
  have hDi (z : Z) (hz : z ∈ U ×ˢ W) : (D z).IsInvertible :=
    spatialDifferential_isInvertible J ⟨hz.1, hMaps hz⟩
      (hJac (z.1, G z) ⟨hz.1, hMaps hz⟩)
  have hInv : ContinuousOn
      (ContinuousLinearMap.inverse :
        (PolarPoint →L[ℝ] PolarPoint) → PolarPoint →L[ℝ] PolarPoint)
      {B | B.IsInvertible} := by
    intro B hB
    have hb : ContDiffAt ℝ ∞ ContinuousLinearMap.inverse B := hB.contDiffAt_map_inverse
    exact hb.continuousAt.continuousWithinAt
  have hA : ContinuousOn A (U ×ˢ W) := hInv.comp hD (fun z hz => hDi z hz)
  have hsp (z : Z) (hz : z ∈ U ×ˢ W) :
      n04NegativeGeometry_spatialDifferential JH (z, G z) = D z := by
    change n04NegativeGeometry_spatialDifferential JH (z, G z) =
      n04NegativeGeometry_spatialDifferential J (z.1, G z)
    rw [n04NegativeGeometry_spatialDifferential_eq_fderiv JH
      (z := (z, G z)) ⟨hz, hMaps hz⟩]
    rw [n04NegativeGeometry_spatialDifferential_eq_fderiv J
      (z := (z.1, G z)) ⟨hz.1, hMaps hz⟩]
    exact fderiv_sub_const z.2
  apply n04NegativeGeometry_implicitSmoothDirections JH (hU.prod hW)
    hG hMaps A hA
  · intro z hz
    change F (z.1, G z) - z.2 = 0
    rw [hRight z hz, sub_self]
  · intro z hz y
    rw [← n04NegativeGeometry_spatialDifferential_apply JH, hsp z hz]
    exact (hDi z hz).inverse_apply_self y
  · exact inverse_contDiffAt_jointAffine J hU hV hW hJac hInj hMaps hRight

end PlanarInverse

end ContinuousFlexibility.Analysis
