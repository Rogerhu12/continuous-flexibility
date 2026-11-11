import ContinuousFlexibility.Radial.InnerAdmissibleSource
import ContinuousFlexibility.Radial.InnerRadialH1Support
import ContinuousFlexibility.Radial.InnerRadialLocalRealization
import ContinuousFlexibility.Radial.InnerBorderTransport

/-!
# The actual supported inner source and physical field realization

The source is a closed subspace of the physical L²/scalar product:
its field is supported in the genuine union of the pieces, and its
scalar is zero in unbordered modes. Local forcing is actual orthogonal
restriction in the same measure.

A broken weak field is realized by the sum of its supported value
coordinates and its one central scalar. The defining domain and row
conditions prove that this field belongs to the same source space.
-/

noncomputable section

namespace ContinuousFlexibility.Radial

open Set MeasureTheory Filter ContinuousFlexibility.Statements
open scoped InnerProductSpace BigOperators

variable (D : ReferenceData) {n : ℕ} (G : InnerRadialChainGeometry D n)

/-- The actual inner region, ignoring only the finite internal cuts. -/
def innerRadialChainRegion : Set ℝ := ⋃ p, Ioo (G.left p) (G.right p)

theorem innerRadialChainRegion_measurable :
    MeasurableSet (innerRadialChainRegion D G) :=
  MeasurableSet.iUnion (fun _ => measurableSet_Ioo)

/-- The same physical measure, true inner support, and scalar-zero
constraint in every unbordered mode. -/
abbrev InnerRadialPhysicalSource (bordered : Bool) :=
  ↥(innerSupportedAdmissibleSource (radialHilbertMeasure D)
    (innerRadialChainRegion D G) bordered)

def innerRadialPhysicalInclusion (bordered : Bool) :
    InnerRadialPhysicalSource D G bordered →ₗᵢ[ℝ]
      InnerBorderL2 (radialHilbertMeasure D) :=
  (innerSupportedAdmissibleSource (radialHilbertMeasure D)
    (innerRadialChainRegion D G) bordered).toSubmodule.subtypeₗᵢ

@[simp] theorem innerRadialPhysicalInclusion_apply (bordered : Bool)
    (F : InnerRadialPhysicalSource D G bordered) :
    innerRadialPhysicalInclusion D G bordered F = F.val := by
  simp only [innerRadialPhysicalInclusion, Submodule.coe_subtypeₗᵢ,
    Submodule.subtype_apply]

def innerRadialPhysicalValue (bordered : Bool) :
    InnerRadialPhysicalSource D G bordered →L[ℝ] RadialModeL2 D :=
  (WithLp.fstL 2 ℝ (RadialModeL2 D) ℝ).comp
    (innerRadialPhysicalInclusion D G bordered).toContinuousLinearMap

def innerRadialPhysicalRow (bordered : Bool) :
    InnerRadialPhysicalSource D G bordered →L[ℝ] ℝ :=
  (WithLp.sndL 2 ℝ (RadialModeL2 D) ℝ).comp
    (innerRadialPhysicalInclusion D G bordered).toContinuousLinearMap

@[simp] theorem innerRadialPhysicalValue_apply (bordered : Bool)
    (F : InnerRadialPhysicalSource D G bordered) :
    innerRadialPhysicalValue D G bordered F = F.val.fst := by
  simp only [innerRadialPhysicalValue, ContinuousLinearMap.comp_apply,
    LinearIsometry.coe_toContinuousLinearMap, innerRadialPhysicalInclusion_apply,
    WithLp.fstL_apply]

@[simp] theorem innerRadialPhysicalRow_apply (bordered : Bool)
    (F : InnerRadialPhysicalSource D G bordered) :
    innerRadialPhysicalRow D G bordered F = F.val.snd := by
  simp only [innerRadialPhysicalRow, ContinuousLinearMap.comp_apply,
    LinearIsometry.coe_toContinuousLinearMap, innerRadialPhysicalInclusion_apply,
    WithLp.sndL_apply]

theorem innerRadialPhysicalRow_unbordered
    (F : InnerRadialPhysicalSource D G false) :
    innerRadialPhysicalRow D G false F = 0 := by
  have h := (mem_innerSupportedAdmissibleSource (radialHilbertMeasure D)
    (innerRadialChainRegion D G) false F.val).mp F.property
  simpa only [innerRadialPhysicalRow_apply, Bool.false_eq_true, false_or] using h.1

/-- Actual orthogonal piece restrictions of the physical source. -/
def innerRadialPhysicalForcing (bordered : Bool) :
    InnerRadialPhysicalSource D G bordered →ₗ[ℝ]
      (Fin (n + 1) → RadialModeL2 D) :=
  LinearMap.pi (fun p =>
    (innerL2PieceProjection (radialHilbertMeasure D)
      (Ioo (G.left p) (G.right p))).toLinearMap.comp
        (innerRadialPhysicalValue D G bordered).toLinearMap)

@[simp] theorem innerRadialPhysicalForcing_apply (bordered : Bool)
    (F : InnerRadialPhysicalSource D G bordered) (p : Fin (n + 1)) :
    innerRadialPhysicalForcing D G bordered F p =
      innerL2PieceProjection (radialHilbertMeasure D)
        (Ioo (G.left p) (G.right p)) F.val.fst := by
  simp only [innerRadialPhysicalForcing, LinearMap.pi_apply, LinearMap.comp_apply,
    ContinuousLinearMap.coe_coe, innerRadialPhysicalValue_apply]

section PhysicalRealization

variable (hw : Continuous D.w) (bordered : Bool) (j : ℝ)
  (central : Fin (n + 1)) (column : RadialModeL2 D)

local notation "H" => InnerRadialPhysicalSource D G bordered
local notation "forcing" => innerRadialPhysicalForcing D G bordered
local notation "rowSource" => (innerRadialPhysicalRow D G bordered).toLinearMap
local notation "W" =>
  ↥(innerRadialBrokenSpace D hw G forcing rowSource bordered j central column)

/-- Sum the actual value fields and retain the single central scalar. -/
def innerRadialBrokenPhysicalCoordinates :
    InnerRadialBrokenData D n H →ₗ[ℝ] (RadialModeL2 D × ℝ) where
  toFun x := (∑ p, (x.1.1 p).1, x.1.2.2)
  map_add' x y := by
    simp only [Prod.fst_add, Prod.snd_add, Pi.add_apply, Finset.sum_add_distrib,
      Prod.mk_add_mk]
  map_smul' c x := by
    simp only [Prod.smul_fst, Prod.smul_snd, Pi.smul_apply, RingHom.id_apply,
      Finset.smul_sum, Prod.smul_mk]

@[simp] theorem innerRadialBrokenPhysicalCoordinates_apply
    (x : InnerRadialBrokenData D n H) :
    innerRadialBrokenPhysicalCoordinates D G bordered x =
      (∑ p, (x.1.1 p).1, x.1.2.2) := rfl

def innerRadialBrokenPhysicalField :
    InnerRadialBrokenData D n H →ₗ[ℝ] InnerBorderL2 (radialHilbertMeasure D) :=
  (innerBorderMaxEquiv (radialHilbertMeasure D)).symm.toLinearMap.comp
    (innerRadialBrokenPhysicalCoordinates D G bordered)

@[simp] theorem innerRadialBrokenPhysicalField_apply
    (x : InnerRadialBrokenData D n H) :
    innerRadialBrokenPhysicalField D G bordered x =
      WithLp.toLp 2 (∑ p, (x.1.1 p).1, x.1.2.2) := by
  rw [innerRadialBrokenPhysicalField, LinearMap.comp_apply,
    innerRadialBrokenPhysicalCoordinates_apply]
  exact innerBorderMaxEquiv_symm_apply (radialHilbertMeasure D) _

theorem innerRadialBrokenPhysicalField_mem (x : W) :
    innerRadialBrokenPhysicalField D G bordered x.val ∈
      innerSupportedAdmissibleSource (radialHilbertMeasure D)
        (innerRadialChainRegion D G) bordered := by
  have hx := (mem_innerRadialBrokenSpace D hw G forcing rowSource bordered j
    central column x.val).mp x.property
  obtain ⟨ξ, hξ⟩ := (innerRadialChainDomain_trace_iff D hw G x.val.1.1).mp hx.1
  have hs (p : Fin (n + 1)) :
      ∀ᵐ r ∂radialHilbertMeasure D,
        r ∉ Ioo (G.left p) (G.right p) → (x.val.1.1 p).1 r = 0 :=
    innerRadialH1Domain_supported D hw (G.left_pos p) (G.in_core p)
      (G.weight_pos p) (hξ p).1
  apply (mem_innerSupportedAdmissibleSource (radialHilbertMeasure D)
    (innerRadialChainRegion D G) bordered _).mpr
  rw [innerRadialBrokenPhysicalField_apply, WithLp.toLp_fst, WithLp.toLp_snd]
  constructor
  · cases bordered with
    | false =>
      right
      simpa only [Bool.false_eq_true, ite_false] using hx.2.2.1.1
    | true => exact Or.inl rfl
  · apply innerL2PieceProjection_eq_self _ _ (innerRadialChainRegion_measurable D G)
    filter_upwards [Lp.coeFn_fun_finsetSum Finset.univ (fun p => (x.val.1.1 p).1),
      ae_all_iff.mpr hs] with r hsum hr
    intro hout
    rw [hsum]
    apply Finset.sum_eq_zero
    intro p _
    exact hr p (fun hp => hout (mem_iUnion.mpr ⟨p, hp⟩))

/-- The actual physical field, in the genuine supported admissible
Hilbert space. Membership follows from the weak domain and scalar row. -/
def innerRadialPhysicalRealization : W →ₗ[ℝ] H where
  toFun x := ⟨innerRadialBrokenPhysicalField D G bordered x.val,
    innerRadialBrokenPhysicalField_mem D G hw bordered j central column x⟩
  map_add' x y := by
    apply Subtype.ext
    exact map_add (innerRadialBrokenPhysicalField D G bordered) x.val y.val
  map_smul' c x := by
    apply Subtype.ext
    exact map_smul (innerRadialBrokenPhysicalField D G bordered) c x.val

@[simp] theorem innerRadialPhysicalRealization_apply (x : W) :
    (innerRadialPhysicalRealization D G hw bordered j central column x).val =
      WithLp.toLp 2 (∑ p, (x.val.1.1 p).1, x.val.1.2.2) :=
  innerRadialBrokenPhysicalField_apply D G bordered x.val

end PhysicalRealization

end ContinuousFlexibility.Radial
