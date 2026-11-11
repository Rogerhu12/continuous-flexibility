import ContinuousFlexibility.Radial.PositiveBufferEnergyForm
import ContinuousFlexibility.Radial.PositiveBufferTraceMap

/-!
# The full bordered inverse in its actual energy domain

The full-model graph supplies the genuine weak derivative and weighted
field. This module turns those coordinates into the energy-space element
used by Green's identity. The scalar restriction in the unbordered case is
retained as part of the domain.
-/

noncomputable section

namespace ContinuousFlexibility.Radial

open Set Filter MeasureTheory Real
open ContinuousFlexibility.Statements
open scoped Topology ContDiff InnerProductSpace

/-- Repackaging the frozen three actual coordinates in the Hilbert graph. -/
def positiveBufferEnergyOfLift {V : ℝ → ℝ} (u d q : RadialL2)
    (h : (u, d, q) ∈ SchrodingerEnergyLift V) : PositiveBufferEnergy V :=
  ⟨WithLp.toLp 2 ![u, d, q], h⟩

@[simp] theorem positiveBufferEnergyOfLift_base {V : ℝ → ℝ} (u d q : RadialL2)
    (h : (u, d, q) ∈ SchrodingerEnergyLift V) :
    positiveBufferEnergyCoordinate V 0 (positiveBufferEnergyOfLift u d q h) = u := rfl

theorem positiveBuffer_exists_energy_of_weak {V : ℝ → ℝ}
    (hreal : ActualClosedFormRealization V) {u f : RadialL2}
    (hu : WeakSchrodingerGraph V u f) :
    ∃ e : PositiveBufferEnergy V, positiveBufferEnergyCoordinate V 0 e = u := by
  obtain ⟨d, q, h, _⟩ := (hreal.2.2.2 u f).mp hu
  exact ⟨positiveBufferEnergyOfLift u d q h, rfl⟩

/-- A weak graph solution satisfies the actual signed form identity against
every energy test, with no regularity hypothesis on that test. -/
theorem positiveBufferEnergyForm_of_weak {V : ℝ → ℝ}
    (hreal : ActualClosedFormRealization V) (hV : Continuous V)
    {u : PositiveBufferEnergy V} {f : RadialL2}
    (hu : WeakSchrodingerGraph V (positiveBufferEnergyCoordinate V 0 u) f)
    (v : PositiveBufferEnergy V) :
    positiveBufferEnergyForm V hV u v = inner ℝ f (positiveBufferEnergyCoordinate V 0 v) := by
  obtain ⟨d, q, h, hform⟩ := (hreal.2.2.2 _ f).mp hu
  have hdu : positiveBufferEnergyCoordinate V 1 u = d :=
    weakRadialDerivative_unique (positiveBufferEnergy_derivative_weak V u) h.1
  have hv : (positiveBufferEnergyCoordinate V 0 v, positiveBufferEnergyCoordinate V 1 v,
      positiveBufferEnergyCoordinate V 2 v) ∈ SchrodingerEnergyLift V := v.property
  rw [positiveBufferEnergyForm_eq_integral, hdu]
  exact (hform _ hv).2.symm

/-- The actual scalar constraint is a linear subspace of the energy pair. -/
def positiveBufferBorderedEnergySpace (V : ℝ → ℝ) (bordered : Bool) :
    Submodule ℝ (PositiveBufferEnergy V × ℝ) where
  carrier := {U | bordered = false → U.2 = 0}
  zero_mem' := by intro _; rfl
  add_mem' := by
    intro U W hU hW hb
    change U.2 + W.2 = 0
    rw [hU hb, hW hb, add_zero]
  smul_mem' := by
    intro a U hU hb
    change a * U.2 = 0
    rw [hU hb, mul_zero]

abbrev PositiveBufferBorderedEnergy (V : ℝ → ℝ) (bordered : Bool) : Type :=
  positiveBufferBorderedEnergySpace V bordered

def positiveBufferBorderedField (V : ℝ → ℝ) (bordered : Bool) :
    PositiveBufferBorderedEnergy V bordered →L[ℝ] PositiveBufferEnergy V :=
  (ContinuousLinearMap.fst ℝ (PositiveBufferEnergy V) ℝ).comp
    (positiveBufferBorderedEnergySpace V bordered).subtypeL

def positiveBufferBorderedScalar (V : ℝ → ℝ) (bordered : Bool) :
    PositiveBufferBorderedEnergy V bordered →L[ℝ] ℝ :=
  (ContinuousLinearMap.snd ℝ (PositiveBufferEnergy V) ℝ).comp
    (positiveBufferBorderedEnergySpace V bordered).subtypeL

@[simp] theorem positiveBufferBorderedField_apply (V : ℝ → ℝ) (bordered : Bool)
    (U : PositiveBufferBorderedEnergy V bordered) : positiveBufferBorderedField V bordered U = U.val.1 := rfl

@[simp] theorem positiveBufferBorderedScalar_apply (V : ℝ → ℝ) (bordered : Bool)
    (U : PositiveBufferBorderedEnergy V bordered) : positiveBufferBorderedScalar V bordered U = U.val.2 := rfl

def positiveBufferBorderedState (V : ℝ → ℝ) (bordered : Bool) :
    PositiveBufferBorderedEnergy V bordered →L[ℝ] (RadialL2 × ℝ) :=
  ((positiveBufferEnergyCoordinate V 0).comp (positiveBufferBorderedField V bordered)).prod
    (positiveBufferBorderedScalar V bordered)

@[simp] theorem positiveBufferBorderedState_apply (V : ℝ → ℝ) (bordered : Bool)
    (U : PositiveBufferBorderedEnergy V bordered) :
    positiveBufferBorderedState V bordered U =
      (positiveBufferEnergyCoordinate V 0 U.val.1, U.val.2) := rfl

theorem positiveBufferBorderedState_injective (V : ℝ → ℝ) (bordered : Bool) :
    Function.Injective (positiveBufferBorderedState V bordered) := by
  intro U W h
  apply Subtype.ext
  apply Prod.ext
  · exact positiveBufferEnergy_base_injective V (congrArg Prod.fst h)
  · exact congrArg Prod.snd h

/-- The pairing of the frozen `L² × ℝ` space does not presume an inner
product for its max norm. -/
def positiveBufferStatePairing : (RadialL2 × ℝ) →ₗ[ℝ] (RadialL2 × ℝ) →ₗ[ℝ] ℝ where
  toFun U :=
    { toFun := fun F => inner ℝ U.1 F.1 + U.2 * F.2
      map_add' := by
        intro F K
        simp only [Prod.fst_add, Prod.snd_add, inner_add_right]
        ring
      map_smul' := by
        intro a F
        simp only [Prod.fst_smul, Prod.snd_smul, inner_smul_right, smul_eq_mul]
        ring }
  map_add' := by
    intro U W
    ext F
    simp only [LinearMap.add_apply, Prod.fst_add, Prod.snd_add, inner_add_left]
    ring
  map_smul' := by
    intro a U
    ext F
    simp only [LinearMap.smul_apply, Prod.fst_smul, Prod.snd_smul,
      inner_smul_left, conj_trivial, smul_eq_mul]
    ring

@[simp] theorem positiveBufferStatePairing_apply (U F : RadialL2 × ℝ) :
    positiveBufferStatePairing U F = inner ℝ U.1 F.1 + U.2 * F.2 := rfl

theorem positiveBufferStatePairing_self_eq_zero (U : RadialL2 × ℝ)
    (h : positiveBufferStatePairing U U = 0) : U = 0 := by
  rw [positiveBufferStatePairing_apply, real_inner_self_eq_norm_sq] at h
  have h1 : ‖U.1‖ = 0 := by nlinarith [sq_nonneg ‖U.1‖, sq_nonneg U.2]
  have h2 : U.2 = 0 := by nlinarith [sq_nonneg ‖U.1‖, sq_nonneg U.2]
  exact Prod.ext (norm_eq_zero.mp h1) h2

theorem positiveBufferStatePairing_symm (U F : RadialL2 × ℝ) :
    positiveBufferStatePairing U F = positiveBufferStatePairing F U := by
  simp only [positiveBufferStatePairing_apply, real_inner_comm, mul_comm]

/-- The physical bordered form, on exactly the admissible energy pairs. -/
def positiveBufferBorderedForm (V : ℝ → ℝ) (hV : Continuous V) (g : RadialL2)
    (bordered : Bool) (U W : PositiveBufferBorderedEnergy V bordered) : ℝ :=
  positiveBufferEnergyForm V hV U.val.1 W.val.1 +
    U.val.2 * inner ℝ g (positiveBufferEnergyCoordinate V 0 W.val.1) +
    W.val.2 * inner ℝ g (positiveBufferEnergyCoordinate V 0 U.val.1)

theorem positiveBufferBorderedForm_symm (V : ℝ → ℝ) (hV : Continuous V) (g : RadialL2)
    (bordered : Bool) (U W : PositiveBufferBorderedEnergy V bordered) :
    positiveBufferBorderedForm V hV g bordered U W =
      positiveBufferBorderedForm V hV g bordered W U := by
  unfold positiveBufferBorderedForm
  rw [positiveBufferEnergyForm_symm V hV U.val.1 W.val.1]
  ring

theorem positiveBufferBorderedForm_of_fullGraph {V : ℝ → ℝ}
    (hreal : ActualClosedFormRealization V) (hV : Continuous V) (g : RadialL2)
    (bordered : Bool) (U : PositiveBufferBorderedEnergy V bordered) (F : RadialL2 × ℝ)
    (hU : BorderedFullGraph V g bordered (positiveBufferBorderedState V bordered U) F)
    (W : PositiveBufferBorderedEnergy V bordered) :
    positiveBufferBorderedForm V hV g bordered U W =
      positiveBufferStatePairing F (positiveBufferBorderedState V bordered W) := by
  cases bordered with
  | false =>
    have hUs := U.property rfl
    have hWs := W.property rfl
    simp only [BorderedFullGraph, Bool.false_eq_true, ite_false,
      positiveBufferBorderedState_apply] at hU
    simp only [positiveBufferBorderedForm, positiveBufferStatePairing_apply,
      positiveBufferBorderedState_apply, hUs, hWs, zero_mul, mul_zero, add_zero]
    exact positiveBufferEnergyForm_of_weak hreal hV hU.1 W.val.1
  | true =>
    simp only [BorderedFullGraph, ite_true, positiveBufferBorderedState_apply] at hU
    have h := positiveBufferEnergyForm_of_weak hreal hV hU.1 W.val.1
    simp only [inner_sub_left, inner_smul_left, conj_trivial] at h
    rw [positiveBufferBorderedForm, positiveBufferStatePairing_apply,
      positiveBufferBorderedState_apply, h, hU.2]
    ring

/-- The physical form is bilinear on the constrained energy domain. -/
def positiveBufferBorderedFormLinear (V : ℝ → ℝ) (hV : Continuous V) (g : RadialL2)
    (bordered : Bool) : PositiveBufferBorderedEnergy V bordered →ₗ[ℝ]
      PositiveBufferBorderedEnergy V bordered →ₗ[ℝ] ℝ :=
  LinearMap.mk₂ ℝ (positiveBufferBorderedForm V hV g bordered)
    (by
      intro U W Z
      simp only [positiveBufferBorderedForm, Submodule.coe_add, Prod.fst_add, Prod.snd_add,
        map_add, ContinuousLinearMap.add_apply, inner_add_right]
      ring)
    (by
      intro a U W
      simp only [positiveBufferBorderedForm, Submodule.coe_smul, Prod.fst_smul, Prod.snd_smul,
        map_smul, ContinuousLinearMap.smul_apply, inner_smul_right, smul_eq_mul]
      ring)
    (by
      intro U W Z
      simp only [positiveBufferBorderedForm, Submodule.coe_add, Prod.fst_add, Prod.snd_add,
        map_add, ContinuousLinearMap.add_apply, inner_add_right]
      ring)
    (by
      intro a U W
      simp only [positiveBufferBorderedForm, Submodule.coe_smul, Prod.fst_smul, Prod.snd_smul,
        map_smul, ContinuousLinearMap.smul_apply, inner_smul_right, smul_eq_mul]
      ring)

@[simp] theorem positiveBufferBorderedFormLinear_apply (V : ℝ → ℝ) (hV : Continuous V)
    (g : RadialL2) (bordered : Bool) (U W : PositiveBufferBorderedEnergy V bordered) :
    positiveBufferBorderedFormLinear V hV g bordered U W =
      positiveBufferBorderedForm V hV g bordered U W :=
  LinearMap.mk₂_apply _ U W

end ContinuousFlexibility.Radial
