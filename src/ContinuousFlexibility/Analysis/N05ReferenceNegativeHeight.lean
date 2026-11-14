module

public import ContinuousFlexibility.Analysis.N05CanonicalGeometryAccess
public import ContinuousFlexibility.Analysis.N05ReferenceNegativeRadial

/-!
# The actual negative reference height is radial

On the interior, the physical determinant is nonzero and the already
identified chart radius is radial.  The exact determinant identity thus
fixes the positive fourth power of the height.  Closed smoothness extends
the resulting radial height identity to both physical endpoints.
-/

@[expose] public section

noncomputable section

namespace ContinuousFlexibility.Statements

open Set
open scoped Topology ContDiff

set_option backward.isDefEq.respectTransparency false

variable {D : ReferenceData} {T : MaterialData} {S : PhysicalSpacesData}
  {C : NonlinearGeometryData S} {R : ReturnEquationData S}
  {L : ReturnCorrectionData S} {K : CanonicalData S} {base loss : ℕ} {ε : ℝ}

theorem n05_negative_reference_height_radial_open
    (hT : IsMaterialData D T) (hS : IsPhysicalSpaces D T S)
    (h : NonlinearPropertiesThrough04 D T S C R L K base loss ε)
    {i : ℕ} (hi : K.positive i = false) {r : ℝ}
    (hr : r ∈ Ioo (K.physicalLeft i) (K.physicalRight i)) (θ : ℝ) :
    K.height (C.referenceState, 0) i (r, θ) = K.height (C.referenceState, 0) i (r, 0) := by
  have h01 := h.1.1.1
  have h04 := h.2.2.2.2.1
  have hpieces := h04.1.referenceBounds
  have hnegative := h04.1.referenceNegative
  have hclosed := n05_reference_closed_properties h04
  have hrClosed : r ∈ Icc (K.physicalLeft i) (K.physicalRight i) := ⟨hr.1.le, hr.2.le⟩
  have hmem : (C.referenceState, 0) ∈ stateNeighborhood S C base ε :=
    n05_referenceState_mem h01.2.1
  have hsector := n05_referenceState_sector h01.2.2.1
  obtain ⟨B, hB⟩ := h01.1.1
  have hrD := (hpieces i).2.2 hr
  have hpositive : 0 < D.w r := hB.1.2.2.2.2.1 r hrD
  have hrpos : 0 < r := hB.1.1.trans hrD.1
  have hdetne : D.w r * (deriv D.w r / r) ≠ 0 :=
    mul_ne_zero hpositive.ne' (div_ne_zero (hnegative i hi r hr).ne hrpos.ne')
  have hhθ := (hclosed hmem hsector i (r, θ) hrClosed).2.2.2
  have hh0 := (hclosed hmem hsector i (r, 0) hrClosed).2.2.2
  have hξ : (K.chart (C.referenceState, 0) i (r, θ)).1 =
      (K.chart (C.referenceState, 0) i (r, 0)).1 := by
    simpa only using
      congrArg Prod.fst (n05_negative_reference_chart_radial hT hS h hi hrClosed θ)
  have hdθ := n05_negative_reference_determinant_closed hT hS h hi
    (x := (r, θ)) hrClosed
  have hd0 := n05_negative_reference_determinant_closed hT hS h hi
    (x := (r, 0)) hrClosed
  apply (pow_left_inj₀ hhθ.le hh0.le (by decide : (4 : ℕ) ≠ 0)).mp
  apply mul_right_cancel₀ hdetne
  rw [hdθ, hd0, hξ]

theorem n05_negative_reference_height_radial
    (hT : IsMaterialData D T) (hS : IsPhysicalSpaces D T S)
    (h : NonlinearPropertiesThrough04 D T S C R L K base loss ε)
    {i : ℕ} (hi : K.positive i = false) {r : ℝ}
    (hr : r ∈ Icc (K.physicalLeft i) (K.physicalRight i)) (θ : ℝ) :
    K.height (C.referenceState, 0) i (r, θ) = K.height (C.referenceState, 0) i (r, 0) := by
  have h01 := h.1.1.1
  have h04 := h.2.2.2.2.1
  have hpieces := h04.1.referenceBounds
  have hclosed := n05_reference_closed_properties h04
  have hmem : (C.referenceState, 0) ∈ stateNeighborhood S C base ε :=
    n05_referenceState_mem h01.2.1
  have hsector := n05_referenceState_sector h01.2.2.1
  apply n05_eqOn_closed_strip_of_nonreflection (hpieces i).1
    (f := K.height (C.referenceState, 0) i)
    (g := fun p => K.height (C.referenceState, 0) i (p.1, 0)) _ _ _ (r, θ) hr
  · intro p hp
    exact (hclosed hmem hsector i p hp).2.1.continuousAt
  · intro p hp
    exact (hclosed hmem hsector i (p.1, 0) hp).2.1.continuousAt.comp
      (f := fun q : PolarPoint => (q.1, 0)) (continuousAt_fst.prodMk continuousAt_const)
  · intro p hp _
    exact n05_negative_reference_height_radial_open hT hS h hi hp p.2

end ContinuousFlexibility.Statements
