import ContinuousFlexibility.Analysis.N07aCoefficientSpatial
import ContinuousFlexibility.Analysis.N07aCoefficientSymmetry
import ContinuousFlexibility.Analysis.N07aReferenceReturn

/-!
# The actual coefficient differences as weighted physical fields

The original N01 coefficient difference is extended by zero outside the
open annulus. Its genuine jets retain the supplied physical decay. The
diagonal differences are actual even heights; the mixed difference is odd
and is retained as an odd field for the subsequent angular primitive.
-/

noncomputable section

namespace ContinuousFlexibility.Analysis

open Set MeasureTheory
open scoped ContDiff
open ContinuousFlexibility.Statements

local instance n07aCoefficientFieldsStateGroup (S : PhysicalSpacesData) :
    AddCommGroup (AnnularState S) := n07aNonlinearAnnularGroup S
local instance n07aCoefficientFieldsStateModule (S : PhysicalSpacesData) :
    Module ℝ (AnnularState S) := n07aNonlinearAnnularModule S
local instance n07aCoefficientFieldsStateAddGroup (S : PhysicalSpacesData) :
    AddGroup (AnnularState S) := n07aNonlinearAnnularAddGroup S
local instance n07aCoefficientFieldsStateSMul (S : PhysicalSpacesData) :
    SMul ℝ (AnnularState S) := n07aNonlinearAnnularSMul S
local instance n07aCoefficientFieldsStateSub (S : PhysicalSpacesData) :
    Sub (AnnularState S) := n07aNonlinearAnnularSub S
local instance n07aCoefficientFieldsPairGroup (S : PhysicalSpacesData) :
    AddCommGroup (AnnularState S × ℝ) := n07aNonlinearAnnularParameterGroup S
local instance n07aCoefficientFieldsPairModule (S : PhysicalSpacesData) :
    Module ℝ (AnnularState S × ℝ) := n07aNonlinearAnnularParameterModule S
local instance n07aCoefficientFieldsPairAddGroup (S : PhysicalSpacesData) :
    AddGroup (AnnularState S × ℝ) := n07aNonlinearAnnularParameterAddGroup S
local instance n07aCoefficientFieldsPairSMul (S : PhysicalSpacesData) :
    SMul ℝ (AnnularState S × ℝ) := n07aNonlinearAnnularParameterSMul S
local instance n07aCoefficientFieldsPairSub (S : PhysicalSpacesData) :
    Sub (AnnularState S × ℝ) := n07aNonlinearAnnularParameterSub S

def n07aOriginalCoefficientField (D : ReferenceData) (S : PhysicalSpacesData)
    (C : NonlinearGeometryData S) (i : Fin 3) (z : AnnularState S × ℝ) : PolarPoint → ℝ :=
  if i = 0 then (originalCoefficients D S C z).a else
  if i = 1 then (originalCoefficients D S C z).b else (originalCoefficients D S C z).c

def n07aCoefficientDifferenceField (D : ReferenceData) (S : PhysicalSpacesData)
    (C : NonlinearGeometryData S) (i : Fin 3) (z : AnnularState S × ℝ)
    (p : PolarPoint) : ℝ := by
  classical
  exact if p ∈ annularOpen D then
    n07aOriginalCoefficientField D S C i z p -
      n07aOriginalCoefficientField D S C i (C.referenceState, 0) p else 0

variable {D : ReferenceData} {T : MaterialData} {S : PhysicalSpacesData}
  {C : NonlinearGeometryData S} {base loss : ℕ} {ε : ℝ}

theorem n07aCoefficientDifferenceField_eqOn (i : Fin 3) (z : AnnularState S × ℝ) :
    EqOn (n07aCoefficientDifferenceField D S C i z)
      (fun p => n07aOriginalCoefficientField D S C i z p -
        n07aOriginalCoefficientField D S C i (C.referenceState, 0) p) (annularOpen D) := by
  classical
  intro p hp
  simp only [n07aCoefficientDifferenceField, ite_eq_left hp]

theorem n07aCoefficientDifferenceField_mixedDerivative
    (i : Fin 3) (z : AnnularState S × ℝ) (a b : ℕ)
    {p : PolarPoint} (hp : p ∈ annularOpen D) :
    mixedDerivative a b (n07aCoefficientDifferenceField D S C i z) p =
      coefficientFamily D S C i a b p z :=
  mixedDerivative_eqOn_of_isOpen (isOpen_Ioo.prod isOpen_univ)
    (n07aCoefficientDifferenceField_eqOn i z) a b hp

theorem n07aOriginalCoefficientField_contDiffOn
    (hS : IsPhysicalSpaces D T S) (hT : IsMaterialData D T)
    (h01 : N01Properties D T S C base loss ε)
    {z : AnnularState S × ℝ} (hz : z ∈ stateNeighborhood S C base ε)
    (hs : stateSector S z.1) (i : Fin 3) :
    ContDiffOn ℝ ∞ (n07aOriginalCoefficientField D S C i z) (annularOpen D) := by
  have h := n07a_originalCoefficients_contDiffOn hS hT h01 hz hs
  unfold n07aOriginalCoefficientField
  split_ifs
  · exact h.1
  · exact h.2.1
  · exact h.2.2

theorem n07aCoefficientDifferenceField_contDiffOn
    (hS : IsPhysicalSpaces D T S) (hT : IsMaterialData D T)
    (h01 : N01Properties D T S C base loss ε)
    {z : AnnularState S × ℝ} (hz : z ∈ stateNeighborhood S C base ε)
    (hs : stateSector S z.1) (i : Fin 3) :
    ContDiffOn ℝ ∞ (n07aCoefficientDifferenceField D S C i z) (annularOpen D) :=
  ((n07aOriginalCoefficientField_contDiffOn hS hT h01 hz hs i).sub
    (n07aOriginalCoefficientField_contDiffOn hS hT h01
      (n07a_reference_mem_stateNeighborhood h01) h01.2.2.1.stateSector i)).congr
        (fun _ hp => n07aCoefficientDifferenceField_eqOn i z hp)

theorem n07aOriginalCoefficientField_periodic (hS : IsPhysicalSpaces D T S)
    (i : Fin 3) (z : AnnularState S × ℝ) :
    Function.Periodic (n07aOriginalCoefficientField D S C i z) (0, Real.pi) := by
  have h := n07a_originalCoefficients_periodic (C := C) hS z
  unfold n07aOriginalCoefficientField
  split_ifs
  · exact h.1
  · exact h.2.1
  · exact h.2.2

theorem n07aCoefficientDifferenceField_periodic (hS : IsPhysicalSpaces D T S)
    (i : Fin 3) (z : AnnularState S × ℝ) :
    Function.Periodic (n07aCoefficientDifferenceField D S C i z) (0, Real.pi) := by
  classical
  intro p
  have hmem : p + (0, Real.pi) ∈ annularOpen D ↔ p ∈ annularOpen D := by
    simp only [annularOpen, mem_prod, Prod.fst_add, add_zero, mem_univ, and_true]
  simp only [n07aCoefficientDifferenceField, hmem,
    n07aOriginalCoefficientField_periodic hS i z p,
    n07aOriginalCoefficientField_periodic hS i (C.referenceState, 0) p]

theorem n07aCoefficientDifferenceField_reflection (hS : IsPhysicalSpaces D T S)
    (i : Fin 3) (z : AnnularState S × ℝ) (r θ : ℝ) :
    n07aCoefficientDifferenceField D S C i z (r, -θ) =
      (if i = 1 then (-1 : ℝ) else 1) *
        n07aCoefficientDifferenceField D S C i z (r, θ) := by
  classical
  have h := n07a_originalCoefficients_reflection (C := C) hS z
  have h₀ := n07a_originalCoefficients_reflection (C := C) hS (C.referenceState, 0)
  by_cases hr : r ∈ Ioo D.a D.b
  · have hp (t : ℝ) : (r, t) ∈ annularOpen D := ⟨hr, mem_univ _⟩
    simp only [n07aCoefficientDifferenceField, ite_eq_left (hp (-θ)), ite_eq_left (hp θ)]
    fin_cases i <;> norm_num [n07aOriginalCoefficientField,
      h.1 r θ, h.2.1 r θ, h.2.2 r θ, h₀.1 r θ, h₀.2.1 r θ, h₀.2.2 r θ] <;> ring
  · have hp (t : ℝ) : (r, t) ∉ annularOpen D := fun h => hr h.1
    simp only [n07aCoefficientDifferenceField, ite_eq_right (hp (-θ)), ite_eq_right (hp θ), mul_zero]

theorem n07aCoefficientDifferenceField_zero_outside
    (i : Fin 3) (z : AnnularState S × ℝ) {p : PolarPoint}
    (hp : p ∉ annularOpen D) : n07aCoefficientDifferenceField D S C i z p = 0 := by
  classical
  simp only [n07aCoefficientDifferenceField, ite_eq_right hp]

theorem n07aCoefficientDifferenceField_weightedJets_memLp
    (hS : IsPhysicalSpaces D T S) (hT : IsMaterialData D T)
    (h01 : N01Properties D T S C base loss ε)
    {γ : ℝ} (hγ : γ < 3 / 64)
    {z : AnnularState S × ℝ} (hz : z ∈ stateNeighborhood S C base ε)
    (hs : stateSector S z.1) (i : Fin 3) (a b c : ℕ) :
    MemLp (weightedPhysicalJet T γ a b c (n07aCoefficientDifferenceField D S C i z))
      2 materialCylinderMeasure := by
  let data := n07a_coefficientFamily_decay_bound hT h01 (a + b)
  let K : ℝ := data.choose
  have hK : 0 < K := data.choose_spec.1
  have hb := data.choose_spec.2
  let B : ℝ := K * (1 + n07aRawParameterSize S
    (a + b + loss) (z - (C.referenceState, 0)))
  have hB : 0 ≤ B := mul_nonneg hK.le (by unfold n07aRawParameterSize; positivity)
  apply n07a_weightedPhysicalJet_memLp_of_decay hT hγ
    (n07aCoefficientDifferenceField_contDiffOn hS hT h01 hz hs i) a b c hB
  intro j hj p hp
  rw [n07aCoefficientDifferenceField_mixedDerivative i z j b hp]
  exact (hb i j b p (Nat.add_le_add_right hj b) hp z hz).trans_eq (by
    dsimp only [B, K, data]
    ring)

/-- Both diagonal differences belong to the original even height model. -/
theorem n07aCoefficientDifferenceField_heightMember
    (hS : IsPhysicalSpaces D T S) (hT : IsMaterialData D T)
    (h01 : N01Properties D T S C base loss ε)
    {γ : ℝ} (hγ : γ < 3 / 64)
    {z : AnnularState S × ℝ} (hz : z ∈ stateNeighborhood S C base ε)
    (hs : stateSector S z.1) (i : Fin 3) (hi : i ≠ 1) :
    HeightMember D T γ (n07aCoefficientDifferenceField D S C i z) := by
  refine ⟨n07aCoefficientDifferenceField_contDiffOn hS hT h01 hz hs i, ?_,
    n07aCoefficientDifferenceField_periodic hS i z,
    fun p hp => n07aCoefficientDifferenceField_zero_outside i z hp,
    n07aCoefficientDifferenceField_weightedJets_memLp hS hT h01 hγ hz hs i⟩
  intro r θ
  simpa only [ite_eq_right hi, one_mul] using
    n07aCoefficientDifferenceField_reflection hS i z r θ

end ContinuousFlexibility.Analysis
