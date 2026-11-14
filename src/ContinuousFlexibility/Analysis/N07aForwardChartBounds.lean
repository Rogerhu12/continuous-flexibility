module

public import ContinuousFlexibility.Analysis.N07aPhysicalAtomBounds
public import ContinuousFlexibility.Analysis.N07aCoordinateJetNorms

/-!
# Forward-chart jets on the fixed reference physical intervals

The forward chart is recovered from its normalized radial component and
angle defect on the fixed intervals sampled by CurrentJets. Its first
derivative is charged in one fixed offset. These reference-domain bounds
do not assert estimates on a moving current physical piece.
-/

@[expose] public section

noncomputable section

namespace ContinuousFlexibility.Analysis

open Set ContinuousFlexibility.Statements
open scoped ContDiff

set_option backward.isDefEq.respectTransparency true

attribute [local instance]
  n07aNonlinearAnnularGroup n07aNonlinearAnnularModule
  n07aNonlinearAnnularAddGroup n07aNonlinearAnnularSMul n07aNonlinearAnnularSub
  n07aNonlinearAnnularParameterGroup n07aNonlinearAnnularParameterModule
  n07aNonlinearAnnularParameterAddGroup n07aNonlinearAnnularParameterSMul
  n07aNonlinearAnnularParameterSub
  n07aNonlinearDirectionsGroup n07aNonlinearDirectionsModule
  n07aNonlinearDirectionsAddGroup n07aNonlinearDirectionsSMul n07aNonlinearDirectionsSub
  n07aNonlinearSectorParameterGroup n07aNonlinearSectorParameterModule
  n07aNonlinearSectorParameterAddGroup n07aNonlinearSectorParameterSMul
  n07aNonlinearSectorParameterSub

variable {D : ReferenceData} {T : MaterialData} {S : PhysicalSpacesData}
  {C : NonlinearGeometryData S} {L : ReturnCorrectionData S} {K : CanonicalData S}
  {base : ℕ} {ε : ℝ}

theorem n07a_forwardChart_eq_rawAtoms
    (m : ℕ) (hm : K.left m < K.right m)
    (hp : K.physicalLeft m < K.physicalRight m)
    (z : CanonicalGeometry.Parameter S) :
    K.chart (liftSectorParameter S C z) m = fun y =>
      (K.left m + (K.right m - K.left m) *
        n07aPhysicalAtomField D T S C L K .chartRadial z m y,
       y.2 + n07aPhysicalAtomField D T S C L K .chartAngleDefect z m y) := by
  have hL : K.right m - K.left m ≠ 0 := (sub_pos.mpr hm).ne'
  funext y
  have hy : CanonicalGeometry.physicalUnitPoint K m
      (n07aCanonicalUnitInversePoint (n07aPhysicalIntervalData K) m y) = y :=
    n07aCanonicalUnitPoint_inverse (K := n07aPhysicalIntervalData K) hp y
  simp only [n07aPhysicalAtomField, Function.comp_apply, CanonicalGeometry.atom, hy]
  apply Prod.ext
  · dsimp only
    field_simp [hL] <;> ring
  · dsimp only
    ring

private theorem n07a_forwardJet_numeric_bound {u a b c P : ℝ}
    (hP : 0 ≤ P)
    (hu : u ≤ c * (a * (1 + P)) + 1 + b * (1 + P)) :
    u ≤ (c * a + 1 + b) * (1 + P) := by
  nlinarith only [hu, hP]

theorem n07a_forwardChart_positive_jets
    (hD : IsAccumulatingProfile D) (hT : IsMaterialData D T)
    (href : CanonicalGeometry.ReferenceJets D T S C L K)
    (hcur : CanonicalGeometry.CurrentJets D T S C L K base ε)
    (hinterval : ∀ m, K.left m < K.right m)
    (hphysical : ∀ m, K.physicalLeft m < K.physicalRight m) :
    ∃ loss : ℕ, ∀ n : ℕ, 0 < n → ∃ e : ℕ → ℝ,
      N07aSampleSubpower T K e ∧ (∀ m, 0 ≤ e m) ∧
        ∀ z ∈ sectorNeighborhood S base ε ε, ∀ m x, x ∈ referencePhysicalPieceOpen S K m →
          ‖iteratedFDeriv ℝ n (K.chart (liftSectorParameter S C z) m) x‖ ≤
            e m * (1 + CanonicalGeometry.parameterGrading S ((n - 1) + loss) z) := by
  have h := n07a_physicalAtomFields_sampleJetBounds hD hT href hcur hphysical
  let d := h.choose
  have hb := h.choose_spec
  have hs (a : CanonicalGeometry.Atom) := n07a_physicalAtomField_smooth hcur hphysical a
  have hL := (n07a_canonicalLength_subpower hD hT href).abs
  refine ⟨d + 1, fun n hn => ?_⟩
  have har := (hb .chartRadial).iteratedFDeriv hD hT
    (fun _ => isOpen_Ioo.prod isOpen_univ) (hs .chartRadial) n
  let a : ℕ → ℝ := har.choose
  have ha := har.choose_spec.1
  have ha0 := har.choose_spec.2.1
  have hab := har.choose_spec.2.2
  have hbr := (hb .chartAngleDefect).iteratedFDeriv hD hT
    (fun _ => isOpen_Ioo.prod isOpen_univ) (hs .chartAngleDefect) n
  let b : ℕ → ℝ := hbr.choose
  have hb' := hbr.choose_spec.1
  have hb0 := hbr.choose_spec.2.1
  have hbb := hbr.choose_spec.2.2
  let e : ℕ → ℝ := fun m => |K.right m - K.left m| * a m + 1 + b m
  have he : N07aSampleSubpower T K e :=
    ((N07aSampleSubpower.mul hD hT hL ha).add
      (N07aSampleSubpower.const hD hT (K := K) 1)).add hb'
  have he0 (m : ℕ) : 0 ≤ e m :=
    add_nonneg (add_nonneg (mul_nonneg (abs_nonneg _) (ha0 m)) zero_le_one) (hb0 m)
  refine ⟨e, he, he0, fun z hz m x hx => ?_⟩
  have hf := (hs .chartRadial z hz m).contDiffAt
    ((isOpen_Ioo.prod isOpen_univ).mem_nhds hx)
  have hg := (hs .chartAngleDefect z hz m).contDiffAt
    ((isOpen_Ioo.prod isOpen_univ).mem_nhds hx)
  have heq := n07a_forwardChart_eq_rawAtoms (D := D) (T := T) (S := S) (C := C) (L := L)
    m (hinterval m) (hphysical m) z
  have hn' : (n - 1) + (d + 1) = n + d := by omega
  have hbound := (n07a_coordinatePair_iteratedFDeriv_bound hf hg (K.left m)
    (K.right m - K.left m) hn).trans
      (add_le_add (add_le_add (mul_le_mul_of_nonneg_left (hab z hz m x hx)
        (abs_nonneg _)) le_rfl) (hbb z hz m x hx))
  have hbnd : ‖iteratedFDeriv ℝ n (K.chart (liftSectorParameter S C z) m) x‖ ≤
      e m * (1 + CanonicalGeometry.parameterGrading S (n + d) z) :=
    (congrArg (fun F : PolarPoint → PolarPoint => ‖iteratedFDeriv ℝ n F x‖) heq).le.trans
      (n07a_forwardJet_numeric_bound (apply_nonneg _ _) hbound)
  exact hbnd.trans_eq (congrArg
    (fun j : ℕ => e m * (1 + CanonicalGeometry.parameterGrading S j z)) hn'.symm)

end ContinuousFlexibility.Analysis
