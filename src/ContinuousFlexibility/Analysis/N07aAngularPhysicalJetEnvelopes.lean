import ContinuousFlexibility.Analysis.N07aAngularFixedJetEnvelope
import ContinuousFlexibility.Analysis.N07aAngularPhysicalCoefficients
import ContinuousFlexibility.Analysis.N07aCanonicalAtomBounds
import ContinuousFlexibility.Analysis.N07aCoordinateJetNorms

/-!
# Physical chart and height jets at a fixed parameter

The height atoms are pulled back from their physical unit interval.
In particular no height atom is misidentified with its value at a
nonlinear inverse-chart point. Reference and current charts use the same
affine calculation, with their actual raw spatial jet bounds.
-/

noncomputable section

namespace ContinuousFlexibility.Analysis

open Set ContinuousFlexibility.Statements
open scoped ContDiff BigOperators

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

theorem n07a_physicalJetField_smooth_of_atoms
    {z : AnnularState S × ℝ}
    (hs : ∀ m a, ContDiffOn ℝ ∞ (CanonicalGeometry.atom D T S C L K z m a)
      CanonicalGeometry.unitStrip)
    (m : ℕ) (hm : K.physicalLeft m < K.physicalRight m) (i : Fin 6) :
    ContDiffOn ℝ ∞ (n07aPhysicalJetField K z m i) (physicalPieceOpen S K m) := by
  have hcomp := (hs m (n07aPhysicalJetAtom i)).comp
    (n07aCanonicalUnitInversePoint_contDiff (K := n07aPhysicalIntervalData K)).contDiffOn
    (n07aCanonicalUnitInversePoint_maps (K := n07aPhysicalIntervalData K) hm)
  apply hcomp.congr
  intro p _
  rw [← n07aPhysicalJetField_unit]
  simp only [Function.comp_apply,
    n07aCanonicalUnitPoint_inverse (K := n07aPhysicalIntervalData K) hm p]

theorem n07a_physicalJetFields_fixedEnvelope_of_atoms
    (hD : IsAccumulatingProfile D) (hT : IsMaterialData D T)
    (href : CanonicalGeometry.ReferenceJets D T S C L K)
    (hphysical : ∀ m, K.physicalLeft m < K.physicalRight m)
    {z : AnnularState S × ℝ}
    (hs : ∀ m a, ContDiffOn ℝ ∞ (CanonicalGeometry.atom D T S C L K z m a)
      CanonicalGeometry.unitStrip)
    (hb : ∀ n : ℕ, ∃ e : ℕ → ℝ, N07aSampleSubpower T K e ∧ (∀ m, 0 ≤ e m) ∧
      ∀ m a p, p ∈ CanonicalGeometry.unitStrip → ∀ i j : ℕ, i + j ≤ n →
        |mixedDerivative i j (CanonicalGeometry.atom D T S C L K z m a) p| ≤ e m)
    (i : Fin 6) :
    N07aAngularFixedJetEnvelope T K (physicalPieceOpen S K) (fun _ => 1)
      (fun m => n07aPhysicalJetField K z m i) := by
  classical
  intro n
  let e : ℕ → ℝ := (hb n).choose
  have he := (hb n).choose_spec.1
  have he0 := (hb n).choose_spec.2.1
  have heb := (hb n).choose_spec.2.2
  let a : Fin (n + 1) → ℕ → ℝ :=
    fun j m => (K.physicalRight m - K.physicalLeft m)⁻¹ ^ j.val * e m
  have ha (j : Fin (n + 1)) : N07aSampleSubpower T K (a j) :=
    N07aSampleSubpower.mul hD hT
      ((n07a_physicalLengthInverse_subpower hD hT href).nat_pow hD hT j.val) he
  have ha0 (j : Fin (n + 1)) (m : ℕ) : 0 ≤ a j m :=
    mul_nonneg (pow_nonneg (inv_nonneg.mpr (sub_pos.mpr (hphysical m)).le) _) (he0 m)
  let A : ℕ → ℝ := fun m => ∑ j, a j m
  have hA : N07aSampleSubpower T K A :=
    N07aSampleSubpower.finset_sum hD hT Finset.univ a (fun j _ => ha j)
  have hA0 (m : ℕ) : 0 ≤ A m := Finset.sum_nonneg (fun j _ => ha0 j m)
  refine ⟨fun m => 2 ^ n * A m,
    N07aSampleSubpower.mul hD hT (N07aSampleSubpower.const hD hT (2 ^ n)) hA,
    fun m => mul_nonneg (pow_nonneg (by norm_num) _) (hA0 m), ?_⟩
  intro m p hp
  have hle := norm_iteratedFDeriv_le_of_mixedDerivative (isOpen_Ioo.prod isOpen_univ)
    (n07a_physicalJetField_smooth_of_atoms hs m (hphysical m) i) n hp (hA0 m)
    (fun b c hbc => by
      let j : Fin (n + 1) := ⟨b, by omega⟩
      let x := n07aCanonicalUnitInversePoint (n07aPhysicalIntervalData K) m p
      have hx : x ∈ CanonicalGeometry.unitStrip :=
        n07aCanonicalUnitInversePoint_maps (K := n07aPhysicalIntervalData K) (hphysical m) hp
      have hh := n07aCanonicalUnit_jet_inverse (K := n07aPhysicalIntervalData K)
        m (hphysical m) (n07aPhysicalJetField K z m i) b c p
      rw [n07aPhysicalJetField_unit] at hh
      have hfactor : 0 ≤ (K.physicalRight m - K.physicalLeft m)⁻¹ ^ b :=
        pow_nonneg (inv_nonneg.mpr (sub_pos.mpr (hphysical m)).le) b
      have hfactor' : 0 ≤
          ((n07aPhysicalIntervalData K).right m -
            (n07aPhysicalIntervalData K).left m)⁻¹ ^ b := hfactor
      rw [Real.norm_eq_abs, hh, abs_mul, abs_of_nonneg hfactor']
      exact (mul_le_mul_of_nonneg_left
        (heb m (n07aPhysicalJetAtom i) x hx b c hbc.le) hfactor).trans
        (Finset.single_le_sum (fun k _ => ha0 k m) (Finset.mem_univ j)))
  simpa only [mul_one] using hle

theorem n07a_referencePhysicalJetFields_fixedEnvelope
    (hD : IsAccumulatingProfile D) (hT : IsMaterialData D T)
    (href : CanonicalGeometry.ReferenceJets D T S C L K)
    (hphysical : ∀ m, K.physicalLeft m < K.physicalRight m) (i : Fin 6) :
    N07aAngularFixedJetEnvelope T K (physicalPieceOpen S K) (fun _ => 1)
      (fun m => n07aPhysicalJetField K (C.referenceState, 0) m i) := by
  apply n07a_physicalJetFields_fixedEnvelope_of_atoms hD hT href hphysical
    (fun m a => (href.1 m a).1)
  intro n
  let B : ℝ := (href.2 n).choose
  have hB := (href.2 n).choose_spec.1
  have hBb := (href.2 n).choose_spec.2
  refine ⟨fun m => B * T.E0 (T.sample (K.cell m)) ^ B,
    N07aSampleSubpower.mul hD hT (N07aSampleSubpower.const hD hT B)
      (N07aSampleSubpower.e0_rpow hD hT B), ?_, hBb⟩
  intro m
  have hm := materialSample_mem_radialCore hT hD.choose_spec.2.1 (K.cell m)
  exact mul_nonneg hB.le (Real.rpow_nonneg (hT.2.1 _ hm).2.2.1.le B)

theorem n07a_currentPhysicalJetFields_fixedEnvelope
    {base : ℕ} {ε : ℝ}
    (hD : IsAccumulatingProfile D) (hT : IsMaterialData D T)
    (href : CanonicalGeometry.ReferenceJets D T S C L K)
    (hcur : CanonicalGeometry.CurrentJets D T S C L K base ε)
    (hphysical : ∀ m, K.physicalLeft m < K.physicalRight m)
    (z : CanonicalGeometry.Parameter S) (hz : z ∈ sectorNeighborhood S base ε ε) (i : Fin 6) :
    N07aAngularFixedJetEnvelope T K (physicalPieceOpen S K) (fun _ => 1)
      (fun m => n07aPhysicalJetField K (liftSectorParameter S C z) m i) := by
  apply n07a_physicalJetFields_fixedEnvelope_of_atoms hD hT href hphysical
    (fun m a => (hcur.1 z hz m a).1)
  let bounds := n07a_geometryAtom_absolute_jet_bound hD hT href hcur
  let d : ℕ := bounds.choose
  have hd := bounds.choose_spec
  intro n
  let e : ℕ → ℝ := (hd n).choose
  have he := (hd n).choose_spec.1
  have he0 := (hd n).choose_spec.2.1
  have heb := (hd n).choose_spec.2.2
  let c : ℝ := 1 + CanonicalGeometry.parameterGrading S (n + d) z
  have hc : 0 ≤ c := add_nonneg zero_le_one (apply_nonneg _ _)
  refine ⟨fun m => e m * c,
    N07aSampleSubpower.mul hD hT he (N07aSampleSubpower.const hD hT c),
    fun m => mul_nonneg (he0 m) hc, fun m a p hp j k hjk => ?_⟩
  exact heb z hz m a ⟨p, hp⟩ j k hjk

theorem n07a_chart_eq_physicalJetFields
    (z : AnnularState S × ℝ) (m : ℕ) (hm : K.left m < K.right m) :
    K.chart z m = fun p =>
      (K.left m + (K.right m - K.left m) * n07aPhysicalJetField K z m 0 p,
        p.2 + n07aPhysicalJetField K z m 1 p) := by
  funext p
  apply Prod.ext
  · change (K.chart z m p).1 = K.left m + (K.right m - K.left m) *
      (((K.chart z m p).1 - K.left m) / (K.right m - K.left m))
    field_simp [(sub_pos.mpr hm).ne']
    ring
  · change (K.chart z m p).2 = p.2 + ((K.chart z m p).2 - p.2)
    ring

theorem n07a_physicalChart_positive_fixedEnvelope
    (hD : IsAccumulatingProfile D) (hT : IsMaterialData D T)
    (href : CanonicalGeometry.ReferenceJets D T S C L K)
    (hinterval : ∀ m, K.left m < K.right m)
    (hphysical : ∀ m, K.physicalLeft m < K.physicalRight m)
    {z : AnnularState S × ℝ}
    (hs : ∀ m a, ContDiffOn ℝ ∞ (CanonicalGeometry.atom D T S C L K z m a)
      CanonicalGeometry.unitStrip)
    (hb : ∀ i : Fin 6,
      N07aAngularFixedJetEnvelope T K (physicalPieceOpen S K) (fun _ => 1)
        (fun m => n07aPhysicalJetField K z m i)) :
    ∀ n : ℕ, 0 < n → ∃ e : ℕ → ℝ, N07aSampleSubpower T K e ∧ (∀ m, 0 ≤ e m) ∧
      ∀ m p, p ∈ physicalPieceOpen S K m → ‖iteratedFDeriv ℝ n (K.chart z m) p‖ ≤ e m := by
  intro n hn
  let a : ℕ → ℝ := (hb 0 n).choose
  have ha := (hb 0 n).choose_spec.1
  have ha0 := (hb 0 n).choose_spec.2.1
  have hab := (hb 0 n).choose_spec.2.2
  let b : ℕ → ℝ := (hb 1 n).choose
  have hb' := (hb 1 n).choose_spec.1
  have hb0 := (hb 1 n).choose_spec.2.1
  have hbb := (hb 1 n).choose_spec.2.2
  let e : ℕ → ℝ := fun m => |K.right m - K.left m| * a m + 1 + b m
  refine ⟨e,
    ((N07aSampleSubpower.mul hD hT (n07a_canonicalLength_subpower hD hT href).abs ha).add
      (N07aSampleSubpower.const hD hT (K := K) 1)).add hb',
    fun m => add_nonneg (add_nonneg (mul_nonneg (abs_nonneg _) (ha0 m)) zero_le_one) (hb0 m), ?_⟩
  intro m p hp
  have h0 := (n07a_physicalJetField_smooth_of_atoms hs m (hphysical m) 0).contDiffAt
    ((isOpen_Ioo.prod isOpen_univ).mem_nhds hp)
  have h1 := (n07a_physicalJetField_smooth_of_atoms hs m (hphysical m) 1).contDiffAt
    ((isOpen_Ioo.prod isOpen_univ).mem_nhds hp)
  rw [n07a_chart_eq_physicalJetFields z m (hinterval m)]
  have hbound := n07a_coordinatePair_iteratedFDeriv_bound h0 h1 (K.left m)
    (K.right m - K.left m) hn
  exact hbound.trans (add_le_add (add_le_add
    (mul_le_mul_of_nonneg_left (by simpa only [mul_one] using hab m p hp) (abs_nonneg _))
    le_rfl) (by simpa only [mul_one] using hbb m p hp))

end ContinuousFlexibility.Analysis
