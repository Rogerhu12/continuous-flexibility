import ContinuousFlexibility.Analysis.N07aProfileHeight
import ContinuousFlexibility.Analysis.N07aPhysicalJetTowers
import ContinuousFlexibility.Analysis.SolveNewtonBridge
import ContinuousFlexibility.Analysis.SolveStateSpaces
import ContinuousFlexibility.Scalar.WeightedSmoothTameLinear

/-!
# The genuine N01 parameter tower of the actual profile

The q=0 coefficient slice is pulled back by the fixed projection which
sets q to zero. This gives the ordinary spatial-jet towers of the actual
profile difference, with exactly the N01 base and loss.
-/

noncomputable section

namespace ContinuousFlexibility.Analysis

open Set
open scoped Topology ContDiff BigOperators
open ContinuousFlexibility.Statements

set_option backward.isDefEq.respectTransparency false

local instance n07aProfileParameterJetsStateGroup (S : PhysicalSpacesData) :
    AddCommGroup (AnnularState S) := n07aNonlinearAnnularGroup S
local instance n07aProfileParameterJetsStateModule (S : PhysicalSpacesData) :
    Module ℝ (AnnularState S) := n07aNonlinearAnnularModule S
local instance n07aProfileParameterJetsStateTopology (S : PhysicalSpacesData) :
    TopologicalSpace (AnnularState S) := inferInstance
local instance n07aProfileParameterJetsStateAddGroup (S : PhysicalSpacesData) :
    AddGroup (AnnularState S) := n07aNonlinearAnnularAddGroup S
local instance n07aProfileParameterJetsStateSMul (S : PhysicalSpacesData) :
    SMul ℝ (AnnularState S) := n07aNonlinearAnnularSMul S
local instance n07aProfileParameterJetsStateSub (S : PhysicalSpacesData) :
    Sub (AnnularState S) := n07aNonlinearAnnularSub S

local instance n07aProfileParameterJetsPairGroup (S : PhysicalSpacesData) :
    AddCommGroup (AnnularState S × ℝ) := n07aNonlinearAnnularParameterGroup S
local instance n07aProfileParameterJetsPairModule (S : PhysicalSpacesData) :
    Module ℝ (AnnularState S × ℝ) := n07aNonlinearAnnularParameterModule S
local instance n07aProfileParameterJetsPairAddGroup (S : PhysicalSpacesData) :
    AddGroup (AnnularState S × ℝ) := n07aNonlinearAnnularParameterAddGroup S
local instance n07aProfileParameterJetsPairSMul (S : PhysicalSpacesData) :
    SMul ℝ (AnnularState S × ℝ) := n07aNonlinearAnnularParameterSMul S
local instance n07aProfileParameterJetsPairSub (S : PhysicalSpacesData) :
    Sub (AnnularState S × ℝ) := n07aNonlinearAnnularParameterSub S

def n07aRawParameterGrading (S : PhysicalSpacesData) :
    ℕ → Seminorm ℝ (AnnularState S × ℝ) :=
  pairGrading (E := AnnularState S) (F := ℝ) (stateGrading S) realGrading

theorem n07aRawParameterGrading_apply (S : PhysicalSpacesData) (s : ℕ)
    (z : AnnularState S × ℝ) :
    n07aRawParameterGrading S s z = n07aRawParameterSize S s z := rfl

theorem n07aRawParameterGrading_withSeminorms (S : PhysicalSpacesData) :
    WithSeminorms (n07aRawParameterGrading S) :=
  withSeminorms_pairGrading (solve_stateGrading_withSeminorms S)
    weighted_realGrading_withSeminorms

theorem n07aRawParameterGrading_monotone (S : PhysicalSpacesData) :
    Monotone (n07aRawParameterGrading S) :=
  tamePairGrading_monotone (solve_stateGrading_monotone S) weighted_realGrading_monotone

theorem n07aRawParameterSize_nonneg (S : PhysicalSpacesData) (s : ℕ)
    (z : AnnularState S × ℝ) : 0 ≤ n07aRawParameterSize S s z := by
  rw [← n07aRawParameterGrading_apply]
  exact apply_nonneg _ _

theorem n07aRawParameterVariation_nonneg (S : PhysicalSpacesData) (b s : ℕ)
    (z : AnnularState S × ℝ) {k : ℕ} (v : Fin k → (AnnularState S × ℝ)) :
    0 ≤ n07aRawParameterVariation S b s z v := by
  unfold n07aRawParameterVariation
  exact add_nonneg
    (mul_nonneg (add_nonneg zero_le_one (n07aRawParameterSize_nonneg S s z))
      (Finset.prod_nonneg fun i _ => n07aRawParameterSize_nonneg S b (v i)))
    (Finset.sum_nonneg fun i _ => mul_nonneg (n07aRawParameterSize_nonneg S s (v i))
      (Finset.prod_nonneg fun j _ => n07aRawParameterSize_nonneg S b (v j)))

theorem n07aRawParameterNeighborhood_isOpen (S : PhysicalSpacesData)
    (C : NonlinearGeometryData S) (base : ℕ) (ε : ℝ) :
    IsOpen (stateNeighborhood S C base ε) := by
  let : IsTopologicalAddGroup (AnnularState S) :=
    (solve_stateGrading_withSeminorms S).isTopologicalAddGroup
  exact (isOpen_lt
    (((solve_stateGrading_withSeminorms S).continuous_seminorm base).comp
      (continuous_fst.sub continuous_const)) continuous_const).inter
        (isOpen_lt (continuous_abs.comp continuous_snd) continuous_const)

def n07aZeroQCLM (S : PhysicalSpacesData) :
    (AnnularState S × ℝ) →L[ℝ] (AnnularState S × ℝ) :=
  (ContinuousLinearMap.fst ℝ (AnnularState S) ℝ).prod 0

theorem n07aZeroQCLM_apply (S : PhysicalSpacesData) (z : AnnularState S × ℝ) :
    n07aZeroQCLM S z = (z.1, 0) := by
  simp only [n07aZeroQCLM, ContinuousLinearMap.prod_apply, ContinuousLinearMap.coe_fst',
    zero_apply]

theorem n07aZeroQCLM_grading_le (S : PhysicalSpacesData) (s : ℕ)
    (z : AnnularState S × ℝ) :
    n07aRawParameterGrading S s (n07aZeroQCLM S z) ≤ n07aRawParameterGrading S s z := by
  simp only [n07aRawParameterGrading_apply, n07aRawParameterSize,
    n07aZeroQCLM_apply, abs_zero, add_zero]
  exact le_add_of_nonneg_right (abs_nonneg _)

theorem n07aZeroQCLM_mapsTo (S : PhysicalSpacesData) (C : NonlinearGeometryData S)
    (base : ℕ) (ε : ℝ) :
    MapsTo (n07aZeroQCLM S) (stateNeighborhood S C base ε) (stateNeighborhood S C base ε) := by
  intro z hz
  rw [n07aZeroQCLM_apply]
  exact ⟨hz.1, by simpa only [abs_zero] using (abs_nonneg z.2).trans_lt hz.2⟩

variable {D : ReferenceData} {T : MaterialData} {S : PhysicalSpacesData}
  {C : NonlinearGeometryData S} {base loss : ℕ} {ε : ℝ}

theorem n07aProfileDifferenceField_contDiffOn
    (hS : IsPhysicalSpaces D T S) (hT : IsMaterialData D T)
    (h01 : N01Properties D T S C base loss ε) (x : AnnularState S) :
    ContDiffOn ℝ ∞ (n07aProfileDifferenceField D S C x) (annularOpen D) := by
  have hf : ContDiff ℝ ∞ (fun p : PolarPoint =>
      stateProfile D S C x p.1 - stateProfile D S C C.referenceState p.1) :=
    ((contDiff_stateProfile_of_n01 hS hT h01 x).comp contDiff_fst).sub
    ((contDiff_stateProfile_of_n01 hS hT h01 C.referenceState).comp contDiff_fst)
  exact hf.contDiffOn.congr (fun _ hp => n07aProfileDifferenceField_eqOn x hp)

def n07aProfileParameterJet
    (hS : IsPhysicalSpaces D T S) (hT : IsMaterialData D T)
    (h01 : N01Properties D T S C base loss ε) (a b : ℕ) (p : annularOpen D) :
    SmoothDirections (E := AnnularState S × ℝ) (F := ℝ)
      (stateNeighborhood S C base ε)
      (fun z => mixedDerivative a b (n07aProfileDifferenceField D S C z.1) p.val) :=
  (smoothDirectionsRestrict
    (solveSmoothDirectionsPrecomp (n07aCoefficientTower hT h01 0 a b p) (n07aZeroQCLM S))
    (n07aRawParameterNeighborhood_isOpen S C base ε) (n07aZeroQCLM_mapsTo S C base ε)).congr
      (fun z _ => by
        rw [n07aZeroQCLM_apply, n07a_coefficientFamily_profile_slice hS hT h01]
        exact (mixedDerivative_eqOn_of_isOpen (isOpen_Ioo.prod isOpen_univ)
          (n07aProfileDifferenceField_eqOn z.1) a b p.property).symm)

theorem n07aProfileParameterJet_D
    (hS : IsPhysicalSpaces D T S) (hT : IsMaterialData D T)
    (h01 : N01Properties D T S C base loss ε) (a b : ℕ) (p : annularOpen D)
    (k : ℕ) (z : AnnularState S × ℝ) (v : Fin k → (AnnularState S × ℝ)) :
    (n07aProfileParameterJet hS hT h01 a b p).D k z v =
      (n07aCoefficientTower hT h01 0 a b p).D k (n07aZeroQCLM S z)
        (fun i => n07aZeroQCLM S (v i)) := by
  simp only [n07aProfileParameterJet, SmoothDirections.congr, smoothDirectionsRestrict,
    solveSmoothDirectionsPrecomp, ContinuousMultilinearMap.compContinuousLinearMap_apply]

set_option backward.isDefEq.respectTransparency true in
theorem n07aProfileParameterJet_decay_bound
    (hS : IsPhysicalSpaces D T S) (hT : IsMaterialData D T)
    (h01 : N01Properties D T S C base loss ε) (k s : ℕ) :
    ∃ B : ℝ, 0 < B ∧ ∀ (a b : ℕ) (p : annularOpen D), a + b ≤ s →
      ∀ z : AnnularState S × ℝ, z ∈ stateNeighborhood S C base ε →
      ∀ v : Fin k → (AnnularState S × ℝ),
        |(n07aProfileParameterJet hS hT h01 a b p).D k z v| ≤
          B * T.H p.val.1 ^ (3 / 64 : ℝ) *
            n07aRawParameterVariation S base (s + loss)
              (z - (C.referenceState, 0) : AnnularState S × ℝ) v := by
  let data := n07aCoefficientTower_decay_bound hT h01 k s
  let B : ℝ := data.choose
  have hB : 0 < B := data.choose_spec.1
  have hbound := data.choose_spec.2
  refine ⟨B, hB, fun a b p hab z hz v => ?_⟩
  rw [n07aProfileParameterJet_D]
  have hb := hbound 0 a b p hab (n07aZeroQCLM S z)
    (n07aZeroQCLM_mapsTo S C base ε hz) (fun i => n07aZeroQCLM S (v i))
  have hlin := solve_oneHighWeight_le (n07aRawParameterGrading S) (n07aRawParameterGrading S)
    (n07aZeroQCLM S).toLinearMap 1 le_rfl
    (fun n x => by
      simpa only [ContinuousLinearMap.coe_coe, one_mul] using
        n07aZeroQCLM_grading_le S n x)
    base (s + loss) (z - (C.referenceState, 0) : AnnularState S × ℝ) v
  have he : n07aZeroQCLM S (z - (C.referenceState, 0) : AnnularState S × ℝ) =
      (n07aZeroQCLM S z) - (C.referenceState, 0) := by
    simp only [n07aZeroQCLM_apply, Prod.mk_sub_mk, Prod.fst_sub, sub_zero]
  have hvar : n07aRawParameterVariation S base (s + loss)
      (n07aZeroQCLM S z - (C.referenceState, 0) : AnnularState S × ℝ)
      (fun i => n07aZeroQCLM S (v i)) ≤
      n07aRawParameterVariation S base (s + loss)
        (z - (C.referenceState, 0) : AnnularState S × ℝ) v := by
    simpa only [ContinuousLinearMap.coe_coe, n07aRawParameterGrading_apply, he,
      one_pow, one_mul, n07aRawParameterVariation] using hlin
  exact hb.trans (mul_le_mul_of_nonneg_left hvar
    (mul_nonneg hB.le (Real.rpow_nonneg (hT.2.1 _ p.property.1).2.1.le _)))

end ContinuousFlexibility.Analysis
