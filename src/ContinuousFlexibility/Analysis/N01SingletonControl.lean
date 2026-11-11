import ContinuousFlexibility.Analysis.CircleSingletonControl
import ContinuousFlexibility.Analysis.N01RadialFlow
import ContinuousFlexibility.Analysis.TameLocalCalculus

/-!
# Single optical control lines in the actual state space

A one-component constant circle field is realized through the supplied
decoder. The associated affine state curve has exactly one kappa mean,
stays in the sector, and has the logarithmic profile used in the optical
variation formulas. Its grading estimate is uniform in the component.
-/

noncomputable section

namespace ContinuousFlexibility.Statements

-- Use the canonical product action directly, avoiding a costly search
-- through the abstract models that make up the state space.
local instance (S : PhysicalSpacesData) : SMul ℝ (AnnularState S) := Prod.instSMul

open Set Filter
open scoped Topology ContDiff

variable {D : ReferenceData} {T : MaterialData} {S : PhysicalSpacesData}
  {C : NonlinearGeometryData S}

def singletonKappaDirection
    (hS : IsCircleModel T (3 / 4 : ℝ) (S.circle (3 / 4 : ℝ))) (m : ℕ) :
    AnnularState S :=
  (0, (0, (circleSingletonLinear hS m 1, 0)))

theorem singletonKappaDirection_sector
    (hS : IsCircleModel T (3 / 4 : ℝ) (S.circle (3 / 4 : ℝ))) (m : ℕ) :
    stateSector S (singletonKappaDirection hS m) := by
  constructor
  · intro n θ φ
    change (S.circle (3 / 4 : ℝ)).decode (circleSingletonLinear hS m 1) n θ =
      (S.circle (3 / 4 : ℝ)).decode (circleSingletonLinear hS m 1) n φ
    rw [circleSingletonLinear_decode]
    rfl
  · intro n θ
    change (S.circle (3 / 4 : ℝ)).decode 0 n (-θ) =
      -(S.circle (3 / 4 : ℝ)).decode 0 n θ
    simp only [map_zero, Pi.zero_apply, neg_zero]

theorem singletonKappaDirection_grading
    (hS : IsCircleModel T (3 / 4 : ℝ) (S.circle (3 / 4 : ℝ))) (m s : ℕ) :
    stateGrading S s (singletonKappaDirection hS m) =
      (S.circle (3 / 4 : ℝ)).grading s (circleSingletonLinear hS m 1) := by
  have hz₁ : heightPairGrading S s (0 : HeightPair S) = 0 := (heightPairGrading S s).map_zero'
  have hz₂ : realGrading s (0 : ℝ) = 0 := (realGrading s).map_zero'
  have hz₃ : (S.circle (3 / 4 : ℝ)).grading s (0 : CircleSpace S) = 0 :=
    ((S.circle (3 / 4 : ℝ)).grading s).map_zero'
  simp only [stateGrading, Analysis.pairGrading_apply, singletonKappaDirection,
    hz₁, hz₂, hz₃, zero_add, add_zero]

theorem singletonKappaDirection_grading_le
    (hS : IsCircleModel T (3 / 4 : ℝ) (S.circle (3 / 4 : ℝ))) (m s : ℕ)
    (hM : 1 ≤ T.M (T.sample m)) (hH : 0 ≤ T.H (T.sample m)) :
    stateGrading S s (singletonKappaDirection hS m) ≤
      circleSingletonGradingConstant s *
        (T.M (T.sample m) ^ s * T.H (T.sample m) ^ (-(3 / 4 : ℝ))) := by
  rw [singletonKappaDirection_grading]
  exact circleSingletonLinear_grading_le hS s m hM hH

theorem singletonKappaLine_control
    (hS : IsCircleModel T (3 / 4 : ℝ) (S.circle (3 / 4 : ℝ)))
    (href : referenceStateConditions D S C) (m : ℕ) (t : ℝ) :
    (C.referenceState + (@SMul.smul ℝ (AnnularState S) inferInstance t (singletonKappaDirection hS m))).2.2.1 =
      circleSingletonLinear hS m t := by
  change C.referenceState.2.2.1 + t • circleSingletonLinear hS m 1 = _
  rw [href.2.2.2.1, zero_add]
  have hsmul := (circleSingletonLinear hS m).map_smul t (1 : ℝ)
  simpa only [smul_eq_mul, mul_one] using hsmul.symm

theorem singletonKappaLine_nu
    (hS : IsCircleModel T (3 / 4 : ℝ) (S.circle (3 / 4 : ℝ)))
    (href : referenceStateConditions D S C) (m : ℕ) (t : ℝ) :
    (C.referenceState + (@SMul.smul ℝ (AnnularState S) inferInstance t (singletonKappaDirection hS m))).2.1 = 0 := by
  change C.referenceState.2.1 + t • (0 : ℝ) = 0
  rw [href.2.2.1, smul_zero, zero_add]

theorem singletonKappaLine_mean
    (hS : IsCircleModel T (3 / 4 : ℝ) (S.circle (3 / 4 : ℝ)))
    (href : referenceStateConditions D S C) (m n : ℕ) (t : ℝ) :
    stateKappa S (C.referenceState + (@SMul.smul ℝ (AnnularState S) inferInstance t (singletonKappaDirection hS m))) n =
      if n = m then t else 0 := by
  unfold stateKappa
  rw [singletonKappaLine_control hS href]
  exact circleSingletonLinear_mean hS m n t

theorem singletonKappaLine_sector
    (hS : IsCircleModel T (3 / 4 : ℝ) (S.circle (3 / 4 : ℝ)))
    (href : referenceStateConditions D S C) (m : ℕ) (t : ℝ) :
    stateSector S (C.referenceState + (@SMul.smul ℝ (AnnularState S) inferInstance t (singletonKappaDirection hS m))) := by
  constructor
  · intro n θ φ
    rw [singletonKappaLine_control hS href, circleSingletonLinear_decode]
    rfl
  · intro n θ
    change (S.circle (3 / 4 : ℝ)).decode (C.referenceState.2.2.2 + t • 0) n (-θ) =
      -(S.circle (3 / 4 : ℝ)).decode (C.referenceState.2.2.2 + t • 0) n θ
    rw [href.2.2.2.2.1, smul_zero, zero_add]
    simp only [map_zero, Pi.zero_apply, neg_zero]

theorem singletonKappaLine_profile
    (hS : IsCircleModel T (3 / 4 : ℝ) (S.circle (3 / 4 : ℝ)))
    (href : referenceStateConditions D S C) (m : ℕ) (t : ℝ) :
    stateProfile D S C (C.referenceState + (@SMul.smul ℝ (AnnularState S) inferInstance t (singletonKappaDirection hS m))) =
      opticalLogPerturbation D.w (C.control m) t := by
  exact stateProfile_of_single_kappa (singletonKappaLine_nu hS href m t)
    (fun n => singletonKappaLine_mean hS href m n t)

theorem singletonKappaLine_mem
    (hS : IsCircleModel T (3 / 4 : ℝ) (S.circle (3 / 4 : ℝ)))
    (m base : ℕ) {ε t : ℝ} (hε : 0 < ε)
    (ht : |t| * stateGrading S base (singletonKappaDirection hS m) < ε) :
    (C.referenceState + (@SMul.smul ℝ (AnnularState S) inferInstance t (singletonKappaDirection hS m)), 0) ∈
      stateNeighborhood S C base ε := by
  constructor
  · simpa only [add_sub_cancel_left, map_smul_eq_mul, Real.norm_eq_abs] using ht
  · simpa only [abs_zero] using hε

theorem singletonKappaLine_eventually_mem
    (hS : IsCircleModel T (3 / 4 : ℝ) (S.circle (3 / 4 : ℝ)))
    (m base : ℕ) {ε : ℝ} (hε : 0 < ε) :
    ∀ᶠ t in 𝓝 (0 : ℝ),
      (C.referenceState + (@SMul.smul ℝ (AnnularState S) inferInstance t (singletonKappaDirection hS m)), 0) ∈
        stateNeighborhood S C base ε := by
  have hc : Continuous (fun t : ℝ =>
      |t| * stateGrading S base (singletonKappaDirection hS m)) :=
    continuous_abs.mul continuous_const
  have hsmall : ∀ᶠ t in 𝓝 (0 : ℝ),
      |t| * stateGrading S base (singletonKappaDirection hS m) < ε :=
    (isOpen_lt hc continuous_const).mem_nhds (by simpa only [Set.mem_setOf_eq, abs_zero, zero_mul] using hε)
  exact hsmall.mono (fun _ ht => singletonKappaLine_mem hS m base hε ht)

theorem N01Properties.minusFlow_singletonKappaLine
    {base loss : ℕ} {ε : ℝ} (hN : N01Properties D T S C base loss ε)
    (hS : IsPhysicalSpaces D T S) (hT : IsMaterialData D T)
    (m : ℕ) (θ : ℝ) {r : ℝ} (hr : r ∈ Icc (C.left m) (C.right m)) :
    ∀ᶠ t in 𝓝 (0 : ℝ),
      C.minusFlow (C.referenceState +
        t • singletonKappaDirection (hS.2.1 (3 / 4 : ℝ)) m, 0) m r θ =
      θ - opticalTravel (opticalLogPerturbation D.w (C.control m) t) (C.left m) r := by
  have hm := singletonKappaLine_eventually_mem
    (C := C) (hS.2.1 (3 / 4 : ℝ)) m base hN.2.1
  filter_upwards [hm] with t ht
  exact hN.minusFlow_zero_single_kappa hS hT ht
    (singletonKappaLine_nu (hS.2.1 (3 / 4 : ℝ)) hN.2.2.1 m t)
    (fun n => singletonKappaLine_mean (hS.2.1 (3 / 4 : ℝ)) hN.2.2.1 m n t) θ hr

end ContinuousFlexibility.Statements
