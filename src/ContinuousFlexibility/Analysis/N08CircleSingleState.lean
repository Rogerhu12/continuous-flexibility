import ContinuousFlexibility.Analysis.N08CircleSingleDecay
import ContinuousFlexibility.Analysis.N08CircleJetComparison

/-!
# One-label states in the actual nonlinear sector

Only the two circle coordinates are retained. Centering this projection
at the reference state preserves the selected control and chart exactly.
The complete state grading inherits the exact single-label decay.
-/

noncomputable section

namespace ContinuousFlexibility.Statements

open Set
open ContinuousFlexibility.Analysis

set_option backward.isDefEq.respectTransparency false

variable {D : ReferenceData} {T : MaterialData} {S : PhysicalSpacesData}

def n08CircleSingleStateDirection (hS : IsPhysicalSpaces D T S)
    (m : ℕ) (x : AnnularState S) : AnnularState S :=
  (0, 0, n08CircleSingle (hS.2.1 (3 / 4 : ℝ)) m x.2.2.1,
    n08CircleSingle (hS.2.1 (3 / 4 : ℝ)) m x.2.2.2)

theorem n08CircleSingleStateDirection_grading
    (hS : IsPhysicalSpaces D T S) (m s : ℕ) (x : AnnularState S) :
    stateGrading S s (n08CircleSingleStateDirection hS m x) =
      (S.circle (3 / 4 : ℝ)).grading s
        (n08CircleSingle (hS.2.1 (3 / 4 : ℝ)) m x.2.2.1) +
      (S.circle (3 / 4 : ℝ)).grading s
        (n08CircleSingle (hS.2.1 (3 / 4 : ℝ)) m x.2.2.2) := by
  change heightPairGrading S s 0 + (‖(0 : ℝ)‖ + (_ + _)) = _
  rw [map_zero, norm_zero, zero_add, zero_add]

theorem n08_circleCoordinates_le_stateGrading (S : PhysicalSpacesData)
    (s : ℕ) (x : AnnularState S) :
    (S.circle (3 / 4 : ℝ)).grading s x.2.2.1 +
      (S.circle (3 / 4 : ℝ)).grading s x.2.2.2 ≤ stateGrading S s x := by
  change _ ≤ heightPairGrading S s x.1 + (‖x.2.1‖ + (_ + _))
  linarith only [apply_nonneg (heightPairGrading S s) x.1, norm_nonneg x.2.1]

theorem n08CircleSingleStateDirection_grading_le
    (hS : IsPhysicalSpaces D T S) (m s : ℕ) (x : AnnularState S) :
    stateGrading S s (n08CircleSingleStateDirection hS m x) ≤ stateGrading S s x := by
  rw [n08CircleSingleStateDirection_grading]
  exact (add_le_add
    (n08CircleSingle_grading_le (hS.2.1 (3 / 4 : ℝ)) m s x.2.2.1)
    (n08CircleSingle_grading_le (hS.2.1 (3 / 4 : ℝ)) m s x.2.2.2)).trans
      (n08_circleCoordinates_le_stateGrading S s x)

theorem n08CircleSingleStateDirection_grading_decay
    (hS : IsPhysicalSpaces D T S) (m s N : ℕ) (x : AnnularState S)
    (hM : 0 < T.M (T.sample m)) :
    stateGrading S s (n08CircleSingleStateDirection hS m x) ≤
      (T.M (T.sample m) ^ N)⁻¹ * stateGrading S (s + N) x := by
  rw [n08CircleSingleStateDirection_grading]
  calc
    _ ≤ (T.M (T.sample m) ^ N)⁻¹ *
        (S.circle (3 / 4 : ℝ)).grading (s + N) x.2.2.1 +
        (T.M (T.sample m) ^ N)⁻¹ *
          (S.circle (3 / 4 : ℝ)).grading (s + N) x.2.2.2 :=
      add_le_add
        (n08CircleSingle_grading_decay (hS.2.1 (3 / 4 : ℝ)) m s N x.2.2.1 hM)
        (n08CircleSingle_grading_decay (hS.2.1 (3 / 4 : ℝ)) m s N x.2.2.2 hM)
    _ = (T.M (T.sample m) ^ N)⁻¹ *
        ((S.circle (3 / 4 : ℝ)).grading (s + N) x.2.2.1 +
          (S.circle (3 / 4 : ℝ)).grading (s + N) x.2.2.2) := (mul_add _ _ _).symm
    _ ≤ _ := mul_le_mul_of_nonneg_left (n08_circleCoordinates_le_stateGrading S (s + N) x)
      (inv_nonneg.mpr (pow_nonneg hM.le _))

theorem n08CircleSingleStateDirection_sector
    (hS : IsPhysicalSpaces D T S) (m : ℕ) {x : AnnularState S}
    (hx : stateSector S x) : stateSector S (n08CircleSingleStateDirection hS m x) := by
  constructor
  · intro n θ φ
    change (S.circle (3 / 4 : ℝ)).decode
        (n08CircleSingle (hS.2.1 (3 / 4 : ℝ)) m x.2.2.1) n θ = _
    simp only [n08CircleSingle_decode]
    by_cases hn : n = m
    · simpa only [n08CircleSingleField, if_pos hn] using hx.1 n θ φ
    · simp only [n08CircleSingleField, if_neg hn, Pi.zero_apply]
  · intro n θ
    change (S.circle (3 / 4 : ℝ)).decode
        (n08CircleSingle (hS.2.1 (3 / 4 : ℝ)) m x.2.2.2) n (-θ) = _
    simp only [n08CircleSingle_decode]
    by_cases hn : n = m
    · simpa only [n08CircleSingleField, if_pos hn] using hx.2 n θ
    · simp only [n08CircleSingleField, if_neg hn, Pi.zero_apply, neg_zero]

def n08CircleSingleState (hS : IsPhysicalSpaces D T S)
    (C : NonlinearGeometryData S) (m : ℕ) (x : AnnularState S) : AnnularState S :=
  C.referenceState + n08CircleSingleStateDirection hS m (x - C.referenceState)

theorem n08CircleSingleState_sub (hS : IsPhysicalSpaces D T S)
    (C : NonlinearGeometryData S) (m : ℕ) (x : AnnularState S) :
    n08CircleSingleState hS C m x - C.referenceState =
      n08CircleSingleStateDirection hS m (x - C.referenceState) := by
  unfold n08CircleSingleState
  abel

theorem n08CircleSingleState_sector (hS : IsPhysicalSpaces D T S)
    {C : NonlinearGeometryData S} (href : referenceStateConditions D S C)
    (m : ℕ) {x : AnnularState S} (hx : stateSector S x) :
    stateSector S (n08CircleSingleState hS C m x) :=
  (stateSectorSubmodule S).add_mem href.stateSector
    (n08CircleSingleStateDirection_sector hS m
      ((stateSectorSubmodule S).sub_mem hx href.stateSector))

private theorem n08CircleSingleState_decode_kappa (hS : IsPhysicalSpaces D T S)
    (C : NonlinearGeometryData S) (m : ℕ) (x : AnnularState S) :
    (S.circle (3 / 4 : ℝ)).decode (n08CircleSingleState hS C m x).2.2.1 m =
      (S.circle (3 / 4 : ℝ)).decode x.2.2.1 m := by
  funext θ
  simp only [n08CircleSingleState, n08CircleSingleStateDirection,
    Prod.snd_add, Prod.fst_add, Prod.snd_sub, Prod.fst_sub, map_add,
    n08CircleSingle_decode, map_sub, Pi.add_apply, Pi.sub_apply,
    n08CircleSingleField_self]
  ring

theorem n08CircleSingleState_kappa (hS : IsPhysicalSpaces D T S)
    (C : NonlinearGeometryData S) (m : ℕ) (x : AnnularState S) :
    stateKappa S (n08CircleSingleState hS C m x) m = stateKappa S x m :=
  congrArg angularMean (n08CircleSingleState_decode_kappa hS C m x)

theorem n08CircleSingleState_chart (hS : IsPhysicalSpaces D T S)
    (C : NonlinearGeometryData S) (m : ℕ) (x : AnnularState S) :
    stateLeftChart S (n08CircleSingleState hS C m x) m = stateLeftChart S x m := by
  funext θ
  simp only [stateLeftChart, n08CircleSingleState, n08CircleSingleStateDirection,
    Prod.snd_add, Prod.snd_sub, map_add, n08CircleSingle_decode, map_sub,
    Pi.add_apply, Pi.sub_apply, n08CircleSingleField_self]
  ring

end ContinuousFlexibility.Statements
