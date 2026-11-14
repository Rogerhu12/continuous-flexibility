module

public import ContinuousFlexibility.Analysis.N08CircleSingleDecay
public import ContinuousFlexibility.Analysis.N08CircleJetComparison

/-!
# One-label states in the actual nonlinear sector

Only the two circle coordinates are retained. Centering this projection
at the reference state preserves the selected control and chart exactly.
The complete state grading inherits the exact single-label decay.
-/

@[expose] public section

noncomputable section

namespace ContinuousFlexibility.Statements

open Set
open ContinuousFlexibility.Analysis

set_option backward.isDefEq.respectTransparency false

private theorem n08_twoCircleDirection_grading
    {E F : Type*} [TopologicalSpace E] [AddCommGroup E] [Module ℝ E]
    [TopologicalSpace F] [AddCommGroup F] [Module ℝ F]
    (p : ℕ → Seminorm ℝ E) (q : ℕ → Seminorm ℝ F) (s : ℕ) (u v : F) :
    pairGrading p (pairGrading realGrading (pairGrading q q)) s (0, 0, u, v) =
      q s u + q s v := by
  change p s 0 + (realGrading s 0 + (q s u + q s v)) = _
  rw [map_zero, map_zero, zero_add, zero_add]

private theorem n08_twoCircleCoordinates_le
    {E F : Type*} [TopologicalSpace E] [AddCommGroup E] [Module ℝ E]
    [TopologicalSpace F] [AddCommGroup F] [Module ℝ F]
    (p : ℕ → Seminorm ℝ E) (q : ℕ → Seminorm ℝ F) (s : ℕ)
    (x : E × (ℝ × (F × F))) :
    q s x.2.2.1 + q s x.2.2.2 ≤
      pairGrading p (pairGrading realGrading (pairGrading q q)) s x := by
  change q s x.2.2.1 + q s x.2.2.2 ≤
    p s x.1 + (realGrading s x.2.1 + (q s x.2.2.1 + q s x.2.2.2))
  linarith only [apply_nonneg (p s) x.1, apply_nonneg (realGrading s) x.2.1]

private theorem n08_two_term_scaled_le {a b c d t w : ℝ}
    (ht : 0 ≤ t) (ha : a ≤ t * c) (hb : b ≤ t * d) (hw : c + d ≤ w) :
    a + b ≤ t * w :=
  (add_le_add ha hb).trans
    ((mul_add t c d).symm.le.trans (mul_le_mul_of_nonneg_left hw ht))

private theorem n08_centered_decode_projection
    {E : Type*} [AddCommGroup E] [Module ℝ E]
    (decode : E →ₗ[ℝ] (ℕ → ℝ → ℝ)) (P : E → E) (m : ℕ) (a x : E)
    (hP : ∀ u, decode (P u) m = decode u m) :
    decode (a + P (x - a)) m = decode x m := by
  funext θ
  simp only [map_add, Pi.add_apply, hP, map_sub, Pi.sub_apply]
  ring

private theorem n08_singleField_constant (f g : ℕ → ℝ → ℝ) (m : ℕ)
    (hg : g = n08CircleSingleField m f) (hf : ∀ n θ φ, f n θ = f n φ) :
    ∀ n θ φ, g n θ = g n φ := by
  rw [hg]
  intro n θ φ
  by_cases hn : n = m
  · simpa only [n08CircleSingleField, if_pos hn] using hf n θ φ
  · simp only [n08CircleSingleField, if_neg hn, Pi.zero_apply]

private theorem n08_singleField_odd (f g : ℕ → ℝ → ℝ) (m : ℕ)
    (hg : g = n08CircleSingleField m f) (hf : ∀ n θ, f n (-θ) = -f n θ) :
    ∀ n θ, g n (-θ) = -g n θ := by
  rw [hg]
  intro n θ
  by_cases hn : n = m
  · simpa only [n08CircleSingleField, if_pos hn] using hf n θ
  · simp only [n08CircleSingleField, if_neg hn, Pi.zero_apply, neg_zero]

variable {D : ReferenceData} {T : MaterialData} {S : PhysicalSpacesData}

private theorem n08CircleSingle_centered_decode (hS : IsPhysicalSpaces D T S)
    (m : ℕ) (a x : CircleSpace S) :
    (S.circle (3 / 4 : ℝ)).decode
      (a + n08CircleSingle (hS.2.1 (3 / 4 : ℝ)) m (x - a)) m =
        (S.circle (3 / 4 : ℝ)).decode x m :=
  n08_centered_decode_projection (S.circle (3 / 4 : ℝ)).decode
    (n08CircleSingle (hS.2.1 (3 / 4 : ℝ)) m) m a x
    (fun u => (congrArg (fun f : ℕ → ℝ → ℝ => f m)
      (n08CircleSingle_decode (hS.2.1 (3 / 4 : ℝ)) m u)).trans
        (n08CircleSingleField_self m ((S.circle (3 / 4 : ℝ)).decode u)))

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
  exact n08_twoCircleDirection_grading (heightPairGrading S)
    (S.circle (3 / 4 : ℝ)).grading s
    (n08CircleSingle (hS.2.1 (3 / 4 : ℝ)) m x.2.2.1)
    (n08CircleSingle (hS.2.1 (3 / 4 : ℝ)) m x.2.2.2)

theorem n08_circleCoordinates_le_stateGrading (S : PhysicalSpacesData)
    (s : ℕ) (x : AnnularState S) :
    (S.circle (3 / 4 : ℝ)).grading s x.2.2.1 +
      (S.circle (3 / 4 : ℝ)).grading s x.2.2.2 ≤ stateGrading S s x :=
  n08_twoCircleCoordinates_le (heightPairGrading S) (S.circle (3 / 4 : ℝ)).grading s x

theorem n08CircleSingleStateDirection_grading_le
    (hS : IsPhysicalSpaces D T S) (m s : ℕ) (x : AnnularState S) :
    stateGrading S s (n08CircleSingleStateDirection hS m x) ≤ stateGrading S s x :=
  (n08CircleSingleStateDirection_grading hS m s x).trans_le
    ((add_le_add
      (n08CircleSingle_grading_le (hS.2.1 (3 / 4 : ℝ)) m s x.2.2.1)
      (n08CircleSingle_grading_le (hS.2.1 (3 / 4 : ℝ)) m s x.2.2.2)).trans
        (n08_circleCoordinates_le_stateGrading S s x))

theorem n08CircleSingleStateDirection_grading_decay
    (hS : IsPhysicalSpaces D T S) (m s N : ℕ) (x : AnnularState S)
    (hM : 0 < T.M (T.sample m)) :
    stateGrading S s (n08CircleSingleStateDirection hS m x) ≤
      (T.M (T.sample m) ^ N)⁻¹ * stateGrading S (s + N) x :=
  (n08CircleSingleStateDirection_grading hS m s x).trans_le
    (n08_two_term_scaled_le (inv_nonneg.mpr (pow_nonneg hM.le _))
      (n08CircleSingle_grading_decay (hS.2.1 (3 / 4 : ℝ)) m s N x.2.2.1 hM)
      (n08CircleSingle_grading_decay (hS.2.1 (3 / 4 : ℝ)) m s N x.2.2.2 hM)
      (n08_circleCoordinates_le_stateGrading S (s + N) x))

theorem n08CircleSingleStateDirection_sector
    (hS : IsPhysicalSpaces D T S) (m : ℕ) {x : AnnularState S}
    (hx : stateSector S x) : stateSector S (n08CircleSingleStateDirection hS m x) := by
  constructor
  · exact n08_singleField_constant _ _ m
      (n08CircleSingle_decode (hS.2.1 (3 / 4 : ℝ)) m x.2.2.1) hx.1
  · exact n08_singleField_odd _ _ m
      (n08CircleSingle_decode (hS.2.1 (3 / 4 : ℝ)) m x.2.2.2) hx.2

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
      (S.circle (3 / 4 : ℝ)).decode x.2.2.1 m :=
  n08CircleSingle_centered_decode hS m C.referenceState.2.2.1 x.2.2.1

theorem n08CircleSingleState_kappa (hS : IsPhysicalSpaces D T S)
    (C : NonlinearGeometryData S) (m : ℕ) (x : AnnularState S) :
    stateKappa S (n08CircleSingleState hS C m x) m = stateKappa S x m :=
  congrArg angularMean (n08CircleSingleState_decode_kappa hS C m x)

theorem n08CircleSingleState_chart (hS : IsPhysicalSpaces D T S)
    (C : NonlinearGeometryData S) (m : ℕ) (x : AnnularState S) :
    stateLeftChart S (n08CircleSingleState hS C m x) m = stateLeftChart S x m := by
  have hd : (S.circle (3 / 4 : ℝ)).decode (n08CircleSingleState hS C m x).2.2.2 m =
      (S.circle (3 / 4 : ℝ)).decode x.2.2.2 m :=
    n08CircleSingle_centered_decode hS m C.referenceState.2.2.2 x.2.2.2
  exact congrArg (fun f : ℝ → ℝ => fun θ : ℝ => θ + f θ) hd

end ContinuousFlexibility.Statements
