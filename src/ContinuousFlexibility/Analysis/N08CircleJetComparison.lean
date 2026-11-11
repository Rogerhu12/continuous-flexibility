import ContinuousFlexibility.Analysis.N08JetDifference
import ContinuousFlexibility.Analysis.N08CircleDiagonalContinuity

/-!
# A quantitative comparison of the actual control diagonal

N02 supplies the second jet of the same tower that defines the control
column. A scalar mean observation of that jet gives a Lipschitz estimate
for each diagonal entry, with only a fixed material-envelope power. The
order, radius and constant are chosen before the control label.
-/

noncomputable section

namespace ContinuousFlexibility.Statements

open Set Filter
open ContinuousFlexibility.Analysis
open scoped Topology BigOperators ENNReal

set_option backward.isDefEq.respectTransparency false

private theorem n08_subtype_pair_grading
    {E : Type*} [TopologicalSpace E] [AddCommGroup E] [Module ℝ E]
    (Q : Submodule ℝ E) (p : ℕ → Seminorm ℝ E) (s : ℕ) (z : Q × ℝ) :
    pairGrading (fun n => (p n).comp Q.subtype) realGrading s z =
      p s z.1.val + |z.2| := by
  change p s z.1.val + ‖z.2‖ = _
  rw [Real.norm_eq_abs]

private theorem n08_subtype_pair_grading_of_value
    {E : Type*} [TopologicalSpace E] [AddCommGroup E] [Module ℝ E]
    (Q : Submodule ℝ E) (p : ℕ → Seminorm ℝ E) (s : ℕ)
    (z : Q × ℝ) (x : E) (q : ℝ) (hx : z.1.val = x) (hq : z.2 = q) :
    pairGrading (fun n => (p n).comp Q.subtype) realGrading s z = p s x + |q| := by
  rw [n08_subtype_pair_grading, hx, hq]

private theorem n08_subtype_pair_sub_grading
    {E : Type*} [TopologicalSpace E] [AddCommGroup E] [Module ℝ E]
    (Q : Submodule ℝ E) (p : ℕ → Seminorm ℝ E) (s : ℕ)
    (z w : Q × ℝ) (a x y : E) (q : ℝ)
    (hz : z.1.val = y - a) (hw : w.1.val = x - a)
    (hzq : z.2 = q) (hwq : w.2 = q) :
    pairGrading (fun n => (p n).comp Q.subtype) realGrading s (z - w) =
      p s (y - x) := by
  have hsub : (y - a) - (x - a) = y - x := by abel
  change p s (z.1.val - w.1.val) + ‖z.2 - w.2‖ = _
  rw [hz, hw, hzq, hwq, hsub, sub_self, norm_zero, add_zero]

private theorem n08_subtype_pair_zero_grading
    {E : Type*} [TopologicalSpace E] [AddCommGroup E] [Module ℝ E]
    (Q : Submodule ℝ E) (p : ℕ → Seminorm ℝ E) (s : ℕ)
    (z : Q × ℝ) (x : E) (hx : z.1.val = x) (hq : z.2 = 0) :
    pairGrading (fun n => (p n).comp Q.subtype) realGrading s z = p s x := by
  simpa only [abs_zero, add_zero] using
    n08_subtype_pair_grading_of_value Q p s z x 0 hx hq

private theorem n08_pair_zero_mem
    {E : Type*} [TopologicalSpace E] [AddCommGroup E] [Module ℝ E]
    (p : ℕ → Seminorm ℝ E) (base : ℕ) {ε : ℝ} (hε : 0 < ε) :
    (0 : E × ℝ) ∈ {z | p base z.1 < ε ∧ |z.2| < ε} := by
  constructor
  · change p base (0 : E) < ε
    simpa only [map_zero] using hε
  · change |(0 : ℝ)| < ε
    simpa only [abs_zero] using hε

variable {D : ReferenceData} {T : MaterialData} {S : PhysicalSpacesData}
  {C : NonlinearGeometryData S} {R : ReturnEquationData S}
  {base loss : ℕ} {ε : ℝ}

theorem n08ControlMeanCoordinate_bound (S : PhysicalSpacesData) (m s : ℕ)
    (u : CircleSpace S) :
    |n08ControlMeanCoordinate S m u| ≤
      n08ControlMeanConstant * (S.circle (3 / 4 : ℝ)).grading s u := by
  rw [n08ControlMeanCoordinate_apply]
  have h := lp.norm_apply_le_norm (by norm_num : (2 : ℝ≥0∞) ≠ 0)
    (n08ControlRestriction S u) m
  have hzero := n08ControlRestriction_norm_le S u
  have hgrade : (S.circle (3 / 4 : ℝ)).grading 0 u ≤
      (S.circle (3 / 4 : ℝ)).grading s u :=
    gradedSeminorm_monotone _ _ (Nat.zero_le s) u
  exact (by simpa only [Real.norm_eq_abs] using h).trans
    (hzero.trans (mul_le_mul_of_nonneg_left hgrade n08ControlMeanConstant_nonneg))

theorem n08CircleSectorPoint_val (hS : IsPhysicalSpaces D T S)
    (href : referenceStateConditions D S C) {x : AnnularState S}
    (hs : stateSector S x) (q : ℝ) :
    (n08CircleSectorPoint hS C (x, q)).1.val = x - C.referenceState :=
  n08_stateProjection_eq_self hS _ ((stateSectorSubmodule S).sub_mem hs href.stateSector)

theorem n08CircleSectorPoint_grading (hS : IsPhysicalSpaces D T S)
    (href : referenceStateConditions D S C) {x : AnnularState S}
    (hs : stateSector S x) (q : ℝ) (s : ℕ) :
    pairGrading (sectorGrading S) realGrading s (n08CircleSectorPoint hS C (x, q)) =
      stateGrading S s (x - C.referenceState) + |q| := by
  exact n08_subtype_pair_grading_of_value (stateSectorSubmodule S) (stateGrading S) s
    (n08CircleSectorPoint hS C (x, q)) (x - C.referenceState) q
    (n08CircleSectorPoint_val hS href hs q) rfl

theorem n08CircleSectorPoint_sub_grading (hS : IsPhysicalSpaces D T S)
    (href : referenceStateConditions D S C) {x y : AnnularState S}
    (hsx : stateSector S x) (hsy : stateSector S y) (q : ℝ) (s : ℕ) :
    pairGrading (sectorGrading S) realGrading s
      (n08CircleSectorPoint hS C (y, q) - n08CircleSectorPoint hS C (x, q)) =
      stateGrading S s (y - x) := by
  exact n08_subtype_pair_sub_grading (stateSectorSubmodule S) (stateGrading S) s
    (n08CircleSectorPoint hS C (y, q)) (n08CircleSectorPoint hS C (x, q))
    C.referenceState x y q (n08CircleSectorPoint_val hS href hsy q)
    (n08CircleSectorPoint_val hS href hsx q) rfl rfl

def n08ControlSectorDirection (hS : IsPhysicalSpaces D T S) (m : ℕ) :
    StateDirections S × ℝ :=
  (n08_sectorProjection hS (0, 0, n08ControlBasis hS m, 0), 0)

theorem n08ControlSectorDirection_grading (hS : IsPhysicalSpaces D T S) (m s : ℕ) :
    pairGrading (sectorGrading S) realGrading s (n08ControlSectorDirection hS m) =
      (S.circle (3 / 4 : ℝ)).grading s (n08ControlBasis hS m) := by
  exact (n08_subtype_pair_zero_grading (stateSectorSubmodule S) (stateGrading S) s
    (n08ControlSectorDirection hS m) (0, (0, (n08ControlBasis hS m, 0)))
    (n08_stateProjection_eq_self hS _ (n08ControlBasis_direction_sector hS m)) rfl).trans
      (n08_controlDirection_grading S s (n08ControlBasis hS m))

theorem n08_sectorNeighborhood_convex (S : PhysicalSpacesData) (base : ℕ) (ε q0 : ℝ) :
    Convex ℝ (sectorNeighborhood S base ε q0) := by
  have h := ((sectorGrading S base).convex_ball 0 ε).prod
    ((normSeminorm ℝ ℝ).convex_ball 0 q0)
  convert h using 1
  ext z
  simp only [sectorNeighborhood, Set.mem_setOf_eq, Set.mem_prod, Seminorm.mem_ball_zero]
  rfl

private theorem n08_graded_diagonal_difference
    {E X Y : Type*}
    [TopologicalSpace E] [AddCommGroup E] [Module ℝ E]
    [TopologicalSpace X] [AddCommGroup X] [Module ℝ X]
    [TopologicalSpace Y] [AddCommGroup Y] [Module ℝ Y]
    (stateP : ℕ → Seminorm ℝ E) (p : ℕ → Seminorm ℝ X) (r : ℕ → Seminorm ℝ Y)
    (hstateP : Monotone stateP) (hp : Monotone p)
    (ref : E) (sector : Set E) (Φ : E × ℝ → X)
    {U : Set X} {f : X → Y} (J : SmoothDirections U f)
    (base : ℕ) (ε : ℝ) (hε : 0 < ε) (hconvex : Convex ℝ U)
    (hΦ : ∀ x ∈ sector, ∀ q s,
      p s (Φ (x, q)) = stateP s (x - ref) + |q|)
    (hΦsub : ∀ x ∈ sector, ∀ y ∈ sector, ∀ q s,
      p s (Φ (y, q) - Φ (x, q)) = stateP s (y - x))
    (hmem : ∀ x ∈ sector, ∀ q,
      stateP base (x - ref) < ε → |q| < ε → Φ (x, q) ∈ U)
    (L : ℕ → Y →L[ℝ] ℝ) (A : ℝ) (hA : 0 ≤ A)
    (hL : ∀ m s u, |L m u| ≤ A * r s u)
    (V : ℕ → X) (B : ℕ → ℝ) (hB : ∀ s, 0 ≤ B s)
    (M : ℕ → ℝ) (hM : ∀ m, 1 ≤ M m)
    (hV : ∀ m s, p s (V m) ≤ B s * M m ^ s)
    (d : E × ℝ → ℕ → ℝ)
    (hd : ∀ z m, d z m = L m (J.D 1 (Φ z) (Fin.cons (V m) Fin.elim0)))
    (hsecond : ∃ l a : ℕ, ∃ ρ K : ℝ, 0 < ρ ∧ 0 ≤ K ∧
      ∀ z ∈ U, p a (z - 0) < ρ → ∀ v : Fin 2 → X,
        r a (J.D 2 z v) ≤ K * tameJetSize p 2 a l a z v) :
    ∃ b : ℕ, ∃ δ K : ℝ, base ≤ b ∧ 0 < δ ∧ δ ≤ ε ∧ 0 ≤ K ∧
      ∀ x y : E, ∀ q : ℝ,
        (stateP b (x - ref) < δ ∧ |q| < δ) →
        (stateP b (y - ref) < δ ∧ |q| < δ) →
        x ∈ sector → y ∈ sector → ∀ m,
        |d (y, q) m - d (x, q) m| ≤ K * M m ^ b * stateP b (y - x) := by
  obtain ⟨l, a, ρ, K, hρ, hK, hjet⟩ := hsecond
  let n := max a (a + l)
  let b := max base n
  let δ := min ε (min ρ 1) / 4
  have hδ : 0 < δ := div_pos (lt_min hε (lt_min hρ zero_lt_one)) (by norm_num)
  have hδε : δ ≤ ε := by
    have h := min_le_left ε (min ρ 1)
    dsimp only [δ]
    linarith only [h, hε]
  have hδρ : 2 * δ < min ρ 1 := by
    have h := min_le_right ε (min ρ 1)
    have hr : 0 < min ρ 1 := lt_min hρ zero_lt_one
    dsimp only [δ]
    linarith only [h, hr]
  let Kout := A * (4 * K) * B n
  have hn : 0 ≤ A * (4 * K) := mul_nonneg hA (mul_nonneg (by norm_num) hK)
  refine ⟨b, δ, Kout, le_max_left _ _, hδ, hδε, mul_nonneg hn (hB n), ?_⟩
  intro x y q hx hy hsx hsy m
  have hX : Φ (x, q) ∈ U := hmem x hsx q
    ((hstateP (le_max_left base n) _).trans_lt (hx.1.trans_le hδε)) (hx.2.trans_le hδε)
  have hY : Φ (y, q) ∈ U := hmem y hsy q
    ((hstateP (le_max_left base n) _).trans_lt (hy.1.trans_le hδε)) (hy.2.trans_le hδε)
  have hsmallX : p n (Φ (x, q)) < min ρ 1 := by
    rw [hΦ x hsx q n]
    have hg := hstateP (le_max_right base n) (x - ref)
    exact (add_lt_add (hg.trans_lt hx.1) hx.2).trans
      (by simpa only [two_mul] using hδρ)
  have hsmallY : p n (Φ (y, q)) < min ρ 1 := by
    rw [hΦ y hsy q n]
    have hg := hstateP (le_max_right base n) (y - ref)
    exact (add_lt_add (hg.trans_lt hy.1) hy.2).trans
      (by simpa only [two_mul] using hδρ)
  have htwo : ∀ z ∈ U, p a z < ρ → ∀ v w,
      r a (J.D 2 z (Fin.cons v (Fin.cons w Fin.elim0))) ≤
        K * oneHighVariationWeight p a (a + l) z (Fin.cons v (Fin.cons w Fin.elim0)) := by
    intro z hz hnear v w
    simpa only [tameJetSize, oneHighVariationWeight] using
      hjet z hz (by simpa only [sub_zero] using hnear) (Fin.cons v (Fin.cons w Fin.elim0))
  have hdiff := n08_firstJet_tame_difference_bound J p hp (r a) hK htwo (L m)
    hA (hL m a) (v := V m) hsmallX hsmallY
    (fun t ht => hconvex.add_smul_sub_mem hX hY ht)
  have hVb : p n (V m) ≤ B n * M m ^ b :=
    (hV m n).trans (mul_le_mul_of_nonneg_left
      (pow_le_pow_right₀ (hM m) (le_max_right base n)) (hB n))
  have hdiffGrade : p n (Φ (y, q) - Φ (x, q)) ≤ stateP b (y - x) :=
    (hΦsub x hsx y hsy q n).trans_le (hstateP (le_max_right base n) _)
  have hfinal := hdiff.trans (mul_le_mul
    (mul_le_mul_of_nonneg_left hdiffGrade hn) hVb (apply_nonneg _ _)
    (mul_nonneg hn (apply_nonneg _ _)))
  rw [hd, hd]
  convert hfinal using 1 <;> dsimp only [Kout] <;> ring

private theorem n08CircleSectorJet_second_bound
    (hR : N02Properties D T S C R base ε) (hε : 0 < ε) :
    ∃ l a : ℕ, ∃ ρ K : ℝ, 0 < ρ ∧ 0 ≤ K ∧
      ∀ z ∈ sectorNeighborhood S base ε ε,
        pairGrading (sectorGrading S) realGrading a (z - 0) < ρ →
        ∀ v : Fin 2 → StateDirections S × ℝ,
          (S.circle (3 / 4 : ℝ)).grading a ((n08CircleSectorJet hR).D 2 z v) ≤
            K * tameJetSize (pairGrading (sectorGrading S) realGrading) 2 a l a z v := by
  have hzero : (0 : StateDirections S × ℝ) ∈ sectorNeighborhood S base ε ε :=
    n08_pair_zero_mem (sectorGrading S) base hε
  obtain ⟨l, a, ρ, hρ, hb⟩ := (n08_return_smoothTame hR).choose_spec 2 0 hzero
  obtain ⟨K, hK, hKb⟩ := hb a le_rfl
  exact ⟨l, a, ρ, K, hρ, hK, hKb⟩

private theorem n08CircleSectorPoint_mem_of_sector
    (hS : IsPhysicalSpaces D T S) (href : referenceStateConditions D S C)
    {x : AnnularState S} (hs : stateSector S x) {q : ℝ}
    (hx : stateGrading S base (x - C.referenceState) < ε) (hq : |q| < ε) :
    n08CircleSectorPoint hS C (x, q) ∈ sectorNeighborhood S base ε ε :=
  n08CircleSectorPoint_mem hS href (z := (x, q))
    ⟨(congrArg (fun y : AnnularState S => stateGrading S base (y - C.referenceState))
      (n08_stateProjection_eq_self hS x hs)).trans_lt hx, hq⟩

private theorem n08ControlSectorDirection_bound
    (hT : IsMaterialData D T) (hS : IsPhysicalSpaces D T S)
    (hD : IsAccumulatingProfile D) (m s : ℕ) :
    pairGrading (sectorGrading S) realGrading s (n08ControlSectorDirection hS m) ≤
      n08ControlBasisConstant s * T.M (T.sample m) ^ s :=
  (n08ControlSectorDirection_grading hS m s).trans_le
    (n08ControlBasis_grading_le hS m s (n08_material_sample_bounds hD hT m).1
      (n08_material_sample_bounds hD hT m).2)

/-- The genuine control diagonal is locally Lipschitz in the state with a
single polynomial material loss, uniformly over its label. -/
theorem n08CircleDiagonal_state_difference_bound
    (hT : IsMaterialData D T) (hS : IsPhysicalSpaces D T S)
    (hN : N01Properties D T S C base loss ε)
    (hR : N02Properties D T S C R base ε) :
    ∃ b : ℕ, ∃ δ K : ℝ, base ≤ b ∧ 0 < δ ∧ δ ≤ ε ∧ 0 ≤ K ∧
      ∀ x y : AnnularState S, ∀ q : ℝ,
        (x, q) ∈ stateNeighborhood S C b δ →
        (y, q) ∈ stateNeighborhood S C b δ →
        stateSector S x → stateSector S y → ∀ m,
        |n08CircleDiagonal hS hR (y, q) m - n08CircleDiagonal hS hR (x, q) m| ≤
          K * T.M (T.sample m) ^ b * stateGrading S b (y - x) := by
  exact n08_graded_diagonal_difference
    (E := AnnularState S) (X := StateDirections S × ℝ) (Y := CircleSpace S)
    (stateGrading S) (pairGrading (sectorGrading S) realGrading)
    (S.circle (3 / 4 : ℝ)).grading (solve_stateGrading_monotone S)
    (pairGrading_monotone (solve_sectorGrading_monotone S) (fun _ _ _ _ => le_rfl))
    C.referenceState (stateSector S) (n08CircleSectorPoint hS C) (n08CircleSectorJet hR)
    base ε hN.2.1 (n08_sectorNeighborhood_convex S base ε ε)
    (fun x hs q s => n08CircleSectorPoint_grading hS hN.2.2.1 (x := x) hs q s)
    (fun x hsx y hsy q s =>
      n08CircleSectorPoint_sub_grading hS hN.2.2.1 (x := x) (y := y) hsx hsy q s)
    (fun x hs q hx hq =>
      n08CircleSectorPoint_mem_of_sector hS hN.2.2.1 (x := x) hs (q := q) hx hq)
    (n08ControlMeanCoordinate S) n08ControlMeanConstant n08ControlMeanConstant_nonneg
    (n08ControlMeanCoordinate_bound S) (n08ControlSectorDirection hS)
    n08ControlBasisConstant n08ControlBasisConstant_nonneg (fun m => T.M (T.sample m))
    (fun m => (n08_material_sample_bounds hN.1.1 hT m).2)
    (n08ControlSectorDirection_bound hT hS hN.1.1) (n08CircleDiagonal hS hR)
    (n08CircleDiagonal_value hS hR) (n08CircleSectorJet_second_bound hR hN.2.1)

end ContinuousFlexibility.Statements
