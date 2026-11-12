import ContinuousFlexibility.Analysis.CirclePositiveJetAssembly

/-!
# Circle towers from positive-order bounds on local neighbourhoods

Each parameter order may use its own open convex neighbourhood of the
base point. That neighbourhood is chosen before the circle output order.
The lifted jets decode to the original scalar family everywhere on the
given domain. Joint continuity at order n only uses a local bound at n+1;
the original scalar derivatives and second envelopes give the same genuine
projective line derivatives on the full domain.
-/

noncomputable section

namespace ContinuousFlexibility.Analysis

open Set Filter ContinuousFlexibility.Statements
open scoped Topology BigOperators

variable {E : Type*} [TopologicalSpace E] [AddCommGroup E] [Module ℝ E]
  [IsTopologicalAddGroup E] [ContinuousSMul ℝ E]
  {F : ℕ → Type*} [∀ s, NormedAddCommGroup (F s)] [∀ s, NormedSpace ℝ (F s)]
  {bond : ∀ s, F (s + 1) →L[ℝ] F s} {U : Set E}

theorem continuousOn_projectiveJets_of_locally_positive_seminorm_bounds
    (A : ∀ n : ℕ, E → E [×n]→L[ℝ] ProjectiveLimit F bond)
    (hline : ∀ n x, x ∈ U → ∀ (v : Fin n → E) (w : E),
      HasProjectiveLineDerivAt (fun y => A n y v) (A (n + 1) x (Fin.cons w v)) x w)
    (hbound : ∀ n x, x ∈ U → ∃ V : Set E,
      IsOpen V ∧ Convex ℝ V ∧ x ∈ V ∧ V ⊆ U ∧
        ∀ s, ∃ p : Seminorm ℝ E, ∃ B : ℝ, Continuous p ∧ 0 ≤ B ∧
          ∀ y ∈ V, ∀ v : Fin (n + 1) → E,
            ‖(A (n + 1) y v).val s‖ ≤ B * (1 + p y) * ∏ i, p (v i))
    (n : ℕ) :
    ContinuousOn (fun z : E × (Fin n → E) => A n z.1 z.2) (U ×ˢ univ) := by
  have hcoordinate (s : ℕ) :
      ContinuousOn (fun z : E × (Fin n → E) => (A n z.1 z.2).val s) (U ×ˢ univ) := by
    rintro ⟨x, v⟩ hx
    obtain ⟨V, hV, hcV, hxV, hVU, hbounds⟩ := hbound n x hx.1
    obtain ⟨p, B, hp, hB, hb⟩ := hbounds s
    have hlineV : ∀ j y, y ∈ V → ∀ (v : Fin j → E) (w : E),
        HasProjectiveLineDerivAt (fun z => A j z v)
          (A (j + 1) y (Fin.cons w v)) y w :=
      fun j y hy v w => hline j y (hVU hy) v w
    apply ContinuousAt.continuousWithinAt
    apply tendsto_iff_norm_sub_tendsto_zero.mpr
    let err : E × (Fin n → E) → ℝ := fun z =>
      B * (1 + p x + p (z.1 - x)) * (p (z.1 - x) * ∏ j, p (z.2 j)) +
        ‖(A n x z.2).val s - (A n x v).val s‖
    have hpbase : Continuous (fun z : E × (Fin n → E) => p (z.1 - x)) :=
      hp.comp (continuous_fst.sub continuous_const)
    have hpdirs : Continuous (fun z : E × (Fin n → E) => ∏ j, p (z.2 j)) :=
      continuous_finsetProd _ (fun j _ => hp.comp ((continuous_apply j).comp continuous_snd))
    have hfixed : Continuous (fun z : E × (Fin n → E) => (A n x z.2).val s) :=
      (projectiveCoordinate F bond s).continuous.comp
        ((A n x).cont.comp continuous_snd)
    have herr : Continuous err :=
      ((continuous_const.mul (continuous_const.add hpbase)).mul (hpbase.mul hpdirs)).add
        (hfixed.sub continuous_const).norm
    have herr0 : err (x, v) = 0 := by
      simp only [err, sub_self, map_zero, mul_zero, zero_mul, norm_zero, add_zero]
    have hmem : ∀ᶠ z : E × (Fin n → E) in 𝓝 (x, v), z.1 ∈ V :=
      continuous_fst.continuousAt.eventually (hV.mem_nhds hxV)
    have hupper : ∀ᶠ z : E × (Fin n → E) in 𝓝 (x, v),
        ‖(A n z.1 z.2).val s - (A n x v).val s‖ ≤ err z := by
      filter_upwards [hmem] with z hz
      have hbase := projectiveJet_base_variation_le (U := V)
        A hlineV hcV n s p hB hb hxV hz z.2
      exact (norm_sub_le_norm_sub_add_norm_sub ((A n z.1 z.2).val s) ((A n x z.2).val s)
        ((A n x v).val s)).trans (add_le_add hbase (le_refl _))
    exact squeeze_zero' (Eventually.of_forall (fun _ => norm_nonneg _)) hupper
      (by simpa only [herr0] using herr.tendsto (x, v))
  intro z hz
  rw [ContinuousWithinAt, tendsto_projectiveLimit_iff]
  exact fun s => hcoordinate s z hz

end ContinuousFlexibility.Analysis

namespace ContinuousFlexibility.Statements

open Set Filter ContinuousFlexibility.Analysis
open scoped Topology ENNReal BigOperators

variable {E : Type*} [TopologicalSpace E] [AddCommGroup E] [Module ℝ E]
  [IsTopologicalAddGroup E] [ContinuousSMul ℝ E]
  {T : MaterialData} {γ : ℝ} {S : CircleModelData} {U : Set E}

def CircleLocalPositiveJetNormBounds
    (A : ∀ n : ℕ, E → MultilinearMap ℝ (fun _ : Fin n => E) (ℕ → ℝ → ℝ)) : Prop :=
  ∀ n x, x ∈ U → ∃ V : Set E,
    IsOpen V ∧ Convex ℝ V ∧ x ∈ V ∧ V ⊆ U ∧
      ∀ s, ∃ p : Seminorm ℝ E, ∃ B : ℝ, Continuous p ∧ 0 ≤ B ∧
        ∀ y ∈ V, ∀ v : Fin (n + 1) → E,
          circleNorm T γ s (A (n + 1) y v) ≤ B * (1 + p y) * ∏ i, p (v i)

def circleLocalPositiveJetLift (hS : IsCircleModel T γ S)
    (A : ∀ n : ℕ, E → MultilinearMap ℝ (fun _ : Fin n => E) (ℕ → ℝ → ℝ))
    (hmember : ∀ n x, x ∈ U → ∀ v, CircleMember T γ (A n x v))
    (hbound : CircleLocalPositiveJetNormBounds (T := T) (γ := γ) (U := U) A) :
    ∀ n : ℕ, E → E [×n]→L[ℝ] S.Space
  | 0, x => by
      classical
      exact if hx : x ∈ U then
        ContinuousMultilinearMap.constOfIsEmpty ℝ (fun _ : Fin 0 => E)
          (circleRealize hS (A 0 x Fin.elim0) (hmember 0 x hx Fin.elim0))
        else 0
  | n + 1, x => by
      classical
      exact if hx : x ∈ U then
        liftCircleContinuousMultilinear hS (A (n + 1) x) (hmember (n + 1) x hx) (by
          intro s
          obtain ⟨V, _hV, _hcV, hxV, _hVU, hbounds⟩ := hbound n x hx
          obtain ⟨p, B, hp, _hB, hb⟩ := hbounds s
          exact ⟨p, B * (1 + p x), hp, hb x hxV⟩)
        else 0

theorem circleLocalPositiveJetLift_decode (hS : IsCircleModel T γ S)
    (A : ∀ n : ℕ, E → MultilinearMap ℝ (fun _ : Fin n => E) (ℕ → ℝ → ℝ))
    (hmember : ∀ n x, x ∈ U → ∀ v, CircleMember T γ (A n x v))
    (hbound : CircleLocalPositiveJetNormBounds (T := T) (γ := γ) (U := U) A)
    (n : ℕ) (x : E) (hx : x ∈ U) (v : Fin n → E) :
    S.decode (circleLocalPositiveJetLift hS A hmember hbound n x v) = A n x v := by
  classical
  cases n with
  | zero =>
      have hv : v = Fin.elim0 := Subsingleton.elim _ _
      rw [hv]
      simp only [circleLocalPositiveJetLift, dif_pos hx,
        ContinuousMultilinearMap.constOfIsEmpty_apply, circleRealize_decode]
  | succ n =>
      simp only [circleLocalPositiveJetLift, dif_pos hx]
      exact liftCircleContinuousMultilinear_decode hS (A (n + 1) x)
        (hmember (n + 1) x hx) _ v

theorem circleLocalPositiveJetLift_coordinate_bound (hS : IsCircleModel T γ S)
    (A : ∀ n : ℕ, E → MultilinearMap ℝ (fun _ : Fin n => E) (ℕ → ℝ → ℝ))
    (hmember : ∀ n x, x ∈ U → ∀ v, CircleMember T γ (A n x v))
    (hbound : CircleLocalPositiveJetNormBounds (T := T) (γ := γ) (U := U) A) :
    ∀ n x, x ∈ U → ∃ V : Set E,
      IsOpen V ∧ Convex ℝ V ∧ x ∈ V ∧ V ⊆ U ∧
        ∀ s, ∃ p : Seminorm ℝ E, ∃ B : ℝ, Continuous p ∧ 0 ≤ B ∧
          ∀ y ∈ V, ∀ v : Fin (n + 1) → E,
            ‖(circleLocalPositiveJetLift hS A hmember hbound (n + 1) y v).val s‖ ≤
              B * (1 + p y) * ∏ i, p (v i) := by
  intro n x hx
  obtain ⟨V, hV, hcV, hxV, hVU, hbounds⟩ := hbound n x hx
  refine ⟨V, hV, hcV, hxV, hVU, ?_⟩
  intro s
  obtain ⟨p, B, hp, hB, hb⟩ := hbounds s
  refine ⟨p, B, hp, hB, ?_⟩
  intro y hy v
  have hnorm :
      ‖(circleLocalPositiveJetLift hS A hmember hbound (n + 1) y v).val s‖ =
        circleNorm T γ s
          (S.decode (circleLocalPositiveJetLift hS A hmember hbound (n + 1) y v)) :=
    hS.2.2.2.2.2.2.2 _ s
  have hdecode := circleLocalPositiveJetLift_decode hS A hmember hbound
    (n + 1) y (hVU hy) v
  exact (hnorm.trans (congrArg (circleNorm T γ s) hdecode)).trans_le (hb y hy v)

/-- The actual scalar jets determine one global circle tower, while each
positive parameter order may use a different local seminorm neighbourhood. -/
theorem exists_circle_smoothDirections_of_locally_positive_scalar_jets
    (hS : IsCircleModel T γ S)
    (hM : ∀ m, 0 ≤ T.M (T.sample m)) (hH : ∀ m, 0 ≤ T.H (T.sample m))
    (hU : IsOpen U) (f : E → S.Space)
    (A : ∀ n : ℕ, E → MultilinearMap ℝ (fun _ : Fin n => E) (ℕ → ℝ → ℝ))
    (hmember : ∀ n x, x ∈ U → ∀ v, CircleMember T γ (A n x v))
    (hbound : CircleLocalPositiveJetNormBounds (T := T) (γ := γ) (U := U) A)
    (hzero : ∀ x ∈ U, A 0 x Fin.elim0 = S.decode (f x))
    (hscalar : ∀ n (x w : E) (v : Fin n → E) (t : ℝ), x + t • w ∈ U → ∀ m b θ,
      HasDerivAt (fun u => iteratedDeriv b (A n (x + u • w) v m) θ)
        (iteratedDeriv b (A (n + 1) (x + t • w) (Fin.cons w v) m) θ) t)
    (henergy : CircleJetSecondEnvelopes (T := T) (γ := γ) (U := U) A) :
    ∃ J : SmoothDirections U f, ∀ n x, x ∈ U → ∀ v : Fin n → E,
      S.decode (J.D n x v) = A n x v := by
  let L : ∀ n : ℕ, E → E [×n]→L[ℝ] S.Space :=
    circleLocalPositiveJetLift hS A hmember hbound
  have hzeroL : ∀ x ∈ U, L 0 x Fin.elim0 = f x := by
    intro x hx
    apply hS.2.2.2.2.2.1
    exact (circleLocalPositiveJetLift_decode hS A hmember hbound 0 x hx Fin.elim0).trans
      (hzero x hx)
  have hline : ∀ n x, x ∈ U → ∀ (v : Fin n → E) (w : E),
      HasProjectiveLineDerivAt (fun y => L n y v) (L (n + 1) x (Fin.cons w v)) x w :=
    circleJetFamily_hasProjectiveLineDerivAt hS hM hH hU A L
      (circleLocalPositiveJetLift_decode hS A hmember hbound) hscalar henergy
  let J : SmoothDirections U f := {
    open_domain := hU
    D := L
    zero := hzeroL
    continuous := continuousOn_projectiveJets_of_locally_positive_seminorm_bounds
      (F := fun s => S.level s) (bond := S.bond) L hline
      (circleLocalPositiveJetLift_coordinate_bound hS A hmember hbound)
    derivative := hline }
  refine ⟨J, ?_⟩
  intro n x hx v
  exact circleLocalPositiveJetLift_decode hS A hmember hbound n x hx v

end ContinuousFlexibility.Statements
