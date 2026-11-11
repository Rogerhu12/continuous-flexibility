import ContinuousFlexibility.Statements.ScalarWeighted
import ContinuousFlexibility.Analysis.TameElementaryCalculus
import ContinuousFlexibility.Analysis.TameTransfer

/-!
# Fixed-neighbourhood scalar derivative towers

The weighted scalar interfaces require one base order and one derivative loss
for the entire directional tower.  These closure lemmas retain those quantifiers.
In particular, a merely local `SmoothTameOn` estimate is never promoted to a
uniform estimate.  The input is always the actual uniform tower bound.
-/

noncomputable section

namespace ContinuousFlexibility.Statements

open Set
open scoped BigOperators
open ContinuousFlexibility.Analysis

section General

variable {E F G : Type*}
  [TopologicalSpace E] [AddCommGroup E] [Module ℝ E]
  [TopologicalSpace F] [AddCommGroup F] [Module ℝ F]
  [TopologicalSpace G] [AddCommGroup G] [Module ℝ G]
  {p : ℕ → Seminorm ℝ E} {q : ℕ → Seminorm ℝ F}
  {r : ℕ → Seminorm ℝ G} {U V : Set E} {f g : E → F}
  {base loss : ℕ}

/-- A uniform estimate supplies the local estimate with exactly its original
base and loss.  No shrinking of the original domain is needed. -/
theorem UniformScalarTowerEstimate.smoothTameOn
    {J : SmoothDirections U f}
    (hJ : UniformScalarTowerEstimate p q U base loss f J) :
    SmoothTameOn p q U f := by
  refine ⟨J, fun k x₀ hx₀ => ⟨loss, base, 1, zero_lt_one, ?_⟩⟩
  intro s hs
  obtain ⟨C, hC, hbound⟩ := hJ k s hs
  exact ⟨C, hC, fun x hx _ v => hbound x hx v⟩

/-- Construct the full weighted-interface predicate directly from a uniform
tower.  Its first conjunct is a consequence, not an additional premise. -/
theorem fixedNeighborhoodSmoothTame_of_uniform
    (J : SmoothDirections U f)
    (hJ : UniformScalarTowerEstimate p q U base loss f J) :
    FixedNeighborhoodSmoothTame p q U base loss f :=
  ⟨hJ.smoothTameOn, J, hJ⟩

theorem fixedNeighborhoodSmoothTame_iff_uniform :
    FixedNeighborhoodSmoothTame p q U base loss f ↔
      ∃ J : SmoothDirections U f, UniformScalarTowerEstimate p q U base loss f J :=
  ⟨fun h => h.2, fun ⟨J, hJ⟩ => fixedNeighborhoodSmoothTame_of_uniform J hJ⟩

/-- Enlarge the two fixed orders without changing the tower or its domain. -/
theorem UniformScalarTowerEstimate.weaken
    {J : SmoothDirections U f}
    (hJ : UniformScalarTowerEstimate p q U base loss f J) (hp : Monotone p)
    {base' loss' : ℕ} (hb : base ≤ base') (hl : loss ≤ loss') :
    UniformScalarTowerEstimate p q U base' loss' f J := by
  intro k s hs
  obtain ⟨C, hC, hbound⟩ := hJ k s (hb.trans hs)
  refine ⟨C, hC, fun x hx v => (hbound x hx v).trans ?_⟩
  exact mul_le_mul_of_nonneg_left (tameJetSize_mono hp hl hb k s x v) hC

theorem FixedNeighborhoodSmoothTame.weaken
    (hf : FixedNeighborhoodSmoothTame p q U base loss f) (hp : Monotone p)
    {base' loss' : ℕ} (hb : base ≤ base') (hl : loss ≤ loss') :
    FixedNeighborhoodSmoothTame p q U base' loss' f := by
  obtain ⟨J, hJ⟩ := hf.2
  exact fixedNeighborhoodSmoothTame_of_uniform J (hJ.weaken hp hb hl)

/-- Restriction keeps the same derivative tower, base order and loss. -/
theorem UniformScalarTowerEstimate.restrict
    {J : SmoothDirections U f}
    (hJ : UniformScalarTowerEstimate p q U base loss f J)
    (hV : IsOpen V) (hVU : V ⊆ U) :
    UniformScalarTowerEstimate p q V base loss f (smoothDirectionsRestrict J hV hVU) := by
  intro k s hs
  obtain ⟨C, hC, hbound⟩ := hJ k s hs
  exact ⟨C, hC, fun x hx v => hbound x (hVU hx) v⟩

theorem FixedNeighborhoodSmoothTame.restrict
    (hf : FixedNeighborhoodSmoothTame p q U base loss f)
    (hV : IsOpen V) (hVU : V ⊆ U) :
    FixedNeighborhoodSmoothTame p q V base loss f := by
  obtain ⟨J, hJ⟩ := hf.2
  exact fixedNeighborhoodSmoothTame_of_uniform (smoothDirectionsRestrict J hV hVU)
    (hJ.restrict hV hVU)

/-- The linear tower has the same bound for every derivative order: only
orders zero and one are nonzero. -/
theorem uniformScalarTowerEstimate_continuousLinear (L : E →L[ℝ] F)
    (hL : IsTameLinear p q L.toLinearMap loss base) :
    UniformScalarTowerEstimate p q univ base loss L (smoothDirectionsLinear L) := by
  intro k s hs
  obtain ⟨C, hC⟩ := hL s hs
  refine ⟨C, C.coe_nonneg, ?_⟩
  intro x _ v
  change q s (continuousLinearJets L k x v) ≤ C * tameJetSize p k s loss base x v
  cases k with
  | zero =>
      rw [tameJetSize_zero]
      simp only [continuousLinearJets, ContinuousMultilinearMap.constOfIsEmpty_apply]
      exact (hC x).trans (mul_le_mul_of_nonneg_left (by linarith) C.coe_nonneg)
  | succ k =>
      cases k with
      | zero =>
          rw [tameJetSize_one]
          simp only [continuousLinearJets, ContinuousMultilinearMap.ofSubsingleton_apply_apply]
          apply (hC (v 0)).trans
          apply mul_le_mul_of_nonneg_left _ C.coe_nonneg
          have hpos : 0 ≤ (1 + p (s + loss) x) * p base (v 0) := by positivity
          linarith
      | succ k =>
          simp only [continuousLinearJets, zero_apply, map_zero]
          exact mul_nonneg C.coe_nonneg (tameJetSize_nonneg _ _ _ _ _ _ _)

theorem fixedNeighborhoodSmoothTame_continuousLinear (L : E →L[ℝ] F)
    (hL : IsTameLinear p q L.toLinearMap loss base) :
    FixedNeighborhoodSmoothTame p q univ base loss L :=
  fixedNeighborhoodSmoothTame_of_uniform (smoothDirectionsLinear L)
    (uniformScalarTowerEstimate_continuousLinear L hL)

/-- Postcomposition applies the continuous linear map to every actual
derivative.  Continuity and the quotient-limit recurrence are transported. -/
def smoothDirectionsScalarPostcompose (J : SmoothDirections U f) (L : F →L[ℝ] G) :
    SmoothDirections U (fun x => L (f x)) where
  open_domain := J.open_domain
  D := fun n x => L.compContinuousMultilinearMap (J.D n x)
  zero := fun x hx => by
    simp only [ContinuousLinearMap.compContinuousMultilinearMap_coe, Function.comp_apply]
    rw [J.zero x hx]
  continuous := fun n => by
    simpa only [ContinuousLinearMap.compContinuousMultilinearMap_coe, Function.comp_def] using
      L.continuous.comp_continuousOn (J.continuous n)
  derivative := fun n x hx v w => by
    simpa only [ContinuousLinearMap.compContinuousMultilinearMap_coe, Function.comp_apply] using
      (J.derivative n x hx v w).clm_comp L

theorem smoothDirectionsScalarPostcompose_apply
    (J : SmoothDirections U f) (L : F →L[ℝ] G) (k : ℕ) (x : E) (v : Fin k → E) :
    (smoothDirectionsScalarPostcompose J L).D k x v = L (J.D k x v) := by
  exact congrFun (ContinuousLinearMap.compContinuousMultilinearMap_coe L (J.D k x)) v

/-- A fixed-loss linear output operation adds its loss to the original
loss, and takes the maximum of the two base orders. -/
theorem UniformScalarTowerEstimate.postcompose
    {J : SmoothDirections U f}
    (hJ : UniformScalarTowerEstimate p q U base loss f J) (hp : Monotone p)
    (L : F →L[ℝ] G) {linearLoss linearBase : ℕ}
    (hL : IsTameLinear q r L.toLinearMap linearLoss linearBase) :
    UniformScalarTowerEstimate p r U (max base linearBase) (linearLoss + loss)
      (fun x => L (f x)) (smoothDirectionsScalarPostcompose J L) := by
  intro k s hs
  obtain ⟨C₁, hC₁⟩ := hL s ((le_max_right _ _).trans hs)
  obtain ⟨C₂, hC₂, hbound⟩ := hJ k (s + linearLoss)
    (((le_max_left _ _).trans hs).trans (Nat.le_add_right _ _))
  refine ⟨C₁ * C₂, mul_nonneg C₁.coe_nonneg hC₂, ?_⟩
  intro x hx v
  rw [smoothDirectionsScalarPostcompose_apply]
  have hsize : tameJetSize p k (s + linearLoss) loss base x v ≤
      tameJetSize p k s (linearLoss + loss) (max base linearBase) x v := by
    simpa only [tameJetSize, Nat.add_assoc] using
      tameJetSize_mono hp (le_refl loss) (le_max_left base linearBase)
        k (s + linearLoss) x v
  calc
    r s (L (J.D k x v)) ≤ C₁ * q (s + linearLoss) (J.D k x v) := hC₁ _
    _ ≤ C₁ * (C₂ * tameJetSize p k (s + linearLoss) loss base x v) :=
      mul_le_mul_of_nonneg_left (hbound x hx v) C₁.coe_nonneg
    _ ≤ C₁ * (C₂ * tameJetSize p k s (linearLoss + loss)
        (max base linearBase) x v) :=
      mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_left hsize hC₂) C₁.coe_nonneg
    _ = _ := by simp only [tameJetSize]; ring

theorem FixedNeighborhoodSmoothTame.postcompose
    (hf : FixedNeighborhoodSmoothTame p q U base loss f) (hp : Monotone p)
    (L : F →L[ℝ] G) {linearLoss linearBase : ℕ}
    (hL : IsTameLinear q r L.toLinearMap linearLoss linearBase) :
    FixedNeighborhoodSmoothTame p r U (max base linearBase) (linearLoss + loss)
      (fun x => L (f x)) := by
  obtain ⟨J, hJ⟩ := hf.2
  exact fixedNeighborhoodSmoothTame_of_uniform (smoothDirectionsScalarPostcompose J L)
    (hJ.postcompose hp L hL)

end General

section Addition

variable {E F : Type*}
  [TopologicalSpace E] [AddCommGroup E] [Module ℝ E]
  [TopologicalSpace F] [AddCommGroup F] [Module ℝ F] [IsTopologicalAddGroup F]
  {p : ℕ → Seminorm ℝ E} {q : ℕ → Seminorm ℝ F}
  {U : Set E} {f g : E → F} {base₁ base₂ loss₁ loss₂ : ℕ}

/-- Sums share the larger of the original base orders and losses, uniformly
for every directional order on the same domain. -/
theorem UniformScalarTowerEstimate.add
    {J : SmoothDirections U f} {K : SmoothDirections U g}
    (hJ : UniformScalarTowerEstimate p q U base₁ loss₁ f J)
    (hK : UniformScalarTowerEstimate p q U base₂ loss₂ g K) (hp : Monotone p) :
    UniformScalarTowerEstimate p q U (max base₁ base₂) (max loss₁ loss₂)
      (fun x => f x + g x) (smoothDirectionsAdd J K) := by
  intro k s hs
  obtain ⟨C₁, hC₁, hbound₁⟩ := hJ k s ((le_max_left _ _).trans hs)
  obtain ⟨C₂, hC₂, hbound₂⟩ := hK k s ((le_max_right _ _).trans hs)
  refine ⟨C₁ + C₂, add_nonneg hC₁ hC₂, ?_⟩
  intro x hx v
  have h₁ := (hbound₁ x hx v).trans (mul_le_mul_of_nonneg_left
    (tameJetSize_mono hp (le_max_left loss₁ loss₂) (le_max_left base₁ base₂) k s x v) hC₁)
  have h₂ := (hbound₂ x hx v).trans (mul_le_mul_of_nonneg_left
    (tameJetSize_mono hp (le_max_right loss₁ loss₂) (le_max_right base₁ base₂) k s x v) hC₂)
  change q s ((J.D k x + K.D k x) v) ≤
    (C₁ + C₂) * tameJetSize p k s (max loss₁ loss₂) (max base₁ base₂) x v
  rw [add_apply]
  calc
    _ ≤ q s (J.D k x v) + q s (K.D k x v) := map_add_le_add _ _ _
    _ ≤ C₁ * tameJetSize p k s (max loss₁ loss₂) (max base₁ base₂) x v +
        C₂ * tameJetSize p k s (max loss₁ loss₂) (max base₁ base₂) x v := add_le_add h₁ h₂
    _ = _ := by ring

theorem FixedNeighborhoodSmoothTame.add
    (hf : FixedNeighborhoodSmoothTame p q U base₁ loss₁ f)
    (hg : FixedNeighborhoodSmoothTame p q U base₂ loss₂ g) (hp : Monotone p) :
    FixedNeighborhoodSmoothTame p q U (max base₁ base₂) (max loss₁ loss₂)
      (fun x => f x + g x) := by
  obtain ⟨J, hJ⟩ := hf.2
  obtain ⟨K, hK⟩ := hg.2
  exact fixedNeighborhoodSmoothTame_of_uniform (smoothDirectionsAdd J K) (hJ.add hK hp)

end Addition

section FiniteOutputs

variable {E : Type*} [TopologicalSpace E] [AddCommGroup E] [Module ℝ E]
  {ι : Type*} {F : ι → Type*}
  [∀ i, TopologicalSpace (F i)] [∀ i, AddCommGroup (F i)] [∀ i, Module ℝ (F i)]
  {U : Set E} {f : ∀ i, E → F i}

/-- A finite vector of actual towers.  This also treats the empty vector:
openness is supplied separately instead of choosing one coordinate. -/
def smoothDirectionsScalarPi (hU : IsOpen U) (J : ∀ i, SmoothDirections U (f i)) :
    SmoothDirections U (fun x i => f i x) where
  open_domain := hU
  D := fun k x => ContinuousMultilinearMap.pi (fun i => (J i).D k x)
  zero := fun x hx => by
    funext i
    rw [ContinuousMultilinearMap.pi_apply, (J i).zero x hx]
  continuous := fun k => by
    apply continuousOn_pi.mpr
    intro i
    simpa only [ContinuousMultilinearMap.pi_apply] using (J i).continuous k
  derivative := fun k x hx v w => by
    unfold HasProjectiveLineDerivAt HasProjectiveCurveDerivAt
    apply tendsto_pi_nhds.mpr
    intro i
    simpa only [HasProjectiveLineDerivAt, HasProjectiveCurveDerivAt,
      Pi.smul_apply, Pi.sub_apply, ContinuousMultilinearMap.pi_apply] using
      (J i).derivative k x hx v w

private theorem scalarFiniteSeminorm_apply (I : Finset ι)
    (q : ∀ i, Seminorm ℝ (F i)) (x : ∀ i, F i) :
    (∑ i ∈ I, (q i).comp (LinearMap.proj i)) x = ∑ i ∈ I, q i (x i) := by
  classical
  induction I using Finset.induction_on with
  | empty => simp only [Finset.sum_empty, zero_apply]
  | @insert i I hi ih =>
      rw [Finset.sum_insert hi, add_apply, ih, Finset.sum_insert hi,
        Seminorm.comp_apply, LinearMap.proj_apply]

/-- Assemble finitely many components with the sum grading used by the
seven jet outputs and the three coefficient outputs. -/
theorem uniformScalarTowerEstimate_pi [Fintype ι]
    {p : ℕ → Seminorm ℝ E} {q : ∀ i, ℕ → Seminorm ℝ (F i)}
    {base loss : ℕ} (hU : IsOpen U) (J : ∀ i, SmoothDirections U (f i))
    (hJ : ∀ i, UniformScalarTowerEstimate p (q i) U base loss (f i) (J i)) :
    UniformScalarTowerEstimate p
      (fun s => ∑ i, (q i s).comp (LinearMap.proj i)) U base loss
      (fun x i => f i x) (smoothDirectionsScalarPi hU J) := by
  classical
  intro k s hs
  choose C hC hbound using fun i => hJ i k s hs
  refine ⟨∑ i, C i, Finset.sum_nonneg (fun i _ => hC i), ?_⟩
  intro x hx v
  rw [scalarFiniteSeminorm_apply]
  simp only [smoothDirectionsScalarPi, ContinuousMultilinearMap.pi_apply]
  calc
    ∑ i, q i s ((J i).D k x v) ≤ ∑ i, C i * tameJetSize p k s loss base x v :=
      Finset.sum_le_sum (fun i _ => hbound i x hx v)
    _ = _ := by rw [Finset.sum_mul]; rfl

theorem fixedNeighborhoodSmoothTame_pi [Fintype ι]
    {p : ℕ → Seminorm ℝ E} {q : ∀ i, ℕ → Seminorm ℝ (F i)}
    {base loss : ℕ} (hU : IsOpen U)
    (hf : ∀ i, FixedNeighborhoodSmoothTame p (q i) U base loss (f i)) :
    FixedNeighborhoodSmoothTame p
      (fun s => ∑ i, (q i s).comp (LinearMap.proj i)) U base loss
      (fun x i => f i x) := by
  choose J hJ using fun i => (hf i).2
  exact fixedNeighborhoodSmoothTame_of_uniform (smoothDirectionsScalarPi hU J)
    (uniformScalarTowerEstimate_pi hU J hJ)

end FiniteOutputs

end ContinuousFlexibility.Statements
