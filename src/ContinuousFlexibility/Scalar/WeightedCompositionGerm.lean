import ContinuousFlexibility.Scalar.WeightedCompositionMaps
import ContinuousFlexibility.Scalar.WeightedUniformTameGermOperations

/-!
# Canonical actual scalar composition and its uniform tame germ

The operation is the unique lift of the literal decoded scalar composition
on the whole height space.  The fixed-neighborhood composition theorem gives
its genuine uniform tower near zero by decoder injectivity.  This canonical
operation can then be composed with actual state germs vanishing at their
center, including smooth cutoff extensions of scalar powers.
-/

noncomputable section

namespace ContinuousFlexibility.Statements

open Set Function ContinuousFlexibility.Analysis
open scoped ContDiff

set_option backward.isDefEq.respectTransparency false

namespace SobolevModelData

variable {D : ReferenceData} {T : MaterialData} {γ : ℝ} {A : SobolevModelData}

/-- The canonical lift of the globally defined actual decoded composition. -/
def weightedCompositionMap
    (hT : IsMaterialData D T) (hA : IsSobolevModel D T γ A)
    (hinterp : HasInterpolation A.grading) (hγ : 0 < γ)
    {F : ℝ → ℝ} (hF : ContDiff ℝ ∞ F) (hF0 : F 0 = 0) (u : A.Space) : A.Space :=
  liftHeight hA (fun p => F (A.decode u p))
    (weightedComposition_heightMember hT hA hinterp hγ hF hF0 u)

theorem decode_weightedCompositionMap
    (hT : IsMaterialData D T) (hA : IsSobolevModel D T γ A)
    (hinterp : HasInterpolation A.grading) (hγ : 0 < γ)
    {F : ℝ → ℝ} (hF : ContDiff ℝ ∞ F) (hF0 : F 0 = 0) (u : A.Space) :
    A.decode (weightedCompositionMap hT hA hinterp hγ hF hF0 u) =
      fun p => F (A.decode u p) :=
  decode_liftHeight hA _ _

theorem weightedCompositionMap_zero
    (hT : IsMaterialData D T) (hA : IsSobolevModel D T γ A)
    (hinterp : HasInterpolation A.grading) (hγ : 0 < γ)
    {F : ℝ → ℝ} (hF : ContDiff ℝ ∞ F) (hF0 : F 0 = 0) :
    weightedCompositionMap hT hA hinterp hγ hF hF0 0 = 0 := by
  apply hA.2.2.2.2.2.1
  rw [decode_weightedCompositionMap, map_zero]
  funext p
  simp only [Pi.zero_apply, hF0]

end SobolevModelData

/-- An injective decoder transports a genuine local tower to any global
map with the same literal decoded values.  All transport takes place with
an abstract carrier, so a concrete lift is never unfolded by rewriting. -/
private theorem uniformTameGerm_of_local_decoder
    {E P V : Type*} [TopologicalSpace E] [AddCommGroup E] [Module ℝ E]
    (p : ℕ → Seminorm ℝ E) (decode : E → P → V) (hinj : Function.Injective decode)
    (φ : E → P → V) (g : E → E) (hg : ∀ x, decode (g x) = φ x)
    (hlocal : ∃ base loss : ℕ, ∃ ε : ℝ, 0 < ε ∧
      ∃ f : E → E,
        (∀ x, p base x < ε → ∀ z, decode (f x) z = φ x z) ∧
        FixedNeighborhoodSmoothTame p p {x | p base x < ε} base loss f) :
    UniformTameGerm p p 0 g := by
  obtain ⟨base, loss, ε, hε, f, hfdecode, hftame⟩ := hlocal
  have hcanonical : FixedNeighborhoodSmoothTame p p
      {x | p base x < ε} base loss g :=
    hftame.congr (fun x hx => hinj ((funext (hfdecode x hx)).trans (hg x).symm))
  refine ⟨base, loss, ε, hε, ?_⟩
  simpa only [sub_zero] using hcanonical

/-- Change the outer center before specializing to an implemented map. -/
private theorem uniformTameGerm_comp_zero
    {X : Type*} [TopologicalSpace X] [AddCommGroup X] [Module ℝ X]
    {E : ℕ → Type*} [∀ n, NormedAddCommGroup (E n)] [∀ n, NormedSpace ℝ (E n)]
    [∀ n, CompleteSpace (E n)] {bond : ∀ n, E (n + 1) →L[ℝ] E n}
    {p : ℕ → Seminorm ℝ X} {q : ℕ → Seminorm ℝ (ProjectiveLimit E bond)}
    {x0 : X} {f : X → ProjectiveLimit E bond}
    {g : ProjectiveLimit E bond → ProjectiveLimit E bond}
    (hf : UniformTameGerm p q x0 f) (hf0 : f x0 = 0)
    (hg : UniformTameGerm q q 0 g)
    (hp : Monotone p) (ht : WithSeminorms p) (hq : Monotone q) :
    UniformTameGerm p q x0 (fun x => g (f x)) := by
  letI : IsTopologicalAddGroup X := ht.isTopologicalAddGroup
  letI : ContinuousSMul ℝ X := ht.continuousSMul
  have houter : UniformTameGerm q q (f x0) g := by
    rw [hf0]
    exact hg
  simpa only [Function.comp_def] using hf.comp houter hp ht hq

/-- The globally defined canonical lift has one fixed-loss actual tower on
one neighborhood of zero in the physical height space. -/
theorem weightedCompositionMap_uniformTameGerm
    {D : ReferenceData} {T : MaterialData} {S : PhysicalSpacesData}
    (hT : IsMaterialData D T) (hS : IsPhysicalSpaces D T S)
    {γ : ℝ} (hγ : 0 < γ) {F : ℝ → ℝ}
    (hF : ContDiff ℝ ∞ F) (hF0 : F 0 = 0) :
    UniformTameGerm (S.height γ).grading (S.height γ).grading 0
      (SobolevModelData.weightedCompositionMap hT (hS.1 γ)
        ((hS.2.2.2.1 γ).2.2) hγ hF hF0) := by
  exact uniformTameGerm_of_local_decoder (S.height γ).grading (S.height γ).decode
    (hS.1 γ).2.2.2.2.2.1 (fun u p => F ((S.height γ).decode u p))
    (SobolevModelData.weightedCompositionMap hT (hS.1 γ)
      ((hS.2.2.2.1 γ).2.2) hγ hF hF0)
    (SobolevModelData.decode_weightedCompositionMap hT (hS.1 γ)
      ((hS.2.2.2.1 γ).2.2) hγ hF hF0)
    (exists_fixedNeighborhood_weightedComposition hT hS hγ hF hF0)

section StateComposition

variable {X : Type*} [TopologicalSpace X] [AddCommGroup X] [Module ℝ X]
  {p : ℕ → Seminorm ℝ X} {x0 : X}
  {D : ReferenceData} {T : MaterialData} {S : PhysicalSpacesData}
  {γ : ℝ} {f : X → (S.height γ).Space}

/-- A state germ which vanishes at its center admits every globally smooth
scalar composition vanishing at zero.  The output is the canonical actual
decoded map, and the source may be the prescribed nested scalar state. -/
theorem UniformTameGerm.weightedComposition
    (hf : UniformTameGerm p (S.height γ).grading x0 f) (hf0 : f x0 = 0)
    (hT : IsMaterialData D T) (hS : IsPhysicalSpaces D T S)
    (hγ : 0 < γ) {F : ℝ → ℝ} (hF : ContDiff ℝ ∞ F) (hF0 : F 0 = 0)
    (hp : Monotone p) (ht : WithSeminorms p) :
    UniformTameGerm p (S.height γ).grading x0
      (fun x => SobolevModelData.weightedCompositionMap hT (hS.1 γ)
        ((hS.2.2.2.1 γ).2.2) hγ hF hF0 (f x)) := by
  letI : ∀ n, CompleteSpace ((S.height γ).level n) :=
    fun n => SobolevModelData.completeSpace_level_of_isSobolevModel (hS.1 γ) n
  exact uniformTameGerm_comp_zero
    (E := (S.height γ).level) (bond := (S.height γ).bond)
    (g := SobolevModelData.weightedCompositionMap hT (hS.1 γ)
      ((hS.2.2.2.1 γ).2.2) hγ hF hF0)
    hf hf0 (weightedCompositionMap_uniformTameGerm hT hS hγ hF hF0)
    hp ht (gradedSeminorm_monotone (fun n => (S.height γ).level n) (S.height γ).bond)

end StateComposition

end ContinuousFlexibility.Statements
