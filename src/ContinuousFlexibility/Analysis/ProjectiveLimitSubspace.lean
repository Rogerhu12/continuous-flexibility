module

public import ContinuousFlexibility.Analysis.Graded
public import Mathlib.Analysis.SpecificLimits.Basic
public import Mathlib.Analysis.Normed.Group.Submodule

/-!
# Closed subspaces, products and constants of projective limits

The abstract Nash–Moser theorem is stated for spaces of the literal form
`ProjectiveLimit E e` with the graded seminorms `gradedSeminorm E e`. This file
shows that the spaces that actually occur are again of this form, with the
same graded seminorms:

* a finite product of two projective limits is the projective limit of the
  levelwise products (`prodEquiv`, `gradedSeminorm_prodEquiv`);
* a normed space is the projective limit of the constant scale with identity
  bonds (`constEquiv`, `gradedSeminorm_constEquiv`);
* a closed linear subspace `W` of a projective limit is the projective limit
  of the closures `subLevel W n` of its coordinate images, with the restricted
  bonds (`subspaceEquiv`, `subspaceEquiv_coordinate`,
  `gradedSeminorm_subspaceEquiv`).

The key point for subspaces is `mem_of_forall_mem_subLevel`: a compatible
family whose coordinates lie in the closures of the coordinate images of a
closed subspace belongs to that subspace. It uses only continuity of the
composite bonds, not bounds on their norms.
-/

@[expose] public section

noncomputable section

set_option backward.isDefEq.respectTransparency false

namespace ContinuousFlexibility.Analysis

open Set Topology Filter

universe u

section Comparison

variable {E : ℕ → Type u} [∀ n, NormedAddCommGroup (E n)] [∀ n, NormedSpace ℝ (E n)]
  {e : ∀ n, E (n + 1) →L[ℝ] E n}
  {F : ℕ → Type u} [∀ n, NormedAddCommGroup (F n)] [∀ n, NormedSpace ℝ (F n)]
  {f : ∀ n, F (n + 1) →L[ℝ] F n}

/-- Graded seminorms of two (possibly different) projective limits compare as
soon as the first `n + 1` coordinate norms compare. -/
theorem gradedSeminorm_le_of_norm_le (n : ℕ) (x : ProjectiveLimit E e)
    (y : ProjectiveLimit F f) (h : ∀ i ≤ n, ‖x.1 i‖ ≤ ‖y.1 i‖) :
    gradedSeminorm E e n x ≤ gradedSeminorm F f n y :=
  (gradedSeminorm_le_iff E e n x (apply_nonneg _ _)).2 fun i hi =>
    (h i hi).trans (norm_coordinate_le_graded F f hi y)

theorem gradedSeminorm_eq_of_norm_eq (n : ℕ) (x : ProjectiveLimit E e)
    (y : ProjectiveLimit F f) (h : ∀ i ≤ n, ‖x.1 i‖ = ‖y.1 i‖) :
    gradedSeminorm E e n x = gradedSeminorm F f n y :=
  le_antisymm (gradedSeminorm_le_of_norm_le n x y fun i hi => (h i hi).le)
    (gradedSeminorm_le_of_norm_le n y x fun i hi => (h i hi).ge)

end Comparison

section Product

variable (E : ℕ → Type u) [∀ n, NormedAddCommGroup (E n)] [∀ n, NormedSpace ℝ (E n)]
  (e : ∀ n, E (n + 1) →L[ℝ] E n)
  (F : ℕ → Type u) [∀ n, NormedAddCommGroup (F n)] [∀ n, NormedSpace ℝ (F n)]
  (f : ∀ n, F (n + 1) →L[ℝ] F n)

/-- The product of two projective limits is the projective limit of the
levelwise products with the product bonds. -/
def prodEquiv : (ProjectiveLimit E e × ProjectiveLimit F f) ≃L[ℝ]
    ProjectiveLimit (fun n => E n × F n) (fun n => (e n).prodMap (f n)) :=
  ContinuousLinearEquiv.equivOfInverse
    (projectiveLift (fun n => E n × F n) (fun n => (e n).prodMap (f n))
      (fun n => (projectiveCoordinate E e n).prodMap (projectiveCoordinate F f n))
      (fun n => ContinuousLinearMap.ext fun p => Prod.ext (p.1.2 n) (p.2.2 n)))
    ((projectiveLift E e
        (fun n => (ContinuousLinearMap.fst ℝ (E n) (F n)).comp
          (projectiveCoordinate (fun n => E n × F n) (fun n => (e n).prodMap (f n)) n))
        (fun n => ContinuousLinearMap.ext fun q => congrArg Prod.fst (q.2 n))).prod
      (projectiveLift F f
        (fun n => (ContinuousLinearMap.snd ℝ (E n) (F n)).comp
          (projectiveCoordinate (fun n => E n × F n) (fun n => (e n).prodMap (f n)) n))
        (fun n => ContinuousLinearMap.ext fun q => congrArg Prod.snd (q.2 n))))
    (fun _ => rfl) (fun _ => rfl)

@[simp] theorem prodEquiv_apply_coord (p : ProjectiveLimit E e × ProjectiveLimit F f)
    (n : ℕ) : (prodEquiv E e F f p).1 n = (p.1.1 n, p.2.1 n) := rfl

@[simp] theorem prodEquiv_symm_apply_fst_coord
    (q : ProjectiveLimit (fun n => E n × F n) (fun n => (e n).prodMap (f n))) (n : ℕ) :
    ((prodEquiv E e F f).symm q).1.1 n = (q.1 n).1 := rfl

@[simp] theorem prodEquiv_symm_apply_snd_coord
    (q : ProjectiveLimit (fun n => E n × F n) (fun n => (e n).prodMap (f n))) (n : ℕ) :
    ((prodEquiv E e F f).symm q).2.1 n = (q.1 n).2 := rfl

/-- The graded seminorms of the product limit are the maxima of the factor
graded seminorms (the norm on `E n × F n` is the max norm). -/
theorem gradedSeminorm_prodEquiv (n : ℕ) (x : ProjectiveLimit E e)
    (y : ProjectiveLimit F f) :
    gradedSeminorm (fun n => E n × F n) (fun n => (e n).prodMap (f n)) n
        (prodEquiv E e F f (x, y)) =
      max (gradedSeminorm E e n x) (gradedSeminorm F f n y) := by
  apply le_antisymm
  · refine (gradedSeminorm_le_iff _ _ n _
      (le_max_of_le_left (apply_nonneg _ _))).2 fun i hi => ?_
    rw [prodEquiv_apply_coord, Prod.norm_mk]
    exact max_le_max (norm_coordinate_le_graded E e hi x)
      (norm_coordinate_le_graded F f hi y)
  · refine max_le (gradedSeminorm_le_of_norm_le n x _ fun i _ => ?_)
      (gradedSeminorm_le_of_norm_le n y _ fun i _ => ?_)
    · rw [prodEquiv_apply_coord, Prod.norm_mk]
      exact le_max_left _ _
    · rw [prodEquiv_apply_coord, Prod.norm_mk]
      exact le_max_right _ _

end Product

section Constant

variable (B : Type u) [NormedAddCommGroup B] [NormedSpace ℝ B]

theorem constScale_coord_eq
    (x : ProjectiveLimit (fun _ : ℕ => B) (fun _ => ContinuousLinearMap.id ℝ B)) (n : ℕ) :
    x.1 n = x.1 0 := by
  induction n with
  | zero => rfl
  | succ n ih => exact (x.2 n).trans ih

/-- A normed space is the projective limit of its constant scale with
identity bonds. -/
def constEquiv : B ≃L[ℝ]
    ProjectiveLimit (fun _ : ℕ => B) (fun _ => ContinuousLinearMap.id ℝ B) :=
  ContinuousLinearEquiv.equivOfInverse
    (projectiveLift (fun _ : ℕ => B) (fun _ => ContinuousLinearMap.id ℝ B)
      (fun _ => ContinuousLinearMap.id ℝ B) (fun _ => ContinuousLinearMap.id_comp _))
    (projectiveCoordinate (fun _ : ℕ => B) (fun _ => ContinuousLinearMap.id ℝ B) 0)
    (fun _ => rfl)
    (fun x => Subtype.ext (funext fun n => (constScale_coord_eq B x n).symm))

@[simp] theorem constEquiv_apply_coord (b : B) (n : ℕ) : (constEquiv B b).1 n = b := rfl

@[simp] theorem constEquiv_symm_apply
    (x : ProjectiveLimit (fun _ : ℕ => B) (fun _ => ContinuousLinearMap.id ℝ B)) :
    (constEquiv B).symm x = x.1 0 := rfl

theorem gradedSeminorm_constEquiv (n : ℕ) (b : B) :
    gradedSeminorm (fun _ : ℕ => B) (fun _ => ContinuousLinearMap.id ℝ B) n
      (constEquiv B b) = ‖b‖ := by
  apply le_antisymm
  · exact (gradedSeminorm_le_iff _ _ n _ (norm_nonneg b)).2 fun i _ => le_of_eq rfl
  · have h := norm_coordinate_le_graded (fun _ : ℕ => B)
      (fun _ => ContinuousLinearMap.id ℝ B) (Nat.zero_le n) (constEquiv B b)
    rwa [constEquiv_apply_coord] at h

end Constant

section Subspace

variable (E : ℕ → Type u) [∀ n, NormedAddCommGroup (E n)] [∀ n, NormedSpace ℝ (E n)]
  (e : ∀ n, E (n + 1) →L[ℝ] E n)

/-- Each coordinate of the projective limit factors continuously through
every later coordinate (through the composite of the bonds). -/
theorem exists_continuous_coordinate_factor {i n : ℕ} (h : i ≤ n) :
    ∃ g : E n → E i, Continuous g ∧ ∀ y : ProjectiveLimit E e, y.1 i = g (y.1 n) := by
  induction n, h using Nat.le_induction with
  | base => exact ⟨id, continuous_id, fun _ => rfl⟩
  | succ n _ ih =>
    obtain ⟨g, hg, hgy⟩ := ih
    exact ⟨g ∘ e n, hg.comp (e n).continuous,
      fun y => (hgy y).trans (congrArg g (y.2 n).symm)⟩

variable {E e} (W : Submodule ℝ (ProjectiveLimit E e))

/-- The `n`-th level of a subspace: the closure of its `n`-th coordinate image. -/
def subLevel (n : ℕ) : Submodule ℝ (E n) :=
  (W.map (projectiveCoordinate E e n).toLinearMap).topologicalClosure

theorem coe_subLevel (n : ℕ) :
    (subLevel W n : Set (E n)) =
      closure ((W.map (projectiveCoordinate E e n).toLinearMap : Submodule ℝ (E n)) :
        Set (E n)) :=
  Submodule.topologicalClosure_coe _

theorem coord_mem_subLevel {w : ProjectiveLimit E e} (hw : w ∈ W) (n : ℕ) :
    w.1 n ∈ subLevel W n :=
  Submodule.le_topologicalClosure _ (Submodule.mem_map_of_mem hw)

theorem bond_mem_subLevel {n : ℕ} {z : E (n + 1)} (hz : z ∈ subLevel W (n + 1)) :
    e n z ∈ subLevel W n := by
  have hz' : z ∈ closure ((W.map (projectiveCoordinate E e (n + 1)).toLinearMap :
      Submodule ℝ (E (n + 1))) : Set (E (n + 1))) := by
    rw [← coe_subLevel]; exact hz
  show e n z ∈ (subLevel W n : Set (E n))
  rw [coe_subLevel]
  refine map_mem_closure (e n).continuous hz' ?_
  intro y hy
  obtain ⟨w, hw, hwy⟩ := Submodule.mem_map.mp hy
  rw [← hwy]
  exact Submodule.mem_map.mpr ⟨w, hw, (w.2 n).symm⟩

/-- The bonds restricted to the subspace levels. -/
def subBond (n : ℕ) : subLevel W (n + 1) →L[ℝ] subLevel W n :=
  ((e n).comp (subLevel W (n + 1)).subtypeL).codRestrict (subLevel W n)
    (fun z => bond_mem_subLevel W z.2)

@[simp] theorem coe_subBond_apply (n : ℕ) (z : subLevel W (n + 1)) :
    ((subBond W n z : subLevel W n) : E n) = e n (z : E (n + 1)) := rfl

/-- The coordinate maps of a subspace into its levels. -/
def subLevelCoordinate (n : ℕ) : W →L[ℝ] subLevel W n :=
  ((projectiveCoordinate E e n).comp W.subtypeL).codRestrict (subLevel W n)
    (fun w => coord_mem_subLevel W w.2 n)

/-- The subspace maps into the projective limit of its levels. -/
def subspaceToLimit : W →L[ℝ] ProjectiveLimit (fun n => subLevel W n) (subBond W) :=
  projectiveLift (V := W) (fun n => subLevel W n) (subBond W)
    (fun n => subLevelCoordinate W n)
    (fun n => ContinuousLinearMap.ext fun (w : W) => Subtype.ext (w.1.2 n))

/-- The projective limit of the levels maps back into the ambient limit. -/
def limitToAmbient :
    ProjectiveLimit (fun n => subLevel W n) (subBond W) →L[ℝ] ProjectiveLimit E e :=
  projectiveLift E e
    (fun n => (subLevel W n).subtypeL.comp
      (projectiveCoordinate (fun n => subLevel W n) (subBond W) n))
    (fun n => ContinuousLinearMap.ext fun x => congrArg Subtype.val (x.2 n))

/-- A compatible family whose coordinates lie in the closures of the
coordinate images of a closed subspace lies in the subspace. -/
theorem mem_of_forall_mem_subLevel (hW : IsClosed (W : Set (ProjectiveLimit E e)))
    (x : ProjectiveLimit E e) (hx : ∀ n, x.1 n ∈ subLevel W n) : x ∈ W := by
  have hpick : ∀ N : ℕ, ∃ w ∈ W, ∀ i ≤ N, dist (w.1 i) (x.1 i) < 1 / ((N : ℝ) + 1) := by
    intro N
    have hδ : (0 : ℝ) < 1 / ((N : ℝ) + 1) := by positivity
    have hfac : ∀ i, i ≤ N → ∃ g : E N → E i, Continuous g ∧
        ∀ y : ProjectiveLimit E e, y.1 i = g (y.1 N) :=
      fun i hi => exists_continuous_coordinate_factor E e hi
    choose g hgc hgy using hfac
    have hev : ∀ᶠ z in 𝓝 (x.1 N), ∀ i ∈ Set.Iic N, ∀ hi : i ≤ N,
        dist (g i hi z) (x.1 i) < 1 / ((N : ℝ) + 1) := by
      refine (Filter.eventually_all_finite (Set.finite_Iic N)).2 fun i hi => ?_
      have hi' : i ≤ N := Set.mem_Iic.mp hi
      have ht := (hgc i hi').tendsto (x.1 N)
      rw [← hgy i hi' x] at ht
      exact (ht.eventually (Metric.ball_mem_nhds _ hδ)).mono fun z hz _ => hz
    have hxN : x.1 N ∈ closure ((W.map (projectiveCoordinate E e N).toLinearMap :
        Submodule ℝ (E N)) : Set (E N)) := by
      rw [← coe_subLevel]; exact hx N
    obtain ⟨z, hzU, hzW⟩ := mem_closure_iff_nhds.mp hxN _ hev
    have hzU' : ∀ i ∈ Set.Iic N, ∀ hi : i ≤ N,
        dist (g i hi z) (x.1 i) < 1 / ((N : ℝ) + 1) := hzU
    obtain ⟨w, hw, hwz⟩ := Submodule.mem_map.mp hzW
    have hz2 : z = w.1 N := hwz.symm
    refine ⟨w, hw, fun i hi => ?_⟩
    have h1 := hzU' i (Set.mem_Iic.mpr hi) hi
    rw [hz2, ← hgy i hi w] at h1
    exact h1
  choose w hwW hw using hpick
  have htend : Tendsto w atTop (𝓝 x) := by
    rw [tendsto_projectiveLimit_iff]
    intro i
    rw [tendsto_iff_dist_tendsto_zero]
    exact squeeze_zero' (Eventually.of_forall fun N => dist_nonneg)
      (eventually_atTop.2 ⟨i, fun N hN => (hw N i hN).le⟩)
      tendsto_one_div_add_atTop_nhds_zero_nat
  exact hW.mem_of_tendsto htend (Eventually.of_forall hwW)

/-- A closed subspace of a projective limit is the projective limit of its
levels `subLevel W n` with the restricted bonds. -/
def subspaceEquiv (hW : IsClosed (W : Set (ProjectiveLimit E e))) :
    W ≃L[ℝ] ProjectiveLimit (fun n => subLevel W n) (subBond W) :=
  ContinuousLinearEquiv.equivOfInverse (subspaceToLimit W)
    ((limitToAmbient W).codRestrict W
      (fun x => mem_of_forall_mem_subLevel W hW _ fun n => (x.1 n).2))
    (fun _ => rfl) (fun _ => rfl)

theorem subspaceEquiv_coordinate (hW : IsClosed (W : Set (ProjectiveLimit E e))) (w : W)
    (n : ℕ) :
    ((projectiveCoordinate (fun n => subLevel W n) (subBond W) n (subspaceEquiv W hW w) :
        subLevel W n) : E n) =
      projectiveCoordinate E e n (w : ProjectiveLimit E e) := rfl

theorem subspaceEquiv_symm_coordinate (hW : IsClosed (W : Set (ProjectiveLimit E e)))
    (x : ProjectiveLimit (fun n => subLevel W n) (subBond W)) (n : ℕ) :
    projectiveCoordinate E e n (((subspaceEquiv W hW).symm x : W) : ProjectiveLimit E e) =
      ((projectiveCoordinate (fun n => subLevel W n) (subBond W) n x : subLevel W n) :
        E n) := rfl

theorem gradedSeminorm_subspaceEquiv (hW : IsClosed (W : Set (ProjectiveLimit E e)))
    (w : W) (n : ℕ) :
    gradedSeminorm (fun n => subLevel W n) (subBond W) n (subspaceEquiv W hW w) =
      gradedSeminorm E e n (w : ProjectiveLimit E e) :=
  gradedSeminorm_eq_of_norm_eq n _ _ fun _ _ => rfl

instance subLevel_completeSpace [∀ n, CompleteSpace (E n)] (n : ℕ) :
    CompleteSpace (subLevel W n) :=
  (Submodule.isClosed_topologicalClosure _).completeSpace_coe

end Subspace

end ContinuousFlexibility.Analysis
