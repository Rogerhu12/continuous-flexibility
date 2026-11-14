module

public import ContinuousFlexibility.Scalar.WeightedDecodeLift
public import Mathlib.Topology.Algebra.Module.Multilinear.Basic

/-!
# Actual multilinear decoder lifts

A finite product estimate in continuous source seminorms gives continuity for
the original projective topology.  The proof uses the finite multilinear
difference formula, so it does not assume continuity of an inverse decoder.
-/

@[expose] public section

noncomputable section

open scoped BigOperators Topology

namespace ContinuousFlexibility.Analysis

/-- A multilinear map bounded, in each target seminorm, by a finite product
of one continuous source seminorm is continuous. -/
theorem multilinear_continuous_of_seminorm_product_bound
    {E F : Type*} [AddCommGroup E] [Module ℝ E] [TopologicalSpace E]
    [AddCommGroup F] [Module ℝ F] [TopologicalSpace F]
    {p : ℕ → Seminorm ℝ E} {q : ℕ → Seminorm ℝ F}
    (hp : WithSeminorms p) (hq : WithSeminorms q) {n : ℕ}
    (L : MultilinearMap ℝ (fun _ : Fin n => E) F)
    (hL : ∀ s : ℕ, ∃ t : ℕ, ∃ C : ℝ, 0 ≤ C ∧
      ∀ u, q s (L u) ≤ C * ∏ i, p t (u i)) :
    Continuous L := by
  classical
  letI : IsTopologicalAddGroup E := hp.isTopologicalAddGroup
  apply continuous_iff_continuousAt.mpr
  intro x
  apply (hq.tendsto_nhds L (L x)).mpr
  intro s ε hε
  obtain ⟨t, C, _hC, hbound⟩ := hL s
  let v (i : Fin n) (u : Fin n → E) (j : Fin n) : E :=
    if j < i then u j else if i = j then u j - x j else x j
  let g (u : Fin n → E) : ℝ := C * ∑ i, ∏ j, p t (v i u j)
  have hv (i j : Fin n) : Continuous (fun u : Fin n → E => v i u j) := by
    dsimp only [v]
    split_ifs
    · exact continuous_apply j
    · exact (continuous_apply j).sub continuous_const
    · exact continuous_const
  have hg : Continuous g := continuous_const.mul
    (continuous_finsetSum Finset.univ (fun i _ =>
      continuous_finsetProd Finset.univ (fun j _ => (hp.continuous_seminorm t).comp (hv i j))))
  have hzero (i : Fin n) : (∏ j, p t (v i x j)) = 0 :=
    Finset.prod_eq_zero (Finset.mem_univ i) (by simp [v])
  have hgx : g x = 0 := by
    simp only [g, hzero, Finset.sum_const_zero, mul_zero]
  have hsmall : ∀ᶠ u in 𝓝 x, g u < ε :=
    (hg.tendsto x).eventually (gt_mem_nhds (by simpa only [hgx] using hε))
  filter_upwards [hsmall] with u hu
  have heq : L u - L x = ∑ i, L (v i u) := by
    simpa only [Finset.piecewise_univ, Finset.mem_univ, true_implies, v] using
      L.map_sub_map_piecewise u x Finset.univ
  have hsum (I : Finset (Fin n)) :
      q s (∑ i ∈ I, L (v i u)) ≤ ∑ i ∈ I, q s (L (v i u)) := by
    induction I using Finset.induction_on with
    | empty => simp
    | @insert i I hi ih =>
        rw [Finset.sum_insert hi, Finset.sum_insert hi]
        exact (map_add_le_add _ _ _).trans (add_le_add (le_refl _) ih)
  calc
    q s (L u - L x) = q s (∑ i, L (v i u)) := by rw [heq]
    _ ≤ ∑ i, q s (L (v i u)) := hsum Finset.univ
    _ ≤ ∑ i, C * ∏ j, p t (v i u j) :=
      Finset.sum_le_sum (fun i _ => hbound (v i u))
    _ = g u := by rw [← Finset.mul_sum]
    _ < ε := hu

end ContinuousFlexibility.Analysis

namespace ContinuousFlexibility.Statements.SobolevModelData

open ContinuousFlexibility.Analysis

variable {D : ReferenceData} {T : MaterialData} {γ : ℝ} {A : SobolevModelData}
  {E : Type*} [AddCommGroup E] [Module ℝ E] {n : ℕ}

/-- An actual field-valued multilinear map with height-member values lifts
multilinearly by injectivity of the frozen decoder. -/
def liftMultilinear (hA : IsSobolevModel D T γ A)
    (L : MultilinearMap ℝ (fun _ : Fin n => E) (PolarPoint → ℝ))
    (hL : ∀ u, HeightMember D T γ (L u)) :
    MultilinearMap ℝ (fun _ : Fin n => E) A.Space where
  toFun u := liftHeight hA (L u) (hL u)
  map_update_add' u i x y := by
    apply hA.2.2.2.2.2.1
    simp only [map_add, decode_liftHeight, MultilinearMap.map_update_add]
  map_update_smul' u i c x := by
    apply hA.2.2.2.2.2.1
    simp only [map_smul, decode_liftHeight, MultilinearMap.map_update_smul, RingHom.id_apply]

theorem decode_liftMultilinear (hA : IsSobolevModel D T γ A)
    (L : MultilinearMap ℝ (fun _ : Fin n => E) (PolarPoint → ℝ))
    (hL : ∀ u, HeightMember D T γ (L u)) (u : Fin n → E) :
    A.decode (liftMultilinear hA L hL u) = L u :=
  decode_liftHeight hA (L u) (hL u)

theorem grading_liftMultilinear (hA : IsSobolevModel D T γ A)
    (L : MultilinearMap ℝ (fun _ : Fin n => E) (PolarPoint → ℝ))
    (hL : ∀ u, HeightMember D T γ (L u)) (s : ℕ) (u : Fin n → E) :
    A.grading s (liftMultilinear hA L hL u) = physicalNorm T γ s (L u) := by
  rw [sobolevGrading_eq_physicalNorm hA, decode_liftMultilinear]

variable [TopologicalSpace E]

/-- A physical product estimate yields a genuine continuous multilinear lift
in the original Sobolev-model topology. -/
def liftContinuousMultilinear (hA : IsSobolevModel D T γ A)
    (L : MultilinearMap ℝ (fun _ : Fin n => E) (PolarPoint → ℝ))
    (hL : ∀ u, HeightMember D T γ (L u))
    {p : ℕ → Seminorm ℝ E} (hp : WithSeminorms p)
    (hbound : ∀ s : ℕ, ∃ t : ℕ, ∃ C : ℝ, 0 ≤ C ∧
      ∀ u, physicalNorm T γ s (L u) ≤ C * ∏ i, p t (u i)) :
    ContinuousMultilinearMap ℝ (fun _ : Fin n => E) A.Space where
  toMultilinearMap := liftMultilinear hA L hL
  cont := by
    apply multilinear_continuous_of_seminorm_product_bound hp
      (withSeminorms_graded (fun s => A.level s) A.bond)
    intro s
    obtain ⟨t, C, hC, hCu⟩ := hbound s
    refine ⟨t, C, hC, fun u => ?_⟩
    change A.grading s (liftMultilinear hA L hL u) ≤ C * ∏ i, p t (u i)
    rw [grading_liftMultilinear]
    exact hCu u

theorem decode_liftContinuousMultilinear (hA : IsSobolevModel D T γ A)
    (L : MultilinearMap ℝ (fun _ : Fin n => E) (PolarPoint → ℝ))
    (hL : ∀ u, HeightMember D T γ (L u))
    {p : ℕ → Seminorm ℝ E} (hp : WithSeminorms p)
    (hbound : ∀ s : ℕ, ∃ t : ℕ, ∃ C : ℝ, 0 ≤ C ∧
      ∀ u, physicalNorm T γ s (L u) ≤ C * ∏ i, p t (u i))
    (u : Fin n → E) :
    A.decode (liftContinuousMultilinear hA L hL hp hbound u) = L u :=
  decode_liftMultilinear hA L hL u

theorem grading_liftContinuousMultilinear (hA : IsSobolevModel D T γ A)
    (L : MultilinearMap ℝ (fun _ : Fin n => E) (PolarPoint → ℝ))
    (hL : ∀ u, HeightMember D T γ (L u))
    {p : ℕ → Seminorm ℝ E} (hp : WithSeminorms p)
    (hbound : ∀ s : ℕ, ∃ t : ℕ, ∃ C : ℝ, 0 ≤ C ∧
      ∀ u, physicalNorm T γ s (L u) ≤ C * ∏ i, p t (u i))
    (s : ℕ) (u : Fin n → E) :
    A.grading s (liftContinuousMultilinear hA L hL hp hbound u) =
      physicalNorm T γ s (L u) :=
  grading_liftMultilinear hA L hL s u

end ContinuousFlexibility.Statements.SobolevModelData
