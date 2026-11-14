module

public import ContinuousFlexibility.Statements.Nonlinear
public import ContinuousFlexibility.Analysis.TameLocalCalculus
public import ContinuousFlexibility.Analysis.TameTransfer

/-!
# Shrinking the common nonlinear neighborhood

The state grading is the actual increasing projective grading on the
physical spaces. Its seminorm balls are open and convex. Increasing the
base order and decreasing the radius therefore restricts to a smaller
neighborhood, without changing the reference state or any geometric data.

These facts allow the low-order smallness choices in the coordinate
construction to use one neighborhood for all subsequent estimates.
-/

@[expose] public section

noncomputable section

namespace ContinuousFlexibility.Analysis

open Set
open scoped Topology BigOperators
open ContinuousFlexibility.Statements

set_option backward.isDefEq.respectTransparency false

theorem heightPairGrading_monotone (S : PhysicalSpacesData) :
    Monotone (heightPairGrading S) :=
  tamePairGrading_monotone (gradedSeminorm_monotone _ _) (fun _ _ _ => le_rfl)

theorem stateGrading_monotone (S : PhysicalSpacesData) : Monotone (stateGrading S) :=
  tamePairGrading_monotone (heightPairGrading_monotone S)
    (tamePairGrading_monotone (fun _ _ _ => le_rfl)
      (tamePairGrading_monotone (gradedSeminorm_monotone _ _)
        (gradedSeminorm_monotone _ _)))

theorem sectorGrading_monotone (S : PhysicalSpacesData) : Monotone (sectorGrading S) := by
  intro m n hmn x
  exact stateGrading_monotone S hmn x.val

private theorem continuous_pairGrading_apply
    {E F : Type*} [TopologicalSpace E] [AddCommGroup E] [Module ℝ E]
    [TopologicalSpace F] [AddCommGroup F] [Module ℝ F]
    {p : ℕ → Seminorm ℝ E} {q : ℕ → Seminorm ℝ F} (n : ℕ)
    (hp : Continuous (p n)) (hq : Continuous (q n)) :
    Continuous (pairGrading p q n) := by
  have he : (pairGrading p q n : E × F → ℝ) =
      fun x => p n x.1 + q n x.2 := funext (pairGrading_apply p q n)
  rw [he]
  exact (hp.comp continuous_fst).add (hq.comp continuous_snd)

theorem continuous_heightPairGrading (S : PhysicalSpacesData) (n : ℕ) :
    Continuous (heightPairGrading S n) :=
  continuous_pairGrading_apply n (continuous_gradedSeminorm _ _ n) continuous_norm

theorem continuous_stateGrading (S : PhysicalSpacesData) (n : ℕ) :
    Continuous (stateGrading S n) :=
  continuous_pairGrading_apply n (continuous_heightPairGrading S n)
    (continuous_pairGrading_apply n continuous_norm
      (continuous_pairGrading_apply n (continuous_gradedSeminorm _ _ n)
        (continuous_gradedSeminorm _ _ n)))

theorem continuous_sectorGrading (S : PhysicalSpacesData) (n : ℕ) :
    Continuous (sectorGrading S n) :=
  (continuous_stateGrading S n).comp continuous_subtype_val

theorem isOpen_stateNeighborhood (S : PhysicalSpacesData) (C : NonlinearGeometryData S)
    (base : ℕ) (ε : ℝ) : IsOpen (stateNeighborhood S C base ε) := by
  exact (isOpen_lt ((continuous_stateGrading S base).comp
    (continuous_fst.sub continuous_const)) continuous_const).inter
    (isOpen_lt continuous_snd.abs continuous_const)

theorem isOpen_sectorNeighborhood (S : PhysicalSpacesData) (base : ℕ) (ε q0 : ℝ) :
    IsOpen (sectorNeighborhood S base ε q0) :=
  (isOpen_lt ((continuous_sectorGrading S base).comp continuous_fst) continuous_const).inter
    (isOpen_lt continuous_snd.abs continuous_const)

private theorem convex_seminorm_parameterNeighborhood
    {E : Type*} [AddCommGroup E] [Module ℝ E]
    (p : Seminorm ℝ E) (x : E) (ε : ℝ) :
    Convex ℝ {z : E × ℝ | p (z.1 - x) < ε ∧ |z.2| < ε} := by
  have he : {z : E × ℝ | p (z.1 - x) < ε ∧ |z.2| < ε} =
      p.ball x ε ×ˢ (normSeminorm ℝ ℝ).ball 0 ε := by
    ext z
    simp only [mem_ofPred, mem_prod, Seminorm.mem_ball,
      coe_normSeminorm, sub_zero, Real.norm_eq_abs]
  rw [he]
  exact (p.convex_ball x ε).prod ((normSeminorm ℝ ℝ).convex_ball 0 ε)

theorem convex_stateNeighborhood (S : PhysicalSpacesData) (C : NonlinearGeometryData S)
    (base : ℕ) (ε : ℝ) : Convex ℝ (stateNeighborhood S C base ε) :=
  convex_seminorm_parameterNeighborhood (stateGrading S base) C.referenceState ε

private theorem seminorm_reference_mem_parameterNeighborhood
    {E : Type*} [AddCommGroup E] [Module ℝ E]
    (p : Seminorm ℝ E) (x : E) {ε : ℝ} (hε : 0 < ε) :
    (x, (0 : ℝ)) ∈ {z : E × ℝ | p (z.1 - x) < ε ∧ |z.2| < ε} := by
  simpa only [mem_ofPred, sub_self, map_zero, abs_zero] using And.intro hε hε

theorem reference_mem_stateNeighborhood (S : PhysicalSpacesData)
    (C : NonlinearGeometryData S) (base : ℕ) {ε : ℝ} (hε : 0 < ε) :
    (C.referenceState, 0) ∈ stateNeighborhood S C base ε :=
  seminorm_reference_mem_parameterNeighborhood (stateGrading S base) C.referenceState hε

theorem stateNeighborhood_mono (S : PhysicalSpacesData) (C : NonlinearGeometryData S)
    {base base' : ℕ} {ε ε' : ℝ} (hb : base ≤ base') (hε : ε' ≤ ε) :
    stateNeighborhood S C base' ε' ⊆ stateNeighborhood S C base ε := by
  intro z hz
  exact ⟨((stateGrading_monotone S hb _).trans_lt hz.1).trans_le hε,
    hz.2.trans_le hε⟩

theorem sectorNeighborhood_mono (S : PhysicalSpacesData)
    {base base' : ℕ} {ε ε' q0 q0' : ℝ}
    (hb : base ≤ base') (hε : ε' ≤ ε) (hq : q0' ≤ q0) :
    sectorNeighborhood S base' ε' q0' ⊆ sectorNeighborhood S base ε q0 := by
  intro z hz
  exact ⟨((sectorGrading_monotone S hb _).trans_lt hz.1).trans_le hε,
    hz.2.trans_le hq⟩

/-- Increasing the low and high orders increases the actual one-high-factor
weight, including the empty list of variations. -/
theorem oneHighVariationWeight_mono
    {E : Type*} [AddCommGroup E] [Module ℝ E]
    {p : ℕ → Seminorm ℝ E} (hp : Monotone p)
    {base base' high high' : ℕ} (hb : base ≤ base') (hh : high ≤ high')
    (x : E) {k : ℕ} (v : Fin k → E) :
    oneHighVariationWeight p base high x v ≤
      oneHighVariationWeight p base' high' x v := by
  classical
  have hprod (s : Finset (Fin k)) :
      (∏ i ∈ s, p base (v i)) ≤ ∏ i ∈ s, p base' (v i) :=
    Finset.prod_le_prod₀ (fun i _ => apply_nonneg _ _) (fun i _ => hp hb (v i))
  unfold oneHighVariationWeight
  apply add_le_add
  · apply mul_le_mul (add_le_add (le_refl 1) (hp hh x)) (hprod Finset.univ)
    · exact Finset.prod_nonneg (fun i _ => apply_nonneg _ _)
    · exact add_nonneg zero_le_one (apply_nonneg _ _)
  · apply Finset.sum_le_sum
    intro i _
    exact mul_le_mul (hp hh (v i)) (hprod (Finset.univ.erase i))
      (Finset.prod_nonneg (fun j _ => apply_nonneg _ _)) (apply_nonneg _ _)

end ContinuousFlexibility.Analysis
