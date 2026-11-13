import ContinuousFlexibility.Analysis.N04RealizationInverseJetFormula
import ContinuousFlexibility.Analysis.N01cStateAngleSelections

/-!
# The actual inverse formula with separate state and spatial slots

The inverse keeps the original state coordinate. Expanding each genuine
partition block into its state and spatial projections gives a recurrence
which only reads the state orders present in the original word. This
avoids estimating a full derivative norm which would introduce unrelated
higher state derivatives.
-/

noncomputable section

namespace ContinuousFlexibility.Analysis

open Set Filter Function
open scoped Topology ContDiff BigOperators

variable {P V Z : Type*}
  [NormedAddCommGroup P] [NormedSpace ℝ P]
  [NormedAddCommGroup V] [NormedSpace ℝ V]
  [NormedAddCommGroup Z] [NormedSpace ℝ Z]

def n04PositiveGeometry_fiberLift (f : P × V → V) (p : P × V) : P × V :=
  (p.1, f p)

def n04PositiveGeometry_slotProjection (state : Bool) : (P × V) →L[ℝ] (P × V) :=
  if state then (ContinuousLinearMap.fst ℝ P V).prod 0
  else (0 : (P × V) →L[ℝ] P).prod (ContinuousLinearMap.snd ℝ P V)

theorem n04PositiveGeometry_slotProjection_apply (state : Bool) (p : P × V) :
    n04PositiveGeometry_slotProjection state p =
      if state then (p.1, 0) else (0, p.2) := by
  cases state <;> rfl

theorem n04PositiveGeometry_slotProjection_idem (state : Bool) (p : P × V) :
    n04PositiveGeometry_slotProjection state
      (n04PositiveGeometry_slotProjection state p) =
        n04PositiveGeometry_slotProjection state p := by
  cases state <;> rfl

theorem n04PositiveGeometry_slotProjection_norm_le (state : Bool) :
    ‖(n04PositiveGeometry_slotProjection state : (P × V) →L[ℝ] (P × V))‖ ≤ 1 := by
  apply ContinuousLinearMap.opNorm_le_bound _ zero_le_one
  intro p
  rw [one_mul, n04PositiveGeometry_slotProjection_apply]
  cases state
  · simpa only [Bool.false_eq_true, if_false, Prod.norm_def, norm_zero,
      max_eq_right (norm_nonneg _)] using norm_snd_le p
  · simpa only [if_true, Prod.norm_def, norm_zero,
      max_eq_left (norm_nonneg _)] using norm_fst_le p

/-- An actual ordinary derivative with its original ordered state and
spatial slots projected separately. -/
def n04PositiveGeometry_projectedJet {n : ℕ} (b : Fin n → Bool)
    (f : P × V → Z) (p : P × V) : (P × V) [×n]→L[ℝ] Z :=
  (iteratedFDeriv ℝ n f p).compContinuousLinearMap
    (fun i => n04PositiveGeometry_slotProjection (b i))

theorem n04PositiveGeometry_projectedJet_apply {n : ℕ} (b : Fin n → Bool)
    (f : P × V → Z) (p : P × V) (v : Fin n → P × V) :
    n04PositiveGeometry_projectedJet b f p v =
      iteratedFDeriv ℝ n f p
        (fun i => n04PositiveGeometry_slotProjection (b i) (v i)) := rfl

def n04PositiveGeometry_triangularInverse
    (A : (P × V) →L[ℝ] V) (B : V →L[ℝ] V) :
    (P × V) →L[ℝ] (P × V) :=
  (ContinuousLinearMap.fst ℝ P V).prod
    (B.comp ((ContinuousLinearMap.snd ℝ P V) -
      A.comp (n04PositiveGeometry_slotProjection true)))

theorem n04PositiveGeometry_triangularInverse_apply
    (A : (P × V) →L[ℝ] V) (B : V →L[ℝ] V) (p : P × V) :
    n04PositiveGeometry_triangularInverse A B p = (p.1, B (p.2 - A (p.1, 0))) := rfl

theorem n04PositiveGeometry_triangularInverse_left
    (A : (P × V) →L[ℝ] V) (B : V →L[ℝ] V)
    (hB : B.comp (A.comp (ContinuousLinearMap.inr ℝ P V)) =
      ContinuousLinearMap.id ℝ V) :
    (n04PositiveGeometry_triangularInverse A B).comp
      ((ContinuousLinearMap.fst ℝ P V).prod A) =
        ContinuousLinearMap.id ℝ (P × V) := by
  apply ContinuousLinearMap.ext
  intro p
  have hb := congrArg (fun L : V →L[ℝ] V => L p.2) hB
  have hdiff : A p - A (p.1, 0) = A (0, p.2) := by
    rw [← map_sub]
    congr 1
    exact Prod.ext (sub_self _) (sub_zero _)
  simp only [ContinuousLinearMap.comp_apply, ContinuousLinearMap.inr_apply,
    ContinuousLinearMap.id_apply] at hb
  change (p.1, B (A p - A (p.1, 0))) = p
  rw [hdiff, hb]

theorem n04PositiveGeometry_fiberLift_jet {f : P × V → V} {p : P × V}
    (hf : ContDiffAt ℝ ∞ f p) {n : ℕ} (hn : 2 ≤ n) (v : Fin n → P × V) :
    iteratedFDeriv ℝ n (n04PositiveGeometry_fiberLift f) p v =
      (0, iteratedFDeriv ℝ n f p v) := by
  change iteratedFDeriv ℝ n (fun q : P × V => (q.1, f q)) p v = _
  rw [iteratedFDeriv_prodMk contDiffAt_fst hf (by simp)]
  change (iteratedFDeriv ℝ n (fun q : P × V => q.1) p v,
    iteratedFDeriv ℝ n f p v) = _
  have hz := flowJet_iteratedFDeriv_clm_eq_zero (ContinuousLinearMap.fst ℝ P V) hn p
  have hz' : iteratedFDeriv ℝ n (fun q : P × V => q.1) p = 0 := by
    simpa only [ContinuousLinearMap.coe_fst'] using hz
  rw [hz', ContinuousMultilinearMap.zero_apply]

theorem n04PositiveGeometry_fiberLift_fderiv {f : P × V → V} {p : P × V}
    (hf : ContDiffAt ℝ ∞ f p) :
    fderiv ℝ (n04PositiveGeometry_fiberLift f) p =
      (ContinuousLinearMap.fst ℝ P V).prod (fderiv ℝ f p) :=
  (hasFDerivAt_fst.prodMk (hf.differentiableAt (by simp)).hasFDerivAt).fderiv

/-- The genuine first derivative is obtained from the original forward
derivative and its spatial inverse, with no derivative of the inverse
family supplied as a quantitative premise. -/
theorem n04PositiveGeometry_fiberInverse_firstJet
    {f g : P × V → V} {x : P × V}
    (hf : ContDiffAt ℝ ∞ f (n04PositiveGeometry_fiberLift g x))
    (hg : ContDiffAt ℝ ∞ g x)
    (hfg : n04PositiveGeometry_fiberLift f ∘ n04PositiveGeometry_fiberLift g
      =ᶠ[𝓝 x] id)
    (B : V →L[ℝ] V)
    (hB : B.comp ((fderiv ℝ f (n04PositiveGeometry_fiberLift g x)).comp
      (ContinuousLinearMap.inr ℝ P V)) = ContinuousLinearMap.id ℝ V)
    (v : P × V) :
    fderiv ℝ g x v = B (v.2 -
      fderiv ℝ f (n04PositiveGeometry_fiberLift g x) (v.1, 0)) := by
  let A := fderiv ℝ f (n04PositiveGeometry_fiberLift g x)
  have hleft : (n04PositiveGeometry_triangularInverse A B).comp
      (fderiv ℝ (n04PositiveGeometry_fiberLift f)
        (n04PositiveGeometry_fiberLift g x)) =
      ContinuousLinearMap.id ℝ (P × V) := by
    rw [n04PositiveGeometry_fiberLift_fderiv hf]
    exact n04PositiveGeometry_triangularInverse_left A B hB
  have he := nonlinearInverse_fderiv_eq (contDiffAt_fst.prodMk hf)
    (contDiffAt_fst.prodMk hg) hfg (n04PositiveGeometry_triangularInverse A B) hleft
  have hv := congrArg (fun L : (P × V) →L[ℝ] (P × V) => (L v).2) he
  simpa only [n04PositiveGeometry_fiberLift_fderiv hg, ContinuousLinearMap.prod_apply,
    n04PositiveGeometry_triangularInverse_apply, A] using hv

/-- Every higher spatial-output jet of the actual parameterized inverse
is a sum of genuine forward jets and strictly lower genuine inverse
graph jets. -/
theorem n04PositiveGeometry_fiberInverse_higherJet
    {f g : P × V → V} {x : P × V}
    (hf : ContDiffAt ℝ ∞ f (n04PositiveGeometry_fiberLift g x))
    (hg : ContDiffAt ℝ ∞ g x)
    (hfg : n04PositiveGeometry_fiberLift f ∘ n04PositiveGeometry_fiberLift g
      =ᶠ[𝓝 x] id)
    (B : V →L[ℝ] V)
    (hB : B.comp ((fderiv ℝ f (n04PositiveGeometry_fiberLift g x)).comp
      (ContinuousLinearMap.inr ℝ P V)) = ContinuousLinearMap.id ℝ V)
    {n : ℕ} (hn : 2 ≤ n) (v : Fin n → P × V) :
    iteratedFDeriv ℝ n g x v = -B (∑ c : OrderedFinpartition n,
      if 2 ≤ c.length then
        iteratedFDeriv ℝ c.length f (n04PositiveGeometry_fiberLift g x)
          (fun i => iteratedFDeriv ℝ (c.partSize i)
            (n04PositiveGeometry_fiberLift g) x (v ∘ c.emb i))
      else 0) := by
  classical
  let A := fderiv ℝ f (n04PositiveGeometry_fiberLift g x)
  have hleft : (n04PositiveGeometry_triangularInverse A B).comp
      (fderiv ℝ (n04PositiveGeometry_fiberLift f)
        (n04PositiveGeometry_fiberLift g x)) =
      ContinuousLinearMap.id ℝ (P × V) := by
    rw [n04PositiveGeometry_fiberLift_fderiv hf]
    exact n04PositiveGeometry_triangularInverse_left A B hB
  have he := n04Realization_inverse_higherJet_apply
    (f := n04PositiveGeometry_fiberLift f) (g := n04PositiveGeometry_fiberLift g)
    (contDiffAt_fst.prodMk hf) (contDiffAt_fst.prodMk hg) hfg
    (n04PositiveGeometry_triangularInverse A B) hleft hn v
  let t : OrderedFinpartition n → V := fun c => if 2 ≤ c.length then
    iteratedFDeriv ℝ c.length f (n04PositiveGeometry_fiberLift g x)
      (fun i => iteratedFDeriv ℝ (c.partSize i)
        (n04PositiveGeometry_fiberLift g) x (v ∘ c.emb i)) else 0
  have hsum : (∑ c : OrderedFinpartition n, if 2 ≤ c.length then
      iteratedFDeriv ℝ c.length (n04PositiveGeometry_fiberLift f)
        (n04PositiveGeometry_fiberLift g x)
        (fun i => iteratedFDeriv ℝ (c.partSize i)
          (n04PositiveGeometry_fiberLift g) x (v ∘ c.emb i)) else 0) =
      (ContinuousLinearMap.inr ℝ P V) (∑ c, t c) := by
    rw [map_sum]
    apply Finset.sum_congr rfl
    intro c _
    by_cases hc : 2 ≤ c.length
    · simp only [if_pos hc, t, n04PositiveGeometry_fiberLift_jet hf hc,
        ContinuousLinearMap.inr_apply]
    · simp only [if_neg hc, t, map_zero]
  rw [hsum, n04PositiveGeometry_fiberLift_jet hg hn] at he
  have hsnd := congrArg Prod.snd he
  simpa only [n04PositiveGeometry_triangularInverse_apply, ContinuousLinearMap.inr_apply,
    Prod.snd_neg, map_zero, sub_zero, t] using hsnd

/-- Multilinearity separates each actual slot into its state and spatial
parts. The same finite set will be used to count the surviving state
singletons in the inverse recurrence. -/
theorem n04PositiveGeometry_multilinear_projection_expansion {n : ℕ}
    (A : (P × V) [×n]→L[ℝ] Z) (v : Fin n → P × V) :
    A v = ∑ s : Finset (Fin n),
      A (fun i => n04PositiveGeometry_slotProjection (decide (i ∈ s)) (v i)) := by
  classical
  have hsplit : v = (fun i => ((v i).1, (0 : V))) +
      (fun i => ((0 : P), (v i).2)) := by
    funext i
    simp only [Pi.add_apply, Prod.mk_add_mk, add_zero, zero_add]
  conv_lhs => rw [hsplit, A.map_add_univ]
  apply Finset.sum_congr rfl
  intro s _
  congr 1
  funext i
  by_cases hi : i ∈ s
  · simp [Finset.piecewise, hi, n04PositiveGeometry_slotProjection_apply]
  · simp [Finset.piecewise, hi, n04PositiveGeometry_slotProjection_apply]

/-- The selected graph block is a genuine lower inverse derivative,
projected at its output and in the original order at its inputs. -/
def n04PositiveGeometry_inverseSelectedBlock {n : ℕ} (b : Fin n → Bool)
    (g : P × V → V) (x : P × V) (c : OrderedFinpartition n)
    (s : Finset (Fin c.length)) (i : Fin c.length) :
    (P × V) [×c.partSize i]→L[ℝ] (P × V) :=
  (n04PositiveGeometry_slotProjection (decide (i ∈ s))).compContinuousMultilinearMap
    (n04PositiveGeometry_projectedJet (b ∘ c.emb i) (n04PositiveGeometry_fiberLift g) x)

def n04PositiveGeometry_inverseSelectedTerm {n : ℕ} (b : Fin n → Bool)
    (f g : P × V → V) (x : P × V) (c : OrderedFinpartition n)
    (s : Finset (Fin c.length)) : (P × V) [×n]→L[ℝ] V :=
  c.compAlongOrderedFinpartition
    (n04PositiveGeometry_projectedJet (fun i => decide (i ∈ s)) f
      (n04PositiveGeometry_fiberLift g x))
    (fun i => n04PositiveGeometry_inverseSelectedBlock b g x c s i)

theorem n04PositiveGeometry_inverseSelectedTerm_apply {n : ℕ} (b : Fin n → Bool)
    (f g : P × V → V) (x : P × V) (c : OrderedFinpartition n)
    (s : Finset (Fin c.length)) (v : Fin n → P × V) :
    n04PositiveGeometry_inverseSelectedTerm b f g x c s v =
      iteratedFDeriv ℝ c.length f (n04PositiveGeometry_fiberLift g x)
        (fun i => n04PositiveGeometry_slotProjection (decide (i ∈ s))
          (iteratedFDeriv ℝ (c.partSize i) (n04PositiveGeometry_fiberLift g) x
            (fun j => n04PositiveGeometry_slotProjection (b (c.emb i j)) (v (c.emb i j))))) := by
  simp only [n04PositiveGeometry_inverseSelectedTerm,
    OrderedFinpartition.compAlongOrderFinpartition_apply,
    OrderedFinpartition.applyOrderedFinpartition_apply,
    n04PositiveGeometry_projectedJet_apply, n04PositiveGeometry_inverseSelectedBlock,
    ContinuousLinearMap.compContinuousMultilinearMap_coe, comp_apply,
    n04PositiveGeometry_slotProjection_idem]

/-- The recurrence is an equality of actual projected multilinear maps.
Its nonlinear terms can therefore be bounded without reading any state
derivative outside the selected original prefix. -/
theorem n04PositiveGeometry_fiberInverse_projected_recursion
    {f g : P × V → V} {x : P × V}
    (hf : ContDiffAt ℝ ∞ f (n04PositiveGeometry_fiberLift g x))
    (hg : ContDiffAt ℝ ∞ g x)
    (hfg : n04PositiveGeometry_fiberLift f ∘ n04PositiveGeometry_fiberLift g
      =ᶠ[𝓝 x] id)
    (B : V →L[ℝ] V)
    (hB : B.comp ((fderiv ℝ f (n04PositiveGeometry_fiberLift g x)).comp
      (ContinuousLinearMap.inr ℝ P V)) = ContinuousLinearMap.id ℝ V)
    {n : ℕ} (hn : 2 ≤ n) (b : Fin n → Bool) :
    n04PositiveGeometry_projectedJet b g x =
      -B.compContinuousMultilinearMap (∑ c : OrderedFinpartition n,
        if 2 ≤ c.length then ∑ s : Finset (Fin c.length),
          n04PositiveGeometry_inverseSelectedTerm b f g x c s else 0) := by
  classical
  ext v
  simp only [ContinuousMultilinearMap.neg_apply,
    ContinuousLinearMap.compContinuousMultilinearMap_coe, comp_apply,
    ContinuousMultilinearMap.sum_apply, ContinuousMultilinearMap.zero_apply]
  rw [n04PositiveGeometry_projectedJet_apply,
    n04PositiveGeometry_fiberInverse_higherJet hf hg hfg B hB hn]
  apply congrArg (fun y => -B y)
  apply Finset.sum_congr rfl
  intro c _
  by_cases hc : 2 ≤ c.length
  · simp only [if_pos hc, ContinuousMultilinearMap.sum_apply]
    rw [n04PositiveGeometry_multilinear_projection_expansion]
    apply Finset.sum_congr rfl
    intro s _
    exact (n04PositiveGeometry_inverseSelectedTerm_apply b f g x c s v).symm
  · simp only [if_neg hc, ContinuousMultilinearMap.zero_apply]

theorem n04PositiveGeometry_clm_multilinear_norm_le
    {E F G : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [NormedAddCommGroup F] [NormedSpace ℝ F]
    [NormedAddCommGroup G] [NormedSpace ℝ G]
    {n : ℕ} (B : F →L[ℝ] G) (A : E [×n]→L[ℝ] F) :
    ‖B.compContinuousMultilinearMap A‖ ≤ ‖B‖ * ‖A‖ := by
  apply ContinuousMultilinearMap.opNorm_le_bound
    (mul_nonneg (norm_nonneg _) (norm_nonneg _))
  intro v
  change ‖B (A v)‖ ≤ _
  exact (B.le_opNorm _).trans
    ((mul_le_mul_of_nonneg_left (A.le_opNorm v) (norm_nonneg B)).trans_eq
      (mul_assoc _ _ _).symm)

theorem n04PositiveGeometry_fiberInverse_projected_norm_terms
    {f g : P × V → V} {x : P × V}
    (hf : ContDiffAt ℝ ∞ f (n04PositiveGeometry_fiberLift g x))
    (hg : ContDiffAt ℝ ∞ g x)
    (hfg : n04PositiveGeometry_fiberLift f ∘ n04PositiveGeometry_fiberLift g
      =ᶠ[𝓝 x] id)
    (B : V →L[ℝ] V)
    (hB : B.comp ((fderiv ℝ f (n04PositiveGeometry_fiberLift g x)).comp
      (ContinuousLinearMap.inr ℝ P V)) = ContinuousLinearMap.id ℝ V)
    {n : ℕ} (hn : 2 ≤ n) (b : Fin n → Bool) :
    ‖n04PositiveGeometry_projectedJet b g x‖ ≤ ‖B‖ *
      ∑ c : OrderedFinpartition n, if 2 ≤ c.length then
        ∑ s : Finset (Fin c.length),
          ‖n04PositiveGeometry_inverseSelectedTerm b f g x c s‖ else 0 := by
  classical
  rw [n04PositiveGeometry_fiberInverse_projected_recursion hf hg hfg B hB hn b, norm_neg]
  apply (n04PositiveGeometry_clm_multilinear_norm_le B _).trans
  apply mul_le_mul_of_nonneg_left _ (norm_nonneg B)
  have hsum : ‖(∑ c : OrderedFinpartition n, if 2 ≤ c.length then
      ∑ s : Finset (Fin c.length), n04PositiveGeometry_inverseSelectedTerm b f g x c s else 0)‖ ≤
      ∑ c : OrderedFinpartition n, ‖if 2 ≤ c.length then
        ∑ s : Finset (Fin c.length), n04PositiveGeometry_inverseSelectedTerm b f g x c s else 0‖ :=
    norm_sum_le _ _
  apply hsum.trans
  exact Finset.sum_le_sum (fun c _ => by
    by_cases hc : 2 ≤ c.length
    · simp only [if_pos hc]
      exact norm_sum_le _ _
    · simp only [if_neg hc, norm_zero, le_refl])

theorem n04PositiveGeometry_fiberInverse_projected_norm_recursion
    {f g : P × V → V} {x : P × V}
    (hf : ContDiffAt ℝ ∞ f (n04PositiveGeometry_fiberLift g x))
    (hg : ContDiffAt ℝ ∞ g x)
    (hfg : n04PositiveGeometry_fiberLift f ∘ n04PositiveGeometry_fiberLift g
      =ᶠ[𝓝 x] id)
    (B : V →L[ℝ] V)
    (hB : B.comp ((fderiv ℝ f (n04PositiveGeometry_fiberLift g x)).comp
      (ContinuousLinearMap.inr ℝ P V)) = ContinuousLinearMap.id ℝ V)
    {n : ℕ} (hn : 2 ≤ n) (b : Fin n → Bool) :
    ‖n04PositiveGeometry_projectedJet b g x‖ ≤ ‖B‖ *
      ∑ c : OrderedFinpartition n, if 2 ≤ c.length then
        ∑ s : Finset (Fin c.length),
          ‖n04PositiveGeometry_projectedJet (fun i => decide (i ∈ s)) f
            (n04PositiveGeometry_fiberLift g x)‖ *
            ∏ i, ‖n04PositiveGeometry_inverseSelectedBlock b g x c s i‖ else 0 := by
  classical
  apply (n04PositiveGeometry_fiberInverse_projected_norm_terms hf hg hfg B hB hn b).trans
  apply mul_le_mul_of_nonneg_left _ (norm_nonneg B)
  apply Finset.sum_le_sum
  intro c _
  by_cases hc : 2 ≤ c.length
  · simp only [if_pos hc]
    apply Finset.sum_le_sum
    intro s _
    exact c.norm_compAlongOrderedFinpartition_le _ _
  · simp only [if_neg hc, le_refl]

end ContinuousFlexibility.Analysis
