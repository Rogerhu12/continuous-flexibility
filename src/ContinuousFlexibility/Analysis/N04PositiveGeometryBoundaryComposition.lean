import ContinuousFlexibility.Analysis.N04PositiveGeometryBoundaryOperatorBounds
import ContinuousFlexibility.Analysis.N04RealizationInverseJetFormula

/-!
# Genuine finite spatial compositions at moving boundary points

Only positive spatial orders occur in a positive composition jet. The
ordinary partition formula therefore constructs its actual parameter
and angular tower without imposing a value bound on an angle lift.
Finite operator evaluation preserves the reserved angular orders.
-/

noncomputable section

namespace ContinuousFlexibility.Analysis

open Set Function ContinuousFlexibility.Statements
open scoped ContDiff BigOperators

variable {X E F G : Type*}
  [TopologicalSpace X] [AddCommGroup X] [Module ℝ X]
  [IsTopologicalAddGroup X] [ContinuousSMul ℝ X]
  [NormedAddCommGroup E] [NormedSpace ℝ E]
  [NormedAddCommGroup F] [NormedSpace ℝ F]
  [NormedAddCommGroup G] [NormedSpace ℝ G]

private theorem boundaryComposition_apply
    {f : E → F} {g : G → E} {q : G}
    (hf : ContDiffAt ℝ ∞ f (g q)) (hg : ContDiffAt ℝ ∞ g q)
    (n : ℕ) (v : Fin n → G) :
    iteratedFDeriv ℝ n (f ∘ g) q v =
      ∑ c : OrderedFinpartition n, iteratedFDeriv ℝ c.length f (g q)
        (fun i => iteratedFDeriv ℝ (c.partSize i) g q (v ∘ c.emb i)) := by
  have hcomp : iteratedFDeriv ℝ n (f ∘ g) q =
      ∑ c : OrderedFinpartition n,
        c.compAlongOrderedFinpartition (iteratedFDeriv ℝ c.length f (g q))
          (fun i => iteratedFDeriv ℝ (c.partSize i) g q) :=
    iteratedFDeriv_comp hf hg (by simp : (n : ℕ∞ω) ≤ ∞)
  have he := congrArg (fun A : G [×n]→L[ℝ] F => A v) hcomp
  simpa only [ContinuousMultilinearMap.sum_apply,
    OrderedFinpartition.compAlongOrderFinpartition_apply,
    OrderedFinpartition.applyOrderedFinpartition_apply] using he

def n04PositiveGeometry_boundaryComposition_directions
    (n : ℕ) (hn : 0 < n) {U : Set X} (hU : IsOpen U)
    (f : X × ℝ → E → F) (g : X × ℝ → G → E) (q : X × ℝ → G)
    (hf : ∀ z ∈ U ×ˢ univ, ContDiffAt ℝ ∞ (f z) (g z (q z)))
    (hg : ∀ z ∈ U ×ˢ univ, ContDiffAt ℝ ∞ (g z) (q z))
    (JF : ∀ j, 1 ≤ j → j ≤ n →
      SmoothDirections (U ×ˢ univ) (fun z => iteratedFDeriv ℝ j (f z) (g z (q z))))
    (JG : ∀ j, 1 ≤ j → j ≤ n → ∀ v : Fin j → G,
      SmoothDirections (U ×ˢ univ) (fun z => iteratedFDeriv ℝ j (g z) (q z) v))
    (v : Fin n → G) :
    SmoothDirections (U ×ˢ univ)
      (fun z => iteratedFDeriv ℝ n (f z ∘ g z) (q z) v) := by
  classical
  let term : OrderedFinpartition n → X × ℝ → F := fun c z =>
    iteratedFDeriv ℝ c.length (f z) (g z (q z))
      (fun i => iteratedFDeriv ℝ (c.partSize i) (g z) (q z) (v ∘ c.emb i))
  let JT : ∀ c, SmoothDirections (U ×ˢ univ) (term c) := fun c =>
    smoothDirections_contDiff_comp
      (smoothDirectionsProd (JF c.length (c.length_pos hn) c.length_le)
        (smoothDirections_vectorTuple (hU.prod isOpen_univ) (fun i =>
          JG (c.partSize i) (c.partSize_pos i) (c.partSize_le i) (v ∘ c.emb i))))
      isOpen_univ (contDiff_multilinearEvaluation c.length).contDiffOn
      (fun _ _ => mem_univ _)
  exact (smoothDirections_finiteSum (hU.prod isOpen_univ) JT).congr
    (fun z hz => (boundaryComposition_apply (hf z hz) (hg z hz) n v).symm)

theorem n04PositiveGeometry_boundaryComposition_bound (N n : ℕ) (hn : 0 < n) :
    ∃ C : ℝ, 1 ≤ C ∧
      ∀ {U : Set X}, IsOpen U →
      ∀ (f : X × ℝ → E → F) (g : X × ℝ → G → E) (q : X × ℝ → G),
      (∀ z ∈ U ×ˢ univ, ContDiffAt ℝ ∞ (f z) (g z (q z))) →
      (∀ z ∈ U ×ˢ univ, ContDiffAt ℝ ∞ (g z) (q z)) →
      ∀ JF : ∀ j, 1 ≤ j → j ≤ n →
        SmoothDirections (U ×ˢ univ) (fun z => iteratedFDeriv ℝ j (f z) (g z (q z))),
      ∀ JG : ∀ j, 1 ≤ j → j ≤ n → ∀ v : Fin j → G,
        SmoothDirections (U ×ˢ univ) (fun z => iteratedFDeriv ℝ j (g z) (q z) v),
      ∀ K s d : ℕ, K + s + d ≤ N → ∀ x ∈ U, ∀ θ P,
      ∀ M H t : ℝ, 1 ≤ M → 0 ≤ H → H ≤ M → 1 ≤ t → ∀ shift,
      (∀ j hj hjn, N04BoundaryWordBounds (JF j hj hjn) K s d x θ P M H t shift) →
      (∀ j hj hjn v, (∀ i, ‖v i‖ ≤ 1) →
        N04BoundaryWordBounds (JG j hj hjn v) K s d x θ P M H t shift) →
      ∀ v : Fin n → G, (∀ i, ‖v i‖ ≤ 1) →
      ∀ Q : SmoothDirections (U ×ˢ univ)
        (fun z => iteratedFDeriv ℝ n (f z ∘ g z) (q z) v),
      N04BoundaryWordBounds Q K s d x θ P (C * M ^ (n + 1 + 2 * N)) H t shift := by
  classical
  choose a ha hbound using fun c : OrderedFinpartition n =>
    n04PositiveGeometry_boundary_multilinearApply_bound (X := X) (E := E) (F := F)
      c.length N
  let A : ℝ := 1 + ∑ c : OrderedFinpartition n, a c
  have hA : 1 ≤ A := le_add_of_nonneg_right
    (Finset.sum_nonneg (fun c _ => zero_le_one.trans (ha c)))
  have haA (c : OrderedFinpartition n) : a c ≤ A :=
    (Finset.single_le_sum (fun c _ => zero_le_one.trans (ha c))
      (Finset.mem_univ c)).trans (le_add_of_nonneg_left zero_le_one)
  let C : ℝ := 1 + (Fintype.card (OrderedFinpartition n) : ℝ) * A
  have hC : 1 ≤ C := le_add_of_nonneg_right
    (mul_nonneg (Nat.cast_nonneg _) (zero_le_one.trans hA))
  refine ⟨C, hC, ?_⟩
  intro U hU f g q hf hg JF JG K s d hN x hx θ P M H t hM hH hHM ht shift
    hJF hJG v hv Q
  let D := n + 1 + 2 * N
  let term : OrderedFinpartition n → X × ℝ → F := fun c z =>
    iteratedFDeriv ℝ c.length (f z) (g z (q z))
      (fun i => iteratedFDeriv ℝ (c.partSize i) (g z) (q z) (v ∘ c.emb i))
  have hterms (c : OrderedFinpartition n) :
      ∃ JT : SmoothDirections (U ×ˢ univ) (term c),
        N04BoundaryWordBounds JT K s d x θ P (A * M ^ D) H t shift := by
    let JV : ∀ i : Fin c.length, SmoothDirections (U ×ˢ univ)
        (fun z => iteratedFDeriv ℝ (c.partSize i) (g z) (q z) (v ∘ c.emb i)) :=
      fun i => JG (c.partSize i) (c.partSize_pos i) (c.partSize_le i) (v ∘ c.emb i)
    let Jtuple := smoothDirections_vectorTuple (hU.prod isOpen_univ) JV
    let Jpair := smoothDirectionsProd (JF c.length (c.length_pos hn) c.length_le) Jtuple
    let JT := smoothDirections_contDiff_comp Jpair isOpen_univ
      (contDiff_multilinearEvaluation c.length).contDiffOn (fun _ _ => mem_univ _)
    have htuple : N04BoundaryWordBounds Jtuple K s d x θ P M H t shift :=
      N04BoundaryWordBounds.vectorTuple hU JV (zero_le_one.trans hM) hH
        (zero_le_one.trans ht) (fun i => hJG _ _ _ _ (fun j => hv (c.emb i j)))
    have htower := hbound c (JF c.length (c.length_pos hn) c.length_le) Jtuple JT
      K s d hN x hx θ P M H t hM hH hHM ht shift (hJF _ _ _) htuple
    refine ⟨JT, htower.enlarge hH (zero_le_one.trans ht) ?_⟩
    exact mul_le_mul (haA c) (pow_le_pow_right₀ hM (Nat.add_le_add_right
      (Nat.add_le_add_right c.length_le 1) (2 * N)))
      (pow_nonneg (zero_le_one.trans hM) _) (zero_le_one.trans hA)
  choose JT hJT using hterms
  have hsum := N04BoundaryWordBounds.finiteSum hU JT hJT
  have hcost : (Fintype.card (OrderedFinpartition n) : ℝ) * (A * M ^ D) ≤ C * M ^ D := by
    dsimp only [C]
    have hp : 0 ≤ M ^ D := pow_nonneg (zero_le_one.trans hM) _
    nlinarith
  exact (hsum.enlarge hH (zero_le_one.trans ht) hcost).congr hx
    (fun z hz => (boundaryComposition_apply (hf z hz) (hg z hz) n v).symm)

end ContinuousFlexibility.Analysis
