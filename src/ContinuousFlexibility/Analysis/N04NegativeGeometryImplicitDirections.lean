import ContinuousFlexibility.Analysis.N04NegativeGeometryImplicitJets
import ContinuousFlexibility.Analysis.N04NegativeGeometryFiniteAffineDirections

/-!
# Genuine parameter towers of actual implicit solutions

Finite-dimensional implicit smoothness identifies the recursively
constructed candidates with actual finite-affine derivatives. Their
joint continuity then gives one all-order tower on the original
topological parameter domain. Neither an inverse parameter tower nor
an inverse jet estimate is an input.
-/

noncomputable section

namespace ContinuousFlexibility.Analysis

open Set Filter Function ContinuousFlexibility.Statements
open scoped Topology ContDiff BigOperators

namespace N04NegativeGeometryImplicitJet

private theorem iteratedFDeriv_graph
    {P Y : Type*} [NormedAddCommGroup P] [NormedSpace ℝ P]
    [FiniteDimensional ℝ P] [NormedAddCommGroup Y] [NormedSpace ℝ Y]
    {g : P → Y} {x : P} (hg : ContDiffAt ℝ ∞ g x)
    {n : ℕ} (hn : 0 < n) (v : Fin n → P) :
    iteratedFDeriv ℝ n (fun q => (q, g q)) x v =
      graph n (iteratedFDeriv ℝ n g x) v := by
  have hid : iteratedFDeriv ℝ n (id : P → P) x =
      continuousLinearJets (ContinuousLinearMap.id ℝ P) n x :=
    ((hasProjectiveJetsOn_continuousLinear (ContinuousLinearMap.id ℝ P) univ).
      eq_iteratedFDeriv_finiteDimensional isOpen_univ n (mem_univ x)).symm
  change iteratedFDeriv ℝ n (fun q => ((id : P → P) q, g q)) x v = _
  rw [iteratedFDeriv_prodMk (contDiffAt_id : ContDiffAt ℝ ∞ (id : P → P) x)
    hg (by simp)]
  change (iteratedFDeriv ℝ n (id : P → P) x v, iteratedFDeriv ℝ n g x v) = _
  rw [hid]
  cases n with
  | zero => omega
  | succ n =>
    cases n with
    | zero =>
      change (v 0, iteratedFDeriv ℝ 1 g x v) =
        (v 0, 0) + (0, iteratedFDeriv ℝ 1 g x v)
      simp only [Prod.mk_add_mk, add_zero, zero_add]
    | succ n =>
      change (0, iteratedFDeriv ℝ (n + 2) g x v) =
        (0 : P × Y) + (0, iteratedFDeriv ℝ (n + 2) g x v)
      rw [zero_add]

variable {E Y : Type*}
  [TopologicalSpace E] [AddCommGroup E] [Module ℝ E]
  [IsTopologicalAddGroup E] [ContinuousSMul ℝ E]
  [NormedAddCommGroup Y] [NormedSpace ℝ Y] [FiniteDimensional ℝ Y]
  {U : Set E} {V : Set Y} {H : E × Y → Y} {g : E → Y}

/-- Differentiating the genuine implicit equation on a finite affine
slice gives the exact zero partition sum. -/
private theorem finiteAffine_partition_zero
    (J : SmoothDirections (U ×ˢ V) H) (hU : IsOpen U)
    (hmap : MapsTo g U V) (hsol : ∀ x ∈ U, H (x, g x) = 0)
    {P : Type*} [NormedAddCommGroup P] [NormedSpace ℝ P] [FiniteDimensional ℝ P]
    (x : E) (hx : x ∈ U) (L : P →L[ℝ] E)
    (hg : ContDiffAt ℝ ∞ (fun q => g (x + L q)) 0)
    {n : ℕ} (hn : 0 < n) (v : Fin n → P) :
    (∑ c : _root_.OrderedFinpartition n,
      J.D c.length (x, g x)
        (fun i => (L.prodMap (ContinuousLinearMap.id ℝ Y))
          (graph (c.partSize i)
            (iteratedFDeriv ℝ (c.partSize i) (fun q => g (x + L q)) 0)
              (v ∘ c.emb i)))) = 0 := by
  let M : (P × Y) →L[ℝ] (E × Y) := L.prodMap (ContinuousLinearMap.id ℝ Y)
  let F : P × Y → Y := fun q => H ((x, (0 : Y)) + M q)
  let g' : P → Y := fun q => g (x + L q)
  let Φ : P → P × Y := fun q => (q, g' q)
  have hM (q : P × Y) : (x, (0 : Y)) + M q = (x + L q.1, q.2) := by
    change (x + L q.1, 0 + q.2) = _
    rw [zero_add]
  have hpoint : (x, (0 : Y)) + M (0, g x) ∈ U ×ˢ V := by
    simpa only [hM, map_zero, add_zero] using (show (x, g x) ∈ U ×ˢ V from ⟨hx, hmap hx⟩)
  let K := smoothDirections_precompAffine J (x, (0 : Y)) M
  have hF : ContDiffAt ℝ ∞ F (0, g x) :=
    (smoothDirections_contDiffOn_finiteDimensional K).contDiffAt
      (K.open_domain.mem_nhds hpoint)
  have hΦ : ContDiffAt ℝ ∞ Φ 0 := contDiffAt_id.prodMk hg
  have hΦ0 : Φ 0 = (0, g x) := by simp only [Φ, g', map_zero, add_zero]
  have houter (k : ℕ) (w : Fin k → P × Y) :
      iteratedFDeriv ℝ k F (0, g x) w = J.D k (x, g x) (fun i => M (w i)) := by
    have hj := smoothDirections_iteratedFDeriv_finiteAffine
      J (x, (0 : Y)) M k hpoint w
    simpa only [F, hM, map_zero, add_zero] using hj
  have hcomp := congrArg (fun A : P [×n]→L[ℝ] Y => A v)
    (iteratedFDeriv_comp (hΦ0.symm ▸ hF) hΦ (by simp : (n : ℕ∞ω) ≤ ∞))
  simp only [ContinuousMultilinearMap.sum_apply,
    OrderedFinpartition.compAlongOrderFinpartition_apply,
    OrderedFinpartition.applyOrderedFinpartition_apply, hΦ0, houter] at hcomp
  have hsum : iteratedFDeriv ℝ n (F ∘ Φ) 0 v =
      ∑ c : _root_.OrderedFinpartition n,
        J.D c.length (x, g x)
          (fun i => M (graph (c.partSize i)
            (iteratedFDeriv ℝ (c.partSize i) g' 0) (v ∘ c.emb i))) := by
    refine hcomp.trans (Finset.sum_congr rfl (fun c _ => ?_))
    congr 1
    funext i
    exact congrArg M (iteratedFDeriv_graph hg (c.partSize_pos i) (v ∘ c.emb i))
  have he : F ∘ Φ =ᶠ[𝓝 (0 : P)] (fun _ => (0 : Y)) := by
    have h0 : x + L (0 : P) ∈ U := by simpa only [map_zero, add_zero] using hx
    filter_upwards [(hU.preimage (continuous_const.add L.continuous)).mem_nhds h0] with q hq
    simpa only [Function.comp_apply, F, Φ, hM, g'] using hsol (x + L q) hq
  have hzero : iteratedFDeriv ℝ n (F ∘ Φ) 0 v = 0 := by
    rw [(he.iteratedFDeriv ℝ n).self_of_nhds]
    simp only [iteratedFDeriv_const_of_ne hn.ne', Pi.zero_apply,
      ContinuousMultilinearMap.zero_apply]
  exact hsum.symm.trans hzero

/-- Every constructed candidate is the actual finite-affine derivative.
The inverse identity is used only for the true spatial first jet. -/
theorem tower_finiteAffine
    (J : SmoothDirections (U ×ˢ V) H) (hU : IsOpen U)
    (hg : ContinuousOn g U) (hmap : MapsTo g U V)
    (A : E → Y →L[ℝ] Y) (hA : ContinuousOn A U)
    (hsol : ∀ x ∈ U, H (x, g x) = 0)
    (hleft : ∀ x ∈ U, ∀ y : Y,
      A x (J.D 1 (x, g x) (fun _ : Fin 1 => (0, y))) = y)
    {P : Type*} [NormedAddCommGroup P] [NormedSpace ℝ P] [FiniteDimensional ℝ P]
    (x : E) (hx : x ∈ U) (L : P →L[ℝ] E)
    (hsmooth : ContDiffAt ℝ ∞ (fun q => g (x + L q)) 0)
    (n : ℕ) (v : Fin n → P) :
    iteratedFDeriv ℝ n (fun q => g (x + L q)) 0 v =
      (tower J hg hmap A hA n).value x (fun i => L (v i)) := by
  let R (k : ℕ) := tower J hg hmap A hA k
  let g' : P → Y := fun q => g (x + L q)
  let M : (P × Y) →L[ℝ] (E × Y) := L.prodMap (ContinuousLinearMap.id ℝ Y)
  induction n using Nat.strong_induction_on with
  | h n ih =>
    cases n with
    | zero =>
      rw [tower_zero_apply]
      simp only [iteratedFDeriv_zero_apply, map_zero, add_zero]
    | succ n =>
      let AJ : ∀ k : ℕ, P [×k]→L[ℝ] (E × Y) :=
        fun k => M.compContinuousMultilinearMap (graph k (iteratedFDeriv ℝ k g' 0))
      let BJ : ∀ k : ℕ, P [×k]→L[ℝ] (E × Y) := fun k =>
        (graph k ((lower (fun j (_ : j < n + 1) => R j) k).value x)).
          compContinuousLinearMap (fun _ => L)
      have hAB (k : ℕ) (hk : k < n + 1) : AJ k = BJ k := by
        apply ContinuousMultilinearMap.ext
        intro w
        dsimp only [AJ, BJ]
        rw [lower_of_lt _ hk]
        exact graph_natural L k (iteratedFDeriv ℝ k g' 0) ((R k).value x) w (ih k hk w)
      have he := n04NegativeGeometry_partition_highest_difference (Nat.succ_pos n)
        (fun k => J.D k (x, g x)) AJ BJ hAB v
      have hzero : (∑ c : _root_.OrderedFinpartition (n + 1),
          J.D c.length (x, g x) (fun i => AJ (c.partSize i) (v ∘ c.emb i))) = 0 :=
        finiteAffine_partition_zero J hU hmap hsol x hx L hsmooth (Nat.succ_pos n) v
      have hforce : (∑ c : _root_.OrderedFinpartition (n + 1),
          J.D c.length (x, g x) (fun i => BJ (c.partSize i) (v ∘ c.emb i))) =
          forcing J g (fun j (_ : j < n + 1) => R j) x (fun i => L (v i)) := by
        rw [forcing_apply]
        rfl
      have hp : M (parameter (n + 1) v) = parameter (n + 1) (fun i => L (v i)) := by
        have hh := graph_natural L (n + 1)
          (0 : P [×(n + 1)]→L[ℝ] Y) (0 : E [×(n + 1)]→L[ℝ] Y) v rfl
        change M (parameter (n + 1) v + 0) = parameter (n + 1) (fun i => L (v i)) + 0 at hh
        simpa only [add_zero] using hh
      have hcurrent : AJ (n + 1) v - BJ (n + 1) v =
          (0, iteratedFDeriv ℝ (n + 1) g' 0 v) := by
        dsimp only [AJ, BJ]
        rw [lower_self]
        change M (parameter (n + 1) v + (0, iteratedFDeriv ℝ (n + 1) g' 0 v)) -
          (parameter (n + 1) (fun i => L (v i)) + 0) = _
        rw [map_add, hp, add_zero, add_sub_cancel_left]
        change (L 0, iteratedFDeriv ℝ (n + 1) g' 0 v) = _
        rw [map_zero]
      rw [hzero, hforce, hcurrent] at he
      have hh := congrArg (A x) he
      rw [map_sub, map_zero, hleft x hx] at hh
      have hvalue : -A x (forcing J g (fun j (_ : j < n + 1) => R j)
          x (fun i => L (v i))) = iteratedFDeriv ℝ (n + 1) g' 0 v := by
        simpa only [zero_sub] using hh
      rw [tower_succ_apply]
      exact hvalue.symm

end N04NegativeGeometryImplicitJet

variable {E Y : Type*}
  [TopologicalSpace E] [AddCommGroup E] [Module ℝ E]
  [IsTopologicalAddGroup E] [ContinuousSMul ℝ E]
  [NormedAddCommGroup Y] [NormedSpace ℝ Y] [FiniteDimensional ℝ Y]
  {U : Set E} {V : Set Y} {H : E × Y → Y} {g : E → Y}

/-- Genuine topological parameter smoothness of an actual implicit
solution follows from the forward tower, joint continuity, spatial
invertibility, and the ordinary finite-affine implicit theorem. -/
def n04NegativeGeometry_implicitSmoothDirections
    (J : SmoothDirections (U ×ˢ V) H) (hU : IsOpen U)
    (hg : ContinuousOn g U) (hmap : MapsTo g U V)
    (A : E → Y →L[ℝ] Y) (hA : ContinuousOn A U)
    (hsol : ∀ x ∈ U, H (x, g x) = 0)
    (hleft : ∀ x ∈ U, ∀ y : Y,
      A x (J.D 1 (x, g x) (fun _ : Fin 1 => (0, y))) = y)
    (hsmooth : ∀ m : ℕ, ∀ x ∈ U, ∀ L : (Fin m → ℝ) →L[ℝ] E,
      ContDiffAt ℝ ∞ (fun q => g (x + L q)) 0) : SmoothDirections U g := by
  let A' : ProjectiveJetFamily E Y :=
    fun n => (N04NegativeGeometryImplicitJet.tower J hg hmap A hA n).value
  exact n04NegativeGeometry_smoothDirections_of_finiteAffine_germs hU A'
    (fun x _ => N04NegativeGeometryImplicitJet.tower_zero_apply J hg hmap A hA x Fin.elim0)
    (fun n => (N04NegativeGeometryImplicitJet.tower J hg hmap A hA n).continuous)
    hsmooth
    (fun m x hx L n v => N04NegativeGeometryImplicitJet.tower_finiteAffine
      J hU hg hmap A hA hsol hleft x hx L (hsmooth m x hx L) n v)

end ContinuousFlexibility.Analysis
