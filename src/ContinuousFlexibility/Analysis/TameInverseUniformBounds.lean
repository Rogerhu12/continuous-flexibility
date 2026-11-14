module

public import ContinuousFlexibility.Analysis.TameInverseBounds
public import ContinuousFlexibility.Analysis.TameUniformGrowth

/-!
# Uniform bounded-set estimates for genuine inverse-family jets

The finite inverse expressions already construct the actual derivatives.
Estimating those same expressions by uniform low-seminorm growth retains
the order of all quantifiers: the low order and loss precede the radius,
the target order, and every base point and directional argument.
-/

@[expose] public section

noncomputable section

namespace ContinuousFlexibility.Analysis

open Set ContinuousFlexibility.Statements
open scoped BigOperators

variable {X Y Z A : Type*}
  [TopologicalSpace X] [AddCommGroup X] [Module ℝ X]
  [IsTopologicalAddGroup X] [ContinuousSMul ℝ X]
  [TopologicalSpace Y] [AddCommGroup Y] [Module ℝ Y]
  [IsTopologicalAddGroup Y] [ContinuousSMul ℝ Y] [T2Space Y]
  [TopologicalSpace Z] [AddCommGroup Z] [Module ℝ Z]
  [IsTopologicalAddGroup Z] [ContinuousSMul ℝ Z] [T2Space Z]
  [TopologicalSpace A] [AddCommGroup A] [Module ℝ A]
  {U : Set X} {L : X → Y →L[ℝ] Z}

theorem inverseFamilyContinuousLinearMap_uniformLowGrowth
    {p : ℕ → Seminorm ℝ X} {q : ℕ → Seminorm ℝ Y} {r : ℕ → Seminorm ℝ Z}
    (V : X → Z →ₗ[ℝ] Y)
    (hV : ContinuousOn (fun z : X × Z => V z.1 z.2) (U ×ˢ univ))
    (hb : HasUniformLowGrowth (pairGrading p r) q (fun z : X × Z => V z.1 z.2)) :
    HasUniformLowGrowth (pairGrading p r) q
      (fun z : X × Z => inverseFamilyContinuousLinearMap V hV z.1 z.2) := by
  classical
  apply hb.of_le
  intro s z
  by_cases hz : z.1 ∈ U
  · rw [inverseFamilyContinuousLinearMap_apply V hV hz]
  · have hzero : inverseFamilyContinuousLinearMap V hV z.1 z.2 = 0 := by
      simp only [inverseFamilyContinuousLinearMap, dif_neg hz, ContinuousLinearMap.zero_apply]
    rw [hzero, map_zero]
    exact (apply_nonneg (q s) (V z.1 z.2))

theorem TameInverseExpression.uniformLowGrowth_eval
    {p : ℕ → Seminorm ℝ X} {q : ℕ → Seminorm ℝ Y} {r : ℕ → Seminorm ℝ Z}
    {a : ℕ → Seminorm ℝ A}
    (hp : Monotone p) (hq : Monotone q) (hr : Monotone r) (ha : Monotone a)
    (e : TameInverseExpression X Y Z A) (he : e.IsZeroLoss p q r a)
    (J : SmoothDirections (U ×ˢ univ) (fun z : X × Y => L z.1 z.2))
    (V : X → Z →L[ℝ] Y)
    (hV : HasUniformLowGrowth (pairGrading p r) q (fun z : X × Z => V z.1 z.2))
    (hJ : ∀ k, HasUniformLowGrowth (jetGrading (pairGrading p q) k) r
      (fun z => J.D k z.1 z.2)) :
    HasUniformLowGrowth (pairGrading (pairGrading p r) a) (pairGrading q r)
      (fun z => e.eval J V z.1 z.2) := by
  let d := pairGrading (pairGrading p r) a
  have hd : Monotone d := tamePairGrading_monotone (tamePairGrading_monotone hp hr) ha
  have hstate : HasUniformLowGrowth d (pairGrading p r)
      (fun z : (X × Z) × A => z.1) := uniformLowGrowth_pair_fst (pairGrading p r) a
  have hx := (uniformLowGrowth_pair_fst p r).comp hd hstate
  have hy := (uniformLowGrowth_pair_snd p r).comp hd hstate
  have haux : HasUniformLowGrowth d a (fun z : (X × Z) × A => z.2) :=
    uniformLowGrowth_pair_snd (pairGrading p r) a
  induction e with
  | zero => exact uniformLowGrowth_const d (pairGrading q r) 0
  | source => exact (uniformLowGrowth_const d q (0 : Y)).prodMk hd hy
  | linearSource c => exact (uniformLowGrowth_of_zeroLoss c he).comp hd haux
  | add e f ie iff => exact (ie he.1).add hd (iff he.2)
  | neg e ie => exact (ie he).neg
  | inverse e ie =>
      have hs := (uniformLowGrowth_pair_snd q r).comp hd (ie he)
      have hi := hV.comp hd (hx.prodMk hd hs)
      exact hi.prodMk hd (uniformLowGrowth_const d r (0 : Z))
  | forward n v e ie =>
      have heval := (uniformLowGrowth_pair_fst q r).comp hd (ie he.2)
      have hdirs (i : Fin n) : HasUniformLowGrowth d p
          (fun z : (X × Z) × A => v i z.2) :=
        (uniformLowGrowth_of_zeroLoss (v i) (he.1 i)).comp hd haux
      have hinput (i : Fin (n + 1)) : HasUniformLowGrowth d (pairGrading p q)
          (fun z : (X × Z) × A => Fin.snoc (α := fun _ : Fin (n + 1) => X × Y)
            (fun j => (v j z.2, (0 : Y)))
            ((0 : X), (e.eval J V z.1 z.2).1) i) := by
        refine Fin.lastCases ?_ (fun j => ?_) i
        · simpa only [Fin.snoc_last, Function.comp_def] using
            (uniformLowGrowth_const d p (0 : X)).prodMk hd heval
        · simpa only [Fin.snoc_castSucc] using
            (hdirs j).prodMk hd (uniformLowGrowth_const d q (0 : Y))
      have hargs := (hx.prodMk hd (uniformLowGrowth_const d q (0 : Y))).prodMk hd
        (HasUniformLowGrowth.pi hd hinput)
      have hj := (hJ (n + 1)).comp hd hargs
      exact (uniformLowGrowth_const d q (0 : Y)).prodMk hd hj

theorem inverseFamilySmoothDirections_uniform_oneHigh
    {p : ℕ → Seminorm ℝ X} {q : ℕ → Seminorm ℝ Y} {r : ℕ → Seminorm ℝ Z}
    (hp : Monotone p) (hq : Monotone q) (hr : Monotone r)
    (J : SmoothDirections (U ×ˢ univ) (fun z : X × Y => L z.1 z.2))
    (hU : IsOpen U) (V : X → Z →L[ℝ] Y)
    (hleft : ∀ x ∈ U, ∀ y, V x (L x y) = y)
    (hright : ∀ x ∈ U, ∀ y, L x (V x y) = y)
    (hV : ContinuousOn (fun z : X × Z => V z.1 z.2) (U ×ˢ univ))
    (hVbound : HasUniformLowGrowth (pairGrading p r) q (fun z : X × Z => V z.1 z.2))
    (hJbound : ∀ k, HasUniformLowGrowth (jetGrading (pairGrading p q) k) r
      (fun z => J.D k z.1 z.2)) :
    ∀ n, ∃ base loss : ℕ, ∀ K : ℝ, 0 ≤ K → ∀ s : ℕ, ∃ C : ℝ, 0 ≤ C ∧
      ∀ x ∈ U ×ˢ univ, pairGrading p r base x ≤ K → ∀ v : Fin n → X × Z,
        q s ((inverseFamilySmoothDirections J hU V hleft hright hV).D n x v) ≤
          C * tameJetSize (pairGrading p r) n s loss base x v := by
  intro n
  have hpair := tamePairGrading_monotone hp hr
  have htuple := tupleGrading_monotone (fun _ : Fin n => pairGrading p r) (fun _ => hpair)
  have hd := tamePairGrading_monotone hpair htuple
  have he := (inverseExpressionJet (X := X) (Y := Y) (Z := Z) n).uniformLowGrowth_eval
    hp hq hr htuple (inverseExpressionJet_zeroLoss p q r n) J V hVbound hJbound
  have hfst := (uniformLowGrowth_pair_fst q r).comp hd he
  apply uniformLowGrowth_multilinear_oneHigh_on
    ((inverseFamilySmoothDirections J hU V hleft hright hV).D n) hfst
  intro x hx v
  exact inverseFamilySmoothDirections_apply J hU V hleft hright hV n hx.1 v

end ContinuousFlexibility.Analysis
