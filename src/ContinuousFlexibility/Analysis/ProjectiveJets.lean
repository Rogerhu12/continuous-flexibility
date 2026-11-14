module

public import ContinuousFlexibility.Analysis.ProjectiveDifferential
public import Mathlib.Topology.Algebra.Module.Multilinear.Basic
public import Mathlib.Data.Fin.VecNotation
public import Mathlib.Tactic.FinCases
public import Mathlib.Tactic.Module

/-!
# Actual continuous multilinear jets in projective Fréchet spaces

Candidate jets are genuine continuous multilinear maps on topological
modules. Their verification requires joint continuity and the actual
projective difference-quotient recurrence at every order. We prove
uniqueness, the Banach-coordinate criterion, and complete jet families for
continuous linear maps and for genuine continuous bilinear diagonals.

The quadratic example has its actual first and second derivatives, and
all derivatives of order at least three are proved to be zero. This does
not prove a general higher-order nonlinear chain rule or Schwarz theorem.
-/

@[expose] public section

noncomputable section

namespace ContinuousFlexibility.Analysis

open Set Filter
open scoped Topology

set_option backward.isDefEq.respectTransparency false

section Jets

variable {V W : Type*} [TopologicalSpace V] [AddCommGroup V] [Module ℝ V]
  [TopologicalSpace W] [AddCommGroup W] [Module ℝ W]

abbrev ProjectiveJetFamily (V W : Type*) [TopologicalSpace V] [AddCommGroup V] [Module ℝ V]
    [TopologicalSpace W] [AddCommGroup W] [Module ℝ W] :=
  ∀ n : ℕ, V → ContinuousMultilinearMap ℝ (fun _ : Fin n => V) W

/-- Concrete verification of continuous multilinear candidates by actual
directional quotient limits. No symmetry or tame estimates are assumed. -/
def HasProjectiveJetsOn (f : V → W) (J : ProjectiveJetFamily V W) (U : Set V) : Prop :=
  (∀ x ∈ U, J 0 x Fin.elim0 = f x) ∧
  (∀ n, ContinuousOn (fun p : V × (Fin n → V) => J n p.1 p.2) (U ×ˢ univ)) ∧
  (∀ n x, x ∈ U → ∀ v vs,
    HasProjectiveLineDerivAt (fun y => J n y vs) (J (n + 1) x (Fin.cons v vs)) x v)

theorem HasProjectiveLineDerivAt.congr_germ [IsTopologicalAddGroup V] [ContinuousSMul ℝ V]
    {f g : V → W} {df : W} {x v : V} (hf : HasProjectiveLineDerivAt f df x v)
    (hgf : g =ᶠ[𝓝 x] f) : HasProjectiveLineDerivAt g df x v := by
  have hline : Tendsto (fun t : ℝ => x + t • v) (𝓝[≠] (0 : ℝ)) (𝓝 x) := by
    have ht : ContinuousAt (fun t : ℝ => x + t • v) 0 :=
      (continuous_const.add (continuous_id.smul continuous_const)).continuousAt
    simpa only [zero_smul, add_zero] using ht.tendsto.mono_left nhdsWithin_le_nhds
  have hnear := hline.eventually hgf
  have hx : g x = f x := hgf.self_of_nhds
  unfold HasProjectiveLineDerivAt HasProjectiveCurveDerivAt at hf ⊢
  simp only [zero_add, zero_smul, add_zero] at hf ⊢
  apply hf.congr'
  filter_upwards [hnear] with t ht
  rw [ht, hx]

/-- All orders are uniquely determined on the same open domain by the
actual difference-quotient recursion. -/
theorem HasProjectiveJetsOn.unique [IsTopologicalAddGroup V] [ContinuousSMul ℝ V] [T2Space W]
    {f : V → W} {J K : ProjectiveJetFamily V W} {U : Set V}
    (hU : IsOpen U) (hJ : HasProjectiveJetsOn f J U) (hK : HasProjectiveJetsOn f K U) :
    ∀ n x, x ∈ U → J n x = K n x := by
  intro n
  induction n with
  | zero =>
    intro x hx
    apply ContinuousMultilinearMap.ext
    intro vs
    have heq : vs = Fin.elim0 := Subsingleton.elim _ _
    rw [heq, hJ.1 x hx, hK.1 x hx]
  | succ n ih =>
    intro x hx
    apply ContinuousMultilinearMap.ext
    intro vs
    have hj := hJ.2.2 n x hx (vs 0) (Fin.tail vs)
    have hk := hK.2.2 n x hx (vs 0) (Fin.tail vs)
    have heq : (fun y => K n y (Fin.tail vs)) =ᶠ[𝓝 x] (fun y => J n y (Fin.tail vs)) := by
      filter_upwards [hU.mem_nhds hx] with y hy
      rw [ih y hy]
    have hv := (hj.congr_germ heq).unique hk
    simpa only [Fin.cons_self_tail] using hv

/-- Exact linear-map jets, including genuinely zero higher derivatives. -/
def continuousLinearJets (L : V →L[ℝ] W) : ProjectiveJetFamily V W
  | 0, x => ContinuousMultilinearMap.constOfIsEmpty ℝ (fun _ : Fin 0 => V) (L x)
  | 1, _ => ContinuousMultilinearMap.ofSubsingleton ℝ V W (0 : Fin 1) L
  | _ + 2, _ => 0

theorem hasProjectiveJetsOn_continuousLinear (L : V →L[ℝ] W) (U : Set V) :
    HasProjectiveJetsOn L (continuousLinearJets L) U := by
  refine ⟨fun _ _ => rfl, ?_, ?_⟩
  · intro n
    cases n with
    | zero => exact (L.continuous.comp continuous_fst).continuousOn
    | succ n =>
      cases n with
      | zero => exact (L.continuous.comp ((continuous_apply 0).comp continuous_snd)).continuousOn
      | succ n => exact continuousOn_const
  · intro n x _ v vs
    cases n with
    | zero => exact hasProjectiveLineDerivAt_clm L x v
    | succ n =>
      cases n with
      | zero => exact hasProjectiveLineDerivAt_const (L (vs 0)) x v
      | succ n => exact hasProjectiveLineDerivAt_const (0 : W) x v

end Jets

section ProjectiveAssembly

variable {V : Type*} [TopologicalSpace V] [AddCommGroup V] [Module ℝ V]
variable {F : ℕ → Type*} [∀ n, NormedAddCommGroup (F n)] [∀ n, NormedSpace ℝ (F n)]
variable {bond : ∀ n, F (n + 1) →L[ℝ] F n}

/-- A genuine continuous multilinear lift into the closed projective
subspace. Its continuity is inherited from the actual product topology. -/
def projectiveMultilinearLift {k : ℕ}
    (A : ∀ n, ContinuousMultilinearMap ℝ (fun _ : Fin k => V) (F n))
    (hA : ∀ n vs, bond n (A (n + 1) vs) = A n vs) :
    ContinuousMultilinearMap ℝ (fun _ : Fin k => V) (ProjectiveLimit F bond) :=
  (ContinuousMultilinearMap.pi A).codRestrict (compatibleSubmodule F bond) (fun vs n => hA n vs)

@[simp] theorem projectiveMultilinearLift_apply {k : ℕ}
    (A : ∀ n, ContinuousMultilinearMap ℝ (fun _ : Fin k => V) (F n))
    (hA : ∀ n vs, bond n (A (n + 1) vs) = A n vs) (vs : Fin k → V) (n : ℕ) :
    (projectiveMultilinearLift A hA vs).1 n = A n vs := rfl

theorem projectiveMultilinearLift_unique {k : ℕ}
    (A : ∀ n, ContinuousMultilinearMap ℝ (fun _ : Fin k => V) (F n))
    (hA : ∀ n vs, bond n (A (n + 1) vs) = A n vs)
    (B : ContinuousMultilinearMap ℝ (fun _ : Fin k => V) (ProjectiveLimit F bond))
    (hB : ∀ n vs, (B vs).1 n = A n vs) : B = projectiveMultilinearLift A hA := by
  apply ContinuousMultilinearMap.ext
  intro vs
  apply Subtype.ext
  funext n
  exact hB n vs

theorem continuousOn_projective_map_iff_levels {X : Type*} [TopologicalSpace X]
    (f : X → ProjectiveLimit F bond) (U : Set X) :
    ContinuousOn f U ↔ ∀ n, ContinuousOn (fun x => (f x).1 n) U := by
  constructor
  · intro hf n
    exact (projectiveCoordinate F bond n).continuous.comp_continuousOn hf
  · intro hf x hx
    rw [ContinuousWithinAt, tendsto_projectiveLimit_iff]
    exact fun n => hf n x hx

/-- The jet predicate is equivalent to actual Banach-coordinate
derivatives and joint continuity, for every order, on one fixed domain. -/
theorem hasProjectiveJetsOn_iff_banach_levels
    (f : V → ProjectiveLimit F bond) (J : ProjectiveJetFamily V (ProjectiveLimit F bond)) (U : Set V) :
    HasProjectiveJetsOn f J U ↔ ∀ n,
      (∀ x ∈ U, (J 0 x Fin.elim0).1 n = (f x).1 n) ∧
      (∀ k, ContinuousOn (fun p : V × (Fin k → V) => (J k p.1 p.2).1 n) (U ×ˢ univ)) ∧
      (∀ k x, x ∈ U → ∀ v vs,
        HasDerivAt (fun t : ℝ => (J k (x + t • v) vs).1 n)
          ((J (k + 1) x (Fin.cons v vs)).1 n) 0) := by
  constructor
  · intro h n
    refine ⟨fun x hx => congrArg (fun z : ProjectiveLimit F bond => z.1 n) (h.1 x hx), ?_, ?_⟩
    · intro k
      exact (continuousOn_projective_map_iff_levels _ _).mp (h.2.1 k) n
    · intro k x hx v vs
      exact (hasProjectiveLineDerivAt_iff_levels _ _ _ _).mp (h.2.2 k x hx v vs) n
  · intro h
    refine ⟨?_, ?_, ?_⟩
    · intro x hx
      apply Subtype.ext
      funext n
      exact (h n).1 x hx
    · intro k
      apply (continuousOn_projective_map_iff_levels _ _).mpr
      exact fun n => (h n).2.1 k
    · intro k x hx v vs
      apply (hasProjectiveLineDerivAt_iff_levels _ _ _ _).mpr
      exact fun n => (h n).2.2 k x hx v vs

end ProjectiveAssembly

section QuadraticJets

variable {V W : Type*} [TopologicalSpace V] [AddCommGroup V] [Module ℝ V]
  [TopologicalSpace W] [AddCommGroup W] [Module ℝ W]

variable (B : ContinuousMultilinearMap ℝ (fun _ : Fin 2 => V) W)

def bilinearJetValue (x y : V) : W := B ![x, y]

private theorem bilinearJet_left_apply (x y : V) :
    B.toContinuousLinearMap ![0, y] 0 x = bilinearJetValue B x y := by
  change B (Function.update ![0, y] 0 x) = B ![x, y]
  congr 1
  funext i
  fin_cases i <;> simp

private theorem bilinearJet_right_apply (x y : V) :
    B.toContinuousLinearMap ![x, 0] 1 y = bilinearJetValue B x y := by
  change B (Function.update ![x, 0] 1 y) = B ![x, y]
  congr 1
  funext i
  fin_cases i <;> simp

private theorem bilinearJet_add_left (x y z : V) :
    bilinearJetValue B (x + y) z = bilinearJetValue B x z + bilinearJetValue B y z := by
  rw [← bilinearJet_left_apply B (x + y) z, map_add,
    bilinearJet_left_apply, bilinearJet_left_apply]

private theorem bilinearJet_add_right (x y z : V) :
    bilinearJetValue B x (y + z) = bilinearJetValue B x y + bilinearJetValue B x z := by
  rw [← bilinearJet_right_apply B x (y + z), map_add,
    bilinearJet_right_apply, bilinearJet_right_apply]

private theorem bilinearJet_smul_left (a : ℝ) (x y : V) :
    bilinearJetValue B (a • x) y = a • bilinearJetValue B x y := by
  rw [← bilinearJet_left_apply B (a • x) y, map_smul, bilinearJet_left_apply]

private theorem bilinearJet_smul_right (a : ℝ) (x y : V) :
    bilinearJetValue B x (a • y) = a • bilinearJetValue B x y := by
  rw [← bilinearJet_right_apply B x (a • y), map_smul, bilinearJet_right_apply]

private theorem continuous_bilinearJetValue : Continuous (fun p : V × V => bilinearJetValue B p.1 p.2) := by
  have h : Continuous (fun p : V × V => (![p.1, p.2] : Fin 2 → V)) := by
    apply continuous_pi
    intro i
    fin_cases i
    · exact continuous_fst
    · exact continuous_snd
  convert B.cont.comp h using 1
  funext p
  rfl

def quadraticJetValue (x : V) : W := bilinearJetValue B x x

variable [IsTopologicalAddGroup W]

def quadraticJetFirst (x : V) : V →L[ℝ] W :=
  B.toContinuousLinearMap ![0, x] 0 + B.toContinuousLinearMap ![x, 0] 1

@[simp] theorem quadraticJetFirst_apply (x v : V) :
    quadraticJetFirst B x v = bilinearJetValue B v x + bilinearJetValue B x v := by
  change B.toContinuousLinearMap ![0, x] 0 v + B.toContinuousLinearMap ![x, 0] 1 v = _
  rw [bilinearJet_left_apply, bilinearJet_right_apply]

def quadraticJetSecond : ContinuousMultilinearMap ℝ (fun _ : Fin 2 => V) W :=
  B + B.domDomCongr (Equiv.swap (0 : Fin 2) 1)

@[simp] theorem quadraticJetSecond_apply (vs : Fin 2 → V) :
    quadraticJetSecond B vs = bilinearJetValue B (vs 0) (vs 1) +
      bilinearJetValue B (vs 1) (vs 0) := by
  have h0 : vs = ![vs 0, vs 1] := by funext i; fin_cases i <;> rfl
  have hs : (fun i => vs (Equiv.swap (0 : Fin 2) 1 i)) = ![vs 1, vs 0] := by
    funext i
    fin_cases i <;> simp
  change B vs + B (fun i => vs (Equiv.swap (0 : Fin 2) 1 i)) = B ![vs 0, vs 1] + B ![vs 1, vs 0]
  exact congrArg₂ (fun a b : W => a + b) (congrArg B h0) (congrArg B hs)

private theorem quadraticJet_increment (x v : V) (a : ℝ) :
    quadraticJetValue B (x + a • v) - quadraticJetValue B x =
      a • (quadraticJetFirst B x v + a • quadraticJetValue B v) := by
  simp only [quadraticJetValue, quadraticJetFirst_apply, bilinearJet_add_left,
    bilinearJet_add_right, bilinearJet_smul_left, bilinearJet_smul_right]
  module

variable [ContinuousSMul ℝ W]

/-- The first derivative of the genuine nonlinear diagonal, in the
original topological target, including a projective Fréchet target. -/
theorem hasProjectiveLineDerivAt_quadraticJetValue (x v : V) :
    HasProjectiveLineDerivAt (quadraticJetValue B) (quadraticJetFirst B x v) x v := by
  unfold HasProjectiveLineDerivAt HasProjectiveCurveDerivAt
  simp only [zero_add, zero_smul, add_zero]
  have hzero : Tendsto (fun a : ℝ => a) (𝓝[≠] (0 : ℝ)) (𝓝 0) :=
    tendsto_id.mono_left nhdsWithin_le_nhds
  have ht : Tendsto (fun a : ℝ => quadraticJetFirst B x v + a • quadraticJetValue B v)
      (𝓝[≠] (0 : ℝ)) (𝓝 (quadraticJetFirst B x v)) := by
    simpa only [zero_smul, add_zero, id_eq] using
      (tendsto_const_nhds (x := quadraticJetFirst B x v)).add
        (hzero.smul (tendsto_const_nhds (x := quadraticJetValue B v)))
  apply ht.congr'
  filter_upwards [self_mem_nhdsWithin] with a ha
  have hne : a ≠ 0 := by simpa using ha
  rw [quadraticJet_increment, smul_smul, inv_mul_cancel₀ hne, one_smul]

def quadraticJets : ProjectiveJetFamily V W
  | 0, x => ContinuousMultilinearMap.constOfIsEmpty ℝ (fun _ : Fin 0 => V) (quadraticJetValue B x)
  | 1, x => ContinuousMultilinearMap.ofSubsingleton ℝ V W (0 : Fin 1) (quadraticJetFirst B x)
  | 2, _ => quadraticJetSecond B
  | _ + 3, _ => 0

omit [ContinuousSMul ℝ W] in
@[simp] theorem quadraticJets_order_ge_three (n : ℕ) (x : V) :
    quadraticJets B (n + 3) x = 0 := rfl

/-- An actual nonlinear, all-order jet family. The second jet is the
symmetrized bilinear map and all later derivatives are genuinely zero. -/
theorem hasProjectiveJetsOn_quadratic (U : Set V) :
    HasProjectiveJetsOn (quadraticJetValue B) (quadraticJets B) U := by
  refine ⟨fun _ _ => rfl, ?_, ?_⟩
  · intro n
    cases n with
    | zero =>
      exact ((continuous_bilinearJetValue B).comp (continuous_fst.prodMk continuous_fst)).continuousOn
    | succ n =>
      cases n with
      | zero =>
        have heq : (fun p : V × (Fin 1 → V) => quadraticJetFirst B p.1 (p.2 0)) =
            (fun p => bilinearJetValue B (p.2 0) p.1 + bilinearJetValue B p.1 (p.2 0)) := by
          funext p
          exact quadraticJetFirst_apply B _ _
        change ContinuousOn (fun p : V × (Fin 1 → V) => quadraticJetFirst B p.1 (p.2 0)) _
        rw [heq]
        have hv : Continuous (fun p : V × (Fin 1 → V) => p.2 0) :=
          (continuous_apply 0).comp continuous_snd
        exact (((continuous_bilinearJetValue B).comp
          (hv.prodMk continuous_fst)).add
            ((continuous_bilinearJetValue B).comp
              (continuous_fst.prodMk hv))).continuousOn
      | succ n =>
        cases n with
        | zero => exact ((quadraticJetSecond B).cont.comp continuous_snd).continuousOn
        | succ n => exact continuousOn_const
  · intro n x _ v vs
    cases n with
    | zero => exact hasProjectiveLineDerivAt_quadraticJetValue B x v
    | succ n =>
      cases n with
      | zero =>
        change HasProjectiveLineDerivAt (fun y => quadraticJetFirst B y (vs 0))
          (quadraticJetSecond B (Fin.cons v vs)) x v
        have hD : quadraticJetSecond B (Fin.cons v vs) = quadraticJetFirst B (vs 0) v := by
          rw [quadraticJetSecond_apply, quadraticJetFirst_apply]
          simp
        rw [hD]
        have heq : (fun y => quadraticJetFirst B y (vs 0)) = (quadraticJetFirst B (vs 0) : V → W) := by
          funext y
          rw [quadraticJetFirst_apply, quadraticJetFirst_apply, add_comm]
        rw [heq]
        exact hasProjectiveLineDerivAt_clm (quadraticJetFirst B (vs 0)) x v
      | succ n =>
        cases n with
        | zero => exact hasProjectiveLineDerivAt_const (quadraticJetSecond B vs) x v
        | succ n => exact hasProjectiveLineDerivAt_const (0 : W) x v

end QuadraticJets

end ContinuousFlexibility.Analysis
