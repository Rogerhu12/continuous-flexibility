module

public import ContinuousFlexibility.Analysis.SmoothDirectionsAngularJets
public import Mathlib.LinearAlgebra.Multilinear.Curry

/-!
# Multilinear expansion of mixed parameter and angular jets

The recursion differentiates one new direction either in the original
parameter or in the angular variable. It is linear in the complete jet
data and multilinear in the joint directions. Currying places each new
parameter direction before the old directions, exactly as required by
the directional derivative convention.
-/

@[expose] public section

noncomputable section

universe u

namespace ContinuousFlexibility.Analysis

open Set Filter ContinuousFlexibility.Statements
open scoped Topology BigOperators

variable {E : Type u} [AddCommGroup E] [Module ℝ E]

abbrev ScalarAngularJetData (E : Type u) [AddCommGroup E] [Module ℝ E] :=
  ∀ b n : ℕ, MultilinearMap ℝ (fun _ : Fin n => E) ℝ

def scalarAngularHead (A : ScalarAngularJetData E) :
    (E × ℝ) →ₗ[ℝ] ScalarAngularJetData E where
  toFun w b n := (A b (n + 1)).curryLeft w.1
  map_add' w v := by
    funext b n
    exact (A b (n + 1)).curryLeft.map_add w.1 v.1
  map_smul' a w := by
    funext b n
    exact (A b (n + 1)).curryLeft.map_smul a w.1

theorem scalarAngularHead_apply (A : ScalarAngularJetData E)
    (w : E × ℝ) (b n : ℕ) (v : Fin n → E) :
    scalarAngularHead A w b n v = A b (n + 1) (Fin.cons w.1 v) :=
  MultilinearMap.curryLeft_apply _ _ _

theorem scalarAngularHead_add (A B : ScalarAngularJetData E) (w : E × ℝ) :
    scalarAngularHead (A + B) w = scalarAngularHead A w + scalarAngularHead B w := by
  funext b n
  ext v
  simp only [scalarAngularHead_apply, Pi.add_apply, add_apply]

theorem scalarAngularHead_smul (a : ℝ) (A : ScalarAngularJetData E) (w : E × ℝ) :
    scalarAngularHead (a • A) w = a • scalarAngularHead A w := by
  funext b n
  ext v
  simp only [scalarAngularHead_apply, Pi.smul_apply, smul_apply]

def scalarAngularShift : ScalarAngularJetData E →ₗ[ℝ] ScalarAngularJetData E where
  toFun A b n := A (b + 1) n
  map_add' _ _ := rfl
  map_smul' _ _ := rfl

theorem scalarAngularShift_apply (A : ScalarAngularJetData E)
    (b n : ℕ) (v : Fin n → E) :
    scalarAngularShift A b n v = A (b + 1) n v := rfl

def scalarAngularExpansion : (n : ℕ) → ScalarAngularJetData E →ₗ[ℝ]
    MultilinearMap ℝ (fun _ : Fin n => E × ℝ) ℝ
  | 0 =>
      { toFun A := MultilinearMap.constOfIsEmpty ℝ (fun _ : Fin 0 => E × ℝ)
          (A 0 0 Fin.elim0)
        map_add' A B := by ext v; rfl
        map_smul' a A := by ext v; rfl }
  | n + 1 =>
      { toFun A :=
          ((scalarAngularExpansion n).comp (scalarAngularHead A) +
            (LinearMap.snd ℝ E ℝ).smulRight
              (scalarAngularExpansion n (scalarAngularShift A))).uncurryLeft
        map_add' A B := by
          ext v
          simp only [LinearMap.uncurryLeft_apply, LinearMap.add_apply,
            MultilinearMap.add_apply, LinearMap.comp_apply,
            LinearMap.smulRight_apply, scalarAngularHead_add, map_add,
            MultilinearMap.smul_apply, smul_add]
          abel
        map_smul' a A := by
          ext v
          simp only [LinearMap.uncurryLeft_apply, LinearMap.add_apply,
            MultilinearMap.add_apply, LinearMap.comp_apply,
            LinearMap.smulRight_apply, scalarAngularHead_smul, map_smul,
            LinearMap.smul_apply, MultilinearMap.smul_apply,
            smul_add, smul_smul, RingHom.id_apply, smul_eq_mul]
          ring }

theorem scalarAngularExpansion_zero_apply (A : ScalarAngularJetData E)
    (v : Fin 0 → E × ℝ) : scalarAngularExpansion 0 A v = A 0 0 Fin.elim0 := rfl

theorem scalarAngularExpansion_succ_apply (n : ℕ) (A : ScalarAngularJetData E)
    (v : Fin (n + 1) → E × ℝ) :
    scalarAngularExpansion (n + 1) A v =
      scalarAngularExpansion n (scalarAngularHead A (v 0)) (Fin.tail v) +
        (v 0).2 * scalarAngularExpansion n (scalarAngularShift A) (Fin.tail v) := by
  change (LinearMap.uncurryLeft (R := ℝ)
    (M := fun _ : Fin (n + 1) => E × ℝ) (M₂ := ℝ)
    ((scalarAngularExpansion n).comp (scalarAngularHead A) +
      (LinearMap.snd ℝ E ℝ).smulRight
        (scalarAngularExpansion n (scalarAngularShift A)))) v = _
  simp only [LinearMap.uncurryLeft_apply, LinearMap.add_apply, MultilinearMap.add_apply,
    LinearMap.comp_apply, LinearMap.smulRight_apply, MultilinearMap.smul_apply,
    LinearMap.snd_apply, smul_eq_mul]

variable [TopologicalSpace E]

/-- Joint continuity is preserved without any operator norm on the parameter space. -/
theorem continuousOn_scalarAngularExpansion (n : ℕ)
    {P : Type u} [TopologicalSpace P] {U : Set P}
    (A : P → ScalarAngularJetData E)
    (hA : ∀ b k, ContinuousOn (fun z : P × (Fin k → E) => A z.1 b k z.2)
      (U ×ˢ univ)) :
    ContinuousOn (fun z : P × (Fin n → E × ℝ) => scalarAngularExpansion n (A z.1) z.2)
      (U ×ˢ univ) := by
  induction n generalizing P with
  | zero =>
      have h := (hA 0 0).comp
        (continuous_fst.prodMk (continuous_const :
          Continuous (fun _ : P × (Fin 0 → E × ℝ) => (Fin.elim0 : Fin 0 → E)))).continuousOn
        (fun z (hz : z ∈ U ×ˢ (univ : Set (Fin 0 → E × ℝ))) => ⟨hz.1, mem_univ _⟩)
      exact h
  | succ n ih =>
      let AH : P × (E × ℝ) → ScalarAngularJetData E :=
        fun z => scalarAngularHead (A z.1) z.2
      have hAH (b k : ℕ) : ContinuousOn
          (fun z : (P × (E × ℝ)) × (Fin k → E) => AH z.1 b k z.2)
          ((U ×ˢ univ) ×ˢ univ) := by
        have hcons : Continuous (fun z : (P × (E × ℝ)) × (Fin k → E) =>
            Fin.cons (α := fun _ : Fin (k + 1) => E) z.1.2.1 z.2) := by
          apply continuous_pi
          intro i
          exact Fin.cases continuous_fst.snd.fst
            (fun j => (continuous_apply j).comp continuous_snd) i
        exact (hA b (k + 1)).comp (continuous_fst.fst.prodMk hcons).continuousOn
          (fun z hz => ⟨hz.1.1, mem_univ _⟩)
      have htail : Continuous (fun z : P × (Fin (n + 1) → E × ℝ) => Fin.tail z.2) :=
        continuous_pi (fun i => (continuous_apply i.succ).comp continuous_snd)
      have hhead := (ih AH hAH).comp
        ((continuous_fst.prodMk ((continuous_apply 0).comp continuous_snd)).prodMk htail).continuousOn
        (fun z (hz : z ∈ U ×ˢ (univ : Set (Fin (n + 1) → E × ℝ))) =>
          ⟨⟨hz.1, mem_univ _⟩, mem_univ _⟩)
      have hshift := (ih (fun p => scalarAngularShift (A p))
        (fun b k => hA (b + 1) k)).comp
        (continuous_fst.prodMk htail).continuousOn
        (fun z (hz : z ∈ U ×ˢ (univ : Set (Fin (n + 1) → E × ℝ))) => ⟨hz.1, mem_univ _⟩)
      have hcoeff : Continuous (fun z : P × (Fin (n + 1) → E × ℝ) => (z.2 0).2) :=
        ((continuous_apply 0).comp continuous_snd).snd
      apply (hhead.add (hcoeff.continuousOn.mul hshift)).congr
      intro z hz
      exact scalarAngularExpansion_succ_apply n (A z.1) z.2

theorem continuous_scalarAngularExpansion (n : ℕ) (A : ScalarAngularJetData E)
    (hA : ∀ b k, Continuous (A b k)) : Continuous (scalarAngularExpansion n A) := by
  have h := continuousOn_scalarAngularExpansion n
    (U := (univ : Set E)) (fun _ : E => A)
    (fun b k => ((hA b k).comp continuous_snd).continuousOn)
  have hc : Continuous (fun z : E × (Fin n → E × ℝ) => scalarAngularExpansion n A z.2) :=
    continuousOn_univ.mp (by simpa only [univ_prod_univ] using h)
  exact hc.comp ((continuous_const : Continuous (fun _ : Fin n → E × ℝ => (0 : E))).prodMk
    continuous_id)

def scalarAngularContinuousExpansion
    (A : ∀ b k : ℕ, E [×k]→L[ℝ] ℝ) (n : ℕ) :
    (E × ℝ) [×n]→L[ℝ] ℝ :=
  { scalarAngularExpansion n (fun b k => (A b k).toMultilinearMap) with
    cont := continuous_scalarAngularExpansion n _ (fun b k => (A b k).cont) }

theorem scalarAngularContinuousExpansion_apply
    (A : ∀ b k : ℕ, E [×k]→L[ℝ] ℝ) (n : ℕ) (v : Fin n → E × ℝ) :
    scalarAngularContinuousExpansion A n v =
      scalarAngularExpansion n (fun b k => (A b k).toMultilinearMap) v := rfl

/-- Differentiation commutes with this finite multilinear expansion. -/
theorem hasDerivAt_scalarAngularExpansion (n : ℕ)
    (A : ℝ → ScalarAngularJetData E) (B : ScalarAngularJetData E) {t : ℝ}
    (hA : ∀ b k (v : Fin k → E),
      HasDerivAt (fun s => A s b k v) (B b k v) t)
    (v : Fin n → E × ℝ) :
    HasDerivAt (fun s => scalarAngularExpansion n (A s) v)
      (scalarAngularExpansion n B v) t := by
  induction n generalizing A B with
  | zero =>
      simpa only [scalarAngularExpansion_zero_apply] using hA 0 0 Fin.elim0
  | succ n ih =>
      have hhead := ih (fun s => scalarAngularHead (A s) (v 0)) (scalarAngularHead B (v 0))
        (fun b k w => hA b (k + 1) (Fin.cons (v 0).1 w)) (Fin.tail v)
      have hshift := ih (fun s => scalarAngularShift (A s)) (scalarAngularShift B)
        (fun b k w => hA (b + 1) k w) (Fin.tail v)
      simpa only [scalarAngularExpansion_succ_apply] using
        hhead.fun_add (hshift.const_mul (v 0).2)

end ContinuousFlexibility.Analysis
