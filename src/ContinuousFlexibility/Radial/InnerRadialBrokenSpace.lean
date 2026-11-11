import ContinuousFlexibility.Radial.InnerRadialPotentialGraph

/-!
# The actual broken weak graph as a linear domain

The graph stores the physical value/gradient fields, their actual signed
potential products, one scalar, and the source. Its defining conditions
are the actual matched H¹ domain, the local weak equations, and the one
central row. No inverse, gluing conclusion, or Schur decomposition is a
field of this space.
-/

noncomputable section

namespace ContinuousFlexibility.Radial

open Set MeasureTheory Filter ContinuousFlexibility.Statements
open scoped ContDiff InnerProductSpace BigOperators

abbrev InnerRadialBrokenData (D : ReferenceData) (n : ℕ) (H : Type*) :=
  ((Fin (n + 1) → InnerRadialH1Pair D) ×
    ((Fin (n + 1) → RadialModeL2 D) × ℝ)) × H

section BrokenGraph

variable (D : ReferenceData) (hw : Continuous D.w) {n : ℕ}
  (G : InnerRadialChainGeometry D n) {H : Type*}
  [AddCommGroup H] [Module ℝ H]
  (forcing : H →ₗ[ℝ] (Fin (n + 1) → RadialModeL2 D))
  (rowSource : H →ₗ[ℝ] ℝ)

/-- The actual piece-value/gradient family. -/
def innerRadialBrokenQ : InnerRadialBrokenData D n H →ₗ[ℝ]
    (Fin (n + 1) → InnerRadialH1Pair D) where
  toFun x := x.1.1
  map_add' _ _ := rfl
  map_smul' _ _ := rfl

/-- The actual field/potential pair on one piece. -/
def innerRadialBrokenUV (p : Fin (n + 1)) :
    InnerRadialBrokenData D n H →ₗ[ℝ] (RadialModeL2 D × RadialModeL2 D) where
  toFun x := ((x.1.1 p).1, x.1.2.1 p)
  map_add' _ _ := rfl
  map_smul' _ _ := rfl

def innerRadialBrokenScalar : InnerRadialBrokenData D n H →ₗ[ℝ] ℝ where
  toFun x := x.1.2.2
  map_add' _ _ := rfl
  map_smul' _ _ := rfl

@[simp] theorem innerRadialBrokenScalar_apply (x : InnerRadialBrokenData D n H) :
    innerRadialBrokenScalar D x = x.1.2.2 := rfl

def innerRadialBrokenSource : InnerRadialBrokenData D n H →ₗ[ℝ] H :=
  LinearMap.snd ℝ _ _

@[simp] theorem innerRadialBrokenSource_apply (x : InnerRadialBrokenData D n H) :
    innerRadialBrokenSource D x = x.2 :=
  LinearMap.snd_apply x

def innerRadialBrokenRow (central : Fin (n + 1)) (column : RadialModeL2 D) :
    InnerRadialBrokenData D n H →ₗ[ℝ] ℝ where
  toFun x := ⟪column, (x.1.1 central).1⟫_ℝ - rowSource x.2
  map_add' x y := by
    simp only [Prod.fst_add, Prod.snd_add, Pi.add_apply, inner_add_right, map_add]
    ring
  map_smul' c x := by
    simp only [Prod.smul_fst, Prod.smul_snd, Pi.smul_apply,
      real_inner_smul_right, map_smul, RingHom.id_apply, smul_eq_mul]
    ring

@[simp] theorem innerRadialBrokenRow_apply (central : Fin (n + 1))
    (column : RadialModeL2 D) (x : InnerRadialBrokenData D n H) :
    innerRadialBrokenRow D rowSource central column x =
      ⟪column, (x.1.1 central).1⟫_ℝ - rowSource x.2 := rfl

/-- There is one row in the bordered mode; otherwise both scalar
coordinates are forced to zero. -/
def innerRadialBrokenBorder (bordered : Bool) (central : Fin (n + 1))
    (column : RadialModeL2 D) : Submodule ℝ (InnerRadialBrokenData D n H) :=
  if bordered then
    (innerRadialBrokenRow D rowSource central column).ker
  else
    (innerRadialBrokenScalar D).ker ⊓
      (rowSource.comp (innerRadialBrokenSource D)).ker

theorem mem_innerRadialBrokenBorder (bordered : Bool) (central : Fin (n + 1))
    (column : RadialModeL2 D) (x : InnerRadialBrokenData D n H) :
    x ∈ innerRadialBrokenBorder D rowSource bordered central column ↔
      if bordered then ⟪column, (x.1.1 central).1⟫_ℝ = rowSource x.2
      else x.1.2.2 = 0 ∧ rowSource x.2 = 0 := by
  cases bordered <;>
    simp only [innerRadialBrokenBorder, Bool.false_eq_true, eq_self_iff_true,
      ite_false, ite_true, Submodule.mem_inf, LinearMap.mem_ker,
      innerRadialBrokenRow_apply, innerRadialBrokenScalar_apply,
      innerRadialBrokenSource_apply, LinearMap.comp_apply, sub_eq_zero]

/-- Linearity of the actual local energy-minus-forcing functional in
the whole broken graph datum. -/
def innerRadialBrokenResidual (central : Fin (n + 1)) (column : RadialModeL2 D)
    (p : Fin (n + 1)) :
    InnerRadialBrokenData D n H →ₗ[ℝ] (InnerRadialH1Pair D →ₗ[ℝ] ℝ) where
  toFun x := innerRadialChainResidual D central column x.1.1 x.1.2.1
    (forcing x.2) x.1.2.2 p
  map_add' x y := by
    apply LinearMap.ext
    intro r
    simp only [innerRadialChainResidual, innerRadialWeakResidual_apply,
      Prod.fst_add, Prod.snd_add, Pi.add_apply, map_add,
      LinearMap.add_apply, inner_add_left]
    ring
  map_smul' c x := by
    apply LinearMap.ext
    intro r
    simp only [innerRadialChainResidual, innerRadialWeakResidual_apply,
      Prod.smul_fst, Prod.smul_snd, Pi.smul_apply, map_smul,
      LinearMap.smul_apply, real_inner_smul_left, RingHom.id_apply, smul_eq_mul]
    ring

def innerRadialBrokenResidualEval (central : Fin (n + 1)) (column : RadialModeL2 D)
    (p : Fin (n + 1)) (r : InnerRadialH1Pair D) :
    InnerRadialBrokenData D n H →ₗ[ℝ] ℝ where
  toFun x := innerRadialBrokenResidual D forcing central column p x r
  map_add' x y := by rw [map_add, LinearMap.add_apply]
  map_smul' c x := by simp only [map_smul, LinearMap.smul_apply, RingHom.id_apply]

/-- The actual local weak graph before total interface cancellation. -/
def innerRadialBrokenSpace (bordered : Bool) (j : ℝ)
    (central : Fin (n + 1)) (column : RadialModeL2 D) :
    Submodule ℝ (InnerRadialBrokenData D n H) where
  carrier := {x |
    innerRadialBrokenQ D x ∈ innerRadialChainDomain D hw G ∧
    (∀ p, innerRadialBrokenUV D p x ∈
      innerRadialPotentialGraph D j (G.left p) (G.right p)) ∧
    x ∈ innerRadialBrokenBorder D rowSource bordered central column ∧
    ∀ p, ∀ r ∈ innerRadialH1Zero D (G.left p) (G.right p),
      innerRadialBrokenResidualEval D forcing central column p r x = 0}
  zero_mem' := by
    refine ⟨?_, ?_, ?_, ?_⟩
    · rw [map_zero]
      exact (innerRadialChainDomain D hw G).zero_mem
    · intro p
      rw [map_zero]
      exact (innerRadialPotentialGraph D j (G.left p) (G.right p)).zero_mem
    · exact (innerRadialBrokenBorder D rowSource bordered central column).zero_mem
    · intro p r _
      exact map_zero _
  add_mem' := by
    rintro x y ⟨hxq, hxv, hxb, hxr⟩ ⟨hyq, hyv, hyb, hyr⟩
    refine ⟨?_, ?_, ?_, ?_⟩
    · rw [map_add]
      exact (innerRadialChainDomain D hw G).add_mem hxq hyq
    · intro p
      rw [map_add]
      exact (innerRadialPotentialGraph D j (G.left p) (G.right p)).add_mem (hxv p) (hyv p)
    · exact (innerRadialBrokenBorder D rowSource bordered central column).add_mem hxb hyb
    · intro p r hr
      rw [map_add, hxr p r hr, hyr p r hr, zero_add]
  smul_mem' := by
    rintro c x ⟨hxq, hxv, hxb, hxr⟩
    refine ⟨?_, ?_, ?_, ?_⟩
    · rw [map_smul]
      exact (innerRadialChainDomain D hw G).smul_mem c hxq
    · intro p
      rw [map_smul]
      exact (innerRadialPotentialGraph D j (G.left p) (G.right p)).smul_mem c (hxv p)
    · exact (innerRadialBrokenBorder D rowSource bordered central column).smul_mem c hxb
    · intro p r hr
      rw [map_smul, hxr p r hr, smul_zero]

theorem mem_innerRadialBrokenSpace (bordered : Bool) (j : ℝ)
    (central : Fin (n + 1)) (column : RadialModeL2 D) (x : InnerRadialBrokenData D n H) :
    x ∈ innerRadialBrokenSpace D hw G forcing rowSource bordered j central column ↔
      x.1.1 ∈ innerRadialChainDomain D hw G ∧
      (∀ p, InnerRadialPotentialClass D j (G.left p) (G.right p) (x.1.1 p).1 (x.1.2.1 p)) ∧
      (if bordered then ⟪column, (x.1.1 central).1⟫_ℝ = rowSource x.2
        else x.1.2.2 = 0 ∧ rowSource x.2 = 0) ∧
      ∀ p, ∀ r ∈ innerRadialH1Zero D (G.left p) (G.right p),
        innerRadialChainResidual D central column x.1.1 x.1.2.1 (forcing x.2) x.1.2.2 p r = 0 := by
  change (_ ∧ _ ∧
    x ∈ innerRadialBrokenBorder D rowSource bordered central column ∧ _) ↔ _
  rw [mem_innerRadialBrokenBorder]
  rfl

/-- The total actual boundary functional, linear in the full graph datum. -/
def innerRadialBrokenFlux (central : Fin (n + 1)) (column : RadialModeL2 D) :
    InnerRadialBrokenData D n H →ₗ[ℝ] (EuclideanSpace ℝ (Fin n) →ₗ[ℝ] ℝ) where
  toFun x := ∑ p, (innerRadialBrokenResidual D forcing central column p x).comp
    (innerRadialChainLift D hw G p)
  map_add' x y := by
    apply LinearMap.ext
    intro ξ
    simp only [LinearMap.sum_apply, LinearMap.comp_apply, map_add, LinearMap.add_apply,
      Finset.sum_add_distrib]
  map_smul' c x := by
    apply LinearMap.ext
    intro ξ
    simp only [LinearMap.sum_apply, LinearMap.comp_apply, map_smul, LinearMap.smul_apply,
      RingHom.id_apply, smul_eq_mul, Finset.mul_sum]

theorem innerRadialBrokenFlux_eq (central : Fin (n + 1)) (column : RadialModeL2 D)
    (x : InnerRadialBrokenData D n H) :
    innerRadialBrokenFlux D hw G forcing central column x =
      innerRadialChainFlux D hw G central column x.1.1 x.1.2.1 (forcing x.2) x.1.2.2 := rfl

/-- The actual global weak graph is the zero-flux part of the concrete
broken graph. The reverse direction follows from the proved weak
gluing equivalence. -/
theorem innerRadialBrokenSpace_global_iff (bordered : Bool) (j : ℝ)
    (central : Fin (n + 1)) (column : RadialModeL2 D) (x : InnerRadialBrokenData D n H) :
    InnerRadialChainWeakGraph D hw G bordered j central column
      x.1.1 x.1.2.1 (forcing x.2) x.1.2.2 (rowSource x.2) ↔
      x ∈ innerRadialBrokenSpace D hw G forcing rowSource bordered j central column ∧
        innerRadialBrokenFlux D hw G forcing central column x = 0 := by
  rw [innerRadialChainWeakGraph_iff, mem_innerRadialBrokenSpace, innerRadialBrokenFlux_eq]
  tauto

end BrokenGraph

end ContinuousFlexibility.Radial
