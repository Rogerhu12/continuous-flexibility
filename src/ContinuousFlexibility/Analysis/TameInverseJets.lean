import ContinuousFlexibility.Analysis.TameInverseExpressions

/-!
# The full directional tower of an inverse family

Iterating the expression differential constructs all derivatives.  In the
new direction the differential is a continuous linear map by construction.
Linearity in each old direction follows by differentiating the corresponding
multilinear identity and using uniqueness of the actual quotient limit.
-/

noncomputable section

namespace ContinuousFlexibility.Analysis

open Set Filter
open scoped Topology BigOperators

set_option backward.isDefEq.respectTransparency false

section AuxiliaryMaps

variable (P : Type*) [TopologicalSpace P] [AddCommGroup P] [Module ℝ P]

/-- Forget the newly prepended direction. -/
def inverseAuxTail (n : ℕ) : (Fin (n + 1) → P) →L[ℝ] (Fin n → P) :=
  ContinuousLinearMap.pi fun i => ContinuousLinearMap.proj i.succ

@[simp] theorem inverseAuxTail_apply (n : ℕ) (v : Fin (n + 1) → P) :
    inverseAuxTail P n v = Fin.tail v := rfl

end AuxiliaryMaps

section Jets

variable {X Y Z : Type*}
  [TopologicalSpace X] [AddCommGroup X] [Module ℝ X]
  [IsTopologicalAddGroup X] [ContinuousSMul ℝ X]
  [TopologicalSpace Y] [AddCommGroup Y] [Module ℝ Y]
  [IsTopologicalAddGroup Y] [ContinuousSMul ℝ Y] [T2Space Y]
  [TopologicalSpace Z] [AddCommGroup Z] [Module ℝ Z]
  [IsTopologicalAddGroup Z] [ContinuousSMul ℝ Z] [T2Space Z]
variable {U : Set X} {L : X → Y →L[ℝ] Z}

/-- The finite formula for the derivative of each order. -/
def inverseExpressionJet : (n : ℕ) → TameInverseExpression X Y Z (Fin n → X × Z)
  | 0 => .inverse .source
  | n + 1 => (inverseExpressionJet n).diff (inverseAuxTail (X × Z) n)
      (ContinuousLinearMap.proj 0)

def inverseExpressionJetValue
    (J : Statements.SmoothDirections (U ×ˢ univ) (fun z : X × Y => L z.1 z.2))
    (V : X → Z →L[ℝ] Y) (n : ℕ) (z : X × Z) (v : Fin n → X × Z) : Y × Z :=
  (inverseExpressionJet n).eval J V z v

@[simp] theorem inverseExpressionJetValue_zero
    (J : Statements.SmoothDirections (U ×ˢ univ) (fun z : X × Y => L z.1 z.2))
    (V : X → Z →L[ℝ] Y) (z : X × Z) (v : Fin 0 → X × Z) :
    inverseExpressionJetValue J V 0 z v = (V z.1 z.2, 0) := rfl

theorem inverseExpressionJetValue_succ
    (J : Statements.SmoothDirections (U ×ˢ univ) (fun z : X × Y => L z.1 z.2))
    (V : X → Z →L[ℝ] Y) (n : ℕ) (z : X × Z) (v : Fin (n + 1) → X × Z) :
    inverseExpressionJetValue J V (n + 1) z v =
      (inverseExpressionJet n).differential J V z (Fin.tail v) (v 0) := by
  exact (inverseExpressionJet n).eval_diff J V (inverseAuxTail (X × Z) n)
    (ContinuousLinearMap.proj 0) z v

variable
  (J : Statements.SmoothDirections (U ×ˢ univ) (fun z : X × Y => L z.1 z.2))
  (hU : IsOpen U) (V : X → Z →L[ℝ] Y)
  (hleft : ∀ x ∈ U, ∀ u, V x (L x u) = u)
  (hright : ∀ x ∈ U, ∀ y, L x (V x y) = y)
  (hV : ContinuousOn (fun z : X × Z => V z.1 z.2) (U ×ˢ univ))

/-- The constructed formulas satisfy the genuine derivative recurrence at
every order. -/
theorem hasProjectiveLineDerivAt_inverseExpressionJet
    (n : ℕ) {z : X × Z} (hz : z.1 ∈ U) (v : Fin n → X × Z) (h : X × Z) :
    HasProjectiveLineDerivAt (fun w => inverseExpressionJetValue J V n w v)
      (inverseExpressionJetValue J V (n + 1) z (Fin.cons h v)) z h := by
  have hd := (inverseExpressionJet n).hasLineDerivAt_eval J hU V hleft hright hV hz v h
  simpa only [inverseExpressionJetValue_succ, Fin.tail_cons, Fin.cons_zero,
    inverseExpressionJetValue] using hd

/-- Additivity in every direction follows from actual differentiation,
including directions occurring inside arbitrary nested inverse formulas. -/
theorem inverseExpressionJetValue_update_add :
    ∀ n z, z.1 ∈ U → ∀ (v : Fin n → X × Z) (i : Fin n) (a b : X × Z),
      inverseExpressionJetValue J V n z (Function.update v i (a + b)) =
        inverseExpressionJetValue J V n z (Function.update v i a) +
          inverseExpressionJetValue J V n z (Function.update v i b) := by
  intro n
  induction n with
  | zero => intro z hz v i; exact Fin.elim0 i
  | succ n ih =>
      intro z hz v i a b
      refine Fin.cases ?_ (fun j => ?_) i
      · simp only [inverseExpressionJetValue_succ, Fin.tail_update_zero, Function.update_self]
        exact map_add _ a b
      · let w : Fin n → X × Z := Fin.tail v
        let h : X × Z := v 0
        have hsum :=
          (hasProjectiveLineDerivAt_inverseExpressionJet J hU V hleft hright hV
            n hz (Function.update w j a) h).add
          (hasProjectiveLineDerivAt_inverseExpressionJet J hU V hleft hright hV
            n hz (Function.update w j b) h)
        have hall := hasProjectiveLineDerivAt_inverseExpressionJet J hU V hleft hright hV
          n hz (Function.update w j (a + b)) h
        have hgerm :
            (fun x => inverseExpressionJetValue J V n x (Function.update w j a) +
              inverseExpressionJetValue J V n x (Function.update w j b)) =ᶠ[𝓝 z]
            (fun x => inverseExpressionJetValue J V n x (Function.update w j (a + b))) := by
          filter_upwards [(hU.prod isOpen_univ).mem_nhds ⟨hz, mem_univ z.2⟩] with x hx
          exact (ih x hx.1 w j a b).symm
        have heq := (hall.congr_germ hgerm).unique hsum
        simpa only [w, h, Fin.cons_update, Fin.cons_self_tail] using heq

/-- Homogeneity in every direction is obtained by the same uniqueness
argument, so zero low seminorms cause no exceptional case. -/
theorem inverseExpressionJetValue_update_smul :
    ∀ n z, z.1 ∈ U → ∀ (v : Fin n → X × Z) (i : Fin n) (c : ℝ) (a : X × Z),
      inverseExpressionJetValue J V n z (Function.update v i (c • a)) =
        c • inverseExpressionJetValue J V n z (Function.update v i a) := by
  intro n
  induction n with
  | zero => intro z hz v i; exact Fin.elim0 i
  | succ n ih =>
      intro z hz v i c a
      refine Fin.cases ?_ (fun j => ?_) i
      · simp only [inverseExpressionJetValue_succ, Fin.tail_update_zero, Function.update_self]
        exact map_smul _ c a
      · let w : Fin n → X × Z := Fin.tail v
        let h : X × Z := v 0
        have hsmul :=
          (hasProjectiveLineDerivAt_inverseExpressionJet J hU V hleft hright hV
            n hz (Function.update w j a) h).const_smul c
        have hall := hasProjectiveLineDerivAt_inverseExpressionJet J hU V hleft hright hV
          n hz (Function.update w j (c • a)) h
        have hgerm :
            (fun x => c • inverseExpressionJetValue J V n x (Function.update w j a)) =ᶠ[𝓝 z]
            (fun x => inverseExpressionJetValue J V n x (Function.update w j (c • a))) := by
          filter_upwards [(hU.prod isOpen_univ).mem_nhds ⟨hz, mem_univ z.2⟩] with x hx
          exact (ih x hx.1 w j c a).symm
        have heq := (hall.congr_germ hgerm).unique hsmul
        simpa only [w, h, Fin.cons_update, Fin.cons_self_tail] using heq

/-- The formulas are bundled as continuous multilinear maps at every
point of the open domain. -/
def inverseExpressionJetMultilinear (n : ℕ) (z : X × Z) (hz : z.1 ∈ U) :
    (X × Z) [×n]→L[ℝ] (Y × Z) where
  toMultilinearMap := MultilinearMap.mk' (inverseExpressionJetValue J V n z)
    (inverseExpressionJetValue_update_add J hU V hleft hright hV n z hz)
    (inverseExpressionJetValue_update_smul J hU V hleft hright hV n z hz)
  cont := by
    have hc := (inverseExpressionJet n).continuousOn_eval J V hV
    have hm : Continuous (fun v : Fin n → X × Z => (z, v)) :=
      continuous_const.prodMk continuous_id
    exact continuousOn_univ.mp (hc.comp hm.continuousOn
      (fun v _ => ⟨⟨hz, mem_univ z.2⟩, mem_univ v⟩))

@[simp] theorem inverseExpressionJetMultilinear_apply
    (n : ℕ) (z : X × Z) (hz : z.1 ∈ U) (v : Fin n → X × Z) :
    inverseExpressionJetMultilinear J hU V hleft hright hV n z hz v =
      inverseExpressionJetValue J V n z v := rfl

/-- The global family of multilinear maps is set to zero outside the open
domain; this does not change any germ at a point in the domain. -/
def inverseExpressionJets : ProjectiveJetFamily (X × Z) (Y × Z) := by
  classical
  exact fun n z => if hz : z.1 ∈ U then
    inverseExpressionJetMultilinear J hU V hleft hright hV n z hz else 0

@[simp] theorem inverseExpressionJets_apply
    (n : ℕ) {z : X × Z} (hz : z.1 ∈ U) (v : Fin n → X × Z) :
    inverseExpressionJets J hU V hleft hright hV n z v =
      inverseExpressionJetValue J V n z v := by
  simp only [inverseExpressionJets, dif_pos hz, inverseExpressionJetMultilinear_apply]

/-- All expression jets form one smooth directional tower on the original
open domain, with no restriction to a smaller parameter neighborhood. -/
theorem hasProjectiveJetsOn_inverseFamily :
    HasProjectiveJetsOn (fun z : X × Z => (V z.1 z.2, (0 : Z)))
      (inverseExpressionJets J hU V hleft hright hV) (U ×ˢ univ) := by
  refine ⟨?_, ?_, ?_⟩
  · intro z hz
    rw [inverseExpressionJets_apply J hU V hleft hright hV 0 hz.1,
      inverseExpressionJetValue_zero]
  · intro n
    apply ((inverseExpressionJet n).continuousOn_eval J V hV).congr
    intro p hp
    exact inverseExpressionJets_apply J hU V hleft hright hV n hp.1.1 p.2
  · intro n z hz h v
    have hactual := hasProjectiveLineDerivAt_inverseExpressionJet
      J hU V hleft hright hV n hz.1 v h
    have hgerm :
        (fun x => inverseExpressionJets J hU V hleft hright hV n x v) =ᶠ[𝓝 z]
        (fun x => inverseExpressionJetValue J V n x v) := by
      filter_upwards [(hU.prod isOpen_univ).mem_nhds hz] with x hx
      exact inverseExpressionJets_apply J hU V hleft hright hV n hx.1 v
    simpa only [inverseExpressionJets_apply J hU V hleft hright hV (n + 1) hz.1]
      using hactual.congr_germ hgerm

/-- Projection of the expression tower gives the directional tower of the
inverse itself. -/
def inverseFamilySmoothDirections :
    Statements.SmoothDirections (U ×ˢ univ) (fun z : X × Z => V z.1 z.2) where
  open_domain := hU.prod isOpen_univ
  D := fun n z => (ContinuousLinearMap.fst ℝ Y Z).compContinuousMultilinearMap
    (inverseExpressionJets J hU V hleft hright hV n z)
  zero := by
    intro z hz
    have hzero := (hasProjectiveJetsOn_inverseFamily J hU V hleft hright hV).1 z hz
    exact congrArg Prod.fst hzero
  continuous := fun n =>
    ((hasProjectiveJetsOn_inverseFamily J hU V hleft hright hV).2.1 n).fst
  derivative := fun n z hz v h =>
    ((hasProjectiveJetsOn_inverseFamily J hU V hleft hright hV).2.2 n z hz h v).clm_comp
      (ContinuousLinearMap.fst ℝ Y Z)

@[simp] theorem inverseFamilySmoothDirections_apply
    (n : ℕ) {z : X × Z} (hz : z.1 ∈ U) (v : Fin n → X × Z) :
    (inverseFamilySmoothDirections J hU V hleft hright hV).D n z v =
      (inverseExpressionJetValue J V n z v).1 := by
  change (inverseExpressionJets J hU V hleft hright hV n z v).1 = _
  rw [inverseExpressionJets_apply J hU V hleft hright hV n hz]

end Jets

end ContinuousFlexibility.Analysis
