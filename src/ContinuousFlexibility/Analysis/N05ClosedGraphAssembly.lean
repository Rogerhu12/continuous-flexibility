import ContinuousFlexibility.Statements.Nonlinear
import Mathlib.Topology.Algebra.Module.ContinuousLinearMap.PiProd
import Mathlib.Topology.Algebra.Module.ContinuousLinearMap.Restrict

/-!
# Closed graph assembly for the actual canonical reference relation

A separately proved characterization of a physical relation by a bounded
inverse turns that literal relation into a closed submodule.  The relation
is the carrier of the submodule; no physical equation is replaced by an
inverse-image definition.
-/

noncomputable section

namespace ContinuousFlexibility.Statements

open Set
open scoped Topology

section Relation

variable {E F : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [NormedAddCommGroup F] [NormedSpace ℝ F]
  (R : F → E → Prop) (G : E →L[ℝ] F)
  (hR : ∀ u f, R u f ↔ u = G f)

/-- The carrier is the original relation, with linearity supplied by its
identification with the independently constructed continuous inverse. -/
def n05RelationGraph : Submodule ℝ (F × E) where
  carrier := {z | R z.1 z.2}
  zero_mem' := (hR 0 0).mpr G.map_zero.symm
  add_mem' := by
    intro a b ha hb
    apply (hR _ _).mpr
    change a.1 + b.1 = G (a.2 + b.2)
    rw [(hR _ _).mp ha, (hR _ _).mp hb, map_add]
  smul_mem' := by
    intro c a ha
    apply (hR _ _).mpr
    change c • a.1 = G (c • a.2)
    rw [(hR _ _).mp ha, map_smul]

@[simp] theorem n05RelationGraph_mem (z : F × E) :
    z ∈ n05RelationGraph R G hR ↔ R z.1 z.2 := Iff.rfl

theorem n05RelationGraph_isClosed :
    IsClosed (n05RelationGraph R G hR : Set (F × E)) := by
  have he : (n05RelationGraph R G hR : Set (F × E)) =
      {z : F × E | z.1 = G z.2} := by
    apply Set.ext
    intro z
    exact hR z.1 z.2
  rw [he]
  exact isClosed_eq continuous_fst (G.continuous.comp continuous_snd)

def n05RelationInverse : E →L[ℝ] n05RelationGraph R G hR :=
  (G.prod (ContinuousLinearMap.id ℝ E)).codRestrict (n05RelationGraph R G hR)
    (fun f => (hR (G f) f).mpr rfl)

@[simp] theorem n05RelationInverse_val (f : E) :
    (n05RelationInverse R G hR f).val = (G f, f) := by
  simp only [n05RelationInverse, ContinuousLinearMap.coe_codRestrict_apply,
    ContinuousLinearMap.prod_apply, ContinuousLinearMap.id_apply]

theorem n05RelationInverse_right (f : E) :
    (n05RelationInverse R G hR f).val.2 = f := by
  rw [n05RelationInverse_val]

theorem n05RelationInverse_left (u : n05RelationGraph R G hR) :
    n05RelationInverse R G hR u.val.2 = u := by
  apply Subtype.ext
  rw [n05RelationInverse_val]
  apply Prod.ext
  · exact ((hR _ _).mp u.prop).symm
  · rfl

theorem n05RelationGraph_norm_bound :
    ∃ C0 : ℝ, 0 < C0 ∧ ∀ u : n05RelationGraph R G hR,
      ‖u‖ ≤ C0 * ‖u.val.2‖ := by
  refine ⟨max ‖G‖ 1, lt_of_lt_of_le zero_lt_one (le_max_right _ _), ?_⟩
  intro u
  have hu : u.val.1 = G u.val.2 := (hR _ _).mp u.prop
  have hout : ‖u.val.1‖ ≤ max ‖G‖ 1 * ‖u.val.2‖ := by
    rw [hu]
    exact (G.le_opNorm _).trans
      (mul_le_mul_of_nonneg_right (le_max_left _ _) (norm_nonneg _))
  have hin : ‖u.val.2‖ ≤ max ‖G‖ 1 * ‖u.val.2‖ := by
    calc
      ‖u.val.2‖ = 1 * ‖u.val.2‖ := (one_mul _).symm
      _ ≤ max ‖G‖ 1 * ‖u.val.2‖ :=
        mul_le_mul_of_nonneg_right (le_max_right _ _) (norm_nonneg _)
  change ‖u.val‖ ≤ _
  rw [Prod.norm_def]
  exact max_le hout hin

theorem n05RelationGraph_completeSpace [CompleteSpace E] [CompleteSpace F] :
    CompleteSpace (n05RelationGraph R G hR) :=
  (n05RelationGraph_isClosed R G hR).isComplete.completeSpace_coe

end Relation

section Canonical

variable (D : ReferenceData) (T : MaterialData) (S : PhysicalSpacesData)
  (C : NonlinearGeometryData S) (K : CanonicalData S) (V : VolumeModelData S K)
  (b : ℕ) (γ M0 M1 loss : ℝ)
  (G : V.level (3 / 4 : ℝ) 0 b →L[ℝ] CanonicalUnknown S K)
  (globalInverse : CanonicalSequence S K → CanonicalUnknown S K)
  (hR : ∀ u F, ReferenceCanonicalRelation D T S C K V γ M0 M1 loss u
      (V.forget (3 / 4 : ℝ) 0 b F) ↔ u = G F)

/-- Assemble the frozen domain data after the actual physical relation has
been characterized. All coefficient and endpoint orders stay explicit. -/
def n05CanonicalDomainOfRelation : CanonicalDomainData S K V b where
  weakExponent := γ
  sourceMaterial := M0
  outputMaterial := M1
  lossMaterial := loss
  graph := n05RelationGraph
    (fun u F => ReferenceCanonicalRelation D T S C K V γ M0 M1 loss u
      (V.forget (3 / 4 : ℝ) 0 b F)) G hR
  inverse := n05RelationInverse _ G hR
  globalInverse := globalInverse

theorem n05CanonicalDomainOfRelation_graph :
    ∀ z, z ∈ (n05CanonicalDomainOfRelation D T S C K V b γ M0 M1 loss
      G globalInverse hR).graph ↔
      ReferenceCanonicalRelation D T S C K V γ M0 M1 loss z.1
        (V.forget (3 / 4 : ℝ) 0 b z.2) :=
  fun _ => Iff.rfl

theorem n05CanonicalDomainOfRelation_closed :
    IsClosed ((n05CanonicalDomainOfRelation D T S C K V b γ M0 M1 loss
      G globalInverse hR).graph :
        Set (CanonicalUnknown S K × V.level (3 / 4 : ℝ) 0 b)) :=
  n05RelationGraph_isClosed _ G hR

theorem n05CanonicalDomainOfRelation_global
    (hglobal : ∀ F, G F = globalInverse (V.forget (3 / 4 : ℝ) 0 b F)) :
    ∀ F, ((n05CanonicalDomainOfRelation D T S C K V b γ M0 M1 loss
      G globalInverse hR).inverse F).val.1 =
      globalInverse (V.forget (3 / 4 : ℝ) 0 b F) := by
  intro F
  exact (congrArg Prod.fst (n05RelationInverse_val _ G hR F)).trans (hglobal F)

end Canonical

end ContinuousFlexibility.Statements
