import Mathlib.Analysis.Normed.Operator.Bilinear
import Mathlib.Topology.Algebra.Module.Equiv

/-!
# The explicit graph change for a source normalizer

Changing a normalizing source column changes the source coordinate by
F ↦ F + lambda(U) d. If (v,d) is in the original graph and lambda(v)=0,
the corresponding change of unknown is U ↦ U + lambda(U) v. Both are
actual bounded linear shears. The graph equivalence retains the source
projection exactly.
-/

noncomputable section

namespace ContinuousFlexibility.Analysis

open Set

variable {X E : Type*} [NormedAddCommGroup X] [NormedSpace ℝ X]
  [NormedAddCommGroup E] [NormedSpace ℝ E]

def n06NormalizerSourceShear (ℓ : X →L[ℝ] ℝ) (d : E) : (X × E) →L[ℝ] X × E :=
  (ContinuousLinearMap.fst ℝ X E).prod
    (ContinuousLinearMap.snd ℝ X E +
      (ℓ.comp (ContinuousLinearMap.fst ℝ X E)).smulRight d)

theorem n06NormalizerSourceShear_apply (ℓ : X →L[ℝ] ℝ) (d : E) (x : X × E) :
    n06NormalizerSourceShear ℓ d x = (x.1, x.2 + ℓ x.1 • d) := by
  simp only [n06NormalizerSourceShear, ContinuousLinearMap.prod_apply,
    ContinuousLinearMap.coe_fst', ContinuousLinearMap.coe_snd', add_apply,
    ContinuousLinearMap.smulRight_apply, ContinuousLinearMap.comp_apply]

def n06NormalizerGraph (G : Submodule ℝ (X × E)) (ℓ : X →L[ℝ] ℝ) (d : E) :
    Submodule ℝ (X × E) :=
  G.comap (n06NormalizerSourceShear ℓ d).toLinearMap

theorem n06NormalizerGraph_mem (G : Submodule ℝ (X × E))
    (ℓ : X →L[ℝ] ℝ) (d : E) (x : X × E) :
    x ∈ n06NormalizerGraph G ℓ d ↔ (x.1, x.2 + ℓ x.1 • d) ∈ G := by
  simp only [n06NormalizerGraph, Submodule.mem_comap,
    ContinuousLinearMap.coe_coe, n06NormalizerSourceShear_apply]

theorem n06NormalizerGraph_closed (G : Submodule ℝ (X × E))
    (ℓ : X →L[ℝ] ℝ) (d : E) (hG : IsClosed (G : Set (X × E))) :
    IsClosed (n06NormalizerGraph G ℓ d : Set (X × E)) := by
  have he : (n06NormalizerGraph G ℓ d : Set (X × E)) =
      (n06NormalizerSourceShear ℓ d) ⁻¹' (G : Set (X × E)) := by
    ext x
    exact Submodule.mem_comap
  rw [he]
  exact hG.preimage (n06NormalizerSourceShear ℓ d).continuous

def n06NormalizerUnknownShear (ℓ : X →L[ℝ] ℝ) (v : X) : X →L[ℝ] X :=
  ContinuousLinearMap.id ℝ X + ℓ.smulRight v

theorem n06NormalizerUnknownShear_apply (ℓ : X →L[ℝ] ℝ) (v x : X) :
    n06NormalizerUnknownShear ℓ v x = x + ℓ x • v := by
  simp only [n06NormalizerUnknownShear, add_apply, ContinuousLinearMap.id_apply,
    ContinuousLinearMap.smulRight_apply]

private theorem n06_normalizer_add_sub (ℓ : X →L[ℝ] ℝ) {v : X}
    (hv : ℓ v = 0) (x : X) :
    x + ℓ x • v - ℓ (x + ℓ x • v) • v = x := by
  rw [map_add, map_smul, hv, smul_eq_mul, mul_zero, add_zero]
  exact add_sub_cancel_right x (ℓ x • v)

private theorem n06_normalizer_sub_add (ℓ : X →L[ℝ] ℝ) {v : X}
    (hv : ℓ v = 0) (x : X) :
    x - ℓ x • v + ℓ (x - ℓ x • v) • v = x := by
  rw [map_sub, map_smul, hv, smul_eq_mul, mul_zero, sub_zero]
  exact sub_add_cancel x (ℓ x • v)

private theorem n06_normalizer_forward_mem (G : Submodule ℝ (X × E))
    (ℓ : X →L[ℝ] ℝ) (d : G) (hd : ℓ d.val.1 = 0) (x : G) :
    ((n06NormalizerUnknownShear ℓ d.val.1).prodMap
      (ContinuousLinearMap.id ℝ E)).comp G.subtypeL x ∈
        n06NormalizerGraph G ℓ d.val.2 := by
  rw [n06NormalizerGraph_mem]
  simp only [ContinuousLinearMap.comp_apply, Submodule.subtypeL_apply,
    ContinuousLinearMap.coe_prodMap', Prod.map_apply', ContinuousLinearMap.id_apply,
    n06NormalizerUnknownShear_apply]
  rw [map_add, map_smul, hd, smul_eq_mul, mul_zero, add_zero]
  exact G.add_mem x.property (G.smul_mem (ℓ x.val.1) d.property)

def n06NormalizerGraphForward (G : Submodule ℝ (X × E))
    (ℓ : X →L[ℝ] ℝ) (d : G) (hd : ℓ d.val.1 = 0) :
    G →L[ℝ] n06NormalizerGraph G ℓ d.val.2 :=
  (((n06NormalizerUnknownShear ℓ d.val.1).prodMap
    (ContinuousLinearMap.id ℝ E)).comp G.subtypeL).codRestrict
      (n06NormalizerGraph G ℓ d.val.2) (n06_normalizer_forward_mem G ℓ d hd)

theorem n06NormalizerGraphForward_apply (G : Submodule ℝ (X × E))
    (ℓ : X →L[ℝ] ℝ) (d : G) (hd : ℓ d.val.1 = 0) (x : G) :
    (n06NormalizerGraphForward G ℓ d hd x).val =
      (x.val.1 + ℓ x.val.1 • d.val.1, x.val.2) := by
  simp only [n06NormalizerGraphForward, ContinuousLinearMap.coe_codRestrict_apply,
    ContinuousLinearMap.comp_apply, Submodule.subtypeL_apply,
    ContinuousLinearMap.coe_prodMap', Prod.map_apply', ContinuousLinearMap.id_apply,
    n06NormalizerUnknownShear_apply]

private theorem n06_normalizer_backward_mem (G : Submodule ℝ (X × E))
    (ℓ : X →L[ℝ] ℝ) (d : G) (x : n06NormalizerGraph G ℓ d.val.2) :
    (((ContinuousLinearMap.id ℝ X - ℓ.smulRight d.val.1).prodMap
      (ContinuousLinearMap.id ℝ E)).comp (n06NormalizerGraph G ℓ d.val.2).subtypeL) x ∈ G := by
  have hx : (x.val.1, x.val.2 + ℓ x.val.1 • d.val.2) ∈ G :=
    (n06NormalizerGraph_mem G ℓ d.val.2 x.val).mp x.property
  have hsub := G.sub_mem hx (G.smul_mem (ℓ x.val.1) d.property)
  have he : (x.val.1, x.val.2 + ℓ x.val.1 • d.val.2) - ℓ x.val.1 • d.val =
      (x.val.1 - ℓ x.val.1 • d.val.1, x.val.2) := by
    apply Prod.ext
    · simp only [Prod.fst_sub, Prod.smul_fst]
    · simp only [Prod.snd_sub, Prod.smul_snd, add_sub_cancel_right]
  rw [he] at hsub
  simpa only [ContinuousLinearMap.comp_apply, Submodule.subtypeL_apply,
    ContinuousLinearMap.coe_prodMap', Prod.map_apply', ContinuousLinearMap.id_apply,
    sub_apply, ContinuousLinearMap.smulRight_apply, Prod.fst_sub, Prod.snd_sub,
    Prod.smul_fst, Prod.smul_snd, add_sub_cancel_right] using hsub

def n06NormalizerGraphBackward (G : Submodule ℝ (X × E))
    (ℓ : X →L[ℝ] ℝ) (d : G) :
    n06NormalizerGraph G ℓ d.val.2 →L[ℝ] G :=
  (((ContinuousLinearMap.id ℝ X - ℓ.smulRight d.val.1).prodMap
    (ContinuousLinearMap.id ℝ E)).comp (n06NormalizerGraph G ℓ d.val.2).subtypeL).codRestrict
      G (n06_normalizer_backward_mem G ℓ d)

theorem n06NormalizerGraphBackward_apply (G : Submodule ℝ (X × E))
    (ℓ : X →L[ℝ] ℝ) (d : G) (x : n06NormalizerGraph G ℓ d.val.2) :
    (n06NormalizerGraphBackward G ℓ d x).val =
      (x.val.1 - ℓ x.val.1 • d.val.1, x.val.2) := by
  simp only [n06NormalizerGraphBackward, ContinuousLinearMap.coe_codRestrict_apply,
    ContinuousLinearMap.comp_apply, Submodule.subtypeL_apply,
    ContinuousLinearMap.coe_prodMap', Prod.map_apply', ContinuousLinearMap.id_apply,
    sub_apply, ContinuousLinearMap.smulRight_apply]

def n06NormalizerGraphEquiv (G : Submodule ℝ (X × E))
    (ℓ : X →L[ℝ] ℝ) (d : G) (hd : ℓ d.val.1 = 0) :
    G ≃L[ℝ] n06NormalizerGraph G ℓ d.val.2 where
  toLinearEquiv :=
    { toLinearMap := (n06NormalizerGraphForward G ℓ d hd).toLinearMap
      invFun := n06NormalizerGraphBackward G ℓ d
      left_inv := by
        intro x
        apply Subtype.ext
        change (n06NormalizerGraphBackward G ℓ d
          (n06NormalizerGraphForward G ℓ d hd x)).val = x.val
        rw [n06NormalizerGraphBackward_apply, n06NormalizerGraphForward_apply]
        exact Prod.ext (n06_normalizer_add_sub ℓ hd x.val.1) rfl
      right_inv := by
        intro x
        apply Subtype.ext
        change (n06NormalizerGraphForward G ℓ d hd
          (n06NormalizerGraphBackward G ℓ d x)).val = x.val
        rw [n06NormalizerGraphForward_apply, n06NormalizerGraphBackward_apply]
        exact Prod.ext (n06_normalizer_sub_add ℓ hd x.val.1) rfl }
  continuous_toFun := (n06NormalizerGraphForward G ℓ d hd).continuous
  continuous_invFun := (n06NormalizerGraphBackward G ℓ d).continuous

theorem n06NormalizerGraphEquiv_apply (G : Submodule ℝ (X × E))
    (ℓ : X →L[ℝ] ℝ) (d : G) (hd : ℓ d.val.1 = 0) (x : G) :
    (n06NormalizerGraphEquiv G ℓ d hd x).val =
      (x.val.1 + ℓ x.val.1 • d.val.1, x.val.2) :=
  n06NormalizerGraphForward_apply G ℓ d hd x

end ContinuousFlexibility.Analysis
