"""Generate blueprint v3 (one-off, kept for the record).

v3 regroups the v2 nodes by the actual structure of the statements: small
nodes are merged into one line, large nodes are split along the top-level
structure of their statements, and the last link asks only for a solution at
one nonzero parameter instead of a smooth branch.

Node files that already exist are not overwritten.
"""
import pathlib

ROOT = pathlib.Path(__file__).resolve().parent.parent
ST = ROOT / "src/ContinuousFlexibility/Statements"
BP = ROOT / "src/ContinuousFlexibility/Blueprint"
TASKS = ROOT / "docs/tasks"
P = "paper/flexible-surface-rewrite/"


def lines_of(name: str) -> list[str]:
    return (ST / name).read_text(encoding="utf-8").split("\n")


def block(src: list[str], first: str, last_contains: str) -> list[str]:
    i = next(k for k, l in enumerate(src) if l.startswith(first))
    j = next(k for k in range(i, len(src)) if last_contains in src[k])
    return src[i : j + 1]


radial = lines_of("Radial.lean")
targets = lines_of("RadialTargets.lean")

# ---- R06: split the statement along its three top-level clauses -------------
r06 = block(radial, "def R06Statement", "DeepTailParameterContinuity η₀ K₀")
assert r06[1].strip() == "∃ C η₀ K₀ : ℝ, 0 < C ∧ 0 < η₀ ∧ η₀ < 1 ∧ 1 < K₀ ∧"
k_full_end = next(k for k, l in enumerate(r06) if "TailNaturalLineAndKernel T ∧ TailGreenKernel T G) ∧" in l)
full = r06[2 : k_full_end + 1]
full[-1] = full[-1].replace("TailGreenKernel T G) ∧", "TailGreenKernel T G)")
oper = r06[2:k_full_end]
assert oper[-1].rstrip().endswith("(𝓝 (G f)))) ∧"), oper[-1]
oper[-1] = oper[-1].rstrip()[: -len(" ∧")] + ")"
phys = r06[k_full_end + 1 : -1]
assert phys[-1].rstrip().endswith("TailPhysicalSourceIdentity D T right j) ∧"), phys[-1]
phys[-1] = phys[-1].rstrip()[: -len(" ∧")]

# ---- R11: the statement without its last conjunct ---------------------------
r11 = block(targets, "def R11Statement", "FirstNormalInverseEstimate D γ M₀ M₁ G")
assert r11[-2].rstrip().endswith("ReferenceInverseProperties D γ M₀ M₁ G ∧"), r11[-2]
r11a = r11[1:-1]
r11a[-1] = r11a[-1].rstrip()[: -len(" ∧")]

statements = f'''import ContinuousFlexibility.Statements.Milestones

/-!
# Statements of blueprint v3

Intermediate statements that the earlier statement layer does not contain. They split
large nodes along the top-level structure of their statements, and state the last link
of the chain for one nonzero parameter. All definitions are built from the existing
data and property definitions of `ContinuousFlexibility.Statements`.
-/

noncomputable section

namespace ContinuousFlexibility.Blueprint

open Set Filter MeasureTheory Real
open scoped Topology ContDiff
open ContinuousFlexibility.Statements

/-! ## R05: realization, then mass and resistance -/

/-- The chain of cells and joins is realized for every admissible height sequence. -/
def R05aStatement : Prop :=
  ∀ initial : ℕ, ∃ T : MorseChainData, initial ≤ T.index ∧
    ∃ C : ℕ → ℝ, ∃ family : (ℕ → ℝ) → ReferenceData,
      (∀ σ, (∀ n, 1 ≤ σ n ∧ σ n ≤ 2) → MorseChainRealization T σ (family σ) C) ∧
      (∀ σ τ, (family σ).a = (family τ).a ∧ (family σ).b = (family τ).b ∧
        (family σ).cells = (family τ).cells)

/-- Every realized chain has the mass and resistance bounds, after enlarging the constants. -/
def R05bStatement : Prop :=
  ∀ (T : MorseChainData) (C : ℕ → ℝ) (family : (ℕ → ℝ) → ReferenceData),
    (∀ σ, (∀ n, 1 ≤ σ n ∧ σ n ≤ 2) → MorseChainRealization T σ (family σ) C) →
    ∃ C' : ℕ → ℝ, ∀ σ, (∀ n, 1 ≤ σ n ∧ σ n ≤ 2) →
      MorseChainRealization T σ (family σ) C' ∧ MorseMassResistanceBounds T σ (family σ) C'

/-! ## R06: inverse, then natural line and Green kernel, then the physical clauses -/

/-- Form identification and the inverse with its truncations, for given constants. -/
def R06Operator (C η₀ K₀ : ℝ) : Prop :=
{chr(10).join(oper)}

/-- The first clause of `R06Statement`, for given constants. -/
def R06Full (C η₀ K₀ : ℝ) : Prop :=
{chr(10).join(full)}

/-- The second clause of `R06Statement`, for given constants. -/
def R06Physical (η₀ K₀ : ℝ) : Prop :=
{chr(10).join(phys)}

def R06aStatement : Prop :=
  ∃ C η₀ K₀ : ℝ, 0 < C ∧ 0 < η₀ ∧ η₀ < 1 ∧ 1 < K₀ ∧ R06Operator C η₀ K₀

def R06bStatement : Prop :=
  ∀ C η₀ K₀ : ℝ, 0 < C → 0 < η₀ → η₀ < 1 → 1 < K₀ → R06Operator C η₀ K₀ →
    ∃ C' η₀' K₀' : ℝ, 0 < C' ∧ 0 < η₀' ∧ η₀' < 1 ∧ 1 < K₀' ∧ R06Full C' η₀' K₀'

def R06cStatement : Prop :=
  ∀ C η₀ K₀ : ℝ, 0 < C → 0 < η₀ → η₀ < 1 → 1 < K₀ → R06Full C η₀ K₀ →
    ∃ C' η₀' K₀' : ℝ, 0 < C' ∧ 0 < η₀' ∧ η₀' < 1 ∧ 1 < K₀' ∧ R06Full C' η₀' K₀' ∧
      R06Physical η₀' K₀' ∧ DeepTailParameterContinuity η₀' K₀'

/-! ## R10: the inner and outer pieces, then the matching -/

/-- Everything in `ActualMatchedRepresentation` that precedes the inversion of the
matching matrix: cuts, the selected margin, the inner and outer realizations. -/
def MatchedPieces (D : ReferenceData) (M : RadialMatchingData D) : Prop :=
  D.a < M.innerLeft ∧ M.innerLeft < M.innerRight ∧ M.innerRight < D.b ∧
    Function.support (referenceColumn D) ⊆ Ioo M.innerLeft M.innerRight ∧
    0 < M.margin ∧
    (∀ i, 0 < M.boundaryScale i ∧ 0 < M.D0 i ∧ M.D0 i ≤ 1 / 2 ∧
      M.margin ≤ |M.A i i * M.D0 i - M.B i i|) ∧
    (∀ i j, |M.Db i j - (if i = j then M.D0 i else 0)| ≤ M.margin / 16) ∧
    MatchingLocalRealizations D M ∧
    (∀ i j, M.Db i j = M.Db j i) ∧
    (∀ i j, i ≠ j → M.A i j = 0 ∧ M.B i j = 0) ∧
    (∀ i, M.A i i ^ 2 + M.B i i ^ 2 = 1)

def R10aStatement : Prop :=
  ∃ D : ReferenceData, IsAccumulatingProfile D ∧ RadialTrueBorder D ∧
    ∀ j : ℕ, 2 ≤ j → Even j →
      ∃ M : RadialMatchingData D, M.frequency = j ∧ MatchedPieces D M

def R10bStatement : Prop :=
  ∀ D : ReferenceData, IsAccumulatingProfile D → RadialTrueBorder D →
    ∀ j : ℕ, 2 ≤ j → Even j → ∀ M : RadialMatchingData D, M.frequency = j →
      MatchedPieces D M →
      ∃ G : RadialModePair D →L[ℝ] RadialModePair D,
        ModeInverseProperties D j G ∧
        ∃ M' : RadialMatchingData D, M'.frequency = j ∧ ActualMatchedRepresentation D G M'

/-! ## R11: the weighted inverse estimates, then the first normal estimate -/

/-- `R11Statement` without the first normal estimate. -/
def R11aStatement : Prop :=
{chr(10).join(r11a)}

/-! ## N04: canonical coordinates apart from the three standalone targets -/

/-- `N04Statement` without `RootCompositionTarget`, `CubicDivisionTarget` and
`PhysicalTransmissionTarget`, which are independent of all project data. -/
def N04cStatement : Prop :=
  ∃ A : RadialReference, ∃ T : MaterialData, ∃ S : PhysicalSpacesData,
    ∃ C : NonlinearGeometryData S, ∃ R : ReturnEquationData S,
      ∃ L : ReturnCorrectionData S, ∃ K : CanonicalData S,
        ∃ base loss : ℕ, ∃ ε : ℝ,
          IsMaterialData A.val T ∧ IsPhysicalSpaces A.val T S ∧
            NonlinearPropertiesThrough03 A.val T S C R L base loss ε ∧
              N04Properties A.val T S C L K base loss ε

/-! ## N07: the scalar inverse, then its identification with the Banach solution -/

/-- `N07Statement` without `ScalarBanachBridgeProperties`. -/
def N07aStatement : Prop :=
  ∃ A : RadialReference, ∃ T : MaterialData, ∃ S : PhysicalSpacesData,
    ∃ C : NonlinearGeometryData S, ∃ R : ReturnEquationData S,
      ∃ L : ReturnCorrectionData S, ∃ K : CanonicalData S,
        ∃ Vol : VolumeModelData S K, ∃ b : ℕ,
          ∃ Domain : CanonicalDomainData S K Vol b,
            ∃ Relative : RelativeInverseData S K Vol b Domain,
              ∃ G : ScalarInverseData S, ∃ base loss : ℕ, ∃ ε : ℝ,
                IsMaterialData A.val T ∧ IsPhysicalSpaces A.val T S ∧
                  NonlinearPropertiesThrough06 A.val T S C R L K Vol b Domain Relative
                    base loss ε ∧
                  ScalarInverseProperties A.val S C L G base ε

/-! ## The nonlinear solution at one nonzero parameter -/

/-- One solution of the scalar and both return equations at one nonzero parameter, on the
same reference, spaces and geometry. This is the pointwise part of `IsWeakBranch`; the
main theorem fixes one nonzero parameter and does not use smoothness of the branch in it. -/
def PointBranchStatement : Prop :=
  ∃ A : RadialReference, ∃ T : MaterialData, ∃ S : PhysicalSpacesData,
    IsMaterialData A.val T ∧ IsPhysicalSpaces A.val T S ∧
    ∃ C : NonlinearGeometryData S, ∃ R : ReturnEquationData S, ∃ base loss : ℕ, ∃ ε : ℝ,
      N01Properties A.val T S C base loss ε ∧
      ∃ x : AnnularState S, ∃ q : ℝ, q ≠ 0 ∧
        (x, q) ∈ stateNeighborhood S C base ε ∧
        stateSector S x ∧
        referenceRow A.val (stateU S x) = 1 ∧
        (∀ p ∈ annularOpen A.val, scalarResidualField A.val S C (x, q) p = 0) ∧
        R.residual (x, q) = 0 ∧
        ∀ m θ,
          rightChartCandidate S C (x, q) m (C.minusFlow (x, q) m (C.right m) θ) =
            stateLeftChart S x m θ - C.travel m ∧
          rightChartCandidate S C (x, q) m (-C.minusFlow (x, q) m (C.right m) (-θ)) =
            stateLeftChart S x m θ + C.travel m

end ContinuousFlexibility.Blueprint
'''

# (name, hypotheses, conclusion, sources, one-line description)
NODES = [
    ("ScalarCalculus", "", "S03CalculusStatement ∧ S04CalculusStatement ∧ S05CalculusStatement",
     [("03-height-equation.tex", 11, 106), ("03-height-equation.tex", 287, 376)],
     "The pointwise and finite-rectangle calculus of the height equation: connection, residual, conservation, type correction."),
    ("ScalarWeighted", "", "S03WeightedStatement ∧ S04WeightedStatement ∧ S05WeightedStatement",
     [("03-height-equation.tex", 287, 376), ("07-fixed-geometry.tex", 72, 157)],
     "The same three statements on the weighted function spaces, up to the flat endpoints."),
    ("Tame", "", "H01Statement ∧ H02Statement",
     [("07-fixed-geometry.tex", 102, 150), ("08-stable-inverse.tex", 523, 550)],
     "Tame calculus on projective limits of Banach scales and Hamilton's theorem on families of inverses."),
    ("Spaces", " (hW01 : W01Statement) (hTame : H01Statement ∧ H02Statement)", "W02Statement ∧ W03Statement",
     [("07-fixed-geometry.tex", 72, 157)],
     "The weighted height, source and circle spaces with their tame structure, and smooth flat extension of their elements."),
    ("R05a", " (hR04 : R04Statement)", "R05aStatement",
     [("05-flat-end-chain.tex", 20, 182)],
     "The accumulating chain of Morse cells and joins for every admissible height sequence, with flatness and coefficient bounds."),
    ("R05b", "", "R05bStatement",
     [("05-flat-end-chain.tex", 184, 269)],
     "Mass and resistance of every cell and join of a realized chain."),
    ("R06a", "", "R06aStatement",
     [("05-flat-end-chain.tex", 271, 417)],
     "Deep tail: identification of the Friedrichs form, the inverse with norm C/Λ, and convergence of the Dirichlet truncations."),
    ("R06b", "", "R06bStatement",
     [("05-flat-end-chain.tex", 418, 505)],
     "Deep tail: the unique square-integrable line, its decay, and the localized Green kernel."),
    ("R06c", "", "R06cStatement",
     [("05-flat-end-chain.tex", 443, 505)],
     "Deep tail: flatness in the original radius, the source identity, and continuity in the height ratios."),
    ("R07", " (hR04 : R04Statement) (hR05 : R05Statement) (hR06 : R06Statement)", "R07Statement",
     [("05-flat-end-chain.tex", 507, 667)],
     "One transition cell per frequency and one height sequence with all matching angles bounded below."),
    ("R08", " (hR03 : R03Statement) (hR07 : R07Statement)", "R08Statement",
     [("06-global-reference-inverse.tex", 50, 98)],
     "Joining the central model to the selected tails while keeping the second-mode solution."),
    ("R09", "", "R09Statement",
     [("06-global-reference-inverse.tex", 100, 229)],
     "Cutting a model inverse inside a positive buffer."),
    ("R10a", " (hR06 : R06Statement) (hR07 : R07Statement) (hR08 : R08Statement) (hR09 : R09Statement)", "R10aStatement",
     [("06-global-reference-inverse.tex", 231, 522)],
     "At every even frequency: the inner inverse, the outer inverse, their Poisson functions and the selected margin on one geometry."),
    ("R10b", "", "R10bStatement",
     [("06-global-reference-inverse.tex", 522, 598)],
     "Inversion of the matching matrix and the exact matched inverse."),
    ("R11a", " (hR05 : R05Statement) (hR10 : R10Statement)", "R11aStatement",
     [("06-global-reference-inverse.tex", 599, 742)],
     "The weighted bound of the matched inverse at the three exponents on the same geometry."),
    ("R11b", " (hR11a : R11aStatement)", "R11Statement",
     [("06-global-reference-inverse.tex", 744, 764)],
     "The first normal estimate for the same inverse."),
    ("R12", " (hR06 : R06Statement) (hR08 : R08Statement) (hR10 : R10Statement) (hR11 : R11Statement)", "R12Statement",
     [("04-designing-the-profile.tex", 74, 106), ("06-global-reference-inverse.tex", 766, 883)],
     "The fixed radial reference: graph domain, zero mode, final border, two-sided inverse."),
    ("N01", " (hR12 : R12Statement) (hW01 : W01Statement) (hW02 : W02Statement) (hS05 : S05Statement)", "N01Statement",
     [("07-fixed-geometry.tex", 159, 339)],
     "Root scales, quantitative optical controls and the uniform physical geometry on one neighbourhood."),
    ("N02N03", " (hN01 : N01Statement) (hS05 : S05Statement)", "N03Statement",
     [("07-fixed-geometry.tex", 341, 460)],
     "The return residual with its small-divisor inverse, and the correction that fixes the characteristic returns."),
    ("N04Root", "", "RootCompositionTarget",
     [("07-fixed-geometry.tex", 496, 549)],
     "Even and odd parts of a smooth function under the substitution λ = x^(3/2), with fixed loss."),
    ("N04Cubic", "", "CubicDivisionTarget",
     [("07-fixed-geometry.tex", 676, 690)],
     "Division by y³ of a function vanishing to third order, in L² with three derivatives lost."),
    ("N04Transmission", "", "PhysicalTransmissionTarget",
     [("07-fixed-geometry.tex", 706, 715)],
     "Piecewise smooth solutions with matching value and conormal derivative have matching jets."),
    ("N04Coordinates", " (hN03 : N03Statement)", "N04cStatement",
     [("07-fixed-geometry.tex", 462, 494), ("07-fixed-geometry.tex", 551, 704)],
     "Canonical coordinates on the negative and positive pieces, the Airy form, the cut condition and the source conversion."),
    ("N05", " (hN04 : N04Statement)", "N05Statement",
     [("08-stable-inverse.tex", 14, 171)],
     "The canonical reference inverse on the two-weight volume spaces and its closed common domain."),
    ("N06", " (hN05 : N05Statement)", "N06Statement",
     [("08-stable-inverse.tex", 194, 340)],
     "The perturbed operator as a relatively small perturbation on one Banach space."),
    ("N07a", " (hN06 : N06Statement) (hTame : H01Statement ∧ H02Statement)", "N07aStatement",
     [("08-stable-inverse.tex", 342, 511)],
     "Angular and normal regularity of the inverse and its tame estimates at all orders."),
    ("N07b", " (hN07a : N07aStatement)", "N07Statement",
     [("08-stable-inverse.tex", 523, 550)],
     "The physical scalar inverse is the chosen Banach solution."),
    ("N08", " (hN07 : N07Statement) (hS04 : S04Statement)", "N08Statement",
     [("09-solving-the-equation.tex", 13, 137)],
     "The joint residual of height and circle equations and its control columns."),
    ("Solve", " (hN08 : N08Statement) (hTame : H01Statement ∧ H02Statement)", "PointBranchStatement",
     [("09-solving-the-equation.tex", 139, 242)],
     "The coupled inverse, the exact quadratic error, the Nash–Moser iteration, and one solution at a nonzero parameter."),
    ("N12", " (hBranch : PointBranchStatement) (hW03 : W03Statement) (hS03 : S03Statement)", "N12Statement",
     [("10-endpoint-and-sphere.tex", 250, 317)],
     "The flat annular core from one solution at a nonzero parameter."),
]

CLOSED_OLD = ["S01", "S02", "R01", "R02", "R03", "R04"]
REMOVED_OLD = ["S03", "S04", "S05", "H01", "H02", "H03", "W02", "W03", "R05", "R06", "R10", "R11",
               "N02", "N03", "N04", "N07", "N09", "N10", "N11", "N12", "R07", "R08", "R09", "R12",
               "N01", "N05", "N06", "N08", "W01"]


def main() -> None:
    (BP / "Statements.lean").write_text(statements, encoding="utf-8", newline="\n")
    for old in REMOVED_OLD:
        for f in (BP / f"{old}.lean", TASKS / f"{old}.md"):
            if f.exists():
                f.unlink()
    # W01 is closed by an existing theorem
    (BP / "W01.lean").write_text(
        "import ContinuousFlexibility.Statements.Milestones\n"
        "import ContinuousFlexibility.Analysis.AffineMaterialFull\n\n"
        "/-!\n# Blueprint node W01\n\n"
        f"Source: `{P}07-fixed-geometry.tex` lines 22–59. Proved.\n-/\n\n"
        "namespace ContinuousFlexibility.Blueprint\n\n"
        "open ContinuousFlexibility.Statements\n\n"
        "theorem W01 : W01Statement :=\n  ContinuousFlexibility.Statements.affineMaterial_W01_statement\n\n"
        "end ContinuousFlexibility.Blueprint\n",
        encoding="utf-8", newline="\n")
    for name, hyps, concl, srcs, desc in NODES:
        src = "; ".join(f"`{P}{f}` lines {a}–{b}" for f, a, b in srcs)
        lean = BP / f"{name}.lean"
        if not lean.exists():
            lean.write_text(
                "import ContinuousFlexibility.Blueprint.Statements\n\n"
                f"/-!\n# Blueprint node {name}\n\n{desc}\n\nSource: {src}.\n\n"
                f"Task file: `docs/tasks/{name}.md`. The statement is frozen; replace the `sorry`.\n-/\n\n"
                "namespace ContinuousFlexibility.Blueprint\n\n"
                "open ContinuousFlexibility.Statements\n\n"
                f"theorem {name}{hyps} : {concl} := by\n  sorry\n\n"
                "end ContinuousFlexibility.Blueprint\n",
                encoding="utf-8", newline="\n")
        (TASKS / f"{name}.md").write_text(
            f"# {name}\n\n## Problem\n\n{desc}\n\n"
            f"Prove `ContinuousFlexibility.Blueprint.{name}` in "
            f"`src/ContinuousFlexibility/Blueprint/{name}.lean`:\n\n"
            f"```lean\ntheorem {name}{hyps} : {concl}\n```\n\n"
            "## Completion standard\n\n"
            f"- `theorem {name}` has exactly this statement and its proof contains no `sorry`; "
            f"`#print axioms ContinuousFlexibility.Blueprint.{name}` shows only `propext`, "
            "`Classical.choice`, `Quot.sound`.\n"
            "- Every module the proof uses is in the root import and CI is green.\n"
            "- A weaker, relative or conditional version does not complete the task. If the frozen "
            "statement is false or cannot be derived from its hypotheses, record that in "
            "`docs/STATUS.md` with the exact clause, and repair the statement together with "
            "`Blueprint/Assembly.lean`.\n\n"
            f"## Source\n\n{src}.\n",
            encoding="utf-8", newline="\n")

    imports = CLOSED_OLD + ["W01"] + [n[0] for n in NODES]
    asm = [f"import ContinuousFlexibility.Blueprint.{n}" for n in imports] + ['''
/-!
# Blueprint assembly

The blueprint nodes compose to `Nonempty FlatAnnularCore`. This file contains no `sorry`;
the result depends on `sorryAx` exactly through the nodes that are still open.
-/

namespace ContinuousFlexibility.Blueprint

open ContinuousFlexibility.Statements

theorem S03_of_nodes : S03Statement := ⟨ScalarCalculus.1, ScalarWeighted.1⟩
theorem S04_of_nodes : S04Statement := ⟨ScalarCalculus.2.1, ScalarWeighted.2.1⟩
theorem S05_of_nodes : S05Statement := ⟨ScalarCalculus.2.2, ScalarWeighted.2.2⟩

theorem R05_of_nodes (hA : R05aStatement) (hB : R05bStatement) : R05Statement := by
  intro initial
  obtain ⟨T, hT, C, family, hreal, hind⟩ := hA initial
  obtain ⟨C', hC'⟩ := hB T C family hreal
  exact ⟨T, hT, C', family, hC', hind⟩

theorem R06_of_nodes (hA : R06aStatement) (hB : R06bStatement) (hC : R06cStatement) :
    R06Statement := by
  obtain ⟨C, η, K, h1, h2, h3, h4, hop⟩ := hA
  obtain ⟨C₁, η₁, K₁, h1', h2', h3', h4', hfull⟩ := hB C η K h1 h2 h3 h4 hop
  obtain ⟨C₂, η₂, K₂, g1, g2, g3, g4, hfull', hphys, hcont⟩ := hC C₁ η₁ K₁ h1' h2' h3' h4' hfull
  exact ⟨C₂, η₂, K₂, g1, g2, g3, g4, hfull', hphys, hcont⟩

theorem R10_of_nodes (hA : R10aStatement) (hB : R10bStatement) : R10Statement := by
  obtain ⟨D, hacc, hborder, hpieces⟩ := hA
  refine ⟨D, hacc, hborder, fun j hj he => ?_⟩
  obtain ⟨M, hM, hp⟩ := hpieces j hj he
  exact hB D hacc hborder j hj he M hM hp

theorem N04_of_nodes (hc : N04cStatement) (hroot : RootCompositionTarget)
    (hcubic : CubicDivisionTarget) (htrans : PhysicalTransmissionTarget) : N04Statement := by
  obtain ⟨A, T, S, C, R, L, K, base, loss, ε, h1, h2, h3, h4⟩ := hc
  exact ⟨A, T, S, C, R, L, K, base, loss, ε, h1, h2, h3, hroot, hcubic, htrans, h4⟩

/-- The analytic existence statement, assembled from the blueprint nodes. -/
theorem flatAnnularCore_nonempty : Nonempty FlatAnnularCore := by
  have hS03 : S03Statement := S03_of_nodes
  have hS04 : S04Statement := S04_of_nodes
  have hS05 : S05Statement := S05_of_nodes
  have hR03 : R03Statement := R03 (R02 R01)
  have hR04 : R04Statement := R04 (R02 R01)
  have hTame : H01Statement ∧ H02Statement := Tame
  have hR05 : R05Statement := R05_of_nodes (R05a hR04) R05b
  have hR06 : R06Statement := R06_of_nodes R06a R06b R06c
  have hR07 : R07Statement := R07 hR04 hR05 hR06
  have hR08 : R08Statement := R08 hR03 hR07
  have hR09 : R09Statement := R09
  have hR10 : R10Statement := R10_of_nodes (R10a hR06 hR07 hR08 hR09) R10b
  have hR11 : R11Statement := R11b (R11a hR05 hR10)
  have hR12 : R12Statement := R12 hR06 hR08 hR10 hR11
  have hW01 : W01Statement := W01
  have hSpaces : W02Statement ∧ W03Statement := Spaces hW01 hTame
  have hN01 : N01Statement := N01 hR12 hW01 hSpaces.1 hS05
  have hN03 : N03Statement := N02N03 hN01 hS05
  have hN04 : N04Statement := N04_of_nodes (N04Coordinates hN03) N04Root N04Cubic N04Transmission
  have hN05 : N05Statement := N05 hN04
  have hN06 : N06Statement := N06 hN05
  have hN07 : N07Statement := N07b (N07a hN06 hTame)
  have hN08 : N08Statement := N08 hN07 hS04
  have hBranch : PointBranchStatement := Solve hN08 hTame
  exact N12 hBranch hSpaces.2 hS03

end ContinuousFlexibility.Blueprint
''']
    (BP / "Assembly.lean").write_text("\n".join(asm), encoding="utf-8", newline="\n")
    print("nodes:", len(NODES), "open;", len(CLOSED_OLD) + 1, "closed")


if __name__ == "__main__":
    main()
