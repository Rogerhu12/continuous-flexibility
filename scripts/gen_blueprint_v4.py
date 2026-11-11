"""Generate blueprint v4 from v3 (one-off, kept for the record).

v4 follows the lemma structure of the readable manuscript
(paper/flexible-surface-readable): N01 and the canonical coordinates are cut
into pipelines along the conjuncts of their property bundles, Solve is cut
into its linear part and the Nash-Moser step, every task file cites the
readable manuscript, and tool tasks without a blueprint node are added for
the abstract lemmas the manuscript isolates.

Node files that already exist and are not superseded are left untouched.
"""
import pathlib

ROOT = pathlib.Path(__file__).resolve().parent.parent
ST = ROOT / "src/ContinuousFlexibility/Statements"
BP = ROOT / "src/ContinuousFlexibility/Blueprint"
TASKS = ROOT / "docs/tasks"
P = "paper/flexible-surface-readable/"
F = {3: "03-height-equation.tex", 4: "04-reference-overview.tex", 5: "05-flat-end-chain.tex",
     6: "06-global-reference-inverse.tex", 7: "07-fixed-geometry.tex", 8: "08-stable-inverse.tex",
     9: "09-solving-the-equation.tex", 10: "10-endpoint-and-sphere.tex"}


def strip_and(line: str) -> str:
    assert line.rstrip().endswith(" ∧"), line
    return line.rstrip()[: -len(" ∧")]


def bundle(name: str, stop: str) -> list[str]:
    src = (ST / "Nonlinear.lean").read_text(encoding="utf-8").split("\n")
    i = next(k for k, l in enumerate(src) if l.startswith(f"def {name} "))
    j = next(k for k in range(i, len(src)) if src[k].startswith(stop))
    b = src[i:j]
    while b and b[-1].strip() == "":
        b.pop()
    return b


# ---- N01Properties: reference and controls | one neighbourhood | tame bounds ----
n01 = bundle("N01Properties", "/-- The first concrete stage")
assert n01[2].strip() == ("IsRadialReference D ∧ 0 < ε ∧ referenceStateConditions D S C ∧ "
                          "controlGeometryConditions D S C ∧")
i5 = next(k for k, l in enumerate(n01) if l.startswith("  (∃ B : ℝ, 0 < B ∧ ∀ m,"))
i7 = next(k for k, l in enumerate(n01) if l.startswith("  ordinaryFlowConditions"))
i12 = next(k for k, l in enumerate(n01) if l.startswith("  (∀ k s : ℕ, ∃ B : ℝ, 0 < B ∧ ∀ m i a b p,"))
n01a = ["  IsRadialReference D ∧ referenceStateConditions D S C ∧ controlGeometryConditions D S C ∧"]
n01a += n01[i5:i7]
n01a[-1] = strip_and(n01a[-1])
n01b = n01[i7:i12]
n01b[-1] = strip_and(n01b[-1])

# ---- N04Properties: pieces and charts | canonical form | bounds and sources ----
n04 = bundle("N04Properties", "/-- The coordinate stage retains")
assert n04[3].strip() == "let U := stateNeighborhood S C base ε"
iB = next(k for k in range(len(n04) - 1)
          if n04[k] == "  (∀ m," and "K.positive (K.cutPair m).1 = false" in n04[k + 1])
iC = next(k for k, l in enumerate(n04) if l.startswith("  (∀ s : ℕ, ∃ B : ℝ, 0 < B ∧ ∀ z ∈ U, ∀ m p,"))
n04a = n04[4:iB]
n04a[-1] = strip_and(n04a[-1])
n04b = n04[iB:iC]
n04b[-1] = strip_and(n04b[-1])
n04c = n04[iC:]
J = "\n".join

ADDITION = f'''
/-! ## N01: reference and controls, then one neighbourhood, then the tame bounds -/

/-- The conjuncts of `N01Properties` about the reference and the travel-angle controls. -/
def N01PartA (D : ReferenceData) (T : MaterialData) (S : PhysicalSpacesData)
    (C : NonlinearGeometryData S) : Prop :=
{J(n01a)}

/-- The conjuncts of `N01Properties` about flows, charts, denominators and the type,
on one neighbourhood. -/
def N01PartB (D : ReferenceData) (S : PhysicalSpacesData)
    (C : NonlinearGeometryData S) (base : ℕ) (ε : ℝ) : Prop :=
{J(n01b)}

def N01aStatement : Prop :=
  ∃ A : RadialReference, ∃ T : MaterialData, ∃ S : PhysicalSpacesData,
    ∃ C : NonlinearGeometryData S,
      IsMaterialData A.val T ∧ IsPhysicalSpaces A.val T S ∧ N01PartA A.val T S C

def N01bStatement : Prop :=
  ∃ A : RadialReference, ∃ T : MaterialData, ∃ S : PhysicalSpacesData,
    ∃ C : NonlinearGeometryData S, ∃ base : ℕ, ∃ ε : ℝ,
      IsMaterialData A.val T ∧ IsPhysicalSpaces A.val T S ∧ N01PartA A.val T S C ∧
        0 < ε ∧ N01PartB A.val S C base ε

/-! ## N04: pieces and charts, then the canonical form, then bounds and sources -/

/-- The conjuncts of `N04Properties` about the pieces and their charts. -/
def N04PartA (D : ReferenceData) (S : PhysicalSpacesData) (C : NonlinearGeometryData S)
    (K : CanonicalData S) (base : ℕ) (ε : ℝ) : Prop :=
  let U := stateNeighborhood S C base ε
{J(n04a)}

/-- The conjuncts of `N04Properties` about the cut pairs and the canonical operator. -/
def N04PartB (S : PhysicalSpacesData) (C : NonlinearGeometryData S)
    (L : ReturnCorrectionData S) (K : CanonicalData S) (base : ℕ) (ε : ℝ) : Prop :=
  let U := stateNeighborhood S C base ε
{J(n04b)}

def N04aStatement : Prop :=
  ∃ A : RadialReference, ∃ T : MaterialData, ∃ S : PhysicalSpacesData,
    ∃ C : NonlinearGeometryData S, ∃ R : ReturnEquationData S,
      ∃ L : ReturnCorrectionData S, ∃ K : CanonicalData S,
        ∃ base loss : ℕ, ∃ ε : ℝ,
          IsMaterialData A.val T ∧ IsPhysicalSpaces A.val T S ∧
            NonlinearPropertiesThrough03 A.val T S C R L base loss ε ∧
              N04PartA A.val S C K base ε

def N04bStatement : Prop :=
  ∃ A : RadialReference, ∃ T : MaterialData, ∃ S : PhysicalSpacesData,
    ∃ C : NonlinearGeometryData S, ∃ R : ReturnEquationData S,
      ∃ L : ReturnCorrectionData S, ∃ K : CanonicalData S,
        ∃ base loss : ℕ, ∃ ε : ℝ,
          IsMaterialData A.val T ∧ IsPhysicalSpaces A.val T S ∧
            NonlinearPropertiesThrough03 A.val T S C R L base loss ε ∧
              N04PartA A.val S C K base ε ∧ N04PartB S C L K base ε

end ContinuousFlexibility.Blueprint
'''

# (name, hypotheses, conclusion, sources [(section, first, last)], description)
NODES = [
    ("ScalarCalculus", "", "S03CalculusStatement ∧ S04CalculusStatement ∧ S05CalculusStatement",
     [(3, 23, 189), (3, 406, 543)],
     "The pointwise and finite-rectangle calculus of the height equation: connection, residual, conservation, type correction."),
    ("ScalarWeighted", "", "S03WeightedStatement ∧ S04WeightedStatement ∧ S05WeightedStatement",
     [(3, 406, 543), (7, 108, 506)],
     "The same three statements on the weighted function spaces, up to the flat endpoints."),
    ("Tame", "", "H01Statement ∧ H02Statement",
     [(7, 108, 354), (9, 251, 273)],
     "Tame calculus on projective limits of Banach scales and Hamilton's theorem on families of inverses (Theorem 9.3)."),
    ("Spaces", " (hW01 : W01Statement) (hTame : H01Statement ∧ H02Statement)", "W02Statement ∧ W03Statement",
     [(7, 108, 237), (7, 399, 506)],
     "The weighted height, source and circle spaces with their tame structure, and smooth flat extension of their elements (Lemma 7.4)."),
    ("R05a", " (hR04 : R04Statement)", "R05aStatement",
     [(5, 28, 323)],
     "The accumulating chain of Morse cells and joins for every admissible height sequence, with flatness and coefficient bounds."),
    ("R05b", "", "R05bStatement",
     [(5, 323, 472)],
     "Mass and resistance of every cell and join of a realized chain."),
    ("R06a", "", "R06aStatement",
     [(5, 472, 725)],
     "Deep tail: identification of the Friedrichs form, the inverse with norm C/Λ, and convergence of the Dirichlet truncations."),
    ("R06b", "", "R06bStatement",
     [(5, 513, 790)],
     "Deep tail: the unique square-integrable line, its decay, and the localized Green kernel."),
    ("R06c", "", "R06cStatement",
     [(5, 513, 790)],
     "Deep tail: flatness in the original radius, the source identity, and continuity in the height ratios."),
    ("R07", " (hR04 : R04Statement) (hR05 : R05Statement) (hR06 : R06Statement)", "R07Statement",
     [(5, 790, 1013)],
     "One transition cell per frequency and one height sequence with all matching angles bounded below."),
    ("R08", " (hR03 : R03Statement) (hR07 : R07Statement)", "R08Statement",
     [(6, 100, 180)],
     "Joining the central model to the selected tails while keeping the second-mode solution."),
    ("R09", "", "R09Statement",
     [(6, 180, 352)],
     "Cutting a model inverse inside a positive buffer."),
    ("R10a", " (hR06 : R06Statement) (hR07 : R07Statement) (hR08 : R08Statement) (hR09 : R09Statement)", "R10aStatement",
     [(6, 352, 776)],
     "At every even frequency: the inner inverse, the outer inverse, their Poisson functions and the selected margin on one geometry. The tool tasks R10a-Inner and R10a-Outer carry the two regions."),
    ("R10b", "", "R10bStatement",
     [(6, 776, 850)],
     "Inversion of the matching matrix and the exact matched inverse."),
    ("R11a", " (hR05 : R05Statement) (hR10 : R10Statement)", "R11aStatement",
     [(6, 850, 1017)],
     "The weighted bound of the matched inverse at the three exponents on the same geometry."),
    ("R11b", " (hR11a : R11aStatement)", "R11Statement",
     [(6, 850, 1017)],
     "The first normal estimate for the same inverse."),
    ("R12", " (hR06 : R06Statement) (hR08 : R08Statement) (hR10 : R10Statement) (hR11 : R11Statement)", "R12Statement",
     [(4, 49, 201), (6, 1017, 1169)],
     "The fixed radial reference: graph domain, zero mode, final border, two-sided inverse."),
    ("N01a", " (hR12 : R12Statement) (hW01 : W01Statement) (hW02 : W02Statement)", "N01aStatement",
     [(7, 506, 646)],
     "Root collars and the travel-angle controls of the reference profile (Lemmas 7.5 and 7.6)."),
    ("N01b", " (hN01a : N01aStatement) (hS05 : S05Statement)", "N01bStatement",
     [(7, 646, 761)],
     "One neighbourhood of the reference state on which the type, the denominators, the flows and the charts are controlled (Lemma 7.7)."),
    ("N01c", " (hN01b : N01bStatement)", "N01Statement",
     [(7, 761, 806), (7, 1303, 1725)],
     "The tame bounds of the coefficient and flow families on that neighbourhood (part of Proposition 7.8)."),
    ("N02N03", " (hN01 : N01Statement) (hS05 : S05Statement)", "N03Statement",
     [(7, 806, 992)],
     "The return residual with its small-divisor inverse, and the correction that fixes the characteristic returns."),
    ("N04Root", "", "RootCompositionTarget",
     [(7, 1046, 1211)],
     "Even and odd parts of a smooth function under the substitution at a root, with fixed loss."),
    ("N04Cubic", "", "CubicDivisionTarget",
     [(7, 1211, 1303)],
     "Division by y³ of a function vanishing to third order, in L² with three derivatives lost."),
    ("N04Transmission", "", "PhysicalTransmissionTarget",
     [(7, 1725, 1755)],
     "Piecewise smooth solutions with matching value and conormal derivative have matching jets."),
    ("N04a", " (hN03 : N03Statement)", "N04aStatement",
     [(7, 992, 1046), (7, 1211, 1303), (7, 1316, 1497)],
     "The negative and positive pieces and their coordinates: charts, inverse charts, height factors, symmetries."),
    ("N04b", " (hN04a : N04aStatement)", "N04bStatement",
     [(7, 992, 1303)],
     "The cut pairs, the transmission condition at a cut, and the canonical form of the operator on negative and positive pieces."),
    ("N04Coordinates", " (hN04b : N04bStatement)", "N04cStatement",
     [(7, 1497, 1725)],
     "The uniform bounds of the potential and of the divided differences, and the conversion of sources (rest of Proposition 7.8)."),
    ("N05", " (hN04 : N04Statement)", "N05Statement",
     [(8, 34, 256)],
     "The canonical reference inverse on the two-weight volume spaces and its closed common domain."),
    ("N06", " (hN05 : N05Statement)", "N06Statement",
     [(8, 256, 489)],
     "The perturbed operator as a relatively small perturbation on one Banach space."),
    ("N07a", " (hN06 : N06Statement) (hTame : H01Statement ∧ H02Statement)", "N07aStatement",
     [(8, 489, 774)],
     "Angular and normal regularity of the inverse and its tame estimates at all orders."),
    ("N07b", " (hN07a : N07aStatement)", "N07Statement",
     [(8, 774, 806)],
     "The physical scalar inverse is the chosen Banach solution."),
    ("N08", " (hN07 : N07Statement) (hS04 : S04Statement)", "N08Statement",
     [(9, 20, 189)],
     "The joint residual of height and circle equations and its control columns."),
    ("N09N10", " (hN08 : N08Statement) (hTame : H01Statement ∧ H02Statement)", "N10Statement",
     [(9, 189, 251), (9, 299, 346)],
     "The approximate right inverse of the coupled system and the exact quadratic error identity."),
    ("Solve", " (hN10 : N10Statement) (hTame : H01Statement ∧ H02Statement)", "PointBranchStatement",
     [(9, 251, 413)],
     "The Nash–Moser iteration with quadratic error (Theorem 9.4) applied to the coupled system: one solution at a nonzero parameter."),
    ("N12", " (hBranch : PointBranchStatement) (hW03 : W03Statement) (hS03 : S03Statement)", "N12Statement",
     [(10, 304, 430)],
     "The flat annular core from one solution at a nonzero parameter."),
]

# (name, sources, description, consumer)
TOOLS = [
    ("Tool-OneHighFactor", [(7, 237, 399)],
     "Lemma 7.2 (estimates with one high factor: interpolation, product, composition with a smooth function, composition and inversion of circle diffeomorphisms) and Lemma 7.3 (flows on the circle).",
     "Spaces, N01c, N04Coordinates"),
    ("Tool-AngularCommutator", [(8, 512, 774)],
     "Lemma 8.4: regularity of an inverse from a commutator, on a Hilbert space with a nonnegative self-adjoint angular frequency operator, including the three-lines interpolation step.",
     "N07a"),
    ("Tool-SobolevExtension", [(7, 237, 354)],
     "A linear extension operator from a half-line or an interval to the line that is bounded in every Sobolev norm (appendix on external inputs), and the Hadamard three-lines lemma in the form used by Lemma 8.4.",
     "Tool-OneHighFactor, Tool-AngularCommutator"),
    ("Tool-R10a-Inner", [(6, 352, 526)],
     "Lemma 6.3: the inner inverse on the finite inner domain at one frequency, from the cut models, the positive connectors and the interface matrix, with its two weighted bounds.",
     "R10a"),
    ("Tool-R10a-Outer", [(6, 526, 657)],
     "Lemmas 6.4 and 6.5: the inputs from the transition core and the deep tail, and the outer inverse built from two homogeneous solutions without division by a boundary value.",
     "R10a"),
]

SUPERSEDED = ["N01", "N04Coordinates", "Solve"]
CLOSED = ["S01", "S02", "R01", "R02", "R03", "R04", "W01"]


def cite(srcs) -> str:
    return "; ".join(f"`{P}{F[s]}` lines {a}–{b}" for s, a, b in srcs)


def main() -> None:
    stf = BP / "Statements.lean"
    text = stf.read_text(encoding="utf-8")
    if "def N01PartA" not in text:
        tail = "\nend ContinuousFlexibility.Blueprint\n"
        assert text.endswith(tail), "unexpected end of Statements.lean"
        stf.write_text(text[: -len(tail)] + ADDITION, encoding="utf-8", newline="\n")
        for old in SUPERSEDED:
            f = BP / f"{old}.lean"
            if f.exists():
                f.unlink()
    for f in TASKS.glob("*.md"):
        if f.name != "README.md":
            f.unlink()
    for name, hyps, concl, srcs, desc in NODES:
        lean = BP / f"{name}.lean"
        if not lean.exists():
            lean.write_text(
                "import ContinuousFlexibility.Blueprint.Statements\n\n"
                f"/-!\n# Blueprint node {name}\n\n{desc}\n\nSource: {cite(srcs)}.\n\n"
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
            f"## Source\n\n{cite(srcs)}.\n",
            encoding="utf-8", newline="\n")
    for name, srcs, desc, consumer in TOOLS:
        (TASKS / f"{name}.md").write_text(
            f"# {name}\n\n## Problem\n\n{desc}\n\n"
            "This is a tool task: it has no blueprint node. State the lemma in Lean exactly as the "
            "manuscript states it, in new modules under `src/ContinuousFlexibility/`, and prove it. "
            f"It is used by: {consumer}.\n\n"
            "## Completion standard\n\n"
            "- Every assertion of the cited lemma is a Lean theorem with the same hypotheses and "
            "conclusions, in the generality the manuscript uses; nothing is weakened, specialised to "
            "an easier case or left as a hypothesis.\n"
            "- No `sorry`; only the axioms `propext`, `Classical.choice`, `Quot.sound`.\n"
            "- The modules are in the root import and CI is green.\n"
            "- The pull request lists each assertion of the lemma with the name of its Lean theorem.\n\n"
            f"## Source\n\n{cite(srcs)}.\n",
            encoding="utf-8", newline="\n")

    imports = CLOSED + [n[0] for n in NODES]
    asm = (BP / "Assembly.lean").read_text(encoding="utf-8")
    head_end = asm.index("\n/-!")
    new_head = "\n".join(f"import ContinuousFlexibility.Blueprint.{n}" for n in imports) + "\n"
    asm = new_head + asm[head_end:]
    old = "  have hN01 : N01Statement := N01 hR12 hW01 hSpaces.1 hS05\n"
    assert old in asm
    asm = asm.replace(old, "  have hN01 : N01Statement := N01c (N01b (N01a hR12 hW01 hSpaces.1) hS05)\n")
    old = "N04_of_nodes (N04Coordinates hN03) N04Root N04Cubic N04Transmission"
    assert old in asm
    asm = asm.replace(old, "N04_of_nodes (N04Coordinates (N04b (N04a hN03))) N04Root N04Cubic N04Transmission")
    old = "  have hBranch : PointBranchStatement := Solve hN08 hTame\n"
    assert old in asm
    asm = asm.replace(old, "  have hN10 : N10Statement := N09N10 hN08 hTame\n"
                           "  have hBranch : PointBranchStatement := Solve hN10 hTame\n")
    (BP / "Assembly.lean").write_text(asm, encoding="utf-8", newline="\n")
    print("open nodes:", len(NODES), "closed:", len(CLOSED), "tool tasks:", len(TOOLS))


if __name__ == "__main__":
    main()
