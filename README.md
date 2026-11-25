# newMath (`Mathmatica`)

A Lean 4 + Mathlib formalization project exploring **Renormalization Group (RG) Dynamics**, **Spontaneous Symmetry Breaking**, **Feigenbaum Theory**, and their structural bridges to **Computational Complexity ($P \text{ vs } NP$)** and **SAT Proof Complexity**.

All modules are designed following Mathlib conventions (zero `sorry`, zero warnings) with the goal of gradually upstreaming general-purpose theorems (such as the Schwarzian Derivative and Davis–Putnam Resolution Completeness) to `leanprover-community/mathlib4`.

## Verified Lean 4 Modules

| Module | Formalized Theorems (Machine-Verified, 0 `sorry`) | Role |
|---|---|---|
| `Mathmatica/Renormalization.lean` | Feigenbaum operator `renorm`, evenness preservation, scaling identity `g 1 = -1/α`; equivariant dynamics, stabilizer preservation, spontaneous symmetry breaking (`ssb_implies_multiple_fixed_points`), $\mathbb{Z}_2$ pitchfork bifurcation | Continuous RG & Symmetry Breaking |
| `Mathmatica/Schwarzian.lean` | **Mathlib4 PR-Ready** (`ContDiffAt ℝ 3` + `iteratedDeriv`): Schwarzian derivative cocycle chain rule (`schwarzian_comp_of_contDiffAt`), negative Schwarzian closure under composition, `schwarzian_affine`, `schwarzian_logistic` (`-6 / (1 - 2x)^2 < 0`) | **Mathlib Candidate**: 1D Dynamics & Feigenbaum Analysis |
| `Mathmatica/SATSymmetry.lean` | Variable permutation group $S_n$ action on CNF-SAT, solution-space orbit invariance, Symmetry Breaking Predicate (SBP) equisatisfiability (`sbp_equisatisfiable`) | Discrete Symmetry Breaking in SAT |
| `Mathmatica/RGComplexity.lean` | Abstract equisatisfiable `RGSolver` flow; constant $\delta$-expansion scaling (`rg_linear_expansion`, polynomial at $k = \log_2 n$) vs. nonlinear quadratic coupling blowup (`rg_quadratic_expansion`, exponential $C_0^n$ at $k = \log_2 n$) | Bridge II: Expansion Rate & Complexity Scaling |
| `Mathmatica/SATDecimation.lean` | Full Davis–Putnam real-space decimation operator `decimateVar`, soundness & lifting completeness (`decimateVar_equisatisfiable`), `RGSolver` instance, 2-SAT fixed point (`w = 2`) vs. 3-SAT coupling divergence (`2^k + 2`) | Bridge I: Renormalizable vs. Non-Renormalizable Phase Transition |
| `Mathmatica/ResolutionCompleteness.lean` | Davis–Putnam refutation completeness (`¬ Satisfiable φ ↔ [] ∈ decimateAll n φ`), exact closure of 2-SAT under `decimateVar` (`decimateVar_preserves_2sat`) | **Mathlib Candidate**: Propositional Resolution Completeness |
| `Mathmatica/EquivariantRG.lean` | Group equivariance of real-space decimation (`decimateVar_equivariant`), fixed-point variable elimination preserving symmetry groups, combined RG + SBP equisatisfiability | Bridge III: Equivariant RG & Symmetry Obstructions |
| `Mathmatica/OverlapGap.lean` | Hamming distance metric axioms & permutation isometry, Overlap Gap Property (`HasOGP`), clustering equivalence relation (`ogp_clustering_equivalence` for $2\nu_1 < \nu_2$), cluster quotient `Setoid` | Bridge IV: 1-RSB Solution-Space Shattering & OGP |
| `Mathmatica/BSWTradeoff.lean` | Tree-like Resolution (`ResTree`), restriction (`restrictTree`), lifting (`liftTree`), and **Ben-Sasson–Wigderson (2001) Width–Size Tradeoff** (`bsw_tree_width_size` & exponential lower bound `bsw_tree_size_lower_bound`: $S > 2^{W - w_0}$) | **Mathlib Candidate**: Proof Complexity Lower Bounds |
| `Mathmatica/TwoSATPoly.lean` | Deduplicated `Finset` 2-SAT decimation (`decimateVar` / `decimateList`), exact 2-clause count `1 + 2n + C(2n, 2)`, and polynomial RG state-space bound `(decimateList vs φ).card ≤ (2n + 1)^2` | **Mathlib Candidate**: 2-SAT Polynomial RG Closure |
| `Mathmatica/OGPBarrier.lean` | Discrete Intermediate Value Theorem in Hamming space (`discrete_ivt_hamming`), Coupled OGP (`HasCoupledOGP`), `δ`-stable solvers, and **OGP Stability Barrier Theorem** (`ogp_rules_out_stable_solver`: no stable algorithm can find valid states across a coupled OGP path) | Bridge IV Completed: Dynamical Continuity to Search Impossibility |
| `Mathmatica/ExplicitBarriers.lean` | Explicit ferromagnetic Ising chain family `isingChainCNF n` (exact twin ground states, full-width `HasOGP ... 0 n`, concrete instantiation of `ogp_rules_out_stable_solver`) and explicit Pigeonhole Principle CNF family `phpCNF m` (`¬ Satisfiable (phpCNF m)`) | Explicit Concrete Families for OGP & Symmetric Unsatisfiability |
| `Mathmatica/DynamicalComplexity.lean` | Unified **Dynamical–Complexity Correspondence** (`SolverDynamics`, `ThreePhaseSummary`, `three_phase_correspondence`): Phase I (finite-attractor periodicity via pigeonhole, Feigenbaum log-depth polynomial scaling `feigenbaum_log_depth_poly`, 2-SAT closure), Phase II (Critical OGP stability barrier & Ising witness), Phase III (Chaotic/non-renormalizable BSW exponential barrier $2^d < S$) | Unified Three-Phase Correspondence Framework |
| `Mathmatica/RGUniversality.lean` | Built on Mathlib's `ContractingWith` (Banach Fixed-Point Theorem): `ContractingRGFlow`, unique universal fixed point, geometric erasure of microscopic differences (`rg_erases_microscopic_details`), and universality of continuous macroscopic observables (`rg_observable_universality`) | Continuous RG Universality (via Mathlib `ContractingWith`) |
| `Mathmatica/PeriodDoubling.lean` | Built on Mathlib's `Function.IsPeriodicPt` & `Function.minimalPeriod`: logistic map fixed-point instability threshold at $\mu = 3$ (`deriv = -1`), explicit period-2 orbit $p_\pm(\mu)$ for $\mu > 3$, and strict `minimalPeriod = 2` (`minimalPeriod_periodTwoPos`) | **Mathlib Candidate**: Logistic Map Period-Doubling Bifurcation |
| `Mathmatica/ProverDelayer.lean` | **Pudlák–Impagliazzo (2000) Prover–Delayer Game**: `minScore`, exponential tree-like resolution size lower bound (`2 ^ minScore ≤ T.size`), semantic adversary theorem (`size_lower_bound_of_adversary`), and unconditional $2^n \le T.\text{size}$ lower bound for `allClauses n` | **Mathlib Candidate**: Proof Complexity Adversary Lower Bounds |
| `Mathmatica/ComplexityBarriers.lean` | Straight-line DAG Boolean circuits (`Circuit n s`), `card_boolFn = 2^(2^n)`, closed-form circuit counting bound `(3(n+s)^2)^s(n+s)`, Shannon existence theorem, and **Razborov–Rudich Natural Proofs Barrier** (`natural_property_hits_prg_barrier`) | Barrier Desk: Circuit Lower Bounds & Natural Proofs |
| `Mathmatica/DAGResolution.lean` | General DAG Resolution / CDCL (`IsDAGProof`, `IsDAGRefutation`), **BSW (2001) Lemma 3.5** double-counting fat-clause averaging (`exists_popular_lit_in_fatClauses`), restriction shrinkage (`2n |B'| ≤ (2n - k) |B|`), and geometric decay (`(2n)^r b_r ≤ (2n - k)^r b_0`) | **Mathlib Candidate**: General DAG Resolution BSW Engine |
| `Mathmatica/CircuitEntropy.lean` | Bounded-memory coarse-grainers (`CoarseGrainer`), pigeonhole compression & bitwidth lower bounds, and **Positive Trajectory Entropy $\implies$ Exponential Macro State Space** (`positive_entropy_forces_exponential_macro`: $2^k \le |\mathrm{Macro}|$) | Bridge: Dynamical Entropy to Algorithmic Compression Barriers |
| `Mathmatica/BSWDAGFull.lean` | **Full Ben-Sasson–Wigderson (2001) General DAG Resolution (CDCL) Width–Size Tradeoff** (`bsw_dag_width_size_tradeoff` & `bsw_dag_size_lower_bound`: $(2n)^r \le (2n - k)^r \cdot |\pi|$), via DAG restriction, lifting, unit-clause merging, and double induction | **Mathlib Candidate**: Flagship CDCL Proof Complexity Theorem |
| `Mathmatica/RGTreewidth.lean` | Bounded RG elimination width (`HasElimWidthBounded w vs φ`) $\implies$ full-trajectory polynomial state-space bound `(rgTrace vs φ t).card ≤ (2n + 1)^w` (`rg_bounded_elimWidth_poly`), generalizing `TwoSATPoly` ($w = 2$) to arbitrary bounded-treewidth $k$-SAT | **Mathlib Candidate**: Bounded-Treewidth RG Polynomial Solvability |

## Conjecture Bridges (Research Roadmap)

1. **Bridge I — Renormalizability = Polynomial-Time Solvability**: Characterizing Schaefer's dichotomy ($P$ vs. NP-complete CSPs) via closure under local equisatisfiable coarse-graining operators (finite-order effective interaction manifolds vs. non-renormalizable higher-order coupling blowup).
2. **Bridge II — Unstable Manifold Dimension = Complexity Class**: Distinguishing finite-dimensional unstable RG manifolds (e.g., Feigenbaum's single eigenvalue $\delta \approx 4.669$, yielding polynomial $n^{O(\log \delta)}$ at logarithmic depth) from diverging unstable dimensions / nonlinear feedback yielding exponential barriers.
3. **Bridge III — Equivariant RG Symmetry Obstructions**: Linking equivariant decimation on highly symmetric unsatisfiable families (e.g., PHP) to resolution width lower bounds, and linking hidden 1-RSB symmetry breaking to NP-hardness of canonical orbit representatives.
4. **Bridge IV — Negative Schwarzian Rigidity vs. Discrete OGP**: Seeking a discrete curvature/Schwarzian-type RG invariant whose sign flip marks the algorithmic phase transition from unimodal/local tractability to OGP shattering.

## Build & Verify

```bash
# Fetch precompiled Mathlib cache
lake exe cache get

# Build the library
lake build Mathmatica
```
