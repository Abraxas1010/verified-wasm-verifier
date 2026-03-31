import Lake
open Lake DSL

package «HeytingLean» where

require mathlib from git
  "https://github.com/leanprover-community/mathlib4" @ "v4.24.0"

-- Mathlib `v4.24.0` depends on a set of auxiliary libraries that are specified as moving branches
-- in Mathlib's own `lakefile.lean`. To keep builds reproducible, pin the ones we rely on to the
-- revisions recorded in Mathlib's `lake-manifest.json` for `v4.24.0`.
--
-- This prevents confusing failures *inside Mathlib* after `lake update` (e.g. missing `Fin.modNat`
-- if Batteries drifts away from Mathlib's expected revision).
require Cli from git
  "https://github.com/leanprover/lean4-cli" @ "91c18fa62838ad0ab7384c03c9684d99d306e1da"
require Qq from git
  "https://github.com/leanprover-community/quote4" @ "dea6a3361fa36d5a13f87333dc506ada582e025c"
require aesop from git
  "https://github.com/leanprover-community/aesop" @ "725ac8cd67acd70a7beaf47c3725e23484c1ef50"
require importGraph from git
  "https://github.com/leanprover-community/import-graph" @ "d768126816be17600904726ca7976b185786e6b9"
require LeanSearchClient from git
  "https://github.com/leanprover-community/LeanSearchClient" @ "99657ad92e23804e279f77ea6dbdeebaa1317b98"
require plausible from git
  "https://github.com/leanprover-community/plausible" @ "dfd06ebfe8d0e8fa7faba9cb5e5a2e74e7bd2805"
require batteries from git
  "https://github.com/leanprover-community/batteries" @ "8da40b72fece29b7d3fe3d768bac4c8910ce9bee"

-- Some external projects (e.g. teorth/analysis via subverso) require a newer ProofWidgets
-- than the one pinned transitively in older Mathlib manifests.
require proofwidgets from git
  -- Pinned to the `v0.0.75` tag (toolchain: Lean v4.24.0).
  "https://github.com/leanprover-community/ProofWidgets4" @ "b21695ed5db9bd30f7816621fa9ac142cae39a8f"

-- Doc generator (needed by some external projects like teorth/expdb).
-- Pinned to a toolchain-matched tag for reproducibility.
require «doc-gen4» from git
  "https://github.com/leanprover/doc-gen4" @ "v4.24.0"

-- Quantum information theory foundations (states/channels/POVMs).
-- Pinned to a Lean 4.24.0-compatible revision (mathlib commit matches `v4.24.0`).
require quantumInfo from git
  "https://github.com/Timeroot/Lean-QuantumInfo" @ "65341c7f9ca9496adec7d061cf82822210e3eb74"

-- Combinatorial game theory (migrated out of Mathlib; see Mathlib.SetTheory.PGame.Basic deprecation).
require CombinatorialGames from git
  "https://github.com/vihdzp/combinatorial-games" @ "a195e146cdb97ca2e98a4bf923f50b559a07044a"

-- Metamathematics / modal logic library (FormalizedFormalLogic project).
-- NOTE: the upstream Lake package name is `Foundation` (repo: FormalizedFormalLogic/Foundation).
-- Pinned for reproducibility; deep modal bridge work is deferred.
require Foundation from git
  -- NOTE: upstream `master` currently requires a newer Lean toolchain; pin to a Lean 4.24-era revision.
  -- Forked to avoid a Mathlib name collision (`Matrix.map`); see `WIP/extended_noah_phase7_research_map_2026-01-30.md`.
  "https://github.com/Abraxas1010/Foundation" @ "7f6e9cdcabff8064cf27048886205c2a1e1fdaf4"

-- Physics formalization library (Lorentz tensors, spacetime, QFT foundations).
-- Forked and backported to Mathlib v4.24.0 for HeytingLean compatibility.
-- NOTE: 12 modules have known issues; see BACKPORT_STATUS.md in the PhysLean repo.
require PhysLean from git
  "https://github.com/Abraxas1010/PhysLean" @ "backport-v4.24.0"

-- OSforGFF dependency chain (kolmogorov_extension4 -> BochnerMinlos -> GaussianField -> OSforGFF).
-- Pinned to the published Lean 4.24 backport branch maintained for Heyting integration.
require «OSforGFF» from git
  "https://github.com/Abraxas1010/OSforGFF" @ "backport-v4.24.0"

-- Terence Tao / teorth projects (external math corpora).
-- These are integrated primarily for reuse + searchability via `lean_index/`.
--
-- NOTE: Some teorth repos are on toolchains newer/older than our pinned Lean/Mathlib;
-- we integrate the low-risk ones first and leave heavier backporting to later pins/forks.
require «Analysis» from git
  "https://github.com/teorth/analysis" @ "1d4e8c3dda601cafa8ee7d49d0a219b2936d170e" / "analysis"

require equational_theories from git
  "https://github.com/teorth/equational_theories" @ "9d809baa130e4b111db7f35a7cc89038e85694be"

-- Teorth auxiliary Lean projects (older toolchains upstream; we pin commits and only import stable subsets).
require estimate_tools from git
  "https://github.com/teorth/estimate_tools" @ "baf6cd9d87ed6a36ca93536bf2d8c68ca8d503f9"

require asymptotic from git
  "https://github.com/teorth/asymptotic" @ "a4e2136ed72ea04d3b91b52108c85fc0c07113c3"

require newton from git
  "https://github.com/teorth/newton" @ "869643e19825262deb649430fd33a80417a3e462"

require symmetric_project from git
  "https://github.com/teorth/symmetric_project" @ "10b21714fafe655add33efffa5e68ef8cbb068bd"

-- teorth/pfr + teorth/expdb (pinned to Mathlib v4.24.0 tags).
require PFR from git
  "https://github.com/teorth/pfr" @ "v4.24.0"

require expdb from git
  "https://github.com/teorth/expdb" @ "v4.24.0"

require cslib from git
  "https://github.com/leanprover/cslib" @ "e1fea784d55eae30275c205291f12a1b4868eed3"

-- lean-auto: automated reasoning + SMT solver integration (Z3/CVC5 dispatch).
-- Used by LeanCP for separation logic proof obligation discharge.
-- Pinned to the same commit Loom v4.24.0 uses for compatibility.
require auto from git
  "https://github.com/leanprover-community/lean-auto.git" @ "f62266d7cef8d70a7354f13ba925114642c2445b"

@[default_target]
lean_lib «HeytingLean» where

-- Proof2Vec query modules live outside `HeytingLean.*` so they are never ingested into the DB,
-- but still build within this Lake package (and can be elaborated/extracted by `proof2vec_extract`).
lean_lib Proof2VecQueries where

-- FHE executables (initial wiring)
lean_exe apmt_fhe_cli where
  root := `HeytingLean.Crypto.FHE.CLI

lean_exe apmt_fhe_selftest where
  root := `HeytingLean.Crypto.FHE.Selftest

lean_exe apmt_fhe_audit where
  root := `HeytingLean.Crypto.FHE.Audit

-- Unified JSON demo (packaged/exported separately, but runnable here as well).
lean_exe unified_demo where
  root := `HeytingLean.CLI.UnifiedDemo

lean_exe heytingveil_intake_cli where
  root := `HeytingLean.HeytingVeil.CLI.IntakeDemoMain

lean_exe heytingveil where
  root := `HeytingLean.HeytingVeil.CLI.Main

-- Legacy HeytingVeil command surface (package/promote/promote_apply).
-- Keep this executable stable for replay/promotion contract tooling while the
-- unified JSON CLI (`heytingveil`) evolves independently.
lean_exe heytingveil_legacy where
  root := `HeytingLean.CLI.HeytingVeilMain

lean_exe heytingveil_verify where
  root := `HeytingLean.HeytingVeil.CLI.VerifyMain

lean_exe pde_symbolic_bridge_demo where
  root := `HeytingLean.CLI.PDESymbolicBridgeDemoMain

-- NIST FIPS 203 (ML-KEM) parameter validator (JSON report).
lean_exe pqc_param_validator where
  root := `HeytingLean.CLI.PQCParamValidatorMain

-- NIST FIPS 204 (ML-DSA) parameter validator (JSON report).
lean_exe mldsa_param_validator where
  root := `HeytingLean.CLI.MLDSAParamValidatorMain

-- Gap 3 helper: explore failure-probability tail bounds (windowed counts; JSON output).
lean_exe pqc_failure_bound where
  root := `HeytingLean.CLI.PQCFailureBoundMain

-- Standardized ML-KEM byte-runtime smoke executable over the vendored PQClean backends.
lean_exe mlkem_standard_runtime where
  root := `HeytingLean.CLI.MLKEMStandardRuntimeMain

-- Standardized ML-KEM protocol-path smoke executable over the promoted runtime lane.
lean_exe mlkem_protocol_runtime where
  root := `HeytingLean.CLI.MLKEMProtocolRuntimeMain

-- Hostile-audit executable for protocol runtime tamper/rejection scenarios.
lean_exe mlkem_protocol_runtime_audit where
  root := `HeytingLean.CLI.MLKEMProtocolRuntimeAuditMain

-- Gap 1 helper: check NTT roundtrip/multiplication against a negacyclic reference (runtime).
lean_exe pqc_ntt_check where
  root := `HeytingLean.CLI.PQCNTTCheckMain

-- Closeness & LoFViz executables
lean_exe heyting_closeness where
  root := `HeytingLean.CLI.HeytingCloseness

lean_exe proof_graph_dump where
  root := `HeytingLean.CLI.ProofGraphDump

lean_exe proof_graph_extract where
  root := `HeytingLean.CLI.ProofGraphExtract

lean_exe proof_graph_features where
  root := `HeytingLean.CLI.ProofGraphFeatures

-- Export Lean proof terms as Wolfram-Physics-style hypergraphs (binary + metadata).
lean_exe proof_term_hypergraph where
  root := `HeytingLean.CLI.ProofTermHypergraphMain

lean_exe env_list where
  root := `HeytingLean.CLI.EnvList

lean_exe lean_facts where
  root := `HeytingLean.CLI.LeanFacts

lean_exe export_sky where
  root := `HeytingLean.CLI.ExportSKY

lean_exe verified_check where
  root := `HeytingLean.CLI.VerifiedCheck

lean_exe icc_gpu_verifier_fixture where
  root := `HeytingLean.CLI.ICCGPUVerifierFixtureMain

lean_exe icc_gpu_verifier_corpus where
  root := `HeytingLean.CLI.ICCGPUVerifierCorpusMain

lean_exe diff_atp_topo_corpus where
  root := `HeytingLean.CLI.DiffATPTopoCorpusMain

lean_exe verifier_infer_witness where
  root := `HeytingLean.CLI.VerifierInferWitnessMain

lean_exe icc_witness_export where
  root := `HeytingLean.CLI.ICCWitnessExport

lean_exe icc_encoder_batch where
  root := `HeytingLean.CLI.ICCEncoderBatch

lean_exe arbitrary_lean_semantic_bundle where
  root := `HeytingLean.CLI.ArbitraryLeanSemanticBundle

lean_exe icc_kernel_export where
  root := `HeytingLean.CLI.ICCKernelExportMain

lean_exe icc_kernel_corpus where
  root := `HeytingLean.CLI.ICCKernelCorpusMain

lean_exe icc_kernel_no_loss_check where
  root := `HeytingLean.CLI.ICCKernelNoLossCheckMain

lean_exe icc_kernel_proof_state where
  root := `HeytingLean.CLI.ICCKernelProofStateMain

lean_exe kernel_slice_export where
  root := `HeytingLean.CLI.KernelSliceExportMain

lean_exe kernel_slice_check where
  root := `HeytingLean.CLI.KernelSliceCheckMain

lean_exe kernel_assurance_mint where
  root := `HeytingLean.CLI.KernelAssuranceMintMain

lean_exe kernel_coverage where
  root := `HeytingLean.CLI.KernelCoverageMain

lean_exe kernel_obligation_check where
  root := `HeytingLean.CLI.KernelObligationCheckMain

lean_exe kernel_obligation_assurance_mint where
  root := `HeytingLean.CLI.KernelObligationAssuranceMintMain

lean_exe kernel_obligation_assurance_verify where
  root := `HeytingLean.CLI.KernelObligationAssuranceVerifyMain

lean_exe sky_replay where
  root := `HeytingLean.CLI.SKYReplay

-- LeanClef MLIR export: emit ICC terms as Inet MLIR text.
lean_exe leanclef_mlir where
  root := `HeytingLean.LeanClef.CLI.LeanClefMLIRMain

-- LeanClef verified checker: run buildProgram + checkProgram on test inputs.
lean_exe leanclef_check where
  root := `HeytingLean.LeanClef.CLI.LeanClefCheckMain

-- LeanClef HVM3 emitter: emit ICC terms as HVM3 source text for GPU reduction.
lean_exe leanclef_hvm3 where
  root := `HeytingLean.LeanClef.CLI.LeanClefHVM3Main

-- LeanClef GPU pipeline: verified check → HVM3 emission → GPU execution.
lean_exe leanclef_gpu where
  root := `HeytingLean.LeanClef.CLI.LeanClefGPUMain

-- LeanClef benchmark: standard reduction vs HVM3 interaction net reduction.
lean_exe leanclef_bench where
  root := `HeytingLean.LeanClef.CLI.LeanClefBenchMain

-- LeanClef Inet FFI benchmark: 3-way comparison (Lean native vs Inet FFI vs HVM3).
-- Links against libinet_reduce (precompiled C reduction kernel).
lean_exe leanclef_inet_bench where
  root := `HeytingLean.LeanClef.CLI.LeanClefInetBenchMain
  moreLinkArgs := #[
    ((__dir__ / ".." / "projects" / "inet_mlir" / "lib" / "inet_reduce_ffi.o").toString),
    ((__dir__ / ".." / "projects" / "inet_mlir" / "lib" / "libinet_reduce_core.a").toString)
  ]

-- LeanCP C export: emit the SKY reducer lowering surface as concrete C source.
lean_exe leancp_export where
  root := `HeytingLean.CLI.LeanCPExportMain

-- LeanCP Rust export: translate C IR → Rust IR → .rs source text.
lean_exe leancp_export_rust where
  root := `HeytingLean.CLI.LeanCPExportRustMain

-- LeanCP WebAssembly export: translate C IR → Wasm IR → .wat text.
lean_exe leancp_export_wasm where
  root := `HeytingLean.CLI.LeanCPExportWasmMain

-- IteratedVirtual: dump helix/spiral embedding points as JSON (smoke-runnable with no args).
lean_exe iterated_virtual_spiral_dump where
  root := `HeytingLean.CLI.IteratedVirtualSpiralDumpMain

-- Bug Bounty Hunter (Phase 0): AlgebraIR checker CLI (deterministic JSON I/O).
lean_exe bounty_hunter_algebrair_cli where
  root := `HeytingLean.BountyHunter.CLI.AlgebraIRMain

-- Bug Bounty Hunter: minimal YulTextMini → AlgebraIR → CEI check (semantic spine smoke test).
lean_exe yultextmini_cei_check where
  root := `HeytingLean.BountyHunter.CLI.YulTextMiniCEICheckMain

lean_exe evm_trace_order_check where
  root := `HeytingLean.BountyHunter.CLI.EvmTraceOrderCheckMain

-- Bug Bounty Hunter (Phase 2 checkpoint): toy concrete replay for AlgebraIR traces.
lean_exe bounty_hunter_toy_replay_cli where
  root := `HeytingLean.BountyHunter.CLI.ToyReplayMain

-- Verified finite Heyting lenses: export lookup tables to C/Python + CAB certificates.
lean_exe lens_export where
  root := `HeytingLean.CLI.LensExportMain

-- IteratedVirtual spiral embedding: export a small C library + optional Python wrapper + CAB.
lean_exe spiral_export where
  root := `HeytingLean.CLI.SpiralExportMain

-- Verify CAB certificates produced by lens exports (and other CAB-exported bundles).
lean_exe cab_verify_export where
  root := `HeytingLean.CLI.CABVerifyExportMain

lean_exe verified_pqc_export where
  root := `HeytingLean.CLI.VerifiedPQCExportMain

-- SLICES (Chem/Materials): JSONL benchmark harness for encode/canonEncode/decode round-trips.
lean_exe slices_bench where
  root := `HeytingLean.CLI.SLICESBenchMain

-- Lean→Yul contract DSL: emit small example contracts as Yul object source.
lean_exe lean_yul_dsl_cli where
  root := `HeytingLean.CLI.LeanYulDSLMain

-- Lean contract specs (JSON) → emit Yul object + Solidity wrapper + verification bundle.
lean_exe lean_contracts_cli where
  root := `HeytingLean.CLI.LeanContractsMain

lean_exe alex_metrics where
  root := `HeytingLean.CLI.AlexMetrics

lean_exe tensor_eval where
  root := `HeytingLean.CLI.TensorEval

-- Tensor Logic: JSON rules + TSV facts (TensorLog-style)
lean_exe tensor_logic_cli where
  root := `HeytingLean.CLI.TensorLogicMain

-- Tensor Logic: export backend-neutral tensor graph IR JSON (for tensor backends / autodiff).
lean_exe tensor_logic_export_graph where
  root := `HeytingLean.CLI.TensorLogicExportGraphMain

-- Tensor Homology: Betti numbers from simplicial-complex TSV facts (vertex/edge/face_edge)
lean_exe tensor_homology_cli where
  root := `HeytingLean.CLI.TensorHomologyMain

lean_exe support_is_search_demo where
  root := `HeytingLean.CLI.SupportIsSearchDemoMain

-- Homology (computable): Betti numbers over F₂
lean_exe homology_cli where
  root := `HeytingLean.CLI.HomologyMain

-- Knot invariants: Conway and Alexander polynomial CLIs (Phase: surreal_knots)
lean_exe conway_cli where
  root := `HeytingLean.CLI.ConwayMain

lean_exe alexander_cli where
  root := `HeytingLean.CLI.AlexanderMain

-- FRI soundness executable (minimal harness)
lean_exe fri_soundness where
  root := `HeytingLean.CLI.FriSoundness

lean_exe lof_encode where
  root := `HeytingLean.CLI.LoFEncode

lean_exe omega_slice where
  root := `HeytingLean.CLI.OmegaSlice

-- LoF kernel slice: emit LoFPrimary eval as C and provide an expected truth table.
lean_exe lof_kernel_codegen_demo where
  root := `HeytingLean.CLI.LoFKernelCodegenDemoMain

-- LambdaIR kernel slice: emit verified nat-fragment functions as a C library for FFI.
lean_exe lambda_kernel_export where
  root := `HeytingLean.CLI.LambdaKernelExportMain

-- LambdaIR kernel slice (v1): export a finite spiral embedding table through the certified pipeline.
lean_exe lambda_spiral_export where
  root := `HeytingLean.CLI.LambdaSpiralExportMain

-- Euler/Sheaf/Surreal depth-10 kernel: certified LambdaIR→MiniC→C export bundle.
lean_exe euler_sheaf_surreal_export where
  root := `HeytingLean.CLI.EulerSheafSurrealExportMain

-- MiniC → WASM backend (Phase 1): emit WAT + optional assemble/run via wat2wasm/wasmtime.
lean_exe minic_wasm_export where
  root := `HeytingLean.CLI.MiniCWasmExportMain

-- MiniC → Stylus WASM bridge: emit a Stylus-compatible WAT/WASM module plus a Solidity wrapper.
lean_exe minic_stylus_export where
  root := `HeytingLean.CLI.MiniCStylusExportMain

-- MiniC → CosmWasm bridge: emit a CosmWasm-compatible WAT/WASM module (exports `instantiate/execute/query`).
lean_exe minic_cosmwasm_export where
  root := `HeytingLean.CLI.MiniCCosmWasmExportMain

-- MiniC → zkWASM bridge: emit a zkWASM-compatible WAT/WASM module (exports `zkmain`).
lean_exe minic_zkwasm_export where
  root := `HeytingLean.CLI.MiniCZkWasmExportMain

-- Futamura-1 demos (ProgramCalculus): compile-by-specialization for LambdaIR and SKY.
lean_exe futamura_lambda_ir_demo where
  root := `HeytingLean.CLI.FutamuraLambdaIRDemoMain

-- Same story, but with a nontrivial code type (`Nat` instead of `Bool`).
lean_exe futamura_lambda_ir_nat_demo where
  root := `HeytingLean.CLI.FutamuraLambdaIRNatDemoMain

lean_exe futamura_sky_demo where
  root := `HeytingLean.CLI.FutamuraSKYDemoMain

-- ProgramCalculus: adelic-ops interface harness (baseline instance).
lean_exe adelic_ops_demo where
  root := `HeytingLean.CLI.AdelicOpsDemoMain

-- Organic Alignment stack demos (WIP / executable QA hooks).
lean_exe tropical_relu_demo where
  root := `HeytingLean.CLI.TropicalReLUDemoMain

lean_exe free_energy_demo where
  root := `HeytingLean.CLI.FreeEnergyDemoMain

lean_exe rg_flow_demo where
  root := `HeytingLean.CLI.RGFlowDemoMain

lean_exe sheaf_diffusion_demo where
  root := `HeytingLean.CLI.SheafDiffusionDemoMain

lean_exe adelic_futamura_demo where
  root := `HeytingLean.CLI.AdelicFutamuraDemoMain

lean_exe organic_alignment_stack_test where
  root := `HeytingLean.CLI.OrganicAlignmentStackTestMain

-- LoF "Lean-from-LoF" Phase 4/5: tiny STLC checker compiled to SKY.
lean_exe lof_stlc_demo where
  root := `HeytingLean.CLI.LoFSTLCDemoMain

-- Phase 6 (optional): export a bounded SKY machine + AIG oracle artifact for FPGA demos.
lean_exe lof_stlc_fpga_export where
  root := `HeytingLean.CLI.LoFSTLCFPGAExportMain

-- Phase 15: LeanKernel → SKY end-to-end (data plane) demo CLI.
lean_exe lean4lean_sky_demo where
  root := `HeytingLean.CLI.Lean4LeanSKYMain

-- Phase 20: LeanKernel computation-plane (WHNF/DefEq/Infer) compiled to SKY + cross-validation.
lean_exe kernel_sky_demo where
  root := `HeytingLean.CLI.KernelSKYMain

-- Phase 25: FullKernelSKY (β/ζ/δ/ι + Infer/Check) compiled to SKY + cross-validation.
lean_exe full_kernel_sky_demo where
  root := `HeytingLean.CLI.FullKernelSKYMain

-- Persistent JSON-line oracle for amortizing FullKernelSKY compile/startup cost across many checks.
lean_exe full_kernel_sky_service where
  root := `HeytingLean.CLI.FullKernelSKYService

-- CCI certificate export/check CLIs
lean_exe export_cci where
  root := `HeytingLean.CLI.ExportCCI

lean_exe cci_check where
  root := `HeytingLean.CLI.CCICheck

-- OFI-specific CLI targets omitted intentionally (see WIP/ratchet_plan.md note).

-- Minimal OFI CLI computing a quick index from a tokenized target
lean_exe ofi_quick where
  root := `HeytingLean.CLI.OFIQuickMain

-- WPP multiway demo CLI
lean_exe wpp_multiway where
  root := `HeytingLean.CLI.WPPMultiwayMain

-- SKY (K/S/Y) multiway + branchial demo CLI
lean_exe sky_multiway_demo where
  root := `HeytingLean.CLI.SkyMultiwayMain

-- Differential (DiLL-style) SKY demo: small computable backend + runtime sanity checks.
lean_exe differential_sky_demo where
  root := `HeytingLean.CLI.DifferentialSKYDemoMain

-- Differentiable ATP orchestration: goal embedding + projected GD + lane switching + kernel check.
lean_exe differentiable_atp where
  root := `HeytingLean.CLI.DifferentiableATPMain

lean_exe node_activated_lens_frontier where
  root := `HeytingLean.CLI.NodeActivatedLensFrontierMain

lean_exe pi_search where
  root := `HeytingLean.PathIntegral.Main

-- Lens-transport benchmark runner: standard vs lens-transported search.
lean_exe lens_transport_bench where
  root := `HeytingLean.CLI.LensTransportBenchMain

-- Differentiable Dialectica demo: objective (baseline vs gradient) capability check.
lean_exe dialectica_gradient_demo where
  root := `HeytingLean.CLI.DialecticaGradientDemoMain

-- Lambda (de Bruijn β) multiway + branchial demo CLI
lean_exe lambda_multiway_demo where
  root := `HeytingLean.CLI.LambdaMultiwayMain

-- Wolfram (SetReplace-style) multiway + branchial demo CLI
lean_exe wolfram_multiway_demo where
  root := `HeytingLean.CLI.WolframMultiwayMain

-- Wolfram Physics WM148 demo (fresh vertices; Nat-based)
lean_exe wolfram_wm148_demo where
  root := `HeytingLean.CLI.WolframWM148Main

-- Wolfram Engine integration: lossless binary roundtrip + notebook runner
lean_exe wolfram_roundtrip where
  root := `HeytingLean.CLI.WolframRoundtripMain
-- OFI Set CLI: configurable U and target; computes ofiNat? over Set String

-- Lightweight OFI wrapper (minimal) to exercise runtime and emit main
lean_exe ofi_wrap where
  root := `HeytingLean.CLI.OFIWrapMain

-- Causal hull demo CLI
lean_exe causal_hull where
  root := `HeytingLean.CLI.CausalHullMain

-- Abstract Interpretation (interval demo) CLI
lean_exe absint_demo where
  root := `HeytingLean.CLI.AbsIntDemoMain

-- Walsh demo CLI
lean_exe walsh_demo where
  root := `HeytingLean.CLI.WalshDemoMain

-- SAT spectral metrics CLI (small CNF demo)
lean_exe sat_spectral where
  root := `HeytingLean.CLI.SATSpectralMain

-- Real constraints (semi-algebraic / CAD-adjacent) solver bridge (dReal via Docker)
lean_exe cad_solve where
  root := `HeytingLean.CLI.CADSolveMain

-- Real constraints: produce a SAT-witness certificate (offline-checkable)
lean_exe cad_certify where
  root := `HeytingLean.CLI.CADCertifyMain

-- Real constraints: offline verifier for `cad_certify` certificates
lean_exe cad_verify where
  root := `HeytingLean.CLI.CADVerifyMain

-- Filter/projector demo CLI
lean_exe filter_demo where
  root := `HeytingLean.CLI.FilterDemoMain

-- Graph spectral FT demo CLI
lean_exe graph_ft where
  root := `HeytingLean.CLI.GraphFTMain

-- DFTFloat demo CLI (general-N Float-based DFT)
lean_exe dft_float_demo where
  root := `HeytingLean.CLI.DFTFloatDemoMain

-- Fourier convolution check (tiny N; JSON report)
lean_exe fourier_check where
  root := `HeytingLean.CLI.FourierCheckMain

-- Flow geometry check (tiny trajectory metrics)
lean_exe flow_check where
  root := `HeytingLean.CLI.FlowCheckMain

-- Miranda computational dynamics (TKFT-style reachability spine) demo
lean_exe miranda_dynamics_demo where
  root := `HeytingLean.MirandaDynamics.DemoMain

-- Seismic physical-system integration: offline validator for JSON bundles.
lean_exe seismic_validate_demo where
  root := `HeytingLean.CLI.SeismicValidateMain

-- Miranda billiards: Cantor tape/head-index interleaving demo (computable spine only)
lean_exe miranda_billiards_demo where
  root := `HeytingLean.MirandaDynamics.Billiards.DemoMain

-- Miranda discrete halting ↔ periodic-orbit demo (fully mechanized reduction)
lean_exe miranda_discrete_demo where
  root := `HeytingLean.MirandaDynamics.Discrete.DemoMain

-- CDL / Para(Type) weight-tying smoke test
lean_exe cdl_demo where
  root := `HeytingLean.CDL.DemoMain

-- CDL: Mealy/coalgebra + ClosingTheLoop closure bridge smoke test
lean_exe cdl_mealy_demo where
  root := `HeytingLean.CDL.MealyDemoMain

-- CDL: emit tiny C via LambdaIR → MiniC → C (weight tying via diagonal)
lean_exe cdl_codegen_demo where
  root := `HeytingLean.CDL.CodegenDemoMain

-- Particle Lenia: emit verified C for artificial life simulation
lean_exe particle_lenia_codegen where
  root := `HeytingLean.ParticleLenia.CodegenMain

-- Tensor scaffold demo (optional)
lean_exe tensor_demo where
  root := `HeytingLean.CLI.TensorDemoMain

-- Reasoning scaffold demo (optional)
lean_exe reason_demo where
  root := `HeytingLean.CLI.ReasonDemoMain

-- SOC demo (optional)
lean_exe soc_demo where
  root := `HeytingLean.CLI.SOCDemoMain

-- Quantum demo (optional)
lean_exe quantum_demo where
  root := `HeytingLean.CLI.QuantumDemoMain

-- Quantum on a Laptop (Phase 4): emit TWA/MiniC-generated C to `dist/` and provide a driver main.
lean_exe twa_codegen_demo where
  root := `HeytingLean.CLI.TWACodegenDemoMain

-- Vacuum ↔ Ωᴿ + phase/frame/gravity bridge demo (optional)
lean_exe quantum_vacuum_bridge where
  root := `HeytingLean.CLI.QuantumVacuumBridgeMain

-- QGI + Ωᴿ phase demo (optional)
lean_exe quantum_qgi_phase where
  root := `HeytingLean.CLI.QuantumQGIMain

-- Quantum active inference demo (optional)
lean_exe q_active_infer where
  root := `HeytingLean.CLI.QActiveInferMain

-- Quantum entropy diagonal spectral-vs-entry runtime check
lean_exe qentropy_diag_demo where
  root := `HeytingLean.CLI.QEntropyDiagMain

-- String theory demo (optional)
lean_exe string_demo where
  root := `HeytingLean.CLI.StringDemoMain

-- Matula arborification demo (nat <-> rooted-tree executable roundtrips)
lean_exe matula_demo where
  root := `HeytingLean.CLI.MatulaDemoMain

-- CryptoSheaf demo CLI (Ωᴿ + site/presheaf scaffolding)
lean_exe crypto_sheaf_demo where
  root := `HeytingLean.CLI.CryptoSheafDemo

-- Pretty-printing variant (payload-only, line-broken)
lean_exe crypto_sheaf_demo_pretty where
  root := `HeytingLean.CLI.CryptoSheafDemoPretty

-- Contextuality/valuation demo (quiet JSON)
lean_exe crypto_sheaf_demo_context where
  root := `HeytingLean.CLI.CryptoSheafDemoContext

-- Constructor theory task-existence gate (JSON)
lean_exe constructor_task_gate where
  root := `HeytingLean.CLI.ConstructorTaskGateMain

lean_exe canon_smoke where
  root := `HeytingLean.Numbers.Surreal.Test.CanonSmoke

lean_exe proofs_smoke where
  root := `HeytingLean.Numbers.Surreal.Test.ProofsSmoke

-- Surreal forward/backward proof artifact demo
lean_exe surreal_bidirectional_demo where
  root := `HeytingLean.CLI.SurrealBidirectionalMain

-- Surreal transfinite birthday demo (toy, ordinal notation below ε₀)
lean_exe surreal_transfinite_demo where
  root := `HeytingLean.CLI.SurrealTransfiniteMain

-- Kauffman bracket polynomial demo (toy knot invariant)
lean_exe kauffman_bracket_demo where
  root := `HeytingLean.CLI.KauffmanBracketMain

-- Reidemeister move regression harness (knot theory, Phase 1)
lean_exe knot_moves_demo where
  root := `HeytingLean.CLI.KnotMovesMain

-- Temperley–Lieb cross-check demo (knot theory, Phase 2)
lean_exe tl_demo where
  root := `HeytingLean.CLI.TLDemoMain

-- Assembly metrics demo (Assembly Theory → ML JSON)
lean_exe assembly_metrics_demo where
  root := `HeytingLean.CLI.AssemblyMetricsMain

-- Eigenform / fixed-point demo (Kauffman Phase 3)
lean_exe eigenform_demo where
  root := `HeytingLean.CLI.EigenformDemoMain

-- EigenformSoup runtime parity bundle generator (WS8/WS9 QA support).
lean_exe eigenform_soup_parity where
  root := `HeytingLean.CLI.EigenformSoupParityMain

-- EigenformSoup trace parity bundle generator (protocol sweep support).
lean_exe eigenform_soup_trace_parity where
  root := `HeytingLean.CLI.EigenformSoupTraceParityMain

-- EigenformSoup SUBLEQ-lane trace parity bundle generator (comparison lane).
lean_exe eigenform_soup_subleq_trace_parity where
  root := `HeytingLean.CLI.EigenformSoupSubleqTraceParityMain

-- EigenformSoup native-runtime trace parity bundle generator.
lean_exe eigenform_soup_native_trace_parity where
  root := `HeytingLean.CLI.EigenformSoupNativeTraceParityMain

-- EigenformSoup noncomputable/theorem bridge card exporter.
lean_exe eigenform_soup_bridge_card where
  root := `HeytingLean.CLI.EigenformSoupBridgeCardMain

-- SKY Y-combinator eigenform demo (Kauffman Phase 5)
lean_exe sky_eigenform_demo where
  root := `HeytingLean.CLI.SKYEigenformDemoMain

-- Markov move regression harness (knot theory, Phase 4)
lean_exe markov_demo where
  root := `HeytingLean.CLI.MarkovDemoMain

-- Yang–Baxter braiding operator demo (quantum, Phase 4)
lean_exe yang_baxter_demo where
  root := `HeytingLean.CLI.YangBaxterDemoMain

-- Braid word ↔ presented braid group alignment demo (Phase 6)
lean_exe braid_perm_alignment_demo where
  root := `HeytingLean.CLI.BraidPermAlignmentMain

-- String Q-series canonicalization demo (optional)
lean_exe string_q_demo where
  root := `HeytingLean.CLI.StringQDemoMain

-- String Q-series from weights demo (optional)
lean_exe string_q_from_weights where
  root := `HeytingLean.CLI.StringQFromWeightsMain

-- Payments policy proofing CLIs
lean_exe pm_prove where
  root := `HeytingLean.Payments.CLI.PMProve

lean_exe pm_verify where
  root := `HeytingLean.Payments.CLI.PMVerify

-- LES co-tenant limiter policy oracle (Lean ABI JSON in/out).
lean_exe les_limiter_policy where
  root := `HeytingLean.CLI.LESLimiterPolicyMain

-- GQRE / Perona–Malik report verifier
lean_exe gqre_verify_pm where
  root := `HeytingLean.Exec.GQRE.VerifyPM

-- Emergence selector report checker
lean_exe emergence_select_check where
  root := `HeytingLean.Exec.Emergence.SelectMain

-- Spin-glass chaos / reentrance checker
lean_exe verify_chaos where
  root := `HeytingLean.Exec.SpinGlass.VerifyChaos

-- Birth / interior-nucleus export CLI for finite emergence experiments
lean_exe birth_export_bool where
  root := `HeytingLean.Exec.Birth.ExportMain

lean_exe birth_export_surreal where
  root := `HeytingLean.Exec.Birth.SurrealExportMain

-- Theorem and examples metadata CLIs
lean_exe examples_metadata where
  root := `HeytingLean.CLI.ExamplesMetadata
  supportInterpreter := true

lean_exe theorem_index where
  root := `HeytingLean.CLI.TheoremIndex

lean_exe theorem_metadata where
  root := `HeytingLean.CLI.TheoremMetadata
lean_exe theorem_diagram_export where
  root := `HeytingLean.CLI.TheoremDiagramExportMain

lean_exe lof_packet_export where
  root := `HeytingLean.CLI.LoFPacketExport

lean_exe tcb_metadata where
  root := `HeytingLean.CLI.TCBMetadataMain

-- Consensus core demo CLI
lean_exe consensus_demo where
  root := `HeytingLean.CLI.ConsensusDemo

-- Infra-level consensus demo CLI
lean_exe infra_demo where
  root := `HeytingLean.CLI.InfraDemo

-- Dimensional lenses / SKY / multiway demo CLI
lean_exe dimlens_demo where
  root := `HeytingLean.CLI.DimLensDemoMain

-- RZ dyadic / interval arithmetic demo CLI
lean_exe rz_demo where
  root := `HeytingLean.CLI.RZDemoMain

-- Certified Program Library (Bauer×Symbolica demo) CLIs
lean_exe cert_export_library where
  root := `HeytingLean.CLI.Certified.ExportLibraryMain

lean_exe cert_query where
  root := `HeytingLean.CLI.Certified.QueryMain

lean_exe cert_compose where
  root := `HeytingLean.CLI.Certified.ComposeMain

lean_exe cert_transport where
  root := `HeytingLean.CLI.Certified.TransportMain

lean_exe cert_verify_pipeline where
  root := `HeytingLean.CLI.Certified.VerifyPipelineMain

lean_exe cert_eval_pipeline where
  root := `HeytingLean.CLI.Certified.EvalPipelineMain

-- TT0 / certification CLIs
lean_exe cab_mint where
  root := `HeytingLean.Meta.LeanTT0.CLI.CABMintMain
  supportInterpreter := true

lean_exe cab_check where
  root := `HeytingLean.Meta.LeanTT0.CLI.CABCheckMain
  supportInterpreter := true

lean_exe kernel_commit where
  root := `HeytingLean.Meta.LeanTT0.CLI.KernelCommitMain
  supportInterpreter := true

lean_exe tt0_emit_manifest where
  root := `HeytingLean.Meta.LeanTT0.CLI.EmitManifestMain
  supportInterpreter := true

lean_exe tt0_replay_prove where
  root := `HeytingLean.Meta.LeanTT0.CLI.TT0ReplayProveMain
  supportInterpreter := true

lean_exe tt0_cert_check where
  root := `HeytingLean.Meta.LeanTT0.CLI.TT0CertCheckMain
  supportInterpreter := true
-- ERC / DeFi demo CLIs
lean_exe erc_demo where
  root := `HeytingLean.CLI.ERCDemo

lean_exe defi_demo where
  root := `HeytingLean.CLI.DeFiDemo

-- PEGv0 guard / R1CS demo CLI
lean_exe peg_demo where
  root := `HeytingLean.Blockchain.Contracts.CLI.PEGDemo

-- Commitment / signature demo CLIs
lean_exe commit_demo where
  root := `HeytingLean.CLI.CommitDemo

lean_exe sig_demo where
  root := `HeytingLean.CLI.SigDemo

-- Governance / privacy demo CLIs
lean_exe voting_demo where
  root := `HeytingLean.CLI.VotingDemo

lean_exe privacy_demo where
  root := `HeytingLean.CLI.PrivacyDemo

-- Economics demo CLI
lean_exe economics_demo where
  root := `HeytingLean.CLI.EconomicsDemo

-- External CCI certificate checker
lean_exe cci_external_check where
  root := `HeytingLean.CLI.CCIExternalCheck

lean_exe merkle_demo where
  root := `HeytingLean.CLI.MerkleDemo

lean_exe cab_audit_axioms where
  root := `HeytingLean.CLI.CabAudit.Axioms

lean_exe cab_audit_unsafe where
  root := `HeytingLean.CLI.CabAudit.Unsafe

lean_exe cab_audit_reflect where
  root := `HeytingLean.CLI.CabAudit.Reflect

lean_exe rollup_demo where
  root := `HeytingLean.CLI.RollupDemo

-- Proof2Vec extractor (Lean AST → JSON)
lean_exe proof2vec_extract where
  root := `HeytingLean.Embedding.CLI
  supportInterpreter := true

-- Proof2Vec telescope helper (decl → binder telescope JSON)
lean_exe proof2vec_telescope where
  root := `HeytingLean.Embedding.TelescopeCLI
  supportInterpreter := true

-- Kernel-faithful (Expr-level) exporter: Lean env → JSON (types/values + universes)
lean_exe lean_kernel_export where
  root := `HeytingLean.Bridges.LeanKernelExport
  supportInterpreter := true

-- Example fraud-proof validity demo CLI
lean_exe fraud_demo where
  root := `HeytingLean.CLI.FraudDemo

-- Example ZK bridge soundness demo CLI
lean_exe bridge_demo where
  root := `HeytingLean.CLI.BridgeDemo

-- Example range-proofs correctness demo CLI
lean_exe range_demo where
  root := `HeytingLean.CLI.RangeDemo

-- Example private-voting correctness demo CLI
lean_exe private_voting_demo where
  root := `HeytingLean.CLI.PrivateVotingDemo

-- Example anonymous-credentials correctness demo CLI
lean_exe anonymous_credentials_demo where
  root := `HeytingLean.CLI.AnonymousCredentialsDemo

-- CAB pipeline smoke tests
lean_exe pipeline_subset_smoke where
  root := `HeytingLean.Tests.PipelineSubsetSmoke

lean_exe pipeline_add2_smoke where
  root := `HeytingLean.Tests.PipelineAdd2Smoke

lean_exe pipeline_min2_smoke where
  root := `HeytingLean.Tests.PipelineMin2Smoke

-- Minimal backends/protocol skeleton demos
lean_exe groth16_demo where
  root := `HeytingLean.CLI.Groth16Demo

lean_exe bullet_demo where
  root := `HeytingLean.CLI.BulletDemo

lean_exe halo2_demo where
  root := `HeytingLean.CLI.Halo2Demo

lean_exe stark_demo where
  root := `HeytingLean.CLI.StarkDemo

lean_exe cairo_demo where
  root := `HeytingLean.CLI.CairoDemo

lean_exe zkevm_demo where
  root := `HeytingLean.CLI.ZkEvmDemo

lean_exe payment_channels_demo where
  root := `HeytingLean.CLI.PaymentChannelsDemo

lean_exe payment_channels_evm_demo where
  root := `HeytingLean.CLI.PaymentChannelsEVMDemo

-- Phase 3: trustless facilitator core demo
lean_exe facilitator_demo where
  root := `HeytingLean.CLI.FacilitatorDemoMain

-- Phase 3: emit verified tiny-C for facilitator kernel
lean_exe facilitator_codegen_demo where
  root := `HeytingLean.CLI.FacilitatorCodegenDemoMain

lean_exe cci_crypto_export where
  root := `HeytingLean.CLI.CCICryptoExport

lean_exe cci_crypto_check where
  root := `HeytingLean.CLI.CCICryptoCheck

-- Rosetta / Ω_R diagram export CLI (visualization scaffolding)
lean_exe rosetta_diagram_export where
  root := `HeytingLean.CLI.RosettaDiagramExport

-- LambdaIR / nat pipeline tests
lean_exe test_lambda_ir_basics where
  root := `HeytingLean.Tests.LambdaIR

lean_exe test_minic_basics where
  root := `HeytingLean.Tests.MiniC

lean_exe test_minic_wasm_backend where
  root := `HeytingLean.Tests.MiniCWasmBackend

lean_exe test_lambda_ir_from_leancore_v2 where
  root := `HeytingLean.Tests.LambdaIRFromLeanCoreV2

lean_exe test_lambda_ir_to_minic where
  root := `HeytingLean.Tests.LambdaIRToMiniC

lean_exe test_leancore_v2_basics where
  root := `HeytingLean.Tests.LeanCoreV2

lean_exe test_leancore_basics where
  root := `HeytingLean.Tests.LeanCoreBasics

-- TT0 / TCB / security tests
lean_exe test_poseidon_native where
  root := `HeytingLean.Tests.PoseidonDeterminism

lean_exe test_merkle_correctness where
  root := `HeytingLean.Tests.MerkleCorrectness

lean_exe test_proof_lifecycle where
  root := `HeytingLean.Tests.ProofLifecycle

lean_exe test_proof_tampering where
  root := `HeytingLean.Tests.ProofTampering

lean_exe test_tcb_metadata where
  root := `HeytingLean.Tests.TCBMetadata

lean_exe test_constraints where
  root := `HeytingLean.Tests.ConstraintBenchmarks

lean_exe test_security where
  root := `HeytingLean.Tests.SecurityValidation

lean_exe test_reproducibility where
  root := `HeytingLean.Tests.Reproducibility

lean_exe test_witness_verification where
  root := `HeytingLean.Tests.WitnessVerification

lean_exe test_sha256_vectors where
  root := `Tests.SHA256Vectors

lean_exe test_budget_window where
  root := `HeytingLean.Tests.BudgetWindow

lean_exe test_verifier_parity where
  root := `HeytingLean.Tests.VerifierParity

-- PQC workspace: initial scaffolding (no executables yet)
/-!
  Note: Executables for KAT runners and parity will be added once
  the corresponding Lean modules are implemented.
-/

-- PQC KAT runners (scaffold)
lean_exe kem_kat_runner where
  root := `HeytingLean.CLI.KEMKATRunner

lean_exe dsa_kat_runner where
  root := `HeytingLean.CLI.DSAKATRunner

-- PQC parity + toy demos (Lean-only runners)
lean_exe kem_parity where
  root := `HeytingLean.CLI.KEMParity

lean_exe dsa_parity where
  root := `HeytingLean.CLI.DSAParity

lean_exe kem_keygen_demo where
  root := `HeytingLean.CLI.KEMDemo

lean_exe dsa_sign_demo where
  root := `HeytingLean.CLI.DSADemo
